import time
import math
import csv
from pysat.pb import PBEnc
from collections import defaultdict, deque
from pysat.solvers import Glucose42
from pysat.formula import IDPool

# =============================================================================
# 1. GLOBAL VARIABLES & CONFIG
# =============================================================================
Na = 0  # Number of tasks
Nw = 3  # Number of workstations
Nr = 0  # Number of robots
w1 = 1  # Weight for Cycle Time
w2 = 0  # Weight for Energy (Not fully used yet)

# Data structures
var_map = {}
var_manager = None
T = defaultdict(dict)  # T[j][r]
graph = defaultdict(list)
adj = []
neighbors = []
ip1 = []  # Station feasibility
ip2 = []  # Time feasibility (legacy support)


# =============================================================================
# 2. SAT VARIABLE HELPER FUNCTIONS
# =============================================================================
def get_var(name, *args):
    global var_manager, var_map
    key = (name,) + args
    if key not in var_map:
        var_map[key] = var_manager.id()
    return var_map[key]


def get_key(value):
    for key, val in var_map.items():
        if val == value:
            return key
    return None


# =============================================================================
# 3. INPUT / OUTPUT FUNCTIONS
# =============================================================================
def read_data(file_path):
    global T, graph, Na, Nr, adj, neighbors
    T.clear()
    graph.clear()
    adj.clear()

    with open(file_path, 'r', encoding='utf-8') as f:
        Na = sum(1 for _ in f) - 1

    neighbors = [[0 for i in range(Na)] for j in range(Na)]

    with open(file_path, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f, delimiter='\t')
        robot_cols = [col for col in reader.fieldnames if col.lower().startswith("robot")]
        Nr = len(robot_cols)

        for row in reader:
            task = int(row['Task']) - 1
            if row['Successor'].strip():
                successors = [int(s.strip()) - 1 for s in row['Successor'].split(',')]
                for succ in successors:
                    adj.append((task, succ))
                    neighbors[task][succ] = 1
                graph[task] = successors

            for r_index, col_name in enumerate(robot_cols):
                T[task][r_index] = int(row[col_name])

    print(f"✅ Đọc dữ liệu thành công! Tasks: {Na}, Robots: {Nr}")


def get_solution(this_solution):
    assignment = defaultdict(lambda: {'station': -1, 'robot': -1})
    solution_blocking = []

    for var in this_solution:
        key = get_key(var)
        if not key: continue

        if key[0] == 'X':
            assignment[key[1]]['station'] = key[2]
        elif key[0] == 'Y':
            # Logic: Y(s, r) -> tìm các task ở s gán r
            s, r = key[1], key[2]
            for j in range(Na):
                if assignment[j]['station'] == s:
                    assignment[j]['robot'] = r
        elif key[0] == 'S':
            # Lưu lại thời điểm bắt đầu để tạo blocking clause
            solution_blocking.append(-var)

    station_runtime = [0] * Nw
    total_energy = 0

    for j in range(Na):
        s = assignment[j]['station']
        r = assignment[j]['robot']
        if s != -1 and r != -1:
            station_runtime[s] += T[j][r]
            # total_energy += T[j][r] * EP[r] # Nếu có EP

    return assignment, station_runtime, solution_blocking, total_energy


def print_solution(assignment, runtime, z3):
    print("\n=== KẾT QUẢ TỐI ƯU ===")
    print(f"Cycle Time (CT): {max(runtime)}")
    print(f"Objective Z3: {z3}")
    print("-" * 30)
    for j in range(Na):
        s = assignment[j]['station']
        r = assignment[j]['robot']
        print(f"Task {j + 1:02d} | Station {s + 1} | Robot {r + 1} | Time: {T[j][r]}")


# =============================================================================
# 4. PREPROCESS (IMPROVED with ES/LS)
# =============================================================================
# =============================================================================
# 4. PREPROCESS (FIXED: SAFE BOUNDS)
# =============================================================================
def Preprocess():
    global Na, Nw, T, neighbors

    # --- 1. Tính toán T_min (cho LB) và T_max (cho UB) ---
    T_min = [min(T[j].values()) if T[j] else 0 for j in range(Na)]
    T_max = [max(T[j].values()) if T[j] else 0 for j in range(Na)]

    # --- 2. Lower Bound (LB) dùng T_min (Logic cũ vẫn đúng cho LB) ---
    p = sorted(T_min, reverse=True)
    prefix = [0]
    for x in p: prefix.append(prefix[-1] + x)

    LB = 0
    for k in range(1, len(p) + 1):
        LB = max(LB, math.ceil(prefix[k] / ((k + Nw - 1) // Nw)))

    # --- 3. Topo Sort & Upper Bound (UB) dùng T_MAX (QUAN TRỌNG) ---
    # Dùng T_max để đảm bảo UB là một cận trên an toàn tuyệt đối
    indeg = [0] * Na
    for u in range(Na):
        for v in range(Na):
            if neighbors[u][v]: indeg[v] += 1

    q = deque([i for i in range(Na) if indeg[i] == 0])
    toposort = []

    # Tính đường găng (Critical Path) dựa trên T_MAX
    earliest_finish = [0] * Na

    while q:
        u = q.popleft()
        toposort.append(u)
        current_finish = earliest_finish[u] + T_max[u]

        for v in range(Na):
            if neighbors[u][v]:
                earliest_finish[v] = max(earliest_finish[v], current_finish)
                indeg[v] -= 1
                if indeg[v] == 0: q.append(v)

    # UB an toàn (Safe UB)
    UB = max([earliest_finish[i] + T_max[i] for i in range(Na)]) if toposort else sum(T_max)
    CT_init = int(UB)

    # --- 4. Tính ES và LS (Nới lỏng LS) ---
    # ES tính theo T_min (sớm nhất có thể)
    ES = [0] * Na
    dist_start = [0] * Na
    for u in toposort:
        ES[u] = dist_start[u]
        for v in range(Na):
            if neighbors[u][v]:
                dist_start[v] = max(dist_start[v], ES[u] + T_min[u])

    # LS tính theo T_min nhưng với Deadline là CT_init (đã được nới lỏng theo T_max)
    # Điều này tạo ra Time Window rộng hơn, tránh việc cắt bỏ nghiệm đúng.
    LS = [CT_init] * Na
    dist_end = [CT_init] * Na

    for u in reversed(toposort):
        deadline = dist_end[u]
        LS[u] = max(0, deadline - T_min[u])  # Vẫn dùng T_min để LS rộng nhất có thể

        for k in range(Na):
            if neighbors[k][u]:
                dist_end[k] = min(dist_end[k], LS[u])

    # --- 5. IP Matrices (Station Feasibility) ---
    ip1 = [[0] * Nw for _ in range(Na)]

    # Forward pass
    est_station = [0] * Na
    for j in toposort:
        max_prev_st = -1
        for i in range(Na):
            if neighbors[i][j]:
                max_prev_st = max(max_prev_st, est_station[i])
        est_station[j] = max(0, max_prev_st)
        for s in range(est_station[j]): ip1[j][s] = 1

    # Backward pass
    lst_station = [Nw - 1] * Na
    for j in reversed(toposort):
        min_next_st = Nw
        for i in range(Na):
            if neighbors[j][i]:
                min_next_st = min(min_next_st, lst_station[i])
        lst_station[j] = min(Nw - 1, min_next_st)
        for s in range(lst_station[j] + 1, Nw): ip1[j][s] = 1

    print(f"--- Preprocess (Safe Bounds) ---")
    print(f"LB: {LB}, UB (Safe): {UB}")

    return UB, LB, ip1, toposort, ES, LS


# =============================================================================
# 5. CLAUSE GENERATION (FIXED: Added Precedence)
# =============================================================================
def Fixed_clauses(ES, LS, max_CT):
    global ip1, adj
    clauses = []

    # 1. Assignment (X, Y, Z)
    for j in range(Na):
        valid_stations = [s for s in range(Nw) if ip1[j][s] == 0]
        clauses.append([get_var('X', j, s) for s in valid_stations])
        for s1 in range(Nw):
            for s2 in range(s1 + 1, Nw):
                clauses.append([-get_var('X', j, s1), -get_var('X', j, s2)])
        for s in range(Nw):
            if ip1[j][s] == 1: clauses.append([-get_var('X', j, s)])

    for s in range(Nw):
        clauses.append([get_var('Y', s, r) for r in range(Nr)])
        for r1 in range(Nr):
            for r2 in range(r1 + 1, Nr):
                clauses.append([-get_var('Y', s, r1), -get_var('Y', s, r2)])

    # Link Z <-> X, Y
    for j in range(Na):
        for s in range(Nw):
            if ip1[j][s] == 1: continue
            for r in range(Nr):
                z = get_var('Z', j, s, r)
                clauses.append([-z, get_var('X', j, s)])
                clauses.append([-z, get_var('Y', s, r)])
                clauses.append([-get_var('X', j, s), -get_var('Y', s, r), z])

    # 2. Station Precedence
    for (i, j) in adj:
        for si in range(Nw):
            if ip1[i][si] == 1: continue
            for sj in range(Nw):
                if ip1[j][sj] == 1: continue
                if si > sj:
                    clauses.append([-get_var('X', i, si), -get_var('X', j, sj)])

    # 3. Time Constraints (S, A) with SAFE WINDOWS
    for j in range(Na):
        valid_start_times = range(ES[j], min(max_CT, LS[j] + 1))

        if not valid_start_times:
            # Fallback nếu cửa sổ bị lỗi (hiếm khi xảy ra với Safe UB)
            print(f"⚠️ Task {j} empty window [{ES[j]}, {LS[j]}]. Relaxing...")
            valid_start_times = range(0, max_CT)

        clauses.append([get_var('S', j, t) for t in valid_start_times])
        for t1 in valid_start_times:
            for t2 in valid_start_times:
                if t1 < t2:
                    clauses.append([-get_var('S', j, t1), -get_var('S', j, t2)])

        # Biến A (Active)
        for s in range(Nw):
            if ip1[j][s] == 1: continue
            for r in range(Nr):
                dur = T[j][r]
                z_var = get_var('Z', j, s, r)
                for t_start in valid_start_times:
                    t_end = min(max_CT, t_start + dur)
                    for t_run in range(t_start, t_end):
                        clauses.append([-z_var, -get_var('S', j, t_start), get_var('A', j, t_run)])

    # 4. Resource Constraints (No overlap at same station)
    for s in range(Nw):
        possible_tasks = [j for j in range(Na) if ip1[j][s] == 0]
        for idx1 in range(len(possible_tasks)):
            j1 = possible_tasks[idx1]
            for idx2 in range(idx1 + 1, len(possible_tasks)):
                j2 = possible_tasks[idx2]

                # Check Overlap Potential
                max_dur_j1 = max(T[j1].values())
                max_dur_j2 = max(T[j2].values())

                if LS[j1] + max_dur_j1 <= ES[j2] or LS[j2] + max_dur_j2 <= ES[j1]:
                    continue

                common_start = max(ES[j1], ES[j2])
                common_end = min(LS[j1] + max_dur_j1, LS[j2] + max_dur_j2)

                if common_end > common_start:
                    for t in range(common_start, min(max_CT, common_end)):
                        clauses.append([-get_var('X', j1, s), -get_var('X', j2, s),
                                        -get_var('A', j1, t), -get_var('A', j2, t)])

    # 5. TASK PRECEDENCE (QUAN TRỌNG: Thêm lại để đảm bảo đúng thứ tự)
    # Nếu i -> j, thì Start(j) >= Start(i) + Min_Dur(i)
    # Đây là ràng buộc tối thiểu. Để chính xác tuyệt đối cần phụ thuộc Robot,
    # nhưng ràng buộc này đủ để tránh lỗi logic cơ bản và UNSAT.
    for (i, j) in adj:
        min_dur_i = min(T[i].values())
        valid_start_i = range(ES[i], min(max_CT, LS[i] + 1))
        valid_start_j = range(ES[j], min(max_CT, LS[j] + 1))

        for ti in valid_start_i:
            for tj in valid_start_j:
                if ti + min_dur_i > tj:
                    # Cấm trường hợp j bắt đầu trước khi i (với robot nhanh nhất) hoàn thành
                    clauses.append([-get_var('S', i, ti), -get_var('S', j, tj)])

    return clauses


# =====

def Dynamic_clauses(K):
    global w1, w2
    # Constraint: sum(Z[j][s][r] * cost) <= K for each station s
    clauses = []
    for s in range(Nw):
        lits = []
        coeffs = []
        for j in range(Na):
            if ip1[j][s] == 1: continue
            for r in range(Nr):
                lits.append(get_var('Z', j, s, r))
                cost = w1 * T[j][r] + w2 * 0  # Energy = 0 for now
                coeffs.append(int(cost))

        if lits:
            pb_cnf = PBEnc.leq(lits=lits, weights=coeffs, bound=K, vpool=var_manager)
            clauses.extend(pb_cnf.clauses)
    return clauses


# =============================================================================
# 6. MAIN OPTIMIZATION LOOP
# =============================================================================
def optimize(UB, LB, ES, LS):
    global var_manager, var_map

    var_manager = IDPool()
    var_map = {}

    print(f"\n🚀 Khởi tạo Solver với Time Window [{0}, {UB}]")

    # Generate Fixed Clauses ONCE
    fixed = Fixed_clauses(ES, LS, UB)

    solver = Glucose42(incr=True)
    for c in fixed:
        solver.add_clause(c)

    print(f"✅ Fixed Clauses: {len(fixed)} added.")

    left, right = int(LB), int(UB)
    best_z3 = float('inf')
    best_solution = None

    start_time = time.perf_counter()

    while left <= right:
        # Binary Search Step
        K = (left + right) // 2

        # Assumption variable for this K
        selector = var_manager.id()

        dynamic = Dynamic_clauses(K)
        # Transform: clause -> clause v -selector
        assumptions = [c + [-selector] for c in dynamic]
        solver.append_formula(assumptions)

        print(f"🔎 Checking K = {K} ... ", end="")

        if solver.solve(assumptions=[selector]):
            model = solver.get_model()
            this_sol = [v for v in model if v > 0]
            assignment, runtimes, blocking, _ = get_solution(this_sol)

            actual_z3 = max(runtimes)  # Since w1=1, w2=0

            print(f"✅ Feasible! Actual Z3 = {actual_z3}")

            if actual_z3 < best_z3:
                best_z3 = actual_z3
                best_solution = (assignment, runtimes)
                solver.add_clause(blocking)  # Block this specific assignment

            # GUIDED SEARCH: Jump to actual_z3 - 1
            # If we found solution with cost 80, no need to check 99, 90...
            right = min(K - 1, actual_z3 - 1)

        else:
            print(f"❌ Unsatisfiable.")
            left = K + 1

    total_time = time.perf_counter() - start_time
    print(f"\n🏁 HOÀN THÀNH trong {total_time:.2f}s")

    if best_solution:
        print_solution(best_solution[0], best_solution[1], best_z3)
    else:
        print("Không tìm thấy nghiệm.")


# =============================================================================
# 7. ENTRY POINT
# =============================================================================
def main():
    global ip1, ip2
    try:
        # Giả định file có tên Dataset2.txt cùng thư mục
        read_data("Dataset2.txt")

        # Preprocess để lấy bound và window
        UB, LB, ip1, toposort, ES, LS = Preprocess()

        # Chạy tối ưu
        optimize(UB, LB, ES, LS)

    except FileNotFoundError:
        print("❌ Lỗi: Không tìm thấy file 'Dataset2.txt'")
    except Exception as e:
        print(f"❌ Lỗi runtime: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    main()