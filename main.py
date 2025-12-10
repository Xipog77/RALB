import time
import math
import csv
from pysat.pb import PBEnc
from collections import defaultdict, deque
from pysat.solvers import Glucose42
from pysat.formula import IDPool

Na = 0  # Number of tasks
Nw = 3  # Number of workstations
Nr = 0  # Number of robots
w1 = 1  # Weight for Cycle Time
w2 = 0  # Weight for Energy
LB = int()  # Lower Bound
UB = int()  # Upper Bound
CT = int()  # Cycle Time

# Data structures
var_map = {}
var_counter = 1
var_manager = None  # Initialized in optimize
clauses = []
# previous_solutions = [] # Không cần list này nữa vì sẽ add trực tiếp vào solver

T = defaultdict(dict)  # T[j][r]: time for robot r to do task j
graph = defaultdict(list)  # graph[j]: successors of task j
adj = []
EP = defaultdict(dict)
time_end = []  # Latest start time
visited = []
neighbors = []
reversed_neighbors = []
toposort = []
ip1 = []
ip2 = []


# =============================================================================
# 2. SAT VARIABLE HELPER FUNCTIONS
# =============================================================================
def get_var(name, *args):
    global var_manager
    key = (name,) + args
    if key not in var_map:
        var_map[key] = var_manager.id()
    return var_map[key]


def set_var(var, name, *args):
    key = (name,) + args
    if key not in var_map:
        var_map[key] = var
    return var_map[key]


def get_key(value):
    for key, val in var_map.items():
        if val == value:
            return key


# =============================================================================
# 3. INPUT / OUTPUT FUNCTIONS
# =============================================================================
def read_data(file_path):
    global T, graph, Na, Nr, adj, neighbors, reversed_neighbors
    T.clear()
    graph.clear()
    adj.clear()

    # --- LẤY Na SỚM ---
    with open(file_path, 'r', encoding='utf-8') as f:
        # bỏ dòng header, đếm các dòng dữ liệu
        Na = sum(1 for _ in f) - 1  # -1 vì trừ dòng header

    neighbors = [[0 for i in range(Na)] for j in range(Na)]
    reversed_neighbors = [[0 for i in range(Na)] for j in range(Na)]

    with open(file_path, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f, delimiter='\t')
        robot_cols = [col for col in reader.fieldnames if col.lower().startswith("robot")]
        Nr_detected = len(robot_cols)

        for row in reader:
            task = int(row['Task']) - 1
            successors = []
            if row['Successor'].strip():
                successors = [int(s.strip()) - 1 for s in row['Successor'].split(',')]
                # Tạo danh sách cạnh cho adj
                for succ in successors:
                    adj.append((task, succ))  # <<< thêm cạnh (task → successor)
                    neighbors[task][succ] = 1
                    reversed_neighbors[succ][task] = 1
            graph[task] = successors

            for r_index, col_name in enumerate(robot_cols):
                T[task][r_index] = int(row[col_name])

    # Na = len(T)
    Nr = Nr_detected
    print(f"Đọc dữ liệu thành công! Tasks: {Na}, Robots: {Nr}")
    return


def print_solution(assignment):
    print("\n=== Task Assignment ===")
    station_runtime = [0 for _ in range(Nw)]
    for j in range(Na):
        s = assignment[j]['station']
        r = assignment[j]['robot']
        if s != -1 and r != -1:
            station_runtime[s] += T[j][r]
            print(f"Task {j + 1} → Station {s + 1}, Robot {r + 1}")
        else:
            print(f"Task {j + 1} → Assignment incomplete.")

    ct_result = max(station_runtime) if station_runtime else 0
    print(f"\nCycle Time (CT) Result: {ct_result}")


def get_solution(this_solution):
    assignment = defaultdict(lambda: {'station': -1, 'robot': -1, 'runtime': -1})
    solution = []  # Đây chính là blocking clause (các biến S phủ định)

    for var in this_solution:
        key = get_key(var)
        if not key:
            continue
        if key[0] == 'X':
            j, s = key[1], key[2]
            assignment[j]['station'] = s
        elif key[0] == 'Y':
            s, r = key[1], key[2]
            for j in range(Na):
                if assignment[j]['station'] == s:
                    assignment[j]['robot'] = r
        elif key[0] == 'S':
            j, t = key[1], key[2]
            solution.append(-get_var('S', j, t))

    station_runtime = [0 for _ in range(Nw)]
    total_energy = 0

    for j in range(Na):
        s = assignment[j]['station']
        r = assignment[j]['robot']
        if s != -1 and r != -1:
            time_val = T[j][r]
            station_runtime[s] += time_val
            # total_energy  += time_val * EP[r]
            total_energy += time_val * 0

    return assignment, station_runtime, solution, total_energy


def Preprocess(Nw, Na, T, neighbors):
    # ================================================
    # PHẦN 1: CHUẨN HÓA INPUT + T_min
    # ================================================
    T_min = []
    time_list = [0] * Na

    for j in range(Na):
        if T[j]:
            tmin = min(T[j].values())
            T_min.append(tmin)
            time_list[j] = tmin
        else:
            time_list[j] = 0
            T_min.append(0)

    # ================================================
    # PHẦN 2: TÍNH LB (LB3 Logic)
    # ================================================
    # Sắp xếp giảm dần để tính prefix sum
    p = sorted(T_min, reverse=True)
    prefix = [0]
    for x in p:
        prefix.append(prefix[-1] + x)

    LB = 0
    for k in range(1, len(p) + 1):
        S_k = prefix[k]
        m = (k + Nw - 1) // Nw  # ceil(k / Nw)
        LB3_k = S_k / m
        LB = int(max(LB, LB3_k))

    # ================================================
    # PHẦN 3: TOPOLOGICAL SORT & UB (Critical Path Logic)
    # ================================================
    # Kết hợp tính Topo sort và Critical Path bằng Kahn's Algorithm
    indeg = [0] * Na
    for u in range(Na):
        for v in range(Na):
            if neighbors[u][v]:
                indeg[v] += 1

    # Hàng đợi cho các node có bậc vào = 0
    q = deque([i for i in range(Na) if indeg[i] == 0])
    toposort = []

    # Mảng lưu đường dài nhất đến node v (để tính Critical Path)
    dist = [0] * Na

    while q:
        u = q.popleft()
        toposort.append(u)

        # Cập nhật thời gian hoàn thành sớm nhất của u (tính cả thời gian của chính nó)
        current_finish_time = dist[u] + T_min[u]

        for v in range(Na):
            if neighbors[u][v]:
                # Cập nhật dist[v] dựa trên u
                dist[v] = max(dist[v], current_finish_time)

                indeg[v] -= 1
                if indeg[v] == 0:
                    q.append(v)

    if len(toposort) != Na:
        print("Graph có chu trình → Không xác định được UB chính xác (UB = sum(T_min))")
        UB = sum(T_min)
    else:
        # Critical Path là giá trị lớn nhất trong mảng dist + thời gian của node cuối cùng
        # Tuy nhiên logic dist ở trên là start time, ta cần tính max finish time
        max_dist = 0
        for i in range(Na):
            max_dist = max(max_dist, dist[i] + T_min[i])
        UB = max_dist

    CT = int(math.ceil(UB))  # UB đóng vai trò CT ban đầu

    # ================================================
    # PHẦN 4: EARLIEST / LATEST START & MATRICES (ip1, ip2)
    # ================================================
    # Khởi tạo ma trận
    earliest_start = [[-10 ** 9 for _ in range(Nw)] for _ in range(Na)]
    latest_start = [[10 ** 9 for _ in range(Nw)] for _ in range(Na)]

    ip1 = [[0 for _ in range(Nw)] for _ in range(Na)]
    ip2 = [[[0 for _ in range(CT + 1)] for _ in range(Nw)] for _ in range(Na)]

    # --- Forward pass (Duyệt theo chiều Topo) ---
    for j in toposort:
        k = 0
        earliest_start[j][k] = 0

        for i in range(Na):
            if neighbors[i][j] == 1:
                earliest_start[j][k] = max(
                    earliest_start[j][k],
                    earliest_start[i][k] + time_list[i]
                )

        # Logic điều chỉnh k (trạm) trong forward pass
        temp_k = k
        current_es = earliest_start[j][temp_k]

        while current_es > CT - time_list[j]:
            ip1[j][temp_k] = 1
            temp_k += 1
            if temp_k >= Nw:
                break
            pass

        if temp_k < Nw:
            # Tính lại ES chuẩn xác nhất cho trạm hợp lệ đầu tiên
            final_es = 0
            for i in range(Na):
                if neighbors[i][j] == 1:
                    final_es = max(final_es, earliest_start[i][0] + time_list[i])  # Giả định k=0 cho pre-tasks

            for t in range(int(final_es)):
                if t <= CT:
                    ip2[j][temp_k][t] = 1

    # --- Backward pass (Duyệt ngược Topo) ---
    reverse_topo = toposort[::-1]

    for j in reverse_topo:
        k = Nw - 1
        latest_start[j][k] = CT - time_list[j]

        for i in range(Na):
            if neighbors[j][i] == 1:
                latest_start[j][k] = min(
                    latest_start[j][k],
                    latest_start[i][k] - time_list[j]
                )

        temp_k = k
        current_ls = latest_start[j][temp_k]

        while current_ls < 0:
            ip1[j][temp_k] = 1
            temp_k -= 1
            if temp_k < 0:
                break

        if temp_k >= 0:
            final_ls = CT - time_list[j]
            for i in range(Na):
                if neighbors[j][i] == 1:
                    final_ls = min(final_ls, latest_start[i][Nw - 1] - time_list[j])

            if final_ls >= 0:
                for t in range(int(final_ls) + 1, CT):
                    if t <= CT:
                        ip2[j][temp_k][t] = 1

    return UB, LB, ip1, ip2, CT, toposort


# =============================================================================
# 5. CLAUSE GENERATION
# =============================================================================
def Fixed_clauses():
    global CT, time_end, var_manager, adj, w1, w2, ip1, ip2
    time_end = [max(0, CT - min(T[j].values())) for j in range(Na)]
    fixed_clauses = []

    for j in range(Na):

        set_var(get_var('X', j, 0), "R", j, 0)
        for k in range(1, Nw - 1):
            if ip1[j][k] == 1:
                set_var(get_var("R", j, k - 1), "R", j, k)
            else:
                fixed_clauses.append([-get_var("R", j, k - 1), get_var("R", j, k)])
                fixed_clauses.append([-get_var('X', j, k), get_var("R", j, k)])
                fixed_clauses.append([-get_var('X', j, k), -get_var("R", j, k - 1)])
                fixed_clauses.append([get_var('X', j, k), get_var("R", j, k - 1), -get_var("R", j, k)])
        # last machine
        if ip1[j][Nw - 1] == 1:
            fixed_clauses.append([get_var("R", j, Nw - 2)])
        else:
            fixed_clauses.append([get_var("R", j, Nw - 2), get_var('X', j, Nw - 1)])
            fixed_clauses.append([-get_var("R", j, Nw - 2), -get_var('X', j, Nw - 1)])

    for (i, j) in adj:
        for k in range(Nw - 1):
            if ip1[i][k + 1] == 1:
                continue
            fixed_clauses.append([-get_var("R", j, k), -get_var('X', i, k + 1)])

    for j in range(Na):
        fixed_clauses.append([get_var('X', j, s) for s in range(Nw)])

    for j in range(Na):
        for s1 in range(Nw):
            for s2 in range(s1 + 1, Nw):
                fixed_clauses.append([-get_var('X', j, s1), -get_var('X', j, s2)])

    # (3) Mỗi trạm được gán cho đúng một robot

    for s in range(Nw):
        fixed_clauses.append([get_var('Y', s, r) for r in range(Nr)])

    for s in range(Nw):
        for r1 in range(Nr):
            for r2 in range(r1 + 1, Nr):
                fixed_clauses.append([-get_var('Y', s, r1), -get_var('Y', s, r2)])
    #
    # (4) - (5) - (6)

    for j in range(Na):
        for s in range(Nw):
            for r in range(Nr):
                fixed_clauses.append([-get_var('X', j, s), -get_var('Y', s, r), get_var('Z', j, s, r)])
                fixed_clauses.append([-get_var('Z', j, s, r), get_var('X', j, s)])
                fixed_clauses.append([-get_var('Z', j, s, r), get_var('Y', s, r)])

    # (7) Mỗi công việc phải được khởi động đúng một lần bởi một robot

    for j in range(Na):
        fixed_clauses.append([get_var('S', j, t) for t in range(CT)])

    for j in range(Na):
        for t1 in range(CT):
            for t2 in range(t1 + 1, time_end[j]):
                fixed_clauses.append([-get_var('S', j, t1), -get_var('S', j, t2)])

    # (8) Không khởi động công việc ngoài thời điểm cho phép
    # Cải tiến: gộp lại với (7)

    for j in range(Na):
        for r in range(Nr):
            for t in range(time_end[j] + 1, CT):
                fixed_clauses.append([-get_var('S', j, t)])
    #
    # (9) Không có hai công việc chạy cùng lúc tại cùng một trạm
    # Cải tiến: tạo một tập các công việc có thể được gán vào s

    for s in range(Nw):
        for j1 in range(Na):
            for j2 in range(j1 + 1, Na):
                if (ip1[j1][s] == 1 or ip1[j2][s] == 1):
                    continue
                for t in range(CT):
                    fixed_clauses.append(
                        [-get_var('X', j1, s), -get_var('X', j2, s), -get_var('A', j1, s, t), -get_var('A', j2, s, t)])

    # (10) Công việc đã khởi động thì phải ở trạng thái chạy
    for j in range(Na):
        for s in range(Nw):
            for r in range(Nr):
                for t1 in range(0, time_end[j]):
                    # for t1 in range(0, CT):
                    for t2 in range(t1, min(t1 + T[j][r], CT)):
                        fixed_clauses.append([-get_var('S', j, t1), get_var('A', j, t2)])
    #
    # (11) Nếu cùng trạm, công việc i phải hoàn thành trước j
    # Cải tiến: kết hợp với (9)
    for s in range(Nw):
        for j1 in range(Na):
            for j2 in graph[j1]:
                for t in range(CT):
                    fixed_clauses.append(
                        [-get_var('X', j1, s), -get_var('X', j2, s), -get_var('S', j1, t), -get_var('S', j2, t)])

    # (12) Cấm gán công việc vào trạm không hợp lệ do tiền nhiệm
    for j in range(Na):
        for k in range(Nw):
            if ip1[j][k] == 1:
                fixed_clauses.append([-get_var('X', j, k)])
                continue
            # 11
            for t in range(0, time_end[j]):
                if ip2[j][k][t] == 1:
                    fixed_clauses.append([-get_var('X', j, k), -get_var('S', j, t)])

    return fixed_clauses


def Dynamic_clauses(K):
    # Hàm này chỉ trả về các mệnh đề liên quan đến giới hạn K (Pseudo-Boolean constraints)
    # KHÔNG thêm previous_solutions tại đây nữa (xử lý ở Main Loop)
    dynamic_clauses = []
    for s in range(Nw):
        vars_ = []
        coeffs = []
        for j in range(Na):
            for r in range(Nr):
                z_var = get_var('Z', j, s, r)
                vars_.append(z_var)
                # coeff = w1 * T[j][r] + w2 * T[j][r] * EP[r]
                coeff = w1 * T[j][r] + w2 * T[j][r] * 0
                coeffs.append(coeff)

        if vars_:
            cnf_part = PBEnc.leq(lits=vars_, weights=coeffs, bound=K, vpool=var_manager)
            dynamic_clauses.extend(cnf_part.clauses)

    return dynamic_clauses


# =============================================================================
# 7. MAIN OPTIMIZATION LOOP
# =============================================================================
def optimize():
    global var_map, var_counter, clauses, CT, time_end
    global var_manager, LB, UB, ip
    best_solution = None
    best_z3 = float('inf')

    print(f"🎯 Tìm kiếm nghiệm trong khoảng K = [{LB}, {UB}]")

    var_map = {}
    var_counter = 1
    var_manager = IDPool()
    left, right = LB, UB
    timeout_count = 0
    max_timeout = 5
    total_start = time.perf_counter()

    # 1. Khởi tạo Solver một lần duy nhất
    solver = Glucose42(incr=True)

    # 2. Thêm các ràng buộc cố định (không phụ thuộc K)
    fixed_clauses = Fixed_clauses()
    for clause in fixed_clauses:
        solver.add_clause(clause)

    while left <= right and timeout_count < max_timeout:
        K = int((left + right) / 2)
        iter_start = time.perf_counter()
        time_end = [max(0, CT - min(T[j].values())) for j in range(Na)]

        # 3. Tạo biến selector cho giả định (Assumption)
        # Biến này sẽ kích hoạt tập các mệnh đề ràng buộc K
        selector = var_manager.id()

        dynamic_clauses_k = Dynamic_clauses(K)

        # 4. Biến đổi Dynamic clauses: (Clause) -> (-selector v Clause)
        # Nếu selector = True (được assume) -> Clause gốc phải thỏa mãn
        # Nếu selector không được assume -> Mệnh đề luôn đúng (do -selector), không ảnh hưởng solver
        assumption_clauses = []
        for clause in dynamic_clauses_k:
            assumption_clauses.append(clause + [-selector])

        solver.append_formula(assumption_clauses)

        # 5. Gọi solve với assumption
        if solver.solve(assumptions=[selector]):
            model = solver.get_model()
            this_solution = [var for var in model if var > 0]
            assignment, station_runtime, solution_blocking, total_energy = get_solution(this_solution)

            actual_ct = max(station_runtime) if station_runtime else 0
            actual_e = total_energy
            z3_value = w1 * actual_ct + w2 * actual_e

            print(f"✅ Có nghiệm khả thi với Z3 = {z3_value:.2f} (CT={actual_ct}, E={actual_e:.2f})")

            if z3_value < best_z3:
                best_z3 = z3_value
                best_solution = assignment
                # previous_solutions logic: Thêm blocking clause vĩnh viễn vào solver
                # Để đảm bảo không tìm lại nghiệm y hệt (nếu cần) hoặc chỉ đơn giản là đã tìm được
                # một mốc tốt hơn.
                # Lưu ý: solution_blocking trả về từ get_solution là list [-S_j_t...].
                solver.add_clause(solution_blocking)

            # Giảm giới hạn K để tìm nghiệm nhỏ hơn
            right = K - 1
        else:
            # Không tìm thấy nghiệm với assumption selector -> K không thỏa mãn
            # Không cần reset solver, chỉ cần không assume selector này nữa là xong.
            print(f"❌ Không tìm thấy nghiệm cho K = {K}")
            left = K + 1

        iter_end = time.perf_counter()
        print(f"⏱ Thời gian vòng lặp: {iter_end - iter_start:.2f} giây\n")

    total_end = time.perf_counter()
    total_elapsed = total_end - total_start
    # === KẾT THÚC ĐO THỜI GIAN ===

    if best_solution:
        print(f"\n🎉 NGHIỆM TỐI ƯU CUỐI CÙNG: Z3 = {best_z3:.2f}")
        print(f"⏳ Tổng thời gian chạy: {total_elapsed:.2f} giây")
        print_solution(best_solution)



# =============================================================================
# 8. EXECUTION ENTRY POINT
# =============================================================================
def main():
    global Na, Nw, Nr, T, LB, UB, CT, ip1, ip2, toposort, neighbors

    try:
        read_data("Dataset2.txt")
        UB, LB, ip1, ip2, CT, toposort = Preprocess(Nw, Na, T, neighbors)
        optimize()

    except FileNotFoundError:
        print("❌ Không tìm thấy file")
    except Exception as e:
        print(f"❌ Lỗi: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    main()