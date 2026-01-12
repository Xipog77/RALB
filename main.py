import sys
import math
import csv
import time
from collections import deque
from pysat.solvers import Solver
from pysat.formula import IDPool
from pysat.card import CardEnc
from pysat.pb import PBEnc


# =============================================================================
# 1. DATA READING & BOUNDS CALCULATION
# =============================================================================
def read_and_process_data(filepath, num_stations):
    """Đọc dữ liệu và tính toán LB/UB ngay lập tức."""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            Na = sum(1 for _ in f) - 1
    except FileNotFoundError:
        print(f"File not found: {filepath}")
        sys.exit(1)

    T = [{} for _ in range(Na)]
    adj = [[] for _ in range(Na)]
    neighbors = [[0] * Na for _ in range(Na)]  # Dùng cho tính UB cũ

    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            reader = csv.DictReader(f, delimiter='\t')
            robot_cols = [c for c in reader.fieldnames if c.lower().startswith("robot")]
            Nr = len(robot_cols)

            for row in reader:
                task = int(row['Task']) - 1
                succ_str = row['Successor'].strip()
                if succ_str:
                    for s in succ_str.split(','):
                        succ = int(s.strip()) - 1
                        adj[task].append(succ)
                        neighbors[task][succ] = 1
                for r_idx, col in enumerate(robot_cols):
                    T[task][r_idx] = int(row[col])
    except Exception as e:
        print(f"Error reading data: {e}")
        sys.exit(1)

    # --- TÍNH LB ---
    T_min = [min(T[j].values()) if T[j] else 0 for j in range(Na)]
    p = sorted(T_min, reverse=True)
    prefix = [0]
    for x in p: prefix.append(prefix[-1] + x)

    LB = 0
    for k in range(1, len(p) + 1):
        val = math.ceil(prefix[k] / ((k + num_stations - 1) // num_stations))
        LB = max(LB, int(val))

    # --- TÍNH UB ---
    indeg = [0] * Na
    for u in range(Na):
        for v in adj[u]: indeg[v] += 1

    q = deque([i for i in range(Na) if indeg[i] == 0])
    dist = [0] * Na
    while q:
        u = q.popleft()
        finish_u = dist[u] + T_min[u]
        for v in adj[u]:
            dist[v] = max(dist[v], finish_u)
            indeg[v] -= 1
            if indeg[v] == 0: q.append(v)

    max_dist = max([dist[i] + T_min[i] for i in range(Na)]) if Na else 0
    UB = max(int(math.ceil(max_dist)), LB)

    return Na, Nr, T, adj, LB, UB


# =============================================================================
# 2. CORE SOLVER LOGIC
# =============================================================================
def build_static_constraints(solver, vpool, Na, Nr, Nw, adj):
    """Tạo các biến và ràng buộc cứng (không đổi)."""
    # Tạo Map ID biến
    X = [[vpool.id(f'X_{j}_{s}') for s in range(Nw)] for j in range(Na)]
    Y = [[vpool.id(f'Y_{s}_{r}') for r in range(Nr)] for s in range(Nw)]
    Z = {}  # Dictionary mapping (j, s, r) -> id

    # 1. Assignment Constraints
    for j in range(Na):
        for c in CardEnc.equals(X[j], 1, vpool=vpool).clauses:
            solver.add_clause(c)
    for s in range(Nw):
        for c in CardEnc.equals(Y[s], 1, vpool=vpool).clauses:
            solver.add_clause(c)

    # 2. Precedence Constraints
    for u in range(Na):
        for v in adj[u]:
            for s_u in range(Nw):
                for s_v in range(s_u):
                    solver.add_clause([-X[u][s_u], -X[v][s_v]])

    # 3. Z Variable linking (Z <-> X and Y)
    # Tạo trước tất cả Z để tránh check lại nhiều lần
    for j in range(Na):
        for s in range(Nw):
            for r in range(Nr):
                z = vpool.id(f'Z_{j}_{s}_{r}')
                Z[(j, s, r)] = z
                x = X[j][s]
                y = Y[s][r]
                solver.add_clause([-z, x])
                solver.add_clause([-z, y])
                solver.add_clause([-x, -y, z])

    return X, Y, Z


def solve_schedule(filepath, num_stations):
    # 1. Đọc dữ liệu
    Na, Nr, T, adj, LB, UB = read_and_process_data(filepath, num_stations)

    print(f"Bounds: [{LB}, {UB}]")

    # 2. Khởi tạo Solver & Variables
    vpool = IDPool()
    # LƯU Ý: Không dùng incremental=True trong hàm khởi tạo để tránh lỗi TypeError
    solver = Solver(name='glucose4')

    # 3. Xây dựng ràng buộc tĩnh
    X, Y, Z = build_static_constraints(solver, vpool, Na, Nr, num_stations, adj)

    # 4. Binary Search
    low, high = LB, UB
    best_K = -1
    best_model = None

    start_time = time.time()

    while low <= high:
        mid = (low + high) // 2

        # --- Check Feasibility for K = mid ---
        selector = vpool.id(f'SEL_{mid}')

        # Tạo constraints: Tổng thời gian mỗi trạm <= mid
        for s in range(num_stations):
            lits, weights = [], []
            for j in range(Na):
                for r in range(Nr):
                    t_val = T[j][r]
                    if t_val > 0:
                        lits.append(Z[(j, s, r)])
                        weights.append(t_val)

            if lits:
                # PB Constraint guarded by Selector
                # Clause gốc: (A v B) -> Guarded: (-selector v A v B)
                cnf = PBEnc.leq(lits, weights, mid, vpool=vpool)
                for clause in cnf.clauses:
                    solver.add_clause([-selector] + clause)

        # Giải với assumption
        if solver.solve(assumptions=[selector]):
            best_K = mid
            best_model = solver.get_model()
            high = mid - 1
        else:
            low = mid + 1

    runtime = time.time() - start_time

    # 5. Decode kết quả (nếu có)
    result = None
    if best_model:
        model_set = set(best_model)
        result = {}
        s_robot = {}
        # Tìm robot cho trạm
        for s in range(num_stations):
            for r in range(Nr):
                if Y[s][r] in model_set:
                    s_robot[s] = r
                    break
        # Tìm task cho trạm
        for j in range(Na):
            for s in range(num_stations):
                if X[j][s] in model_set:
                    r = s_robot.get(s, -1)
                    result[j] = {'station': s, 'robot': r, 'time': T[j][r]}
                    break

    solver.delete()
    return best_K, result, runtime


# =============================================================================
# MAIN
# =============================================================================
if __name__ == "__main__":
    INPUT_FILE = "Dataset2.txt"
    NUM_STATIONS = 3

    ct, sol, duration = solve_schedule(INPUT_FILE, NUM_STATIONS)

    if sol:
        print(f"Optimal Cycle Time: {ct}")
        print(f"Runtime: {duration:.4f}s")

        # In chi tiết
        st_loads = [0] * NUM_STATIONS
        st_tasks = [[] for _ in range(NUM_STATIONS)]
        st_rob_map = {}

        for j, info in sol.items():
            s = info['station']
            st_tasks[s].append((j, info['time']))
            st_loads[s] += info['time']
            st_rob_map[s] = info['robot']

        for s in range(NUM_STATIONS):
            rid = st_rob_map.get(s, -1)
            rname = f"Robot {rid + 1}" if rid != -1 else "None"
            print(f"Station {s + 1} ({rname}) | Load: {st_loads[s]}")
            for tid, t in st_tasks[s]:
                print(f"  Task {tid + 1:02d} ({t}s)")
    else:
        print("No solution found.")