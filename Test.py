import time, math, csv
from collections import defaultdict, deque
from pysat.pb import PBEnc
from pysat.formula import IDPool, WCNF
from pysat.examples.rc2 import RC2

# ================= GLOBAL =================
Nw = 3
Na = Nr = 0
T = defaultdict(dict)
adj = []
neighbors = []
LB = UB = 0
vpool = None

# ================= VAR =================
def var(name, *args):
    return vpool.id((name,) + args)

# ================= READ DATA =================
def read_data(path):
    global Na, Nr, T, adj, neighbors
    T.clear(); adj.clear()

    with open(path) as f:
        Na = sum(1 for _ in f) - 1

    neighbors = [[0]*Na for _ in range(Na)]

    with open(path) as f:
        rd = csv.DictReader(f, delimiter="\t")
        robots = [c for c in rd.fieldnames if c.lower().startswith("robot")]
        Nr = len(robots)

        for row in rd:
            j = int(row["Task"]) - 1

            succ = row["Successor"].strip()
            if succ:
                for s in succ.split(","):
                    s = s.strip()
                    if s:
                        i = int(s) - 1
                        adj.append((j, i))
                        neighbors[j][i] = 1

            for r, c in enumerate(robots):
                T[j][r] = int(row[c])

# ================= PREPROCESS =================
def preprocess():
    global LB, UB
    Tmin = [min(T[j].values()) for j in range(Na)]

    # LB
    p = sorted(Tmin, reverse=True)
    pref = [0]
    for x in p: pref.append(pref[-1] + x)
    LB = max(math.ceil(pref[k] / ((k + Nw - 1) // Nw)) for k in range(1, Na + 1))

    # UB (critical path)
    indeg = [0] * Na
    for u, v in adj: indeg[v] += 1

    q = deque(i for i in range(Na) if indeg[i] == 0)
    dist = [0] * Na

    while q:
        u = q.popleft()
        for v in range(Na):
            if neighbors[u][v]:
                dist[v] = max(dist[v], dist[u] + Tmin[u])
                indeg[v] -= 1
                if indeg[v] == 0:
                    q.append(v)

    UB = max(dist[i] + Tmin[i] for i in range(Na))

# ================= HARD =================
def hard_clauses(wcnf):
    # Task → exactly one station
    for j in range(Na):
        xs = [var("X", j, s) for s in range(Nw)]
        wcnf.append(xs)
        for i in range(Nw):
            for k in range(i + 1, Nw):
                wcnf.append([-xs[i], -xs[k]])

    # Precedence
    for i, j in adj:
        for si in range(Nw):
            for sj in range(si):
                wcnf.append([-var("X", i, si), -var("X", j, sj)])

    # Station → exactly one robot
    for s in range(Nw):
        ys = [var("Y", s, r) for r in range(Nr)]
        wcnf.append(ys)
        for r1 in range(Nr):
            for r2 in range(r1 + 1, Nr):
                wcnf.append([-ys[r1], -ys[r2]])

    # Z ↔ X ∧ Y
    for j in range(Na):
        for s in range(Nw):
            for r in range(Nr):
                z = var("Z", j, s, r)
                x = var("X", j, s)
                y = var("Y", s, r)
                wcnf.append([-z, x])
                wcnf.append([-z, y])
                wcnf.append([-x, -y, z])

# ================= SOFT =================
def soft_clauses(wcnf):
    for j in range(Na):
        for s in range(Nw):
            for r in range(Nr):
                wcnf.append([-var("Z", j, s, r)], weight=T[j][r])

# ================= PB =================
def pb_clauses(K):
    cls = []
    for s in range(Nw):
        lits, w = [], []
        for j in range(Na):
            for r in range(Nr):
                lits.append(var("Z", j, s, r))
                w.append(T[j][r])
        if lits:
            cnf = PBEnc.leq(
                lits=lits,
                weights=w,
                bound=K,
                vpool=vpool
            )
            cls.extend(cnf.clauses)
    return cls

# ================= SOLVE =================
def solve(dataset):
    global vpool
    read_data(dataset)
    preprocess()

    start = time.perf_counter()
    best_CT, best_cost = None, None

    low, high = LB, UB
    while low <= high:
        K = (low + high) // 2
        vpool = IDPool()
        wcnf = WCNF()

        hard_clauses(wcnf)
        soft_clauses(wcnf)

        with RC2(wcnf) as rc2:
            for c in pb_clauses(K):
                rc2.add_clause(c)

            model = rc2.compute()
            if model:
                best_CT = K
                best_cost = rc2.cost
                high = K - 1
            else:
                low = K + 1

    return best_CT, best_cost, time.perf_counter() - start

# ================= MAIN =================
if __name__ == "__main__":
    print(f"{'Dataset':12} | {'CT*':5} | {'SoftCost':9} | Time(s)")
    print("-" * 45)

    for f in ["Dataset1.txt", "Dataset2.txt"]:
        try:
            ct, cost, t = solve(f)
            print(f"{f:12} | {ct:<5} | {cost:<9} | {t:.3f}")
        except Exception as e:
            print(f"{f:12} | ERROR: {e}")

# Cell 2: Mã nguồn chính
import time
import math
import csv
import subprocess
import os
from pysat.pb import PBEnc
from pysat.card import CardEnc
from pysat.formula import IDPool, CNF
from collections import defaultdict

# =============================================================================
# 1. ĐỌC DỮ LIỆU (Giữ nguyên logic của bạn)
# =============================================================================
Nw = 3  # Số trạm (Bạn có thể thay đổi tùy bài toán)
Na = 0  # Số task
Nr = 0  # Số robot

T = defaultdict(dict)
graph = defaultdict(list)
adj = []  # Lưu danh sách các cặp ưu tiên (i, j)


def read_data(file_path):
    global T, graph, Na, Nr, adj
    T.clear()
    graph.clear()
    adj = []

    # Tạo file mẫu nếu chưa có để test
    if not os.path.exists(file_path):
        print(f"Không thấy file {file_path}, đang tạo dữ liệu giả lập...")
        with open(file_path, "w") as f:
            f.write("Task\tSuccessor\tRobot 1\tRobot 2\n")
            f.write("1\t2,3\t10\t15\n")
            f.write("2\t4\t20\t25\n")
            f.write("3\t4\t15\t10\n")
            f.write("4\t\t10\t10\n")

    with open(file_path, 'r') as f:
        reader = csv.DictReader(f, delimiter='\t')
        fieldnames = reader.fieldnames
        robot_columns = [col for col in fieldnames if col.lower().startswith('robot')]
        Nr = len(robot_columns)

        for row in reader:
            task = int(row['Task']) - 1
            successors = [int(s.strip()) - 1 for s in row['Successor'].split(',')] if row['Successor'].strip() else []
            graph[task] = successors
            for succ in successors:
                adj.append((task, succ))

            T[task] = [0] * Nr
            for i, robot_col in enumerate(robot_columns):
                T[task][i] = int(row[robot_col])

    Na = len(T)
    print(f"Dataset Loaded: Tasks={Na}, Robots={Nr}")


# =============================================================================
# 2. XÂY DỰNG MÔ HÌNH CNF (SAT Encoding)
# =============================================================================
def build_cnf_model(cycle_time_limit):
    """
    Tạo ra công thức CNF kiểm tra xem có tồn tại lời giải với CT <= cycle_time_limit hay không.
    """
    cnf = CNF()
    vpool = IDPool()

    # --- Biến số ---
    # X[j][s]: Task j gán vào Station s
    def x_var(j, s):
        return vpool.id(f'X_{j}_{s}')

    # Y[s][r]: Station s gán Robot r
    def y_var(s, r):
        return vpool.id(f'Y_{s}_{r}')

    # Z[j][s][r]: Task j ở Station s dùng Robot r (Linearization)
    def z_var(j, s, r):
        return vpool.id(f'Z_{j}_{s}_{r}')

    # --- Ràng buộc ---

    # 1. Mỗi Task được gán vào đúng 1 Trạm (Eq. 8)
    for j in range(Na):
        lits = [x_var(j, s) for s in range(Nw)]
        cnf.extend(CardEnc.equals(lits=lits, bound=1, vpool=vpool))

    # 2. Mỗi Trạm được gán đúng 1 Robot (Eq. 9)
    for s in range(Nw):
        lits = [y_var(s, r) for r in range(Nr)]
        cnf.extend(CardEnc.equals(lits=lits, bound=1, vpool=vpool))

    # 3. Ràng buộc ưu tiên (Precedence) (Eq. 7)
    # Nếu i -> j thì Station(i) <= Station(j)
    # Nghĩa là: Nếu i ở trạm s, thì j KHÔNG THỂ ở trạm s' < s
    for (i, j) in adj:
        for s in range(Nw):
            for s_prime in range(s):
                # X[i][s] -> NOT X[j][s_prime]  <=>  -X[i][s] OR -X[j][s_prime]
                cnf.append([-x_var(i, s), -x_var(j, s_prime)])

    # 4. Linearization Z (Eq. 10-12)
    # Z[j][s][r] <-> X[j][s] AND Y[s][r]
    for j in range(Na):
        for s in range(Nw):
            for r in range(Nr):
                x = x_var(j, s)
                y = y_var(s, r)
                z = z_var(j, s, r)
                # Z -> X
                cnf.append([-z, x])
                # Z -> Y
                cnf.append([-z, y])
                # X AND Y -> Z
                cnf.append([-x, -y, z])

    # 5. Ràng buộc Cycle Time (Eq. 13-14)
    # Tổng thời gian tại mỗi trạm s <= cycle_time_limit
    # Sum(Z[j][s][r] * T[j][r]) <= K
    for s in range(Nw):
        lits = []
        weights = []
        for j in range(Na):
            for r in range(Nr):
                t_val = T[j][r]
                if t_val > 0:  # Chỉ thêm nếu có tốn thời gian
                    lits.append(z_var(j, s, r))
                    weights.append(t_val)

        # Sử dụng Pseudo-Boolean Encoding để chuyển ràng buộc tổng trọng số thành CNF
        if lits:
            pb_clauses = PBEnc.leq(lits=lits, weights=weights, bound=cycle_time_limit, vpool=vpool)
            cnf.extend(pb_clauses)

    return cnf, vpool


# =============================================================================
# 3. GỌI PAINLESS SOLVER
# =============================================================================
def solve_with_painless(cnf_formula):
    filename = "problem.cnf"
    cnf_formula.to_file(filename)

    # Gọi Painless binary
    # -c 4: Sử dụng 4 cores (tùy chỉnh theo Colab)
    # Sử dụng đường dẫn tuyệt đối
    painless_path = os.path.abspath("painless/painless")
    cmd = [painless_path, "-c", "4", filename]

    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)  # Timeout 60s
        output = result.stdout

        if "s SATISFIABLE" in output:
            # Parse model từ output của Painless (dòng bắt đầu bằng 'v')
            model = []
            for line in output.splitlines():
                if line.startswith("v"):
                    parts = line.split()[1:]
                    model.extend([int(x) for x in parts])
            return model
        else:
            return None  # UNSAT
    except subprocess.TimeoutExpired:
        print("Timeout!")
        return None


# =============================================================================
# 4. GIẢI MÃ KẾT QUẢ
# =============================================================================
def print_solution(model, vpool):
    if not model:
        print("Không tìm thấy lời giải.")
        return

    # Chuyển model list thành set để tra cứu nhanh
    model_set = set(model)

    print("\n--- KẾT QUẢ PHÂN CÔNG ---")
    station_load = [0] * Nw
    station_robot = {}

    # Tìm robot cho mỗi trạm
    for s in range(Nw):
        for r in range(Nr):
            if vpool.id(f'Y_{s}_{r}') in model_set:
                station_robot[s] = r
                break

    # In task và tính load
    for s in range(Nw):
        r_idx = station_robot.get(s, -1)
        tasks_in_station = []
        load = 0
        for j in range(Na):
            # Kiểm tra xem X_j_s có đúng không
            if vpool.id(f'X_{j}_{s}') in model_set:
                time_val = T[j][r_idx]
                tasks_in_station.append(f"Task {j + 1} ({time_val}s)")
                load += time_val

        station_load[s] = load
        print(f"Trạm {s + 1} [Robot {r_idx + 1}]: {', '.join(tasks_in_station)} | Tổng thời gian: {load}")

    print(f"\nCycle Time thực tế: {max(station_load)}")
    print(f"Tổng Năng lượng (Er): {sum(station_load)}")  # Giả sử EP_r = 1 (hoặc tính lại theo công thức)


# =============================================================================
# 5. MAIN: TỐI ƯU HÓA (BINARY SEARCH)
# =============================================================================
def optimize_cycle_time():
    # 1. Tính toán Bounds cho Cycle Time
    # Lower Bound (LB): Tổng thời gian chia số trạm (lý tưởng)
    # Upper Bound (UB): Tổng thời gian làm bởi 1 trạm
    min_total_time = sum(min(T[j]) for j in range(Na))
    max_total_time = sum(max(T[j]) for j in range(Na))

    lb = math.ceil(min_total_time / Nw)
    ub = max_total_time

    best_model = None
    best_ct = ub

    print(f"Bắt đầu tìm kiếm nhị phân cho Cycle Time trong khoảng [{lb}, {ub}]...")

    while lb <= ub:
        mid = (lb + ub) // 2
        print(f"  > Kiểm tra Cycle Time = {mid}...", end=" ")

        cnf, vpool = build_cnf_model(mid)
        model = solve_with_painless(cnf)

        if model:
            print("SAT! (Thỏa mãn)")
            best_model = model
            best_ct = mid
            best_vpool = vpool  # Lưu lại để decode
            ub = mid - 1  # Thử tìm thời gian nhỏ hơn
        else:
            print("UNSAT. (Cần tăng thời gian)")
            lb = mid + 1

    if best_model:
        print(f"\n>>> TÌM THẤY TỐI ƯU TOÀN CỤC: Cycle Time = {best_ct}")
        print_solution(best_model, best_vpool)
    else:
        print("Không tìm thấy lời giải khả thi.")


# --- CHẠY CHƯƠNG TRÌNH ---
read_data("Dataset1.txt")  # Đảm bảo file này tồn tại hoặc để code tự tạo file mẫu
optimize_cycle_time()