import time
import math
import csv
import subprocess
import os
from pysat.pb import PBEnc
from pysat.formula import IDPool, CNF
from collections import defaultdict, deque

# =============================================================================
# 1. BIẾN TOÀN CỤC (GLOBALS)
# =============================================================================
PAINLESS_BIN = os.path.abspath("./painless/painless")
TEMP_CNF = "temp_run.cnf"  # Dùng 1 file tạm cố định để đỡ rác

# Cấu hình bài toán
Nw = 3  # Số trạm (Cố định hoặc đọc từ file nếu cần)
Na = 0  # Số task
Nr = 0  # Số robot

# Dữ liệu
T = defaultdict(dict)
adj = []
neighbors = []
var_manager = None

# Biến tính toán
LB = 0
UB = 0
CT = 0


# =============================================================================
# 2. CÁC HÀM XỬ LÝ (CORE FUNCTIONS)
# =============================================================================

def reset_globals():
    """Xóa sạch dữ liệu cũ trước khi nạp bài mới"""
    global Na, Nr, T, adj, neighbors, LB, UB, CT
    Na = 0
    Nr = 0
    T.clear()
    adj.clear()
    neighbors = []
    LB = 0
    UB = 0
    CT = 0


def get_var(name, *args):
    """Lấy ID biến SAT"""
    global var_manager
    key = (name,) + args
    return var_manager.id(key)


def read_data(file_path):
    """Đọc file và nạp vào biến toàn cục"""
    global Na, Nr, T, adj, neighbors

    # 1. Đếm số dòng (Tasks)
    with open(file_path, 'r', encoding='utf-8') as f:
        Na = sum(1 for _ in f) - 1

    neighbors = [[0 for _ in range(Na)] for _ in range(Na)]

    # 2. Đọc chi tiết
    with open(file_path, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f, delimiter='\t')
        robot_cols = [col for col in reader.fieldnames if col.lower().startswith("robot")]
        Nr = len(robot_cols)

        for row in reader:
            task = int(row['Task']) - 1

            # Xử lý Successor
            if row['Successor'] and row['Successor'].strip():
                successors = [int(s.strip()) - 1 for s in row['Successor'].split(',')]
                for succ in successors:
                    adj.append((task, succ))
                    neighbors[task][succ] = 1

            # Xử lý Thời gian Robot
            for r_idx, col_name in enumerate(robot_cols):
                T[task][r_idx] = int(row[col_name])


def preprocess():
    """Tính LB, UB để khoanh vùng tìm kiếm"""
    global LB, UB, CT

    # Lấy min time của mỗi task (bất kể robot nào)
    T_min = []
    for j in range(Na):
        t = min(T[j].values()) if T[j] else 0
        T_min.append(t)

    # 1. Tính Lower Bound (LB)
    p = sorted(T_min, reverse=True)
    prefix = [0]
    for x in p: prefix.append(prefix[-1] + x)

    LB = 0
    for k in range(1, len(p) + 1):
        val = int(math.ceil(prefix[k] / ((k + Nw - 1) // Nw)))
        if val > LB: LB = val

    # 2. Tính Upper Bound (UB) - Đường găng (Critical Path)
    # Dùng Kahn's Algo để tính đường dài nhất
    indeg = [0] * Na
    for u in range(Na):
        for v in range(Na):
            if neighbors[u][v]: indeg[v] += 1

    q = deque([i for i in range(Na) if indeg[i] == 0])
    dist = [0] * Na  # dist[u] là thời gian sớm nhất u hoàn thành

    while q:
        u = q.popleft()
        current_finish = dist[u] + T_min[u]
        for v in range(Na):
            if neighbors[u][v]:
                dist[v] = max(dist[v], current_finish)
                indeg[v] -= 1
                if indeg[v] == 0: q.append(v)

    UB = 0
    for i in range(Na):
        finish = dist[i] + T_min[i]
        if finish > UB: UB = finish

    CT = int(math.ceil(UB))


def generate_cnf(K):
    """Tạo file CNF cho Cycle Time K"""
    formula = CNF()

    # 1. Mỗi Task 1 Trạm
    for j in range(Na):
        formula.append([get_var('X', j, s) for s in range(Nw)])
        for s1 in range(Nw):
            for s2 in range(s1 + 1, Nw):
                formula.append([-get_var('X', j, s1), -get_var('X', j, s2)])

    # 2. Mỗi Trạm 1 Robot
    for s in range(Nw):
        formula.append([get_var('Y', s, r) for r in range(Nr)])
        for r1 in range(Nr):
            for r2 in range(r1 + 1, Nr):
                formula.append([-get_var('Y', s, r1), -get_var('Y', s, r2)])

    # 3. Ràng buộc liên kết Z = X and Y
    for j in range(Na):
        for s in range(Nw):
            for r in range(Nr):
                # Z <-> X ^ Y
                formula.append([-get_var('X', j, s), -get_var('Y', s, r), get_var('Z', j, s, r)])
                formula.append([-get_var('Z', j, s, r), get_var('X', j, s)])
                formula.append([-get_var('Z', j, s, r), get_var('Y', s, r)])

    # 4. Ràng buộc thứ tự (Precedence)
    for (i, j) in adj:
        for k in range(Nw):
            for k_prime in range(0, k):
                # Nếu i làm ở k, j không được làm ở k_prime < k
                formula.append([-get_var('X', i, k), -get_var('X', j, k_prime)])

    # 5. Ràng buộc Cycle Time (Pseudo-Boolean)
    for s in range(Nw):
        vars_ = []
        coeffs = []
        for j in range(Na):
            for r in range(Nr):
                vars_.append(get_var('Z', j, s, r))
                coeffs.append(T[j][r])

        if vars_:
            # Tổng thời gian trạm s <= K
            cnf_part = PBEnc.leq(lits=vars_, weights=coeffs, bound=K, vpool=var_manager)
            formula.extend(cnf_part.clauses)

    return formula


def call_painless_binary(cnf_obj):
    """Ghi file và gọi Painless"""
    cnf_obj.to_file(TEMP_CNF)

    try:
        # Gọi subprocess trực tiếp, output cực gọn
        result = subprocess.run(
            [PAINLESS_BIN, TEMP_CNF],
            capture_output=True, text=True, timeout=60
        )
    except subprocess.TimeoutExpired:
        return None

    out = result.stdout
    # Check Code 10 (SAT) hoặc 20 (UNSAT)
    if result.returncode == 10 or "s SATISFIABLE" in out:
        model = []
        for line in out.splitlines():
            if line.startswith('v'):
                # Parse nhanh dòng biến
                parts = line.split()
                for p in parts[1:]:
                    try:
                        val = int(p)
                        if val != 0: model.append(val)
                    except:
                        pass
        return model

    return None  # UNSAT hoặc Lỗi


def decode_and_print(model, dataset_name, duration, final_K):
    """Giải mã và in bảng kết quả"""
    model_set = set(model)
    assignment = []

    # Map Trạm -> Robot
    station_robot = {}
    for s in range(Nw):
        for r in range(Nr):
            if var_manager.id(('Y', s, r)) in model_set:
                station_robot[s] = r
                break

    # Map Task -> Trạm -> Robot -> Time
    for j in range(Na):
        for s in range(Nw):
            if var_manager.id(('X', j, s)) in model_set:
                r = station_robot.get(s, -1)
                t = T[j][r]
                assignment.append((s + 1, r + 1, j + 1, t))  # (Station, Robot, Task, Time)
                break

    # Sắp xếp: Station tăng dần, sau đó đến Task ID tăng dần
    assignment.sort(key=lambda x: (x[0], x[2]))

    # --- IN KẾT QUẢ ---
    print(f"\n✅ {dataset_name} | Cycle Time Tối Ưu: {final_K} | Thời gian chạy: {duration:.4f}s")
    print("-" * 50)
    print(f"{'Trạm':<8} | {'Robot':<8} | {'Task':<8} | {'Time':<8}")
    print("-" * 50)

    curr_s = -1
    load = 0
    for s, r, task, t in assignment:
        if s != curr_s:
            if curr_s != -1:
                print(f"{' ':27} [Load: {load}]")
                print("-" * 50)
            curr_s = s
            load = 0
        print(f"{s:<8} | {r:<8} | {task:<8} | {t:<8}")
        load += t
    print(f"{' ':27} [Load: {load}]")
    print("=" * 60)


# =============================================================================
# 3. HÀM MAIN (OPTIMIZE LOOP)
# =============================================================================
def main():
    global var_manager

    # Danh sách file cần chạy
    files = ["Dataset1.txt", "Dataset2.txt"]

    if not os.path.exists(PAINLESS_BIN):
        print("❌ Lỗi: Chưa build Painless!")
        return

    for filename in files:
        if not os.path.exists(filename):
            print(f"⚠️ Bỏ qua {filename} (Không tồn tại)")
            continue

        # 1. Reset & Load
        reset_globals()
        read_data(filename)
        preprocess()  # Tính LB, UB

        # 2. Binary Search (Silent)
        best_model = None
        best_K = float('inf')

        left, right = LB, UB
        start_t = time.perf_counter()

        while left <= right:
            mid = (left + right) // 2

            # Reset IDPool mỗi vòng lặp để giữ ID nhỏ nhất -> Solver chạy nhanh hơn
            var_manager = IDPool()

            cnf = generate_cnf(mid)
            res = call_painless_binary(cnf)

            if res is not None:  # SAT
                best_K = mid
                best_model = res
                right = mid - 1
            else:  # UNSAT
                left = mid + 1

        end_t = time.perf_counter()

        # 3. Kết quả
        if best_model:
            # Cần tạo lại var_manager đúng với best_K để decode (vì trong loop ta reset)
            # Hoặc ta chỉ cần biết logic decode không phụ thuộc ID cụ thể nếu ta lưu lại map?
            # Cách an toàn nhất: Chạy lại generate_cnf(best_K) 1 lần nữa để lấy đúng ID map
            # Tuy nhiên, ta đã có best_model là list các số ID.
            # IDPool của vòng lặp cuối cùng (khi SAT) chính là IDPool khớp với best_model?
            # KHÔNG CHẮC CHẮN. Vì vòng lặp cuối cùng có thể là UNSAT (khi right giảm).

            # -> FIX: Để decode đúng, ta regenerate IDPool khớp với best_K
            var_manager = IDPool()
            _ = generate_cnf(best_K)  # Chỉ để fill IDPool

            decode_and_print(best_model, filename, end_t - start_t, best_K)
        else:
            print(f"❌ {filename}: Không tìm thấy nghiệm.")


if __name__ == "__main__":
    main()