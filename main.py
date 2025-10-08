import time

from pysat.pb import PBEnc
from pysat.solvers import Glucose3
from pysat.formula import IDPool
import math
import csv
from collections import defaultdict, deque


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


def read_data(file_path):
    global T, graph, Na, Nr, adj, neighbors, reversed_neighbors
    T.clear();
    graph.clear();
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
    solution = []

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
            time = T[j][r]
            station_runtime[s] += time
            # total_energy  += time * EP[r]
            total_energy  += time * 0

    return assignment, station_runtime, solution, total_energy


import time
from pysat.solvers import Glucose3
from pysat.formula import IDPool


def optimize_ct():
    global var_map, var_counter, clauses, CT, time_end
    global previous_solutions, var_manager, LB, UB, ip
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
    fixed_clauses = Fixed_clauses()

    while left <= right and timeout_count < max_timeout:
        K = int((left + right) / 2)
        iter_start = time.perf_counter()  # đo thời gian cho mỗi vòng lặp

        solver = Glucose3()

        time_end = [max(0, CT - min(T[j].values())) for j in range(Na)]
        dynamic_clauses = Dynamic_clauses(K)

        for clause in fixed_clauses:
            solver.add_clause(clause)

        for clause in dynamic_clauses:
            solver.add_clause(clause)

        if solver.solve():
            model = solver.get_model()
            this_solution = [var for var in model if var > 0]
            assignment, station_runtime, solution, total_energy  = get_solution(this_solution)
            actual_ct = max(station_runtime) if station_runtime else 0
            actual_e = total_energy
            z3_value = w1 * actual_ct + w2 * actual_e

            print(f"✅ Có nghiệm khả thi với Z3 = {z3_value:.2f} (CT={actual_ct}, E={actual_e:.2f})")

            if z3_value < best_z3 :
                best_z3  = z3_value
                best_solution = assignment
                previous_solutions.append(solution)

            # Giảm giới hạn K để tìm nghiệm nhỏ hơn
            right = K - 1
        else:
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
    else:
        print("❌ Không tìm được nghiệm hợp lệ.")
        print(f"⏳ Tổng thời gian chạy: {total_elapsed:.2f} giây")
        print("Debug info:")
        print(f"- Tasks: {Na}, Stations: {Nw}, Robots: {Nr}")
        print(f"- LB: {LB}, UB: {UB}")
        try:
            print(f"- Min times: {Tjr_min_list[:5]}...")  # Show first 5
            print(f"- Total min time: {sum(Tjr_min_list)}")
        except Exception:
            pass

        print("\n🔍 Thử nghiệm với CT = 1000 để debug...")
        debug_test(1000)


def dfs(v, visited, neighbors):
    visited[v] = True
    for i in range(Na):
        if (neighbors[v][i] == 1 and visited[i] == False):
            dfs(i, visited, neighbors)
    toposort.append(v)


def preprocess():
    global Na, Nw, CT, neighbors, reversed_neighbors
    n = math.ceil(Na / Nw)
    Tjr_max_list = [max(T[j].values()) for j in T if T[j]]
    CT = sum(sorted(Tjr_max_list, reverse=True)[:min(n, len(Tjr_max_list))])
    time_list = [min(T[j].values()) for j in T if T[j]]
    visited = [False for i in range(Na)]
    # neighbors = [[0 for i in range(Na)] for j in range(Na)]
    # reversed_neighbors = [[0 for i in range(Na)] for j in range(Na)]
    earliest_start = [[-9999999 for _ in range(Nw)] for _ in range(Na)]
    latest_start = [[99999999 for _ in range(Nw)] for _ in range(Na)]
    ip1 = [[0 for _ in range(Nw)] for _ in range(Na)]
    ip2 = [[[0 for _ in range(CT)] for _ in range(Nw)] for _ in range(Na)]
    print(CT)
    for i in range(Na):
        if not visited[i]:
            dfs(i, visited, neighbors)
    toposort.reverse()

    for j in toposort:
        k = 0
        earliest_start[j][k] = 0
        for i in range(Na):
            if neighbors[i][j] == 1:

                earliest_start[j][k] = max(earliest_start[j][k], earliest_start[i][k] + time_list[i])

                while (earliest_start[j][k] > CT - time_list[j]):
                    ip1[j][k] = 1

                    k = k + 1
                    earliest_start[j][k] = max(0, earliest_start[i][k] + time_list[i])

                if earliest_start[j][k] <= CT - time_list[j]:
                    for t in range(earliest_start[j][k]):
                        if (ip2[j][k][t] == 0):
                            ip2[j][k][t] = 1
    toposort.reverse()
    for j in toposort:
        k = Nw - 1
        latest_start[j][k] = CT - time_list[j]
        for i in range(Na):
            if (neighbors[j][i] == 1):
                latest_start[j][k] = min(latest_start[j][k], latest_start[i][k] - time_list[j])
                while (latest_start[j][k] < 0):
                    ip1[j][k] = 1
                    k = k - 1
                    latest_start[j][k] = min(CT - time_list[j], latest_start[i][k] - time_list[j])

                if (latest_start[j][k] >= 0):
                    for t in range(latest_start[j][k] + 1, CT):

                        if (ip2[j][k][t] == 0):
                            ip2[j][k][t] = 1

    return ip1, ip2


def Fixed_clauses():
    global CT, time_end, previous_solutions, var_manager, adj, w1, w2
    time_end = [max(0, CT - min(T[j].values())) for j in range(Na)]
    fixed_clauses = []

    ip1, ip2 = preprocess()

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

    # (1) Ràng buộc tiền nhiệm
    # j1 Cần làm trước j2 => j2 không thể ở trước j1
    # for j1 in range(Na):
    #     for j2 in graph[j1]:
    #         for s2 in range(Nw):
    #             clause = [-get_var('X', j2, s2)]
    #             clause += [get_var('X', j1, s1) for s1 in range(s2 + 1)]
    #             clauses.append(clause)
    # (2) Mỗi công việc được gán cho đúng một trạm

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

    # for j in range(Na):
    #     last_t = time_end[j]

    #     # Special case: Full cycle tasks (only one feasible start time: t=0)
    #     if last_t == 0:
    #         # Force the task to start at t=0 (equivalent to original constraint #4)
    #         clauses.append([get_var('S', j, 0)])
    #     else:
    #         # First time slot
    #         set_var(get_var('S', j, 0), "T", j, 0)

    #         # Intermediate time slots
    #         for t in range(1, last_t):
    #             clauses.append([-get_var("T", j, t-1), get_var("T", j, t)]) # T[j][t-1] -> T[j][t]
    #             clauses.append([-get_var('S', j, t), get_var("T", j, t)]) # S[j][t] -> T[j][t]
    #             clauses.append([-get_var('S', j, t), -get_var("T", j, t-1)]) # S[j][t] -> ¬T[j][t-1]
    #             clauses.append([get_var('S', j, t), get_var("T", j, t-1), -get_var("T", j, t)]) # T[j][t] -> (T[j][t-1] ∨ S[j][t])

    #         # Last time slot (ensures at least one start time)
    #         clauses.append([get_var("T", j, last_t-1), get_var('S', j, last_t)])
    #         clauses.append([-get_var("T", j, last_t-1), -get_var('S', j, last_t)])

    return fixed_clauses


def Dynamic_clauses(K):
    dynamic_clauses = []
    for s in range(Nw):
        # (13) Giới hạn thời gian chu kỳ tại mỗi trạm
        # (14) Giới hạn năng lượng tiêu thụ
        # for s in range(Nw):
        vars_ = []
        coeffs = []
        for j in range(Na):
            for r in range(Nr):
                z_var = get_var('Z', j, s, r)
                vars_.append(z_var)

                # hệ số cho Z3 = w1*T + w2*T*EP
                # coeff = w1 * T[j][r] + w2 * T[j][r] * EP[r]
                coeff = w1 * T[j][r] + w2 * T[j][r] * 0
                coeffs.append(coeff)

            # Thêm constraint nếu có biến
        if vars_:
            cnf_part = PBEnc.leq(lits=vars_, weights=coeffs, bound=K, vpool=var_manager)
            dynamic_clauses.extend(cnf_part.clauses)
    # (15) Loại bỏ nghiệm trùng lặp
    for sol in previous_solutions:
        dynamic_clauses.append(sol)

    return dynamic_clauses


def compute_ub():
    global Nw, Na, Nr, UB, T, EP, w1, w2, CT

    # if not T or not EP:
    #     print("Warning: Không có dữ liệu để tính UB")
    #     return

    n = math.ceil(Na / Nw)
    Tjr_max_list = [max(T[j].values()) for j in T if T[j]]
    CT = sum(sorted(Tjr_max_list, reverse=True)[:min(n, len(Tjr_max_list))])
    # total_energy = sum(max(T[j].values()) * EP[max(T[j], key=T[j].get)] for j in T if T[j])
    total_energy = sum(max(T[j].values()) * 0 for j in T if T[j])
    UB = w1 * CT + w2 * total_energy

    print(f"CT={CT:.2f}, E={total_energy:.2f}, UB={UB:.2f}")
    return UB


def debug_test(test_ct):
    global var_map, var_counter, clauses, CT, time_end, var_manager

    print(f"Chạy debug test với CT = {test_ct}")

    var_map = {}
    var_counter = 1
    var_manager = IDPool()
    clauses = []
    solver = Glucose3()
    CT = test_ct

    time_end = [max(0, CT - min(T[j].values())) for j in range(Na)]

    # CHỈ THÊM CÁC RÀNG BUỘC CƠ BẢN
    print("Adding basic constraints...")

    # (2) Mỗi công việc được gán cho đúng một trạm
    for j in range(Na):
        clauses.append([get_var('X', j, s) for s in range(Nw)])

    for j in range(Na):
        for s1 in range(Nw):
            for s2 in range(s1 + 1, Nw):
                clauses.append([-get_var('X', j, s1), -get_var('X', j, s2)])

    # (3) Mỗi trạm được gán cho đúng một robot
    for s in range(Nw):
        clauses.append([get_var('Y', s, r) for r in range(Nr)])

    for s in range(Nw):
        for r1 in range(Nr):
            for r2 in range(r1 + 1, Nr):
                clauses.append([-get_var('Y', s, r1), -get_var('Y', s, r2)])

    print(f"Added {len(clauses)} basic clauses")

    for clause in clauses:
        solver.add_clause(clause)

    if solver.solve():
        print("✅ Basic constraints are satisfiable!")
        model = solver.get_model()
        this_solution = [var for var in model if var > 0]
        assignment, station_runtime, solution = get_solution(this_solution)
        print_solution(assignment)
    else:
        print("❌ Even basic constraints are unsatisfiable!")


var_map = {}
var_counter = 1
var_manager = None  # Sẽ được khởi tạo trong optimize_ct()
clauses = []
Na = 0  # Na - jobs
Nw = 3  # Nw - workstations
Nr = 0  # Nr - robots
previous_solutions = []
T = defaultdict(dict)  # T[j][r] là thời gian robot r làm task j
graph = defaultdict(list)  # graph[j] là danh sách các task kế tiếp của task j
adj = []
LB = 0
UB = int()
CT = int()  # cycletime
EP = defaultdict(dict)
Tjr_min_list = []
Tjr_max_list = []
time_end = []  # time_end: thời gian khởi động muộn nhất mà vẫn kịp hoàn thành công việc
visited = []
neighbors = []
reversed_neighbors = []
toposort = []
w1 = 1
w2 = 0


def main():
    global Na, Nw, Nr, T, graph, LB, UB, CT, Tjr_min_list, Tjr_max_list, time_end

    try:
        # read_data(input())
        read_data("/content/drive/MyDrive/Colab Notebooks/Data/Dataset1.txt")
        # Lấy mỗi task j: T[j][r] nhỏ nhất và lớn nhất
        compute_ub()
        optimize_ct()

    except FileNotFoundError:
        print("❌ Không tìm thấy file")
    except Exception as e:
        print(f"❌ Lỗi: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    main()