# from pypblib import pblib
# from pysat.solvers import Solver
from ctypes.wintypes import LCTYPE

import csv
from collections import defaultdict, deque
import heapq

# assign
# Na - jobs
Na = 0
# Nw - workstations
Nw = 3
# Nr - robots
Nr = 0
# pre-process:
#     time-start[j][r]
#     time-end[j][r] = CT - T[j][r] Công việc bắt buộc thực hiện ở thời gian này để kịp hoàn thành trước CT
#     run_time[j][r]
#     ip[j][s] = true Nếu j có thể bắt đầu tại trạm này
#encoding

T = defaultdict(dict)  # T[j][r] là thời gian robot r làm task j
graph = defaultdict(list)  # graph[j] là danh sách các task kế tiếp của task j
LC = int()
UB = int()


def read_data(file_path):
    global T, graph, Na, Nr

    with open(file_path, 'r') as f:
        reader = csv.DictReader(f, delimiter='\t')
        for row in reader:
            task = int(row['Task'])

            # Tạo danh sách successor nếu có
            successors = [int(s.strip()) for s in row['Successor'].split(',')] if row['Successor'].strip() else []
            graph[task] = successors

            # Lưu thời gian của từng robot
            for r in range(1, 5):
                T[task][r] = int(row[f'Robot {r}'])
    Na = len(T)
    Nr = len(T[1])

def upperbound_lowerbound(T, graph, Nw):
    """
    T: defaultdict(dict) - T[j][r] là thời gian robot r làm task j
    graph: defaultdict(list) - graph[j] là danh sách các task kế tiếp của task j
    Nw: int - số trạm làm việc

    Returns: (LC2, UB)
    """
    global LC, UB
    # Helper: tính thời gian tối thiểu mỗi task
    min_proc_time = {j: min(T[j].values()) for j in T}

    # 1. Tìm chuỗi precedence (chain decomposition) từ đồ thị
    def topological_sort(graph):
        indegree = defaultdict(int)
        for u in graph:
            for v in graph[u]:
                indegree[v] += 1
        q = deque()
        for node in T:
            if indegree[node] == 0:
                q.append(node)

        order = []
        while q:
            u = q.popleft()
            order.append(u)
            for v in graph[u]:
                indegree[v] -= 1
                if indegree[v] == 0:
                    q.append(v)
        return order

    # 2. Chain decomposition (greedy): tìm các chuỗi nối tiếp
    def extract_chains(graph):
        used = set()
        chains = []

        for start in topological_sort(graph):
            if start in used:
                continue
            chain = []
            u = start
            while u not in used:
                chain.append(u)
                used.add(u)
                next_nodes = [v for v in graph[u] if v not in used]
                if len(next_nodes) == 1:
                    u = next_nodes[0]
                else:
                    break
            chains.append(chain)
        return chains

    chains = extract_chains(graph)

    # 3. Tính tổng thời gian tối thiểu cho mỗi chuỗi
    chain_times = []
    for chain in chains:
        total_time = sum(min_proc_time[j] for j in chain)
        chain_times.append(total_time)

    # 4. Tính LC2 = tổng thời gian các chuỗi / số trạm
    LC = sum(chain_times) / Nw

    # 5. Tính UB = tổng toàn bộ thời gian tối thiểu cho tất cả tác vụ
    total_min_time = sum(min_proc_time[j] for j in T)
    UB = total_min_time / Nw

def Pre_processing(Na, Nr, Nw, T, graph, robot_assignment):
    """
    Trả về ip[j][s] = 1 nếu task j không được gán vào station s (do không đủ station để thực hiện các task kế tiếp)
    """
    ip = defaultdict(dict)

    for j in range(Na):  # duyệt tất cả task
        rj = robot_assignment[j]
        tj = T[j][rj]

        for s in range(Nw):  # duyệt tất cả workstation
            invalid = False

            for succ in graph[j]:  # succ là task kế tiếp
                rs = robot_assignment[succ]
                ts = T[succ][rs]

                # Số lượng station còn lại sau khi gán task j vào station s
                remaining_stations = Nw - (s + 1)

                # Nếu không còn trạm nào phía sau để gán task kế tiếp → invalid
                if remaining_stations <= 0:
                    invalid = True
                    break

            ip[j][s] = int(invalid)

    return ip

def generate_solver(X, Y, Z, S, A):
    clauses = []

    # (1) Ràng buộc tiền nhiệm
    # j1 Cần làm trước j2 => j2 không thể ở trước j1
    for j1 in range(Na):
        for j2 in graph[j1]:
            for s2 in range(Nw):
                clause = [-X[j2][s2]]
                clause += [X[j1][s1] for s1 in range(s2 + 1)]
                clauses.append(clause)
    # (2) Mỗi công việc được gán cho đúng một trạm

    for j in range(Na):
        clauses.append([X[j][s] for s in range(Nw)])

    for j in range(Na):
        for s1 in range(Nw):
            for s2 in range(s1 + 1, Nw):
                clauses.append([-X[j][s1], -X[j][s2]])

    # (3) Mỗi trạm được gán cho đúng một robot

    for s in range(Nw):
        clauses.append([Y[s][r] for r in range(Nr)])

    for s in range(Nw):
        for r1 in range(Nr):
            for r2 in range(r1 + 1, Nr):
                clauses.append([-Y[j][r1], -Y[j][r2]])

    # (4) - (5) - (6)

    for j in range(Na):
        for s in range(Nw):
            for r in range(Nr):
                clauses.append([-X[j][s], -Y[s][r], Z[j][s][r]])
                clauses.append([-Z[j][s][r], X[j][s]])
                clauses.append([-Z[j][s][r], Y[s][r]])

    # (7) Mỗi công việc phải được khởi động đúng một lần bởi một robot

    for j in range(Na):
        for r in range(Nr):
            clauses.append(S[j][r][t] for t in range(time_start[j][r], T[j][r]))

    for j in range(Na):
        for r in range(Nr):
            for t1 in range(time_start[j][r], time_end[j][r]):
                for t2 in range(t1 + 1, time_end[j][r]):
                    clauses.append([-S[j][r][t1], -S[j][r][t2]])

    # (8) Không khởi động công việc ngoài thời điểm cho phép
    # Cải tiến: gộp lại với (7)

    for j in range(Na):
        for r in range(Nr):
            for t in range(0, time_start[j][r] - 1):
                clauses.append(-S[j][r][t])
            for t in range(time_end[j][r] + 1, CT):
                clauses.append(-S[j][r][t])

    # (9) Không có hai công việc chạy cùng lúc tại cùng một trạm
    # Cải tiến: tạo một tập các công việc có thể được gán vào s

    for s in range(Nw):
        for j1 in range(Na):
            for j2 in range(j1 + 1, Na):
                clauses.append([-X[j1][s], -X[j2][s], -A[j1][s][t], -A[j2][s][t]] for t in range(CT))

    # (10) Công việc đã khởi động thì phải ở trạng thái chạy
    for j in range(Na):
        for s in range(Nw):
            for r in range(Nr):
                for t1 in range(time_start[j][r], time_end[j][r]):
                    for t2 in range(t1, t1 + runtime[j][r]):
                        clauses.append([-S[j][r][t1], A[j][r][t2]])

    # (11) Nếu cùng trạm, công việc i phải hoàn thành trước j
    # Cải tiến: kết hợp với (9)
    for s in range(Nw):
        for j1 in range(Na):
            for j2 in range(j1 + 1, Na):
                clauses.append([-X[j1][s], -X[j2][s], -S[j1][s][t], -S[j2][s][t]] for t in range(CT))

    # (12) Cấm gán công việc vào trạm không hợp lệ do tiền nhiệm
    for j in range(Na):
        for s in range(Nw):
            if(ip[j][s]):
                clauses.append(-X[j][s])

def calculate_time():
    time = 0
    global Z
    for j in range(Na):
        for s in range(Nw):
            for r in range(Nr):
                if Z[j][s][r] > 0:
                    time += T[j][r]

    return time

def add_new_constraints():
    return


read_data(".venv/Dataset.txt")

print("Thời gian task 1:", T[1][1])
print("Successor của task 1:", graph[1])

upperbound_lowerbound(T, graph, 3)

print(LC)
print(UB)

print(Hi)

