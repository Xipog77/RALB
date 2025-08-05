import csv
from collections import defaultdict, deque
from ortools.linear_solver import pywraplp

Nw = 3 # Số trạm
Na = 0 # Số công việc
Nr = 0 # Số robot

T = defaultdict(dict)  # T[j][r] là thời gian robot r làm task j
graph = defaultdict(list)  # graph[j] là danh sách các task kế tiếp của task j


def read_data(file_path):
    global T, graph, Na, Nr

    T.clear()
    graph.clear()

    with open(file_path, 'r') as f:
        reader = csv.DictReader(f, delimiter='\t')
        for row in reader:
            task = int(row['Task']) - 1  # 0-based index
            successors = [int(s.strip()) - 1 for s in row['Successor'].split(',')] if row['Successor'].strip() else []
            graph[task] = successors

            for r in range(1, 5):
                T[task][r - 1] = int(row[f'Robot {r}'])
    Na = len(T)
    Nr = len(T[1])
    print("Đọc dữ liệu thành công!")
    return

def build_model(w1, w2):

    global T, graph, Na, Nr, Nw

    solver = pywraplp.Solver.CreateSolver("SCIP")

    # Biến
    X = [[solver.BoolVar(f'X[{i}][{s}]') for s in range(Nw)] for i in range(Na)]
    Y = [[solver.BoolVar(f'Y[{s}][{r}]') for r in range(Nr)] for s in range(Nw)]
    Z = [[[solver.BoolVar(f'Z[{i}][{s}][{r}]') for r in range(Nr)] for s in range(Nw)] for i in range(Na)]
    CT = solver.NumVar(0, solver.infinity(), 'CT')
    Er = solver.NumVar(0, solver.infinity(), 'Er')

    # 8
    for j in range(Na):
        solver.Add(solver.Sum(X[j][s] for s in range(Nw)) == 1)
    # 9
    for s in range(Nw):
        solver.Add(solver.Sum(Y[s][r] for r in range(Nr)) == 1)

    # 10
    for j in range(Na):
        for s in range(Nw):
            for r in range(Nr):
                solver.Add(Z[j][s][r] <= X[j][s])
                solver.Add(Z[j][s][r] <= Y[s][r])
                solver.Add(Z[j][s][r] >= X[j][s] + Y[s][r] - 1)
    # 7
    for j in range(Na):
        for i in graph[j]:
            lhs = solver.Sum(s * X[i][s] for s in range(Nw))
            rhs = solver.Sum(s * X[j][s] for s in range(Nw))
            solver.Add(lhs <= rhs)

    for s in range(Nw):
        total_time = solver.Sum(Z[i][s][r] * T[i][r] for i in range(Na) for r in range(Nr))
        solver.Add(total_time <= CT)

    total_energy = solver.Sum(Z[i][s][r] * T[i][r] for i in range(Na) for s in range(Nw) for r in range(Nr))
    solver.Add(Er == total_energy)

    # 6 Mục tiêu: hàm tổng có trọng số
    solver.Minimize(w1 * CT + w2 * Er)

    return solver, X, Y, Z, CT, Er

read_data("Dataset.txt")
solver, X, Y, Z, CT, Er = build_model(1, 0)

status = solver.Solve()
if status == pywraplp.Solver.OPTIMAL:
    print(f'Tối ưu: CT = {CT.solution_value()}, Er = {Er.solution_value()}')
    for i in range(Na):
        for s in range(Nw):
            if X[i][s].solution_value() > 0.5:
                for r in range(Nr):
                    if Z[i][s][r].solution_value() > 0.5:
                        print(f'Task {i+1} → Trạm {s+1}, Robot {r+1}')
else:
    print("Không tìm được lời giải.")
