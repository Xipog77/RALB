import openpyxl
import numpy as np
import os
import time
from pysat.solvers import Glucose3

class Task():
    def __init__(self, id, duration, power):
        self.id = id
        self.duration = duration
        self.power = power
    
    def __init__(self, id, duration, power, workstation, start_at):
        self.id = id
        self.duration = duration
        self.power = power
        self.workstation = workstation
        self.start_at = start_at
    
    def setId(self, id):
        self.id = id
    
    def getId(self):
        return self.id
    
    def setDuration(self, duration):
        self.duration = duration
    
    def getDuration(self):
        return self.duration
    
    def setPower(self, power):
        self.power = power
    
    def getPower(self):
        return self.power
    
    def setWorkstation(self, workstation):
        self.workstation = workstation
    
    def getWorkstation(self):
        return self.workstation
    
    def setStartAt(self, start_at):
        self.start_at = start_at
    
    def getStartAt(self):
        return self.start_at

# Helper functions to map variables
def get_var(name, *args):
    global var_counter
    key = (name,) + args
    if key not in var_map:
        var_map[key] = var_counter
        var_counter += 1
    return var_map[key]

def get_key(value):
    for key, val in var_map.items():
        if val == value:
            return key

def generatePowerConsumption(file_name, file_path, n):
    file = open(file_path, 'a')
    for j in range(1, n + 1):
        file.write(str(np.random.randint(5, 51)) + '\n')
    file.close()
    return

def readDatasetFile(dataset_number):
    excelFile = openpyxl.load_workbook('./datasets/dataset.xlsx').active
    row = excelFile[dataset_number]
    file_name = str(row[0].value).upper()
    global n, m, c, task_time, precedence_constraints, task_power
    m = int(row[1].value)
    c = int(row[2].value)

    in2File = open('./datasets/precedence_graphs/' + file_name + '.IN2', 'r')
    content = in2File.readlines()
    for index, line in enumerate(content):
        line = line.strip()
        if index == 0:
            n = int(line)
        elif index in range(1, n + 1):
            task_time.append(int(line))
        else:
            constraints = tuple(map(int, line.split(',')))  # Chuyển thành tuple số nguyên
            if constraints != (-1, -1):  # Bỏ qua (-1, -1)
                precedence_constraints.append(constraints)
            else:
                break
    in2File.close()

    txtFilePath = './datasets/task_power/' + file_name + '.txt'
    if os.path.isfile(txtFilePath):
        txtFile = open(txtFilePath, 'r')
        power_content = txtFile.readlines()
        for index, line in enumerate(power_content):
            line = line.strip()
            task_power.append(int(line))
        txtFile.close()
    else:
        generatePowerConsumption(file_name, txtFilePath, n)
        txtFile = open(txtFilePath, 'r')
        power_content = txtFile.readlines()
        for index, line in enumerate(power_content):
            line = line.strip()
            task_power.append(int(line))
        txtFile.close()

    print('[file_name]', file_name)
    print('[n]', n)
    print('[m]', m)
    print('[c]', c)

def printClauses(clauses):
    tmp = []
    for clause in clauses:
        if isinstance(clause, list):
            arr = []
            for variable in clause:
                if variable >= 0:
                    arr.append(str(get_key(abs(variable))) + ": " + str(variable))
                else:
                    arr.append("-" + str(get_key(abs(variable))) + ": " + str(variable))
            tmp.append(arr)
    print('[clauses]', tmp)

def printAssumption():
    global clauses
    print('\n')
    # print('[clauses]', printClauses(clauses))
    print('[#Var]', var_counter - 1)
    print('[#Cons]', len(clauses))
    print('\n')
    # print('[ip(j, k)]', ip_jk)
    # print('\n[ip(j, k, t)]', ip_jkt)
    # print('\n[A_vars]', A_vars)
    # print('\n')

def printResult(solutions, best_solution, best_iteration, best_value, time_execution):
    print('\n')
    print('[Peak]', best_value)
    print('[#Sol]', len(solutions))
    print('[#SolBB]', best_iteration)
    print('[Time]', round(time_execution, 3), 's - real time:', time_execution, 's')
    print('\n')
    # print('\n[C]', C)
    # print('\n')
    print('[best_solution]')
    printSolution(best_solution, best_iteration, best_power_consumption, best_value)

def printSolution(solution, iteration, power_consumption, power_peak):
    print('[solution ' + str(iteration) + ']')
    tasks = []
    for j in range(1, n + 1):
        for k in range(1, m + 1):
            if get_var('X', j, k) in solution:
                for t in range(0, c - task_time[j] + 1):
                    if get_var('S', j, t) in solution:
                        tasks.append(Task(j, task_time[j], task_power[j], k, t))
                        break
    
    for task in tasks:
        if isinstance(task, Task):
            print('task', task.getId(), ': duration=', task.getDuration(), 'power=', task.getPower(), 'workstation=', task.getWorkstation(), 'start at=', task.getStartAt())
    print('\n')
    print('[power_consumption]', power_consumption)
    print('[power_peak]', power_peak)
    print('\n')

# Pre-process
def preConstraints(n, m, c, task_time, precedence_constraints):
    global clauses
    # (10)
    # Update earliest_start and assigned_workstation based on precedence_constraints
    earliest_start = {j: 0 for j in range(1, n + 1)}
    assigned_workstation = {j: 1 for j in range(1, n + 1)}
    for (i, j) in precedence_constraints:
        if assigned_workstation[j] > assigned_workstation[i]:
            continue
        elif assigned_workstation[j] < assigned_workstation[i]:
            earliest_start[j] = earliest_start[i] + task_time[i]
        else:
            earliest_start[j] = max(earliest_start[j], earliest_start[i] + task_time[i])
        # if task i cannot be assigned to workstation k (start from 1, k++) => task j cannot
        for k in range(1, assigned_workstation[i] + 1):
            # print('[ip_jk[(i, k)]]', (i, k), ip_jk.get((i, k), 0))
            if ip_jk.get((i, k), 0) and not ip_jk.get((j, k), 0):
                ip_jk[(j, k)] = 1
                clauses.append([-get_var('X', j, k)])
        # check if task j can be assigned to the same workstation with task i
        if earliest_start[j] + task_time[j] > c:
            k = assigned_workstation[i]
            if not ip_jk.get((j, k), 0):
                ip_jk[(j, k)] = 1
                clauses.append([-get_var('X', j, k)])
            assigned_workstation[j] = assigned_workstation[i] + 1
            earliest_start[j] = 0
        else:
            assigned_workstation[j] = assigned_workstation[i]
    
    # (11)
    for (i, j) in precedence_constraints:
        for t in range(0, earliest_start[j]):
            k = assigned_workstation[j]
            if not ip_jkt.get((j, k, t), 0):
                ip_jkt[(j, k, t)] = 1
                if not ip_jk.get((j, k), 0):
                    clauses.append([-get_var('X', j, k), -get_var('S', j, t)])

    # (10)
    # Update latest_start and assigned_workstation based on precedence_constraints
    latest_start = {j: c - task_time[j] for j in range(1, n + 1)}
    _assigned_workstation = {j: m for j in range(1, n + 1)}
    for (i, j) in reversed(precedence_constraints):
        if _assigned_workstation[i] < _assigned_workstation[j]:
            continue
        elif _assigned_workstation[i] > _assigned_workstation[j]:
            latest_start[i] = latest_start[j] - task_time[i]
        else:
            latest_start[i] = min(latest_start[i], latest_start[j] - task_time[i])
        # if task j cannot be assign to workstation k (start from 6, k--) => task i cannot
        for k in range(m, _assigned_workstation[j] - 1, -1):
            # print('[ip_jk[(i, k)]]', (j, k), ip_jk.get((j, k), 0))
            if ip_jk.get((j, k), 0) and not ip_jk.get((i, k), 0):
                ip_jk[(i, k)] = 1
                clauses.append([-get_var('X', i, k)])
        # check if task i can be assigned to the workstation with task j
        if latest_start[i] < 0:
            k = _assigned_workstation[j]
            if not ip_jk.get((i, k), 0):
                ip_jk[(i, k)] = 1
                clauses.append([-get_var('X', i, k)])
            _assigned_workstation[i] = _assigned_workstation[j] - 1
            latest_start[i] = c - task_time[i]
        else:
            _assigned_workstation[i] = _assigned_workstation[j]
    
    # (11)
    for (i, j) in reversed(precedence_constraints):
        for t in range(latest_start[i] + 1, c - 1 + 1):
            k = _assigned_workstation[i]
            if not ip_jkt.get((i, k, t), 0):
                ip_jkt[(i, k, t)] = 1
                if not ip_jk.get((i, k), 0):
                    clauses.append([-get_var('X', i, k), -get_var('S', i, t)])

    # (12)
    for j in range(1, n + 1):
        if task_time[j] > c / 2:
            for t in range(c - task_time[j], task_time[j] - 1 + 1):
                clauses.append([get_var('A', j, t)])
                A_vars[(j, t)] = 1

    # print('[earliest_start]', earliest_start)
    # print('[latest_start]', latest_start)
    # print('[assigned_workstation]', assigned_workstation)
    # print('[_assigned_workstation]', _assigned_workstation)

def generateConstraints(n, m, c, task_time, precedence_constraints):
    global clauses
    # (1)
    for j in range(1, n + 1):
        constraints = []
        for k in range(1, m + 1):
            if not ip_jk.get((j, k), 0):
                # clauses.append(get_var('X', j, k))
                constraints.append(get_var('X', j, k))
        clauses.append(constraints)

    # (2)
    for j in range(1, n + 1):
        for k_1 in range(1, m):
            if not ip_jk.get((j, k_1), 0):
                for k_2 in range(k_1 + 1, m + 1):
                    if not ip_jk.get((j, k_2), 0):
                        clauses.append([-get_var('X', j, k_1), -get_var('X', j, k_2)])

    # (3)
    for (i, j) in precedence_constraints:
        for k in range(1, m):
            if not ip_jk.get((j, k), 0):
                for h in range(k + 1, m + 1):
                    if not ip_jk.get((i, h), 0):
                        clauses.append([-get_var('X', j, k), -get_var('X', i, h)])

    # (4)
    for j in range(1, n + 1):
        constraints = []
        for t in range(0, c - task_time[j] + 1):
            if t + task_time[j] <= c:
                # clauses.append(get_var('S', j, t))
                constraints.append(get_var('S', j, t))
        clauses.append(constraints)

    # (5)
    for j in range(1, n + 1):
        for t_1 in range(0, c - task_time[j]):
            for t_2 in range(t_1 + 1, c - task_time[j] + 1):
                clauses.append([-get_var('S', j, t_1), -get_var('S', j, t_2)])

    # (6)
    for j in range(1, n + 1):
        for t in range(c - task_time[j] + 1, c - 1 + 1):
            if t > c - task_time[j]:
                clauses.append([-get_var('S', j, t)])

    # (7)
    for i in range(1, n):
        for j in range(i + 1, n + 1):
            for k in range(1, m + 1):
                if not ip_jk.get((i, k), 0) and not ip_jk.get((j, k), 0):
                    for t in range(0, c - 1 + 1):
                        # if not A_vars.get((i, t), 0) and not A_vars.get((j, t), 0):
                            clauses.append([-get_var('X', i, k), -get_var('X', j, k), -get_var('A', i, t), -get_var('A', j, t)])

    # (8)
    for j in range(1, n + 1):
        for t in range(0, c - task_time[j] + 1):
            for e in range(0, task_time[j] - 1 + 1):
                if not A_vars.get((j, t + e), 0):
                    clauses.append([-get_var('S', j, t), get_var('A', j, t + e)])

    # # Ràng buộc phụ: S(j, t) -> not A(j, t'): t' < t => not S(j, t) or not A(j, t')
    # for j in range(1, n + 1):
    #     for t in range(0, c - task_time[j] + 1):
    #         for t_2 in range(0, t):
    #             clauses.append([-get_var('S', j, t), -get_var('A', j, t_2)])

    # for j in range(1, n + 1):
    #     for t in range(0, c - 1 + 1):
    #         clause = [-get_var('A', j, t)]
    #         if t + 1 < c:
    #             clause.append(get_var('A', j, t + 1))
    #         if t - task_time[j] + 1 >= 0:
    #             clause.append(get_var('S', j, t - task_time[j] + 1))
    #         if len(clause) > 1:
    #             clauses.append(clause)

    for j in range(1, n + 1):
        for t in range(0, c - 1 + 1):
            clause = [-get_var('A', j, t)]
            for t_prime in range(max(0, t - task_time[j] + 1), t + 1):
                clause.append(get_var('S', j, t_prime))
            if len(clause) > 1:
                clauses.append(clause)

    # (9)
    for (i, j) in precedence_constraints:
        for k in range(1, m + 1):
            if not ip_jk.get((i, k), 0) and not ip_jk.get((j, k), 0):
                for t_2 in range(0, c - task_time[j] + 1):
                    if not ip_jkt.get((j, k, t_2), 0):
                        for t_1 in range(t_2 + 1, c - task_time[i] + 1):
                            if not ip_jkt.get((i, k, t_1), 0):
                                clauses.append([-get_var('X', i, k), -get_var('X', j, k), -get_var('S', i, t_1), -get_var('S', j, t_2)])

def satSolver(solver):
    # global status
    status = 0
    if solver.solve():
        model = solver.get_model()
        # print('[model]', model)
        # res = []
        solution = []
        for item in model:
            if item >= 0:
                solution.append(item)
                # res.append(str(get_key(abs(item))) + ": " + str(item))
            # else:
            #     res.append("-" + str(get_key(abs(item))) + ": " + str(item))
        # print('[res]', res)
        status = 1
        return status, solution
    else:
        status = 0
        return status, None

def computeSolutionValue(n, m, c, solution):
    global power_consumption
    power_consumption = {t: 0 for t in range(0, c - 1 + 1)}
    for t in range(0, c - 1 + 1):
        for j in range(1, n + 1):
            if get_var('A', j, t) in solution:
                power_consumption[t] += task_power[j]
    
    power_peak = 0
    for t, power in power_consumption.items():
        if power > power_peak:
            power_peak = power
    
    return power_peak

def addNewConstraints(n, solution, power_consumption, best_value, solver):
    global clauses, C
    for t, power in power_consumption.items():
        tasks = []
        if power >= best_value:
            for j in range(1, n + 1):
                if get_var('A', j, t) in solution:
                    tasks.append(j)
        if len(tasks) > 1 and tasks not in C:
            C.append(tasks)
            for t in range(0, c - 1 + 1):
                tmp = []
                for j in tasks:
                    tmp.append(-get_var('A', j, t))
                clauses.append(tmp)
                solver.add_clause(tmp)

# Global variables
ip_jk = {}
ip_jkt = {}
A_vars = {}

var_map = {}
var_counter = 1

clauses = []
variables = []

# Variable read from file
n = 0 # number of tasks
m = 0 # number of workstations
c = 0 # cycle time

task_time = [None]
precedence_constraints = []
task_power = [None]

# n = 4 # number of tasks
# m = 3 # number of workstations
# c = 5 # cycle time

# task_time = [None, 5, 2, 3, 3]
# precedence_constraints = [(1, 2), (2, 3), (3, 4)]
# task_power = [None, 4, 4, 2, 4]

status = 0
solution = None
solutions = []
best_solution = None
best_value = 9999
current_value = 0
power_consumption = {}
best_power_consumption = {}
C = []
iteration = 1
best_iteration = 1

def main():
    global n, m, c, task_time, precedence_constraints, task_power, status, solution, best_solution, best_value, current_value, power_consumption, best_power_consumption, C, iteration, best_iteration
    
    print('Type your dataset number: ')
    dataset_number = input()

    readDatasetFile(dataset_number)
    # print('[n]', n)
    # print('[m]', m)
    # print('[c]', c)
    # print('[task_time]', task_time)
    # print('[precedence_constraints]', precedence_constraints)
    # print('[task_power]', task_power)
    # print('\n')

    start = time.time()

    preConstraints(n, m, c, task_time, precedence_constraints)
    generateConstraints(n, m, c, task_time, precedence_constraints)
    printAssumption()

    solver = Glucose3()
    for clause in clauses:
        solver.add_clause(clause)

    status, solution = satSolver(solver)
    if not status:
        print('No solution')
        return

    while status:
        current_value = computeSolutionValue(n, m, c, solution)
        # printSolution(solution, iteration, power_consumption, current_value)
        solutions.append(solution)
        if current_value < best_value:
            best_solution = solution
            best_value = current_value
            best_iteration = iteration
            best_power_consumption = power_consumption
        addNewConstraints(n, solution, power_consumption, best_value, solver)
        status, solution = satSolver(solver)
        iteration += 1
        end = time.time()
        if (end - start) > 3600:
            print('time out')
            break

    time_execution = end - start
    printResult(solutions, best_solution, best_iteration, best_value, time_execution)
    # printClauses(clauses)

main()