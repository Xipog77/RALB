import csv
import glob
import os
import time
import zipfile
import shutil
from collections import defaultdict
from ortools.linear_solver import pywraplp

# --- CẤU HÌNH ---
TOTAL_TIME_LIMIT_MINUTES = 30  # Tổng thời gian chạy (phút)
INSTANCE_TIME_LIMIT_SECONDS = 60  # Thời gian tối đa mỗi bài (giây)
DATA_FOLDER_NAME = "dataset_extracted"  # Tên thư mục để giải nén dữ liệu vào


def extract_zip_data():
    """Tìm file zip và giải nén."""
    zip_files = glob.glob("*.zip")
    if not zip_files:
        print("Không tìm thấy file .zip nào trong thư mục hiện tại.")
        return False

    target_zip = zip_files[0]
    print(f"Đang giải nén: {target_zip} vào thư mục '{DATA_FOLDER_NAME}'...")

    if os.path.exists(DATA_FOLDER_NAME):
        shutil.rmtree(DATA_FOLDER_NAME)
    os.makedirs(DATA_FOLDER_NAME)

    with zipfile.ZipFile(target_zip, 'r') as zip_ref:
        zip_ref.extractall(DATA_FOLDER_NAME)
    return True


def parse_alb_file(file_path):
    """
    Bộ đọc dành riêng cho định dạng .alb
    Cấu trúc thường thấy:
    <Số task>
    <Các dòng dữ liệu thời gian>
    <Các dòng ràng buộc thứ tự: i j>
    -1 -1
    """
    try:
        with open(file_path, 'r') as f:
            content = f.read().split()

        iterator = iter(content)

        num_tasks = int(next(iterator))
        raw_integers = [int(x) for x in content]


        try:
            end_marker_index = -1
            for i in range(len(raw_integers) - 1):
                if raw_integers[i] == -1 and raw_integers[i + 1] == -1:
                    end_marker_index = i
                    break
        except:
            end_marker_index = len(raw_integers)

        if end_marker_index == -1:

            precedence_data = []
            time_data = raw_integers[1:]
        else:
            split_idx = 1
            for i in range(1, end_marker_index):
                pass
            precedence_list = []
            curr = end_marker_index - 1  # Bắt đầu trước -1
            temp_prec = []
            idx = 1
            data_chunk = raw_integers[1:end_marker_index]

            p_idx = len(data_chunk)
            parsed_edges = []
            while p_idx >= 2:
                u = data_chunk[p_idx - 2]
                v = data_chunk[p_idx - 1]
                if 1 <= u <= num_tasks and 1 <= v <= num_tasks:
                    parsed_edges.append((u, v))
                    p_idx -= 2
                else:
                    break

            precedence_list = parsed_edges[::-1]

            time_values = data_chunk[:p_idx]

        graph = defaultdict(list)
        for u, v in precedence_list:
            graph[u - 1].append(v - 1)  # 0-based index

        if len(time_values) % num_tasks != 0:
            print(f"Cảnh báo: Dữ liệu thời gian ({len(time_values)}) không chia hết cho số task ({num_tasks}).")
            Nr = 1
        else:
            Nr = len(time_values) // num_tasks

        T = {}
        idx = 0

        for i in range(num_tasks):
            times_for_task_i = []
            for r in range(Nr):
                times_for_task_i.append(time_values[idx])
                idx += 1
            T[i] = times_for_task_i

        return True, T, graph, num_tasks, Nr

    except Exception as e:
        print(f"Lỗi parse .alb file {file_path}: {e}")
        return False, None, None, 0, 0


def read_data_dispatch(file_path):
    """Điều hướng bộ đọc dựa vào đuôi file."""
    if file_path.endswith('.alb') or file_path.endswith('.ALB'):
        return parse_alb_file(file_path)
    else:
        return read_csv_data(file_path)


def read_csv_data(file_path):
    """Bộ đọc cũ cho file .txt (CSV tab-delimited)"""
    T = {}
    graph = defaultdict(list)
    Nr = 0
    try:
        with open(file_path, 'r') as f:
            reader = csv.DictReader(f, delimiter='\t')
            fieldnames = reader.fieldnames
            if not fieldnames: return False, None, None, 0, 0

            robot_columns = [col for col in fieldnames if col.startswith('Robot ')]
            Nr = len(robot_columns)
            for row in reader:
                task = int(row['Task']) - 1
                if row['Successor'].strip():
                    successors = [int(s.strip()) - 1 for s in row['Successor'].split(',')]
                else:
                    successors = []
                graph[task] = successors
                T[task] = [0] * Nr
                for i, robot_col in enumerate(robot_columns):
                    T[task][i] = int(row[robot_col])
        Na = len(T)
        return True, T, graph, Na, Nr
    except:
        return False, None, None, 0, 0


def solve_instance(file_name, T, graph, Na, Nr, time_limit_ms):
    """Hàm giải MIP (Không đổi logic)"""
    Nw = Nr
    solver = pywraplp.Solver.CreateSolver("SCIP")
    if not solver: return "Solver Error"
    solver.SetTimeLimit(int(time_limit_ms))

    # Variables
    X = [[solver.BoolVar(f'X_{i}_{s}') for s in range(Nw)] for i in range(Na)]
    Y = [[solver.BoolVar(f'Y_{s}_{r}') for r in range(Nr)] for s in range(Nw)]
    Z = [[[solver.BoolVar(f'Z_{i}_{s}_{r}') for r in range(Nr)] for s in range(Nw)] for i in range(Na)]
    CT = solver.NumVar(0, solver.infinity(), 'CT')

    # Constraints
    for j in range(Na):
        solver.Add(solver.Sum(X[j][s] for s in range(Nw)) == 1)
    for s in range(Nw):
        solver.Add(solver.Sum(Y[s][r] for r in range(Nr)) == 1)

    # Linearization Z = X * Y
    for j in range(Na):
        for s in range(Nw):
            for r in range(Nr):
                solver.Add(Z[j][s][r] <= X[j][s])
                solver.Add(Z[j][s][r] <= Y[s][r])
                solver.Add(Z[j][s][r] >= X[j][s] + Y[s][r] - 1)

    # Precedence
    for j in range(Na):
        for i in graph[j]:  # j -> i
            solver.Add(solver.Sum(s * X[j][s] for s in range(Nw)) <= solver.Sum(s * X[i][s] for s in range(Nw)))

    # Cycle Time
    for s in range(Nw):
        solver.Add(solver.Sum(Z[i][s][r] * T[i][r] for i in range(Na) for r in range(Nr)) <= CT)

    solver.Minimize(CT)
    status = solver.Solve()

    if status == pywraplp.Solver.OPTIMAL:
        return f"OPTIMAL: CT = {CT.solution_value()}"
    elif status == pywraplp.Solver.FEASIBLE:
        return f"FEASIBLE: CT = {CT.solution_value()}"
    else:
        return "NO SOLUTION"


def main():
    # 1. Giải nén
    has_files = extract_zip_data()
    if not has_files:
        pass

    # 2. Quét file trong thư mục đã giải nén
    search_path = os.path.join(DATA_FOLDER_NAME, "**")
    files = glob.glob(os.path.join(DATA_FOLDER_NAME, "**", "*.txt"), recursive=True) + \
            glob.glob(os.path.join(DATA_FOLDER_NAME, "**", "*.alb"), recursive=True) + \
            glob.glob(os.path.join(DATA_FOLDER_NAME, "**", "*.ALB"), recursive=True)

    files = sorted(list(set(files)))

    print(f"\nTìm thấy {len(files)} file dữ liệu.")
    print(f"Giới hạn thời gian: {TOTAL_TIME_LIMIT_MINUTES} phút (Max {INSTANCE_TIME_LIMIT_SECONDS}s/bài).")
    print("-" * 60)

    global_start = time.time()
    global_limit = global_start + (TOTAL_TIME_LIMIT_MINUTES * 60)

    for file_path in files:
        if time.time() >= global_limit:
            print("ĐÃ HẾT THỜI GIAN TOÀN BỘ CHƯƠNG TRÌNH.")
            break

        file_name = os.path.basename(file_path)

        # Đọc dữ liệu
        success, T, graph, Na, Nr = read_data_dispatch(file_path)

        if not success:
            print(f"{file_name}: Skipped (Read Error)")
            continue

        # Tính thời gian chạy cho instance
        remaining = global_limit - time.time()
        instance_limit = min(remaining, INSTANCE_TIME_LIMIT_SECONDS) * 1000

        print(f"Solving {file_name} (Tasks={Na}, Robots={Nr})... ", end="")
        result = solve_instance(file_name, T, graph, Na, Nr, instance_limit)
        print(result)


if __name__ == "__main__":
    main()