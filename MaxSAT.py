import sys
import math
import csv
import time
from collections import deque
from pysat.solvers import Solver
from pysat.formula import IDPool, WCNF
from pysat.card import CardEnc
from pysat.pb import PBEnc
from pysat.examples.rc2 import RC2  # Solver MaxSAT mạnh nhất của PySAT


# =============================================================================
# 1. DATA PROCESSING
# =============================================================================
class ProblemData:
    def __init__(self, filepath, num_stations=3):
        self.Na = 0
        self.Nr = 0
        self.Nw = num_stations
        self.T = []
        self.adj = []
        self.neighbors = []
        self.LB = 0
        self.UB = 0
        self.T_min = []
        self._read_data(filepath)
        self._calculate_bounds()

    def _read_data(self, filepath):
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                self.Na = sum(1 for _ in f) - 1
            self.T = [{} for _ in range(self.Na)]
            self.adj = [[] for _ in range(self.Na)]
            with open(filepath, 'r', encoding='utf-8') as f:
                reader = csv.DictReader(f, delimiter='\t')
                robot_cols = [c for c in reader.fieldnames if c.lower().startswith("robot")]
                self.Nr = len(robot_cols)
                for row in reader:
                    task = int(row['Task']) - 1
                    succ_str = row['Successor'].strip()
                    if succ_str:
                        for s in succ_str.split(','):
                            succ = int(s.strip()) - 1
                            self.adj[task].append(succ)
                    for r_idx, col in enumerate(robot_cols):
                        self.T[task][r_idx] = int(row[col])
        except Exception:
            sys.exit(1)

    def _calculate_bounds(self):
        self.T_min = [min(self.T[j].values()) if self.T[j] else 0 for j in range(self.Na)]
        p = sorted(self.T_min, reverse=True)
        prefix = [0]
        for x in p: prefix.append(prefix[-1] + x)
        calc_lb = 0
        for k in range(1, len(p) + 1):
            val = math.ceil(prefix[k] / ((k + self.Nw - 1) // self.Nw))
            calc_lb = max(calc_lb, int(val))
        self.LB = calc_lb
        indeg = [0] * self.Na
        for u in range(self.Na):
            for v in self.adj[u]: indeg[v] += 1
        q = deque([i for i in range(self.Na) if indeg[i] == 0])
        dist = [0] * self.Na
        while q:
            u = q.popleft()
            finish_u = dist[u] + self.T_min[u]
            for v in self.adj[u]:
                dist[v] = max(dist[v], finish_u)
                indeg[v] -= 1
                if indeg[v] == 0: q.append(v)
        max_dist = max([dist[i] + self.T_min[i] for i in range(self.Na)]) if self.Na else 0
        self.UB = max(int(math.ceil(max_dist)), self.LB)


# =============================================================================
# 2. PHASE 1: FAST BINARY SEARCH (Tìm CT nhỏ nhất)
# =============================================================================
class Phase1Scheduler:
    def __init__(self, data):
        self.data = data
        self.vpool = IDPool()
        # Sửa: Bỏ tham số incremental=True để tránh lỗi
        self.solver = Solver(name='glucose4')
        self.X = [[self.vpool.id(f'X_{j}_{s}') for s in range(data.Nw)] for j in range(data.Na)]
        self.Y = [[self.vpool.id(f'Y_{s}_{r}') for r in range(data.Nr)] for s in range(data.Nw)]
        self.Z = {}
        self._build_static_model()

    def _get_z(self, j, s, r):
        if (j, s, r) not in self.Z:
            z = self.vpool.id(f'Z_{j}_{s}_{r}')
            self.Z[(j, s, r)] = z
            x, y = self.X[j][s], self.Y[s][r]
            self.solver.add_clause([-z, x])
            self.solver.add_clause([-z, y])
            self.solver.add_clause([-x, -y, z])
        return self.Z[(j, s, r)]

    def _build_static_model(self):
        for j in range(self.data.Na):
            for c in CardEnc.equals(self.X[j], 1, vpool=self.vpool).clauses: self.solver.add_clause(c)
        for s in range(self.data.Nw):
            for c in CardEnc.equals(self.Y[s], 1, vpool=self.vpool).clauses: self.solver.add_clause(c)
        for u in range(self.data.Na):
            for v in self.data.adj[u]:
                for s_u in range(self.data.Nw):
                    for s_v in range(s_u): self.solver.add_clause([-self.X[u][s_u], -self.X[v][s_v]])
        for j in range(self.data.Na):
            for s in range(self.data.Nw):
                for r in range(self.data.Nr): self._get_z(j, s, r)

    def find_min_cycle_time(self):
        low, high = self.data.LB, self.data.UB
        best_K = -1

        while low <= high:
            mid = (low + high) // 2
            selector = self.vpool.id(f'SEL_{mid}')

            # Thêm ràng buộc Cycle Time <= mid với selector
            for s in range(self.data.Nw):
                lits, weights = [], []
                for j in range(self.data.Na):
                    for r in range(self.data.Nr):
                        t = self.data.T[j][r]
                        if t > 0:
                            lits.append(self.Z[(j, s, r)])
                            weights.append(t)
                if lits:
                    cnf = PBEnc.leq(lits, weights, mid, vpool=self.vpool)
                    for c in cnf.clauses: self.solver.add_clause([-selector] + c)

            if self.solver.solve(assumptions=[selector]):
                best_K = mid
                high = mid - 1
            else:
                low = mid + 1

        self.solver.delete()
        return best_K


# =============================================================================
# 3. PHASE 2: MAXSAT OPTIMIZATION (Tối ưu Tổng thời gian)
# =============================================================================
def run_phase2_maxsat(data, optimal_K):
    print(f"🔄 Phase 2: Optimizing Total Time with Cycle Time <= {optimal_K}...")

    # WCNF: Weighted CNF (Định dạng cho MaxSAT)
    wcnf = WCNF()
    vpool = IDPool()

    X = [[vpool.id(f'X_{j}_{s}') for s in range(data.Nw)] for j in range(data.Na)]
    Y = [[vpool.id(f'Y_{s}_{r}') for r in range(data.Nr)] for s in range(data.Nw)]
    Z = {}

    def get_z(j, s, r):
        if (j, s, r) not in Z:
            z = vpool.id(f'Z_{j}_{s}_{r}')
            Z[(j, s, r)] = z
            x, y = X[j][s], Y[s][r]
            # Hard clauses cho Z (Weight = None nghĩa là Hard)
            wcnf.append([-z, x])
            wcnf.append([-z, y])
            wcnf.append([-x, -y, z])
        return Z[(j, s, r)]

    # 1. Hard Clauses (Giống hệt Phase 1)
    for j in range(data.Na):
        for c in CardEnc.equals(X[j], 1, vpool=vpool).clauses: wcnf.append(c)
    for s in range(data.Nw):
        for c in CardEnc.equals(Y[s], 1, vpool=vpool).clauses: wcnf.append(c)
    for u in range(data.Na):
        for v in data.adj[u]:
            for s_u in range(data.Nw):
                for s_v in range(s_u): wcnf.append([-X[u][s_u], -X[v][s_v]])

    # Khởi tạo Z
    for j in range(data.Na):
        for s in range(data.Nw):
            for r in range(data.Nr): get_z(j, s, r)

    # 2. Hard Constraint: Cycle Time <= optimal_K (Kết quả từ Phase 1)
    # Đây là điểm mấu chốt: Ta ép MaxSAT không được vượt quá thời gian Cycle Time tốt nhất
    for s in range(data.Nw):
        lits, weights = [], []
        for j in range(data.Na):
            for r in range(data.Nr):
                if data.T[j][r] > 0:
                    lits.append(Z[(j, s, r)])
                    weights.append(data.T[j][r])
        if lits:
            # PBEnc.leq tạo Hard Clauses
            for c in PBEnc.leq(lits, weights, optimal_K, vpool=vpool).clauses:
                wcnf.append(c)

    # 3. Soft Clauses: Minimize Total Time
    # Logic: Với mỗi khả năng chọn Z_jsr, ta thêm 1 Soft Clause: "Không chọn Z_jsr"
    # Nếu bộ giải CHỌN Z_jsr (Vi phạm clause này), nó phải trả chi phí = Time[j][r]
    # MaxSAT sẽ cố gắng trả ít chi phí nhất -> Tổng thời gian nhỏ nhất
    for j in range(data.Na):
        for s in range(data.Nw):
            for r in range(data.Nr):
                t = data.T[j][r]
                z = Z[(j, s, r)]
                # Soft clause: [-z], weight = t
                wcnf.append([-z], weight=t)

    # Giải bằng RC2 (MaxSAT Solver)
    with RC2(wcnf) as rc2:
        model = rc2.compute()  # Tìm lời giải tối ưu
        total_time_minimized = rc2.cost

        if model:
            return decode_solution(model, data, X, Y, vpool), total_time_minimized
        return None, 0


def decode_solution(model, data, X, Y, vpool):
    model_set = set(model)
    assignment = {}
    s_robot = {}

    # Map lại ID từ vpool sang giá trị thực
    # Vì vpool của Phase 2 khác Phase 1

    # Tìm Robot cho trạm
    for s in range(data.Nw):
        for r in range(data.Nr):
            # Lấy ID thực tế từ vpool object
            y_id = Y[s][r]
            if y_id in model_set:
                s_robot[s] = r
                break

    # Tìm Task cho trạm
    for j in range(data.Na):
        for s in range(data.Nw):
            x_id = X[j][s]
            if x_id in model_set:
                r = s_robot.get(s, -1)
                assignment[j] = {'station': s, 'robot': r, 'time': data.T[j][r]}
                break
    return assignment


# =============================================================================
# MAIN ORCHESTRATOR
# =============================================================================
def solve_lexicographic(filepath, num_stations):
    start_global = time.time()
    data = ProblemData(filepath, num_stations)

    # --- STEP 1: Tìm Cycle Time nhỏ nhất (SAT) ---
    print(f"🚀 Phase 1: Binary Search for Optimal Cycle Time...")
    phase1 = Phase1Scheduler(data)
    best_K = phase1.find_min_cycle_time()

    if best_K == -1:
        print("❌ Unsatisfiable (Phase 1). Check Input.")
        return

    print(f"✅ Found Optimal Cycle Time: {best_K}")

    # --- STEP 2: Tìm Tổng thời gian nhỏ nhất với CT cố định (MaxSAT) ---
    best_sol, min_total_time = run_phase2_maxsat(data, best_K)

    runtime = time.time() - start_global

    # --- OUTPUT ---
    if best_sol:
        print("\n" + "=" * 40)
        print(f"🏆 FINAL RESULT (Lexicographic Optimization)")
        print(f"   1. Cycle Time (Makespan): {best_K} (Optimal)")
        print(f"   2. Total Time (Sum):      {min_total_time} (Minimized)")
        print("=" * 40)

        st_loads = [0] * num_stations
        st_tasks = [[] for _ in range(num_stations)]
        st_rob = {}

        for j, info in best_sol.items():
            s = info['station']
            st_tasks[s].append((j, info['time']))
            st_loads[s] += info['time']
            st_rob[s] = info['robot']

        for s in range(num_stations):
            rid = st_rob.get(s, -1)
            rname = f"Robot {rid + 1}" if rid != -1 else "N/A"
            print(f"Station {s + 1} ({rname}) | Load: {st_loads[s]}")
            for tid, t in st_tasks[s]:
                print(f"  - Task {tid + 1:02d} ({t}s)")
        print(f"\n⏱ Total Runtime: {runtime:.4f}s")
    else:
        print("Error in Phase 2.")


if __name__ == "__main__":
    solve_lexicographic("Dataset2.txt", 3)