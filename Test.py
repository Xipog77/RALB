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
