import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gtools import *
from fractions import Fraction as Fr

LEV = sys.argv[1]
subs = list(itertools.combinations(range(1, 6), 2))
PET = [(a, b) for a, b in itertools.combinations(subs, 2) if not set(a) & set(b)]
def C(k, pre='v'): return [(f'{pre}{i}', f'{pre}{i % k + 1}') for i in range(1, k + 1)]
def F2(t):
    E = C(5)
    for j in range(t): E += [(f'A1_{j}', 'v1'), (f'A3_{j}', 'v3'), (f'A1_{j}', f'A3_{j}')]
    return E
def F0p(t):
    E = C(6)
    for j in range(t): E += [(f'Y1_{j}', 'v1'), (f'Y4_{j}', 'v4'), (f'Y1_{j}', f'Y4_{j}')]
    return E
def leaves(E, v, k, tag): return E + [(v, f'leaf{tag}{j}') for j in range(k)]

def stats(E):
    a = decode(g6_from_named(E)); n = len(a)
    return dict(n=n, e=sum(map(len, a)) // 2, c4=has_c4(a), p=longest_induced_path(a), r=radius(a), S=S_of(a),
                T=sum(len(a[u] & a[v]) for u in range(n) for v in a[u]) // 6)

# ---- Theorem 5.6 extremal graphs by canonical form ----
u, w = (1, 2), (3, 4)    # adjacent Petersen vertices
def Pab(a, b): return leaves(leaves(PET, u, a, 'u'), w, b, 'w')
def predicted(n):
    out = []
    if 10 <= n <= 16:
        out += [g6_from_named(Pab(a, n - 10 - a)) for a in range(n - 10, -1, -1) if a >= n - 10 - a]
    if n % 2 == 1 and n >= 15: out.append(g6_from_named(F2((n - 5) // 2)))
    if n % 2 == 0 and n >= 16:
        t = (n - 6) // 2
        out += [g6_from_named(F0p((n - 6) // 2)),
                g6_from_named(leaves(F2(t), 'v1', 1, 'h')),
                g6_from_named(leaves(F2(t), 'v2', 1, 'm'))]
    return out
print("Theorem 5.6 extremal sets equal the named graphs:")
for n in range(10, 26):
    G = [l.strip() for l in open(os.path.join(LEV, f"g5p7_{n}.txt"))]
    es = [sum(map(len, decode(g))) // 2 for g in G]
    me = max(es); ext = [g for g, e in zip(G, es) if e == me]
    pred = predicted(n)
    print(f"  n={n}: {sorted(canon(ext)) == sorted(canon(pred)) and len(set(canon(pred))) == len(pred)}  ({len(ext)} graphs)")

# ---- Proposition 6.2 / Corollary 6.3 ----
print("\nProposition 6.2 theta_k (should be F0'(k-2)): (n,r,p,S,3n-6)")
for k in range(3, 9):
    E = []
    for i in range(k): E += [('x', f'a{i}'), (f'a{i}', f'b{i}'), (f'b{i}', 'y')]
    s = stats(E)
    print(f"  k={k}: n={s['n']} r={s['r']} p={s['p']} S={s['S']} 3n-6={3*s['n']-6} C4={s['c4']} iso F0'(k-2): {canon([g6_from_named(E)]) == canon([g6_from_named(F0p(k-2))])}")
print("Corollary 6.3 F2(t): (n,r,p,ell, 3-5/n)")
for t in range(2, 7):
    s = stats(F2(t)); print(f"  t={t}: n={s['n']} r={s['r']} p={s['p']} ell={Fr(s['S'], s['n'])} target={3 - Fr(5, s['n'])}")

# ---- Example S4.3 ----
Pg = g6_from_named(PET); a = decode(Pg)
# find induced P5 ends u,v
best = None
def paths5(adj):
    n = len(adj)
    def dfs(path, B):
        if len(path) == 5: yield list(path); return
        for y in adj[path[-1]] - B:
            yield from dfs(path + [y], B | adj[path[-1]] | {path[-1]})
    for s in range(n): yield from dfs([s], set())
P5 = next(paths5(a))
E = [(i, j) for i in range(10) for j in a[i] if i < j] + [(P5[0], 'L1'), (P5[-1], 'L2')]
s = stats(E)
print(f"\nExample S4.3: (r,p,n,S,ell)=({s['r']},{s['p']},{s['n']},{s['S']},{Fr(s['S'], s['n'])})  C4={s['c4']} T={s['T']}")

# ---- Example S3.4 ----
adjl = {0: [4, 8, 11], 1: [5, 8, 10], 2: [6, 8, 9], 3: [7, 10], 4: [0, 9, 10], 5: [1, 9, 11], 6: [2, 10, 11], 7: [3, 11],
        8: [0, 1, 2, 12], 9: [2, 4, 5], 10: [1, 3, 4, 6, 13], 11: [0, 5, 6, 7, 14], 12: [8, 13, 14], 13: [10, 12], 14: [11, 12]}
sym = all(u in adjl[v] for u in adjl for v in adjl[u])
E = [(u, v) for u in adjl for v in adjl[u] if u < v]
A = [set(adjl[i]) for i in range(15)]
tri = sum(len(A[u] & A[v]) for u in range(15) for v in A[u]) // 6
# maximal induced paths starting 12,8
res = []
def ext(path, B):
    cand = A[path[-1]] - B
    if not cand: res.append(path); return
    for y in cand: ext(path + [y], B | A[path[-1]] | {path[-1]})
ext([12, 8], A[12] | {12})
q = max(map(len, res)); Eset = sorted({p[-1] for p in res if len(p) == q})
def S_minus(U):
    keep = [v for v in range(15) if v not in U]; idx = {v: i for i, v in enumerate(keep)}
    B = [set(idx[x] for x in A[v] if x in idx) for v in keep]
    return S_of(B)
D = S_of(A) - S_minus(set(Eset))
print(f"\nExample S3.4: symmetric={sym} n=15 e={len(E)} T={tri} C4={has_c4(A)} S={S_of(A)}; q={q}, terminal set E={Eset}, D(E)={D} vs q|E|={q*len(Eset)}")
print("   #maximal paths from (12,8):", len(res), " orders:", sorted(len(p) for p in res))

# ---- Example S3.2 ----
def two_pet_vertex():
    E1 = [((0,) + x, (0,) + y) for x, y in PET]; E2 = [((1,) + x, (1,) + y) for x, y in PET]
    # identify (0,(1,2)) with (1,(1,2))
    ren = lambda v: 'hub' if v in ((0, 1, 2), (1, 1, 2)) else v
    return [(ren(x), ren(y)) for x, y in E1 + E2]
s = stats(two_pet_vertex())
a = decode(g6_from_named(two_pet_vertex())); n = len(a)
L = [2 * len(a[v]) - 3 * (sum(len(a[x] & a[v]) for x in a[v]) // 2) for v in range(n)]
print(f"\nExample S3.2 (two Petersen at a vertex): n={s['n']} S={s['S']} p={s['p']} minL={min(L)} C4={s['c4']}")

# ---- Example S3.6 Heawood ----
# Heawood graph: points/lines of Fano plane
lines = [(0, 1, 3), (1, 2, 4), (2, 3, 5), (3, 4, 6), (4, 5, 0), (5, 6, 1), (6, 0, 2)]
E = [(f'p{p}', f'L{i}') for i, l in enumerate(lines) for p in l]
s = stats(E); a = decode(g6_from_named(E)); n = len(a)
Z = sum(1 for x in range(n) for y in range(x + 1, n) if y not in a[x] and not (a[x] & a[y]))
print(f"\nExample S3.6 Heawood: n={s['n']} T={s['T']} r={s['r']} S={s['S']} Z={Z} p={s['p']} sum d^2={sum(len(x)**2 for x in a)} n(n-1)+6T-2Z={n*(n-1)+6*s['T']-2*Z}")

# ---- Example S3.5 Petersen eligible cores ----
print("\nExample S3.5: eligible cores of Petersen (proper, connected, dominating, p(H) <= p(G)-2 = 3):")
a = decode(Pg); n = 10; cores = []
for mask in range(1, 1 << n):
    U = [v for v in range(n) if mask >> v & 1]
    if len(U) == n: continue
    Us = set(U)
    if any(not (a[v] & Us) and v not in Us for v in range(n)): continue
    idx = {v: i for i, v in enumerate(U)}; B = [set(idx[x] for x in a[v] if x in Us) for v in U]
    if not all(B[i] or len(U) == 1 for i in range(len(U))): pass
    if radius(B) >= 10**9: continue
    if longest_induced_path(B) <= 3: cores.append((U, S_of(B)))
print(f"   count={len(cores)} sizes={sorted(set(len(c[0]) for c in cores))} S(H) values={sorted(set(c[1] for c in cores))}")
