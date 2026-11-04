"""Triangle-free strong-C4-free P7-free connected graphs (girth>=5, no induced P7).
Checks: Theorem 5.5, Theorem 5.6 (f(n) and number of extremal classes), Lemma 2.10,
and that every 2-connected member is in the family F of Lemma 5.1 as transcribed in the manuscript."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gtools import *

LEV = sys.argv[1]; NMAX = int(sys.argv[2])

def load(n):
    with open(os.path.join(LEV, f"g5p7_{n}.txt")) as f:
        return [l.strip() for l in f if l.strip()]

def ecount(adj): return sum(map(len, adj)) // 2

def connected(adj, removed=frozenset()):
    vs = [v for v in range(len(adj)) if v not in removed]
    if not vs: return True
    seen = {vs[0]}; st = [vs[0]]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in removed and y not in seen: seen.add(y); st.append(y)
    return len(seen) == len(vs)

def biconnected(adj):
    return len(adj) >= 3 and all(connected(adj, frozenset([v])) for v in range(len(adj)))

def edge_cutset(adj):
    return any(connected(adj) and not connected(adj, frozenset([u, v]))
               for u in range(len(adj)) for v in adj[u] if u < v)

# ---- family F of Lemma 5.1 as described in the manuscript ----
def C(k, pre='v'): return [(f'{pre}{i}', f'{pre}{i % k + 1}') for i in range(1, k + 1)]
def F2(t):
    E = C(5)
    for j in range(t):
        E += [(f'A1_{j}', 'v1'), (f'A3_{j}', 'v3'), (f'A1_{j}', f'A3_{j}')]
    return E
def F0p(t):
    E = C(6)
    for j in range(t):
        E += [(f'Y1_{j}', 'v1'), (f'Y4_{j}', 'v4'), (f'Y1_{j}', f'Y4_{j}')]
    return E
F3 = C(5) + [('a3', 'a1'), ('a1', 'a4')] + [(f'a{i}', f'v{i}') for i in (1, 3, 4)]
F4 = C(5) + [('a5', 'a3'), ('a3', 'a1'), ('a1', 'a4')] + [(f'a{i}', f'v{i}') for i in (1, 3, 4, 5)]
subs = list(itertools.combinations(range(1, 6), 2))
PET = [(a, b) for a, b in itertools.combinations(subs, 2) if not set(a) & set(b)]
def x(i): return [(f'x{i}', f'v{i}'), (f'x{i}', f'v{(i + 2) % 7 + 1}')]   # x_i ~ v_i, v_{i+3} on C7 (1-indexed)
F6 = C(7); F7 = F6 + x(1); F8 = F6 + x(1) + x(2); F9 = F8 + [('y', 'x1'), ('y', 'x2')]
F10 = F6 + x(1) + x(5); F11 = F6 + x(1) + x(2) + x(5); F12 = F11 + [('y', 'x1'), ('y', 'x2')]
fixed = {'F1=C5': C(5), 'F3': F3, 'F4': F4, 'F5=P': PET, 'F0=C6': C(6), 'F6=C7': F6, 'F7': F7,
         'F8': F8, 'F9': F9, 'F10': F10, 'F11': F11, 'F12': F12}

def family(n):
    out = {}
    for name, E in fixed.items():
        g = g6_from_named(E)
        if g[0] == chr(n + 63): out[name] = g
    if n >= 7 and (n - 5) % 2 == 0: out[f'F2(t={(n-5)//2})'] = g6_from_named(F2((n - 5) // 2))
    if n >= 8 and (n - 6) % 2 == 0: out[f"F0'(t'={(n-6)//2})"] = g6_from_named(F0p((n - 6) // 2))
    return out

print("Lemma 5.2 table (n, e, 3n-2e) and class membership of family members:")
for name, E in list(fixed.items()) + [('F2(t=1)', F2(1)), ('F2(t=4)', F2(4)), ("F0'(t'=1)", F0p(1)), ("F0'(t'=4)", F0p(4))]:
    a = decode(g6_from_named(E)); n = len(a); e = ecount(a)
    tri = any(adj_u & a[w] for w in range(n) for adj_u in [a[w]] for _ in [0] if False)
    tri = any(a[u] & a[v] for u in range(n) for v in a[u])
    print(f"  {name:10s} n={n:2d} e={e:2d} 3n-2e={3*n-2*e:2d}  C4={has_c4(a)} tri={tri} p={longest_induced_path(a)} "
          f"2conn={biconnected(a)} edgecut={edge_cutset(a)}")

def fpred(n):  # Theorem 5.6
    return 3 * n - min(n - 10, 5 + (1 if n % 2 == 0 else 0))
def classes_pred(n):
    if 10 <= n <= 14: return (n - 10) // 2 + 1
    return {15: 4, 16: 7}.get(n, 1 if n % 2 else 3)

print("\nTheorem 5.5 / 5.6:")
for n in range(2, NMAX + 1):
    G = load(n)
    adjs = [decode(g) for g in G]
    es = [ecount(a) for a in adjs]
    me = max(es)
    ext = [g for g, e in zip(G, es) if e == me]
    over = [g for g, e in zip(G, es) if 2 * e > 3 * n]
    eq = [g for g, e in zip(G, es) if 2 * e == 3 * n]
    line = f"n={n:2d} #graphs={len(G):6d} max 2e={2*me:3d}"
    if n >= 10:
        line += f" (pred {fpred(n)}) #extremal={len(ext)} (pred {classes_pred(n)})"
        line += "  OK" if 2 * me == fpred(n) and len(ext) == classes_pred(n) else "  MISMATCH"
    line += f"  2e>3n:{len(over)} 2e=3n:{len(eq)}"
    # Lemma 2.10 and core family
    bic = [(g, a) for g, a in zip(G, adjs) if biconnected(a)]
    bad210 = [g for g, a in bic if edge_cutset(a)]
    fam = family(n)
    famc = set(canon(list(fam.values()))) if fam else set()
    cores_c = canon([g for g, _ in bic]) if bic else []
    notin = [c for c in cores_c if c not in famc]
    missing = [nm for nm, g in fam.items() if canon([g])[0] not in set(cores_c)]
    line += f" | 2-conn:{len(bic)} clique-cutset:{len(bad210)} notInFamily:{len(notin)} familyMissing:{missing}"
    print(line)
