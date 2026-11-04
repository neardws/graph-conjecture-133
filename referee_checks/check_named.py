import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gtools import *

RES = sys.argv[1]

def rows(n):
    with open(os.path.join(RES, f"p7free_{n}.txt")) as f:
        for line in f:
            g6, *v = line.split(); v = list(map(int, v))
            yield g6, v

# Petersen as Kneser K(5,2)
subs = list(itertools.combinations(range(1, 6), 2))
pet_edges = [(a, b) for a, b in itertools.combinations(subs, 2) if not set(a) & set(b)]
PET = g6_from_named(pet_edges)

# H_{3,2}: K5 on A={a1,a2,a3}, B={b1,b2}; subdivide each A-B edge once
A = ['a1', 'a2', 'a3']; B = ['b1', 'b2']
H32 = [('a1', 'a2'), ('a1', 'a3'), ('a2', 'a3'), ('b1', 'b2')]
for a in A:
    for b in B:
        z = 'z' + a[1] + b[1]
        H32 += [(a, z), (z, b)]
H32g6 = g6_from_named(H32)
adj = decode(H32g6)
print("H_{3,2}: n=%d e=%d C4=%s p=%d S=%d" % (len(adj), sum(map(len, adj)) // 2, has_c4(adj),
      longest_induced_path(adj), S_of(adj)))
L = []
for v in range(len(adj)):
    Nv = adj[v]; t = sum(len(adj[u] & Nv) for u in Nv) // 2; L.append(2 * len(Nv) - 3 * t)
print("   deletion losses:", sorted(L))

# Lemma 5.7 hit at n=11
hits = [g for g, v in rows(11) if v[2] >= 1 and v[8] >= 4 and v[9] == 0]
print("Lemma 5.7 enumerated graph == H_{3,2}:", canon(hits) == canon([H32g6]))
eq = [g for g, v in rows(10) if v[3] == 30]
print("S=3n graph at n=10 == Petersen:", canon(eq) == canon([PET]))

# Theorem 3.6 named extremal graphs
def cycle6():
    return [(f'c{i}', f'c{(i+1)%6}') for i in range(6)]
def gamma(h):
    E = cycle6() + [('a', 'c0'), ('a', 'c3')] + [('a', f'l{j}') for j in range(h)]
    return g6_from_named(E)
def layered(k, hsec):   # Case 1 graphs with k first-layer vertices on distinct antipodal pairs, hsec second-layer
    E = cycle6()
    for i in range(k): E += [(f'a{i}', f'c{i}'), (f'a{i}', f'c{i+3}')]
    for j in range(hsec):
        for i in range(k): E += [(f'x{j}', f'a{i}')]
    return g6_from_named(E)

P_minus_v = layered(3, 0)
print("(3,0) ~ (2,1) [both claimed = P - v]:", canon([layered(3, 0)]) == canon([layered(2, 1)]))
print("(3,1) == Petersen:", canon([layered(3, 1)]) == canon([PET]))
for n in range(7, 15):
    R = [(g, v) for g, v in rows(n) if v[4] <= 5]
    m = max(v[3] for g, v in R)
    ext = [g for g, v in R if v[3] == m]
    if n == 8: named = layered(2, 0); nm = 'H8'
    elif n == 9: named = layered(3, 0); nm = 'P-v'
    elif n == 10: named = PET; nm = 'Petersen'
    else: named = gamma(n - 7); nm = f'Gamma_{n-7}'
    print(f"n={n}: unique extremal == {nm}: {canon(ext) == canon([named])}")

# Gamma_h P6-free and S=2n+2 for larger h
for h in range(0, 12):
    a = decode(gamma(h)); n = len(a)
    assert not has_c4(a) and longest_induced_path(a) <= 5 and S_of(a) == 2 * n + 2, h
print("Gamma_h (h<12): C4-free, P6-free, S=2n+2  OK")
