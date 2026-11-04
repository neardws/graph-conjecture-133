"""Checks on connected strong-C4-free P7-free graphs (from gstat output files).
Columns: g6 n e T S p r diam hasC4 minL adjdeg2 minDeg
"""
import sys, os
from fractions import Fraction as F

RES = sys.argv[1]
NMAX = int(sys.argv[2])

def rows(n):
    fn = os.path.join(RES, f"p7free_{n}.txt")
    with open(fn) as f:
        for line in f:
            g6, *v = line.split()
            n_, e, T, S, p, r, dm, c4, minL, a2, mind = map(int, v)
            yield dict(g6=g6, n=n_, e=e, T=T, S=S, p=p, r=r, diam=dm, c4=c4, minL=minL, a2=a2, mind=mind)

def decode(g6):
    s = g6.encode()
    n = s[0] - 63
    adj = [set() for _ in range(n)]
    bits = []
    for ch in s[1:]:
        v = ch - 63
        bits.extend((v >> (5 - k)) & 1 for k in range(6))
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i].add(j); adj[j].add(i)
            k += 1
    return adj

M_expected = {7: F(16, 7), 8: F(5, 2), 9: F(8, 3), 10: F(3)}
print("== Theorem 3.6 (P6-free, i.e. p<=5) and Theorem 5.8 (P7-free, p<=6) ==")
for n in range(2, NMAX + 1):
    R = list(rows(n))
    assert all(x['c4'] == 0 for x in R)
    p6 = [x for x in R if x['p'] <= 5]
    mS6 = max(x['S'] for x in p6)
    ext6 = [x for x in p6 if x['S'] == mS6]
    mS7 = max(x['S'] for x in R)
    ext7 = [x for x in R if x['S'] == mS7]
    exp = M_expected.get(n, F(2 * n + 2, n) if n >= 11 else None)
    flag6 = '' if exp is None else ('OK' if F(mS6, n) == exp else 'MISMATCH')
    viol3n = [x for x in R if x['S'] > 3 * n]
    eq3n = [x for x in R if x['S'] == 3 * n]
    print(f"n={n:2d}  P6-free: maxS={mS6:3d} (ell={str(F(mS6,n)):>6}) #extremal={len(ext6)} {flag6:8s} "
          f"| P7-free: maxS={mS7:3d} #ext={len(ext7)}  S>3n:{len(viol3n)}  S=3n:{[x['g6'] for x in eq3n]}")
    if n in (4, 6) or (n >= 7 and len(ext6) != 1):
        print("     P6-free extremal graphs:", [x['g6'] for x in ext6])

print()
print("== Lemma 5.7: triangle, min L>=4, no adjacent degree-2 pair (P7-free C4-free connected) ==")
for n in range(2, NMAX + 1):
    hits = [x for x in rows(n) if x['T'] >= 1 and x['minL'] >= 4 and x['a2'] == 0]
    print(f"n={n:2d}: {len(hits)} graphs", [(x['g6'], x['e'], x['T'], x['S']) for x in hits])

print()
print("== Corollary 6.3: p = 6 => S <= 3n-1;   sup ell on (r,p)=(2,6),(3,6) ==")
for n in range(2, NMAX + 1):
    R = [x for x in rows(n) if x['p'] == 6]
    if not R: continue
    mx = max(x['S'] for x in R)
    by = {}
    for x in R:
        key = (x['r'], x['p'])
        by[key] = max(by.get(key, 0), x['S'])
    print(f"n={n:2d}: max S with p=6: {mx} (3n-1={3*n-1})  by (r,p): " +
          ", ".join(f"{k}:{v} (3n-S={3*n-v})" for k, v in sorted(by.items())))

print()
print("== Lemma S5.6 / S5.7: deficit Delta = 2n-3-e on connected C4-free P7-free ==")
for n in range(2, NMAX + 1):
    R = list(rows(n))
    worst = min(2 * n - 3 - x['e'] for x in R)
    t1 = [2 * n - 3 - x['e'] for x in R if x['T'] <= 1]
    t2 = [2 * n - 3 - x['e'] for x in R if x['T'] == 2]
    s_t1 = [x['S'] for x in R if x['T'] == 1]
    s_t2 = [x['S'] for x in R if x['T'] >= 2]
    msg = f"n={n:2d}: min Delta={worst}"
    if t1 and n >= 5: msg += f"  min Delta(T<=1)={min(t1)}"
    if t2 and n >= 6: msg += f"  min Delta(T=2)={min(t2)}"
    if s_t1 and n >= 5: msg += f"  max S(T=1)={max(s_t1)} (4n-13={4*n-13})"
    if s_t2 and n >= 4: msg += f"  max S(T>=2)={max(s_t2)} (4n-14={4*n-14})"
    print(msg)

print()
print("== Lemma 3.3: P5-free (p<=4): S <= 2n - h, h = #{v: lambda(v) >= 3} ==")
bad = 0; tot = 0; tight = 0
for n in range(2, NMAX + 1):
    for x in rows(n):
        if x['p'] > 4: continue
        adj = decode(x['g6'])
        lam = []
        for v in range(n):
            Nv = adj[v]
            t = sum(len(adj[u] & Nv) for u in Nv) // 2
            lam.append(len(Nv) - t)
        h = sum(1 for l in lam if l >= 3)
        assert sum(lam) == x['S']
        tot += 1
        if x['S'] > 2 * n - h: bad += 1; print("  VIOLATION", x['g6'])
        if x['S'] == 2 * n - h: tight += 1
print(f"checked {tot} P5-free graphs, violations: {bad}, tight: {tight}")
