"""Theorem 4.3 / Corollaries 4.5-4.6: compare enumerated (r=4, p=7) C4-free graphs with the construction."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gtools import *

RES = sys.argv[1]; NMAX = int(sys.argv[2])

def constructions(n):
    """All graphs from Theorem 4.3's construction on n vertices (with S, b, m)."""
    out = {}
    for b_mask in range(64):
        b = bin(b_mask).count('1')
        a = n - 6 - b
        if a < 6: continue
        # compositions of a into 6 positive parts
        def comps(total, parts):
            if parts == 1:
                yield (total,); return
            for x in range(1, total - parts + 2):
                for rest in comps(total - x, parts - 1): yield (x,) + rest
        for sizes in comps(a, 6):
            # matching sizes per class
            ranges = [range(0, s // 2 + 1) for s in sizes]
            for ms in itertools.product(*ranges):
                E = [(f'v{i}', f'v{(i+1)%6}') for i in range(6)]
                for i, (s, mi) in enumerate(zip(sizes, ms)):
                    for j in range(s): E.append((f'v{i}', f'w{i}_{j}'))
                    for j in range(mi): E.append((f'w{i}_{2*j}', f'w{i}_{2*j+1}'))
                for i in range(6):
                    if b_mask >> i & 1:
                        E += [(f'y{i}', f'v{i}'), (f'y{i}', f'v{(i+1)%6}')]
                g = g6_from_named(E)
                out[g] = (b, sum(ms))
    return out

for n in range(8, NMAX + 1):
    fn = os.path.join(RES, f"p8free_{n}.txt")
    enum = []
    with open(fn) as f:
        for line in f:
            g6, *v = line.split(); v = list(map(int, v))
            if v[4] == 7 and v[5] == 4:   # p=7, r=4
                enum.append((g6, v[3]))
    cons = constructions(n)
    cg = list(cons.keys())
    canon_cons = dict(zip(canon(cg), cg)) if cg else {}
    canon_enum = canon([g for g, _ in enum]) if enum else []
    c8 = set()
    if n == 8:
        c8 = set(canon([to_g6(8, [(i, (i + 1) % 8) for i in range(8)])]))
    ok_cover = all(c in canon_cons or c in c8 for c in canon_enum)
    ok_converse = set(canon_cons) <= set(canon_enum)
    # check S formula on constructions
    ok_S = True
    for g, (b, m) in cons.items():
        a = decode(g); nn = len(a)
        if S_of(a) != 2 * nn - b - m or has_c4(a) or longest_induced_path(a) != 7 or radius(a) != 4:
            ok_S = False
    smax = max([s for _, s in enum], default=None)
    print(f"n={n:2d}: enumerated (r=4,p=7): {len(enum):4d}  construction classes: {len(canon_cons):4d}  "
          f"enum ⊆ cons∪{{C8}}: {ok_cover}  cons ⊆ enum: {ok_converse}  S=2n-b-m & props on cons: {ok_S}  max S={smax} (2n={2*n})")
