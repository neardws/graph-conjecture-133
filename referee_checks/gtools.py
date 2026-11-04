"""Small helpers: graph6 encode/decode, canonical labelling via nauty labelg, invariants."""
import subprocess, itertools

def to_g6(n, edges):
    bits = []
    E = set(frozenset(e) for e in edges)
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if frozenset((i, j)) in E else 0)
    while len(bits) % 6: bits.append(0)
    s = chr(n + 63)
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k + 6]: v = (v << 1) | b
        s += chr(v + 63)
    return s

def decode(g6):
    s = g6.encode(); n = s[0] - 63
    adj = [set() for _ in range(n)]
    bits = []
    for ch in s[1:]:
        v = ch - 63; bits.extend((v >> (5 - k)) & 1 for k in range(6))
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]: adj[i].add(j); adj[j].add(i)
            k += 1
    return adj

def canon(g6list):
    out = subprocess.run(["labelg", "-q"], input="\n".join(g6list) + "\n",
                         capture_output=True, text=True).stdout.split()
    return out

def relabel(edges):
    vs = sorted({v for e in edges for v in e}, key=str)
    idx = {v: i for i, v in enumerate(vs)}
    return len(vs), [(idx[a], idx[b]) for a, b in edges]

def g6_from_named(edges, extra_vertices=()):
    vs = sorted({v for e in edges for v in e} | set(extra_vertices), key=str)
    idx = {v: i for i, v in enumerate(vs)}
    return to_g6(len(vs), [(idx[a], idx[b]) for a, b in edges])

def longest_induced_path(adj):
    n = len(adj); best = 0
    def dfs(last, B, ln):
        nonlocal best
        best = max(best, ln)
        for y in adj[last] - B:
            dfs(y, B | adj[last] | {last}, ln + 1)
    for s in range(n): dfs(s, set(), 1)
    return best

def has_c4(adj):
    n = len(adj)
    return any(len(adj[u] & adj[w]) >= 2 for u in range(n) for w in range(u + 1, n))

def S_of(adj):
    tot = 0
    for v in range(len(adj)):
        Nv = adj[v]; t = sum(len(adj[u] & Nv) for u in Nv) // 2
        tot += len(Nv) - t   # valid in C4-free graphs
    return tot

def ecc(adj, v):
    n = len(adj); dist = {v: 0}; fr = [v]
    while fr:
        nf = []
        for x in fr:
            for y in adj[x]:
                if y not in dist: dist[y] = dist[x] + 1; nf.append(y)
        fr = nf
    return max(dist.values()) if len(dist) == n else 10**9

def radius(adj): return min(ecc(adj, v) for v in range(len(adj)))
