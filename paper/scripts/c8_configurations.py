#!/usr/bin/env python3
"""Enumerate dominating-C8 extensions used in Remark on the radius-four count.

The cycle is the labelled 8-cycle 0-1-...-7-0. A trace is a nonempty subset of
the cycle. The trace is admissible when the graph obtained by adding one vertex
adjacent exactly to that subset has no 4-cycle subgraph and no induced P8.
Configurations are built by adding admissible traces in increasing bitmask
order. A new outside vertex may be joined to any subset of the outside
vertices already chosen. A graph is kept only when it still has no 4-cycle
subgraph and no induced P8. The bare cycle is included.

The script prints the number of labelled configurations by order and the
number of isomorphism classes of the underlying unlabelled graphs.
"""

from __future__ import annotations

import sys
from collections import defaultdict


def has_c4(adj: list[set[int]]) -> bool:
    n = len(adj)
    for i in range(n):
        for j in range(i + 1, n):
            if len(adj[i] & adj[j]) >= 2:
                return True
    return False


def has_induced_path(adj: list[set[int]], length: int) -> bool:
    """True if some induced path has `length` vertices."""
    n = len(adj)
    target = length

    def dfs(path: list[int], used: set[int]) -> bool:
        if len(path) == target:
            return True
        u = path[-1]
        earlier = path[:-1]
        for v in adj[u]:
            if v in used:
                continue
            if any(v in adj[w] for w in earlier):
                continue
            used.add(v)
            path.append(v)
            if dfs(path, used):
                return True
            path.pop()
            used.remove(v)
        return False

    for s in range(n):
        if dfs([s], {s}):
            return True
    return False


def cycle_graph() -> list[set[int]]:
    adj = [set() for _ in range(8)]
    for i in range(8):
        adj[i].add((i + 1) % 8)
        adj[i].add((i - 1) % 8)
    return adj


def admissible_traces() -> list[int]:
    base = cycle_graph()
    good = []
    for mask in range(1, 256):
        adj = [set(s) for s in base]
        adj.append(set())
        for i in range(8):
            if mask & (1 << i):
                adj[8].add(i)
                adj[i].add(8)
        if has_c4(adj) or has_induced_path(adj, 8):
            continue
        good.append(mask)
    return good


def add_vertex(adj: list[set[int]], trace: int, edge_mask: int) -> list[set[int]]:
    out = [set(s) for s in adj]
    v = len(out)
    out.append(set())
    for i in range(8):
        if trace & (1 << i):
            out[v].add(i)
            out[i].add(v)
    bit = 0
    for u in range(8, v):
        if edge_mask & (1 << bit):
            out[v].add(u)
            out[u].add(v)
        bit += 1
    return out


def refine(adj: list[set[int]], colors: list[int]) -> list[int]:
    n = len(adj)
    current = colors
    while True:
        buckets: dict[tuple, list[int]] = defaultdict(list)
        sigs = []
        for v in range(n):
            counts: dict[int, int] = defaultdict(int)
            for u in adj[v]:
                counts[current[u]] += 1
            sig = (current[v], tuple(sorted(counts.items())))
            sigs.append(sig)
            buckets[sig].append(v)
        order = sorted(buckets)
        rank = {sig: i for i, sig in enumerate(order)}
        nxt = [rank[sig] for sig in sigs]
        if nxt == current:
            return current
        current = nxt


def canonical(adj: list[set[int]]) -> tuple[tuple[int, int], ...]:
    n = len(adj)
    best: list[tuple[tuple[int, int], ...] | None] = [None]

    def consider(colors: list[int]) -> None:
        order = sorted(range(n), key=lambda v: colors[v])
        pos = {v: i for i, v in enumerate(order)}
        edges = []
        for v in range(n):
            for u in adj[v]:
                if pos[v] < pos[u]:
                    edges.append((pos[v], pos[u]))
        cert = tuple(sorted(edges))
        if best[0] is None or cert < best[0]:
            best[0] = cert

    def search(colors: list[int]) -> None:
        colors = refine(adj, colors)
        cells: dict[int, list[int]] = defaultdict(list)
        for v, c in enumerate(colors):
            cells[c].append(v)
        multi = None
        for c in sorted(cells):
            if len(cells[c]) > 1:
                multi = cells[c]
                break
        if multi is None:
            consider(colors)
            return
        fresh = max(colors) + 1
        for v in multi:
            nxt = colors[:]
            nxt[v] = fresh
            search(nxt)

    search([len(adj[v]) for v in range(n)])
    assert best[0] is not None
    return best[0]


def main() -> int:
    traces = admissible_traces()
    print(f"admissible traces: {len(traces)}")
    sizes: dict[int, int] = defaultdict(int)
    for mask in traces:
        sizes[bin(mask).count("1")] += 1
    print("trace sizes:", dict(sorted(sizes.items())))

    by_order: dict[int, int] = defaultdict(int)
    classes: set[tuple[tuple[int, int], ...]] = set()
    # Store graphs as (trace, edge_mask) sequences so the certificate can be
    # computed after the search, once the count is known.
    stored: list[list[tuple[int, int]]] = []

    def rec(idx_start: int, chosen: list[tuple[int, int]], adj: list[set[int]]) -> None:
        by_order[len(adj)] += 1
        stored.append(list(chosen))
        k = len(chosen)
        if k >= 6:
            return
        for t_index in range(idx_start, len(traces)):
            trace = traces[t_index]
            for edge_mask in range(1 << k):
                nxt = add_vertex(adj, trace, edge_mask)
                if has_c4(nxt) or has_induced_path(nxt, 8):
                    continue
                chosen.append((trace, edge_mask))
                rec(t_index + 1, chosen, nxt)
                chosen.pop()

    rec(0, [], cycle_graph())
    orders = [by_order[n] for n in range(8, 14)]
    print("by order 8..13:", orders)
    print("labelled total:", sum(orders))

    radius_at_least_four = 0
    for chosen in stored:
        adj = cycle_graph()
        for trace, edge_mask in chosen:
            adj = add_vertex(adj, trace, edge_mask)
        classes.add(canonical(adj))
        if radius(adj) >= 4:
            radius_at_least_four += 1
    print("isomorphism classes:", len(classes))
    print("labelled graphs of radius at least 4:", radius_at_least_four)
    return 0


def radius(adj: list[set[int]]) -> int:
    n = len(adj)
    best = n
    for s in range(n):
        dist = [-1] * n
        dist[s] = 0
        queue = [s]
        for v in queue:
            for u in adj[v]:
                if dist[u] < 0:
                    dist[u] = dist[v] + 1
                    queue.append(u)
        ecc = max(dist)
        if ecc < best:
            best = ecc
    return best


if __name__ == "__main__":
    sys.exit(main())
