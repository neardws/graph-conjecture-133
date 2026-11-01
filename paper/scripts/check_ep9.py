#!/usr/bin/env python3
"""Check the adjacency list in the EP(9) example.

Vertices are 0..14 with the lists printed in the manuscript. The script checks
that the graph is triangle-free and has no 4-cycle subgraph, records n, e and
S=2e, and checks the two induced paths of order 9 from the oriented edge
(12, 8). It then deletes {10, 11} and prints the deletion loss.
"""

from __future__ import annotations

LISTS = {
    0: [4, 8, 11],
    1: [5, 8, 10],
    2: [6, 8, 9],
    3: [7, 10],
    4: [0, 9, 10],
    5: [1, 9, 11],
    6: [2, 10, 11],
    7: [3, 11],
    8: [0, 1, 2, 12],
    9: [2, 4, 5],
    10: [1, 3, 4, 6, 13],
    11: [0, 5, 6, 7, 14],
    12: [8, 13, 14],
    13: [10, 12],
    14: [11, 12],
}


def main() -> None:
    n = 15
    adj = [set() for _ in range(n)]
    for v, nbrs in LISTS.items():
        for u in nbrs:
            adj[v].add(u)
            adj[u].add(v)
    edges = sum(len(s) for s in adj) // 2
    triangles = 0
    for v in range(n):
        nbrs = list(adj[v])
        for i, a in enumerate(nbrs):
            for b in nbrs[i + 1 :]:
                if b in adj[a]:
                    triangles += 1
    triangles //= 3
    c4 = False
    for i in range(n):
        for j in range(i + 1, n):
            if len(adj[i] & adj[j]) >= 2:
                c4 = True
    print(f"n={n} e={edges} T={triangles} S={2 * edges - 3 * triangles} C4={c4}")

    def induced(path: list[int]) -> bool:
        for i, u in enumerate(path):
            for j in range(i + 1, len(path)):
                linked = path[j] in adj[u]
                if linked != (j == i + 1):
                    return False
        return True

    paths = [
        [12, 8, 2, 9, 4, 10, 3, 7, 11],
        [12, 8, 2, 9, 5, 11, 7, 3, 10],
    ]
    for path in paths:
        print("path", path, "induced" if induced(path) else "NOT induced", "order", len(path))

    # Deletion loss of U={10,11} in a triangle-free graph is twice the number
    # of edges that meet U.
    u_set = {10, 11}
    meet = 0
    for v in range(n):
        for w in adj[v]:
            if v < w and (v in u_set or w in u_set):
                meet += 1
    print(f"edges meeting {{10,11}}={meet} deletion loss={2 * meet}")


if __name__ == "__main__":
    main()
