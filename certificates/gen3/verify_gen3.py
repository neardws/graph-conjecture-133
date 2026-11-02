#!/usr/bin/env python3
"""Verify two finite graph certificates for the GEN3 proof note. Python 3.10+.

Graph labels are consecutive integers. An adjacency list is a tuple of integer
bit masks. Choices in each certificate are supplied in depth-first preorder.
An integer names one vertex, a tuple names a pair, and None means unrestricted.
There is no cutoff on the order. Run this file without arguments.
"""

from collections import Counter
from itertools import combinations, product


def require(condition, message):
    if not condition:
        raise ValueError(message)


def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def graph_from_edges(order, edges):
    rows = [0] * order
    for a, b in edges:
        rows[a] |= 1 << b
        rows[b] |= 1 << a
    return tuple(rows)


def triangle_seed(distance):
    first = [(0, 1), (1, 2), (2, 0)]
    if distance is None:
        return graph_from_edges(3, first)
    if distance == 0:
        return graph_from_edges(5, first + [(0, 3), (3, 4), (4, 0)])
    bridge = [0, *range(3, 3 + distance)]
    a = bridge[-1]
    second = [(a, a + 1), (a + 1, a + 2), (a + 2, a)]
    return graph_from_edges(a + 3, first + list(zip(bridge, bridge[1:])) + second)


def loss(graph, v):
    neighbors = list(vertices(graph[v]))
    triangles = sum((graph[a] >> b) & 1 for a, b in combinations(neighbors, 2))
    return 2 * len(neighbors) - 3 * triangles


def adjacent_degree_two_pair(graph, a, b):
    return (a != b and bool(graph[a] & (1 << b))
            and graph[a].bit_count() == graph[b].bit_count() == 2)


def p7_traces(graph):
    """For each old six-set, list all traces of a new vertex making a P7.

    Removing the new vertex from such a P7 leaves one or two path components.
    To reconstruct the P7, join the new vertex to exactly one end in each.
    An isolated vertex is its own end.
    """
    constraints = []
    for six in combinations(range(len(graph)), 6):
        mask = sum(1 << v for v in six)
        degrees = {v: (graph[v] & mask).bit_count() for v in six}
        if max(degrees.values()) > 2:
            continue
        edge_count = sum(degrees.values()) // 2
        if edge_count not in (4, 5):
            continue
        remaining = set(six)
        ends = []
        while remaining:
            start = remaining.pop()
            component = [start]
            for v in component:
                fresh = remaining.intersection(vertices(graph[v]))
                component.extend(fresh)
                remaining.difference_update(fresh)
            ends.append([v for v in component if degrees[v] <= 1])
        if len(ends) != 6 - edge_count or any(not group for group in ends):
            continue
        traces = {sum(1 << v for v in attachment) for attachment in product(*ends)}
        constraints.append((mask, traces))
    return constraints


def extensions(graph, required_mask):
    """Visit every legal neighbourhood, in increasing mask order."""
    constraints = p7_traces(graph)
    order = len(graph)
    for mask in range(1, 1 << order):
        if not (mask & required_mask):
            continue
        # A 4-cycle through the new vertex would have an opposite old vertex
        # with two neighbours in the chosen mask.
        if any((row & mask).bit_count() >= 2 for row in graph):
            continue
        if any((mask & six) in traces for six, traces in constraints):
            continue
        rows = list(graph)
        for v in vertices(mask):
            rows[v] |= 1 << order
        yield tuple(rows) + (mask,)


def is_exceptional(graph):
    """The K5 in which all six edges of a 3+2 cut are subdivided once."""
    if len(graph) != 11:
        return False
    high = [v for v, row in enumerate(graph) if row.bit_count() == 4]
    low = [v for v, row in enumerate(graph) if row.bit_count() == 2]
    if len(high) != 5 or len(low) != 6:
        return False
    high_mask = sum(1 << v for v in high)
    triangle = [v for v in high if (graph[v] & high_mask).bit_count() == 2]
    others = [v for v in high if v not in triangle]
    if len(triangle) != 3 or not all(graph[a] & (1 << b)
                                      for a, b in combinations(triangle, 2)):
        return False
    a, b = others
    if not (graph[a] & (1 << b)):
        return False
    expected = {(1 << u) | (1 << v) for u in triangle for v in others}
    return {graph[v] for v in low} == expected


CERTIFICATES = {
    None: [0, 1, 2, 0, 1, 2, 3, 4, 5, 6, 9, 9, 6, 9, 9, 5, 9, 9, 3, 4, 10, 11, 11, (4, 10), 4, 3, 3,
     3, 3, 9, 3, 9, 4, 10, 10, 4, 10, 10, (4, 14), 4, 9, 11, 4, 4, 3, 10, 4, 4, 5, 5, 4, 4, 6,
     6, None, 11, 11, 11, 11, 11, 5, 5, 4, 4, None, 11, 11, 11, 11, 11, 4, 4, 5, 5, None, 11,
     11, 11, 11, 11, 4, 4, None, 11, 11, 11, 11, 11, 2, 5, 8, 5, 8, 3, 10, 10, 3, 10, 10,
     (3, 14), 3, 8, 11, 3, 3, 5, 10, 3, 3, 1, 4, 7, 2, 4, 7, 3, 9, 9, 3, 9, 9, (3, 14), 3, 7,
     10, 3, 3, 4, 9, 3, 3, 2, 5, 9, 9, 0, 1, 3, 6, 2, 3, 6, 4, 9, 9, 4, 9, 9, (4, 14), 4, 6, 10,
     4, 4, 3, 9, 4, 4, 2, 5, 9, 9, 1, 3, 4, 6, 8, 10, 10],
    0: [0, 1, 2, 1, 3, 4, 2, 3, 4, 6, 9, 9, 6, 9, 9, 7, 7, 4, 10, 6, 6, 3, 9, 6, 6, 2, 7, 9, 9, 1,
     3, 4, 6, 8, 10, 10],
    1: [0, 3, 1, 2, 4, 5, 8, 8, 2, 1, 2, 1, 2, 1, 3, 7, 1, 2, 4, 5, 10, 10, 0, 3, 6, 1, 2, 4, 5,
     10, 10],
    2: [0, 1, 2, 5, 4, 4, 5, 2, 5, 1, 5, 2, 1, 2, 1, 1, 2, 5, 4, 7, 1, 2, 4, 2, 1, 6, 6, 2, 6, 1,
     6, 2, 1, 1, 2, 4, 2, 1, 5, 5, 2, 1, 2, 5, 1, 5],
    3: [1, 6, 1, 6, 1],
}


def verify(distance, choices):
    single = distance is None
    decisions = iter(choices)
    visits = Counter()
    leaves = 0
    unrestricted = 0

    def visit(graph):
        nonlocal leaves, unrestricted
        order = len(graph)
        visits[order] += 1
        try:
            choice = next(decisions)
        except StopIteration:
            raise ValueError('Missing decision for a legal child') from None
        if choice is None:
            require(single, 'Unrestricted node in two-triangle proof')
            require(all(loss(graph, v) >= 4 for v in range(order)),
                    'Unrestricted node has a deficient vertex')
            require(not any(adjacent_degree_two_pair(graph, a, b)
                            for a, b in combinations(range(order), 2)),
                    'Unrestricted node has an adjacent degree-two pair')
            require(is_exceptional(graph), 'Unclassified unrestricted node')
            unrestricted += 1
            target = (1 << order) - 1
        elif isinstance(choice, tuple):
            a, b = choice
            require(single and adjacent_degree_two_pair(graph, a, b),
                    'The designated pair does not force an extension')
            target = (1 << a) | (1 << b)
        else:
            require(0 <= choice < order and loss(graph, choice) < 4,
                    'The designated vertex does not force an extension')
            target = 1 << choice

        has_child = False
        for child in extensions(graph, target):
            has_child = True
            visit(child)
        if not has_child:
            leaves += 1

    visit(triangle_seed(distance))
    sentinel = object()
    require(next(decisions, sentinel) is sentinel, 'Unused certificate entries')
    return sum(visits.values()), max(visits), leaves, unrestricted


def main():
    results = []
    for distance, choices in CERTIFICATES.items():
        result = verify(distance, choices)
        results.append(result)
        name = 'one triangle' if distance is None else f'triangle distance {distance}'
        print(f'{name:22s} nodes={result[0]:3d}  maximum order={result[1]:2d}'
              f'  leaves={result[2]:2d}  unrestricted={result[3]}')
    expected = [(169, 17), (36, 17), (31, 15), (46, 11), (5, 10)]
    require([item[:2] for item in results] == expected, 'Unexpected tree sizes')
    require(results[0][2:] == (52, 4), 'Unexpected single-triangle outcomes')
    print('PASS. All branches and all decision entries verified.')


if __name__ == '__main__':
    main()
