"""独立核验第 256 题的十四点见证与下界证明的有限情形。"""

import re
from itertools import combinations
from pathlib import Path


def profile(edges):
    adjacency = {v: set() for edge in edges for v in edge}
    for u, v in edges:
        adjacency[u].add(v)
        adjacency[v].add(u)
    order = len(adjacency)
    delta = min(map(len, adjacency.values()))
    min_neighborhood = set().union(
        *(row for row in adjacency.values() if len(row) == delta)
    )
    maximum = max(len(adjacency[u] | adjacency[v]) for u, v in edges)
    gamma = next(
        k
        for k in range(2, 4)
        if any(
            len(set().union(*(adjacency[v] for v in subset))) == order
            for subset in combinations(adjacency, k)
        )
    )
    return order, delta, len(min_neighborhood), maximum, gamma


def cycle_witness():
    return (
        [(0, 1), (1, 2), (1, 3)]
        + [(0, v) for v in range(4, 9)]
        + [(2, v) for v in range(9, 14)]
        + [(v, v + 1) for v in range(3, 13)]
        + [(13, 3)]
    )


def validate_encoding14():
    source = Path(__file__).with_name("WOWII256Small.lean").read_text(encoding="utf-8")
    record = re.search(r"def rowMask.* := !\[([\d, ]+)\]", source)
    masks = [int(word) for word in record[1].split(",")]
    expected = [0] * 14
    for u, v in cycle_witness():
        expected[u] |= 1 << v
        expected[v] |= 1 << u
    assert masks == expected


def check_small_domination_structures(size):
    """仅检查总支配集诱导的四点或五点局部图。"""
    possible = list(combinations(range(size), 2))
    for mask in range(1 << len(possible)):
        edges = [edge for i, edge in enumerate(possible) if (mask >> i) & 1]
        deg = [sum(v in edge for edge in edges) for v in range(size)]
        if min(deg) == 0:
            continue
        disjoint_pair = any(not (set(e) & set(f)) for e, f in combinations(edges, 2))
        if size == 4 and not disjoint_pair:
            assert sorted(deg) == [1, 1, 1, 3]
        if size == 5 and max(deg) <= 3:
            assert disjoint_pair


def check_lower_bound_arithmetic():
    """核对阶数下界证明中留下的整数情形。"""
    candidates = []
    for order in range(2, 14):
        for gamma in range(3, 7):
            if 2 * gamma >= order:
                continue
            for maximum in range(2, order):
                if gamma * maximum >= 2 * order or gamma * (maximum - 2) < order:
                    continue
                if gamma == 3 and order + 3 <= 2 * maximum:
                    candidates.append((order, maximum))
                    assert order + 3 == 2 * maximum
                    assert 2 * (order - 1) <= gamma * maximum
                if gamma == 4:
                    assert max(2 * maximum, 3 * maximum - 8) < order
                if gamma == 5:
                    assert maximum == 5 and 3 * maximum - 3 < order
                if gamma == 6:
                    raise AssertionError((order, gamma, maximum))
    assert candidates == [(11, 7), (13, 8)]
