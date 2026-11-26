"""重建第 256 题的分组二分图并核验小参数。"""

from collections import deque
from itertools import combinations


def build_graph(groups, size, batches):
    """每组原左点与普通右点成完全二分图，每批新增一个左点。"""
    hub = ("hub",)
    left = {(i, j): ("p", i, j) for i in range(groups) for j in range(size)}
    witness = {(i, b): ("w", i, b) for i in range(groups) for b in range(batches)}
    edges = {(u, hub) for u in [*left.values(), *witness.values()]}
    for i in range(groups):
        for b in range(batches):
            for j in range(size):
                right = ("r", i, b, j)
                edges.add((witness[i, b], right))
                edges.update((left[i, a], right) for a in range(size))
    adjacency = {v: set() for e in edges for v in e}
    for u, v in edges:
        adjacency[u].add(v)
        adjacency[v].add(u)
    return adjacency, hub, edges


def connected(adjacency, start):
    visited = {start}
    queue = deque([start])
    while queue:
        vertex = queue.popleft()
        for neighbor in adjacency[vertex] - visited:
            visited.add(neighbor)
            queue.append(neighbor)
    return len(visited) == len(adjacency)


def verify(groups, size, batches):
    adjacency, hub, edges = build_graph(groups, size, batches)
    order = len(adjacency)
    degrees = {v: len(row) for v, row in adjacency.items()}
    delta = min(degrees.values())
    min_neighborhood = set().union(
        *(adjacency[v] for v, degree in degrees.items() if degree == delta)
    )
    max_edge = max(len(adjacency[u] | adjacency[v]) for u, v in edges)
    domination = next(
        k
        for k in range(1, groups + 2)
        if any(
            len(set().union(*(adjacency[v] for v in chosen))) == order
            for chosen in combinations(adjacency, k)
        )
    )
    assert connected(adjacency, hub)
    assert order == groups * (size * batches + size + batches) + 1
    assert delta == size + 1
    assert len(min_neighborhood) == order
    assert max_edge == size * batches + 1 + groups * (size + batches)
    assert domination == groups + 1
    return order, len(edges), delta, max_edge, domination


def verify_lean_encoding():
    _, _, edges = build_graph(2, 4, 5)
    ordered = (
        [("p", i, a) for i in range(2) for a in range(4)]
        + [("w", i, b) for i in range(2) for b in range(5)]
        + [("r", i, b, a) for i in range(2) for b in range(5) for a in range(4)]
        + [("hub",)]
    )
    numbered = {vertex: i for i, vertex in enumerate(ordered)}
    expected = {(numbered[u], numbered[v]) for u, v in edges}
    encoded = {
        (u, v)
        for u in range(18)
        for v in range(18, 59)
        if v == 58
        or (u < 8 and u // 4 == (v - 18) // 20)
        or (8 <= u and u - 8 == (v - 18) // 4)
    }
    assert encoded == expected


if __name__ == "__main__":
    verify_lean_encoding()
    assert verify(2, 4, 4) == (49, 176, 5, 33, 3)
    assert verify(2, 4, 5) == (59, 218, 5, 39, 3)
    assert 3 * 39 < 2 * 59
    print("59 阶见证及阈值两侧的小参数通过独立整数核验。")
