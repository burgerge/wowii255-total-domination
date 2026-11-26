"""独立核验有序对构造的小型实例及严格界。"""

from collections import deque
from fractions import Fraction


def build_graph(n, copies):
    if n < 2 or copies < 1:
        raise ValueError("需要至少两对标签和一个副本")
    labels = 2 * n
    points = labels * labels
    vertices = points + 2 + labels * copies
    rows = [set() for _ in range(vertices)]

    def add_edge(p, block):
        rows[p].add(block)
        rows[block].add(p)

    for i in range(labels):
        for j in range(labels):
            p = i * labels + j
            if (i, j) != (0, 0):
                add_edge(p, points)
            if (i, j) != (n, 0):
                add_edge(p, points + 1)
            for label in {i, j}:
                for copy in range(copies):
                    add_edge(p, points + 2 + label * copies + copy)
    chosen = {i * labels + i + n for i in range(n)} | {points, points + 1}
    return rows, chosen


def eccentricity(rows, u):
    seen = {u: 0}
    queue = deque([u])
    while queue:
        v = queue.popleft()
        for w in rows[v] - seen.keys():
            seen[w] = seen[v] + 1
            queue.append(w)
    if len(seen) != len(rows):
        raise ValueError("图不连通")
    return max(seen.values())


def inspect(n, copies):
    rows, chosen = build_graph(n, copies)
    assert len(chosen) == n + 2 and all(row & chosen for row in rows)
    assert all(eccentricity(rows, v) == 3 for v in range(len(rows)))
    maximum = max(
        len(rows[v] | rows[w]) for v, row in enumerate(rows) for w in row if v < w
    )
    assert maximum <= 2 * copies + 2 + 4 * n * n
    return len(rows), maximum, len(chosen)


if __name__ == "__main__":
    n = 3
    copies = n * (4 * n * n + 2)
    order, maximum, chosen_size = inspect(n, copies)
    ratio_upper = Fraction(chosen_size * maximum, order)
    assert ratio_upper <= 1 + Fraction(3, n) and ratio_upper < 2
    print(
        f"n={n}, 副本数={copies}, 阶数={order}, 最大边邻域={maximum}, 总支配集={chosen_size}"
    )
    print(f"归一化比值上界为 {ratio_upper}，严格小于 2。")
