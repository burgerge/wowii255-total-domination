"""从构造规则独立核对十一阶证书与小阶下界的整数部分。"""

from collections import deque
from itertools import combinations


def adjacency(paths=4):
    """用互不相交的内部顶点构造 H_s。"""
    if paths < 2:
        raise ValueError("路径数至少为 2")
    rows = [set() for _ in range(2 * paths + 3)]

    edges = [(0, 1), (1, 2)]
    xs = range(3, 3 + paths)
    for x in xs:
        y = x + paths
        edges.extend(((0, x), (x, y), (y, 2)))
    edges.extend(combinations(xs, 2))
    for u, v in edges:
        rows[u].add(v)
        rows[v].add(u)
    return rows


def eccentricity(rows, start):
    distance = {start: 0}
    queue = deque([start])
    while queue:
        u = queue.popleft()
        for v in rows[u] - distance.keys():
            distance[v] = distance[u] + 1
            queue.append(v)
    if len(distance) != len(rows):
        raise ValueError("图不连通")
    return max(distance.values())


def graph_parameters(rows):
    """从边表精确计算中心、边邻域和总支配数。"""
    vertices = set(range(len(rows)))
    eccentricities = [eccentricity(rows, u) for u in vertices]
    center = sum(e == min(eccentricities) for e in eccentricities)
    maximum = max(len(rows[u] | rows[v]) for u in vertices for v in rows[u])
    domination = next(
        k
        for k in range(2, len(rows) + 1)
        if any(
            set().union(*(rows[u] for u in chosen)) == vertices
            for chosen in combinations(vertices, k)
        )
    )
    return center, maximum, domination


def small_order_arithmetic():
    """检查结构引理导出的整数约束在 2 至 10 阶无解。"""
    for order in range(2, 11):
        for domination in range(3, order + 1):
            for maximum in range(2, order):
                if order > domination * (maximum - 2):
                    continue
                if domination == 3 and order + 3 > 2 * maximum:
                    continue
                if domination * maximum < 2 * order:
                    return False
    return True


def main():
    rows = adjacency()
    center, maximum, domination = graph_parameters(rows)
    if (len(rows), center, maximum, domination) != (11, 11, 7, 3):
        raise AssertionError("最小见证的精确参数与证明不符")
    if not small_order_arithmetic():
        raise AssertionError("小阶下界的整数约束存在例外")
    print("11 阶反例：中心数 11，最大边邻域 7，总支配数 3；21 < 22。")
    print("2 至 10 阶的整数推论通过；结构引理见 Lean 证明。")


if __name__ == "__main__":
    main()
