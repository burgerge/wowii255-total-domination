"""核对十一阶见证的编码和参数化构造。"""

import unittest

from verify_minimum import adjacency, graph_parameters, small_order_arithmetic


class MinimumTest(unittest.TestCase):
    def test_lean_vertex_encoding(self):
        rows = adjacency()
        masks = [sum(1 << v for v in row) for row in rows]
        self.assertEqual(masks, [122, 5, 1922, 241, 361, 601, 1081, 12, 20, 36, 68])
        self.assertEqual(sum(map(len, rows)), 40)

    def test_family_on_both_sides_of_threshold(self):
        for paths in (2, 3, 4, 5):
            with self.subTest(paths=paths):
                center, maximum, domination = graph_parameters(adjacency(paths))
                self.assertEqual(
                    (center, maximum, domination), (2 * paths + 3, paths + 3, 3)
                )
                self.assertEqual(domination * maximum < 2 * center, paths >= 4)

    def test_small_order_arithmetic(self):
        self.assertTrue(small_order_arithmetic())


if __name__ == "__main__":
    unittest.main()
