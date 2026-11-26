"""检查有序对构造的参数边界及示例不变量。"""

from fractions import Fraction
import unittest

from verify_pair_family import build_graph, inspect


class PairFamilyTests(unittest.TestCase):
    def test_reject_outside_domain(self):
        for args in [(1, 1), (2, 0)]:
            with self.subTest(args=args), self.assertRaises(ValueError):
                build_graph(*args)

    def test_smallest_parameters(self):
        order, maximum, chosen = inspect(2, 1)
        self.assertEqual((order, maximum, chosen), (22, 19, 4))

    def test_counterexample_for_coefficient_two(self):
        order, maximum, chosen = inspect(3, 114)
        self.assertEqual((order, maximum, chosen), (722, 265, 5))
        self.assertLess(Fraction(maximum * chosen, order), 2)


if __name__ == "__main__":
    unittest.main()
