"""检验第 256 题的图编码、整数参数和下界证明的有限步骤。"""

import unittest

from verify_minimum_256 import (
    check_lower_bound_arithmetic,
    check_small_domination_structures,
    cycle_witness,
    profile,
    validate_encoding14,
)
from verify_transfer_256 import verify, verify_lean_encoding


class Conjecture256Test(unittest.TestCase):
    def test_cycle_witness(self):
        validate_encoding14()
        self.assertEqual(profile(cycle_witness()), (14, 3, 14, 9, 3))

    def test_bipartite_family(self):
        verify_lean_encoding()
        for batches, expected in [
            (4, (49, 176, 5, 33, 3)),
            (5, (59, 218, 5, 39, 3)),
        ]:
            with self.subTest(batches=batches):
                result = verify(2, 4, batches)
                self.assertEqual(result, expected)
                order, _, _, maximum, domination = result
                self.assertEqual(domination * maximum < 2 * order, batches == 5)

    def test_lower_bound_reductions(self):
        check_lower_bound_arithmetic()
        for size in (4, 5):
            with self.subTest(size=size):
                check_small_domination_structures(size)


if __name__ == "__main__":
    unittest.main()
