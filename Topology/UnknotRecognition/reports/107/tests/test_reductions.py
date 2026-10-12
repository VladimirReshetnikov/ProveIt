import unittest
from dualforest.reductions import cnf_instance
from dualforest.dependencies import peel, columns
from dualforest import solve, verify_positive, verify_negative

class ReductionTests(unittest.TestCase):
    def test_satisfying_assignment(self):
        inst, _ = cnf_instance(2, [[1, 2], [-1, 2], [1, -2]])
        self.assertIsNotNone(peel(inst, [0, 2]))
        self.assertIsNone(peel(inst, [1, 3]))
        self.assertLessEqual(max(map(len, columns(inst).values())), 3)

    def test_unsatisfiable(self):
        inst, _ = cnf_instance(1, [[1], [-1]])
        ans = solve(inst, try_incumbent=False)
        self.assertEqual(ans['status'], 'no')
        self.assertTrue(verify_negative(inst, ans['negative_certificate']))

    def test_empty_clause(self):
        inst, _ = cnf_instance(1, [[]])
        self.assertIsNone(peel(inst, [0]))
        self.assertIsNone(peel(inst, [1]))

    def test_single_tautology(self):
        inst, _ = cnf_instance(1, [[1, -1]])
        ans = solve(inst, try_incumbent=False)
        self.assertTrue(verify_positive(inst, ans['certificate']))

    def test_callback_interrupt(self):
        inst, _ = cnf_instance(1, [[1], [-1]])
        def stop():
            raise InterruptedError('budget exhausted')
        with self.assertRaises(InterruptedError):
            solve(inst, check=stop)

if __name__ == '__main__':
    unittest.main()
