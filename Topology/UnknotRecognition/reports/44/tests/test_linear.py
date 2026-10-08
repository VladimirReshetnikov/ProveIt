import copy
import itertools
import random
import unittest
from terminal_updates.linear import *

class LinearTests(unittest.TestCase):
    def assert_state(self, a, state):
        self.assertTrue(verify_normal_form(a, state.certificate()))
        self.assertEqual(det_mod(a, state.p), state.determinant)
        self.assertEqual(bareiss(a) % state.p, state.determinant)

    def test_empty(self):
        s = DynamicRank([], 2)
        self.assert_state([], s)
        self.assertEqual(s.update([], []), 'zero')

    def test_zero_matrix(self):
        self.assert_state([[0]*4 for _ in range(4)], DynamicRank([[0]*4 for _ in range(4)], 3))

    def test_full_matrix(self):
        a = [[1,2,4],[3,1,0],[2,4,1]]
        self.assert_state(a, DynamicRank(a, 7))

    def test_left_tail_rank_increase(self):
        s = DynamicRank([[1,0],[0,0]], 5)
        self.assertEqual(s.update([0,1],[0,1]), 'tail_left')
        self.assert_state([[1,0],[0,1]], s)

    def test_left_tail_rank_preserved(self):
        s = DynamicRank([[1,0],[0,0]], 5)
        self.assertEqual(s.update([2,1],[1,0]), 'tail_left')
        self.assert_state([[3,0],[1,0]], s)

    def test_right_tail(self):
        s = DynamicRank([[1,0],[0,0]], 5)
        self.assertEqual(s.update([1,0],[2,1]), 'tail_right')
        self.assert_state([[3,1],[0,0]], s)

    def test_regular(self):
        s = DynamicRank(eye(2), 5)
        self.assertEqual(s.update([1,1],[2,1]), 'regular')
        self.assert_state([[3,1],[2,2]], s)

    def test_rank_drop(self):
        for p in (2,3,101):
            s = DynamicRank(eye(2), p)
            self.assertEqual(s.update([1,0],[-1,0]), 'rank_drop')
            self.assert_state([[0,0],[0,1]], s)
            s.update([1,0],[1,0])
            self.assert_state(eye(2), s)

    def test_zero_update(self):
        s = DynamicRank(eye(3), 5)
        before = s.certificate()
        self.assertEqual(s.update([0]*3,[1]*3), 'zero')
        self.assertEqual(before, s.certificate())

    def test_all_binary_two_by_two(self):
        vectors = list(itertools.product(range(2), repeat=2))
        for entries in itertools.product(range(2), repeat=4):
            a = [list(entries[:2]),list(entries[2:])]
            base = DynamicRank(a, 2)
            for u in vectors:
                for v in vectors:
                    s = base.clone()
                    s.update(u,v)
                    b = [[a[i][j]+u[i]*v[j] for j in range(2)] for i in range(2)]
                    self.assert_state(b,s)

    def test_random_streams(self):
        rng = random.Random(1729)
        seen = set()
        for p in (2,3,5,101):
            for n in (1,3,6):
                a = [[0]*n for _ in range(n)]
                s = DynamicRank(a,p)
                for _ in range(80):
                    u,v = ([rng.randrange(p) for _ in range(n)] for __ in range(2))
                    seen.add(s.update(u,v))
                    a = [[(a[i][j]+u[i]*v[j])%p for j in range(n)] for i in range(n)]
                    self.assert_state(a,s)
        self.assertEqual(seen, {'zero','tail_left','tail_right','regular','rank_drop'})

    def test_reject_composite_and_shapes(self):
        for p in (0,1,4,9,25):
            with self.assertRaises(ValueError): DynamicRank([[1]],p)
        with self.assertRaises(ValueError): DynamicRank([[1,2]],3)
        with self.assertRaises(ValueError): DynamicRank([[1.0]],3)
        with self.assertRaises(ValueError): DynamicRank([[1]],3).update([],[])

    def test_independent_certificate_tamper(self):
        a = [[1,2],[3,4]]
        cert = DynamicRank(a,101).certificate()
        for key in ('scale','rank'):
            bad = copy.deepcopy(cert); bad[key] += 1
            self.assertFalse(verify_normal_form(a,bad))
        bad = copy.deepcopy(cert); bad['left'][0][0] += 1
        self.assertFalse(verify_normal_form(a,bad))

    def test_clone_isolation(self):
        parent = DynamicRank(eye(2),5)
        child = parent.clone(); child.update([1,0],[-1,0])
        self.assertEqual(parent.determinant,1)
        self.assertEqual(child.determinant,0)

    def test_fraction_free_row_swaps(self):
        for a in ([[0,2],[3,4]],[[0,0,2],[0,3,4],[5,6,7]],[[1,2],[2,4]]):
            for p in (2,3,5,101): self.assertEqual(bareiss(a)%p,det_mod(a,p))

    def test_budget(self):
        with self.assertRaises(BudgetExceeded): DynamicRank(eye(3),3,Budget(units_left=0))
        with self.assertRaises(BudgetExceeded): DynamicRank(eye(2),3).clone(Budget(deadline=0))
