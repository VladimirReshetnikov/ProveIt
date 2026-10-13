"""Weighted partial cancellation: independent subset oracle and deep kernels."""
from copy import deepcopy
from itertools import product
import random
import unittest

from fastunknot.cycle_block_cancellation import Limits, ResourceLimit, optimize_counts, verify_plan


def oracle(counts, weights, allowed):
    best = 0
    rows = sorted(counts)
    for mask in range(1 << len(rows)):
        live = {r for i, r in enumerate(rows) if mask >> i & 1}
        score = sum(weights[r] for r in live)
        if score <= best: continue
        while live:
            unit = next(((r, c) for r, c in allowed if r in live
                         and all(not counts[s].get(c, 0) for s in live - {r})), None)
            if unit is None: break
            live.remove(unit[0])
        if not live: best = score
    return best


class CycleBlockCancellationTests(unittest.TestCase):
    def check_plan(self, counts, weights=None, allowed=None):
        if weights is None: weights = dict.fromkeys(counts, 1)
        if allowed is None: allowed = {(r, c) for r in counts for c, a in counts[r].items() if a == 1}
        expected = oracle(counts, weights, allowed)
        for prepeel in (True, False):
            plan = optimize_counts(counts, weights, allowed=allowed, prepeel=prepeel)
            self.assertEqual(plan['status'], 'OPTIMAL_MATRIX_PLAN')
            self.assertTrue(verify_plan(counts, plan, weights, allowed=allowed))
            self.assertEqual(plan['matched_weight'], expected)
        return plan

    def test_exhaustive_binary_three_by_three(self):
        for values in product(range(2), repeat=9):
            self.check_plan({r: {c: values[3*r+c] for c in range(3)} for r in range(3)})

    def test_random_weighted_restricted_and_heavy(self):
        rng = random.Random(116260013)
        for _ in range(500):
            counts = {3*r+2: {5*c+1: rng.randrange(4) for c in range(rng.randrange(1,7))}
                      for r in range(rng.randrange(1,7))}
            weights = {r: rng.randrange(10) for r in counts}
            allowed = {(r, c) for r in counts for c, a in counts[r].items() if a == 1 and rng.randrange(3)}
            self.check_plan(counts, weights, allowed)

    def test_articulation_capacity_and_unbounded_residual(self):
        for n in (1, 3, 25):
            counts = {r: {0:1, r//2+1:1} for r in range(2*n)}
            plan = optimize_counts(counts, single_deferral=False)
            self.assertEqual(plan['matched_weight'], n)
            self.assertEqual(plan['deferred_weight'], n)
            self.assertEqual(plan['stats']['max_block_rank'], 1)
            self.assertTrue(verify_plan(counts, plan))

    def test_unbounded_paths_use_explicit_stack(self):
        # K_(2,270): any two selected distinct rows/columns make an alternating
        # four-cycle, so the optimum is one regardless of enumeration order.
        counts = {r: dict.fromkeys(range(270), 1) for r in range(2)}
        plan = optimize_counts(counts, single_deferral=False, limits=Limits(max_work=None, max_block_rank=None, max_paths=None))
        self.assertEqual(plan['matched_weight'], 1)
        self.assertEqual(plan['stats']['max_paths_per_block'], 270)
        self.assertGreater(plan['stats']['cycle_prefix_prunes'], 0)
        self.assertTrue(verify_plan(counts, plan))

    def test_caps_are_inconclusive(self):
        counts = {0:{0:1,1:1}, 1:{0:1,1:1}}
        for limits in (Limits(max_work=0), Limits(max_entries=0), Limits(max_block_rank=0), Limits(max_paths=0)):
            self.assertEqual(optimize_counts(counts, limits=limits, single_deferral=False)['status'], 'RESOURCE_LIMIT')
        for limits in (Limits(max_paths=True), Limits(max_work=-1)):
            with self.assertRaises(ValueError): optimize_counts(counts, limits=limits)

    def test_callback_exceptions_are_not_budget_refusals(self):
        for error in (ResourceLimit('caller stop'), ValueError('caller stop')):
            class Stop:
                def __bool__(self): return False
                def __call__(self): raise error
            for counts in ({}, {0:{0:1,1:1},1:{0:1,1:1}}):
                with self.assertRaisesRegex(type(error), 'caller stop'):
                    optimize_counts(counts, check=Stop())
        calls = 0
        def later():
            nonlocal calls
            calls += 1
            if calls == 30: raise ResourceLimit('late caller stop')
        with self.assertRaisesRegex(ResourceLimit, 'late caller stop'):
            optimize_counts({r:dict.fromkeys(range(4),1) for r in range(4)}, check=later)

    def test_forged_schema_and_private_schedule(self):
        counts = {0:{0:1,1:1},1:{0:1,1:1}}
        plan = optimize_counts(counts)
        for mutate in (lambda x:x.update(schema='wrong'),
                       lambda x:x.update(matched_weight=True),
                       lambda x:x.update(cancellations=[[0,0],[1,1]],cancelled_rows=[0,1],remaining_rows=[],matched_weight=2,deferred_weight=0)):
            bad = deepcopy(plan); mutate(bad)
            self.assertFalse(verify_plan(counts, bad))

    def test_empty_rows_and_zero_weights_remain_real_rows(self):
        self.check_plan({2:{}, 8:{3:2}, 10:{1:1}}, {2:10,8:0,10:0})

    def test_minimum_weight_deferral_is_exact_and_requires_stalling(self):
        counts={0:{0:1,1:1},1:{0:1,1:1},2:{2:1}}
        p=optimize_counts(counts,{0:4,1:7,2:1})
        self.assertEqual(p['matched_weight'],8)
        self.assertEqual(p['remaining_rows'],[0])
        self.assertTrue(p['stats']['single_deferral_success'])
        self.assertEqual(p['stats']['forced_rows'],1)
        p=optimize_counts({0:{0:1},1:{1:1}})
        self.assertEqual(p['deferred_weight'],0)
        self.assertFalse(p['stats']['single_deferral_success'])

    def test_single_trial_cap_falls_through_to_exact_solver(self):
        counts={r:{0:1,r//2+1:1} for r in range(20)}
        for cap in (0,1,8,None):
            p=optimize_counts(counts, limits=Limits(max_single_trials=cap))
            self.assertEqual(p['matched_weight'],10)
            self.assertTrue(verify_plan(counts,p))
            self.assertEqual(p['stats']['single_deferral_trials'],20 if cap is None else cap)


if __name__ == '__main__': unittest.main()
