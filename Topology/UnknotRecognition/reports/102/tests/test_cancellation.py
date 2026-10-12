import copy
import random
import unittest

from cancellation import (column_cancellation_plan, verify_peeling_certificate,
                          verify_stopping_set, replay_positive, deferred_plan,
                          replay_with_passive)
from reference.native_planner_excerpt import capped_cancellation_plan, leaf_cancellation_plan


def certificate(plan):
    return dict(schema='positive-column-peeling-v1',
                cancellations=plan['cancellations'], remaining_rows=plan['remaining_rows'])


class CancellationTests(unittest.TestCase):
    def check_plan(self, a):
        plan = column_cancellation_plan(a)
        self.assertTrue(verify_peeling_certificate(a, certificate(plan)))
        self.assertIsNotNone(replay_positive(a, plan['cancellations']))
        if plan['remaining_rows']:
            self.assertTrue(verify_stopping_set(a, plan['remaining_rows']))
        return plan

    def test_empty(self):
        self.assertFalse(self.check_plan({})['remaining_rows'])

    def test_zero_row_is_obstruction(self):
        self.assertEqual(self.check_plan({12: {}})['remaining_rows'], [12])

    def test_one_by_two(self):
        a = {0: {0: 1, 1: 1}}
        self.assertTrue(leaf_cancellation_plan(a)['remaining_rows'])
        self.assertFalse(self.check_plan(a)['remaining_rows'])

    def test_rectangular_private_columns(self):
        a = {r: {r: 1, 17: 2} for r in range(17)}
        self.assertTrue(leaf_cancellation_plan(a)['remaining_rows'])
        self.assertFalse(self.check_plan(a)['remaining_rows'])

    def test_unimodular_stopping_example(self):
        self.assertTrue(self.check_plan({0: {0: 1, 1: 1}, 1: {0: 1, 1: 2}})['remaining_rows'])

    def test_partial_is_not_full_peeling(self):
        a = {0: {0: 1, 1: 1}, 1: {0: 1, 1: 1}}
        self.assertEqual(len(self.check_plan(a)['cancellations']), 0)
        self.assertEqual(len(capped_cancellation_plan(a)['cancellations']), 1)
        result = deferred_plan(a, 1)
        self.assertEqual(result['status'], 'FOUND')
        self.assertEqual(len(result['deferred_rows']), 1)
        self.assertEqual(list(result['residual'].values()), [{1: 2}])

    def test_saturation_large_counts(self):
        big = 1 << 16384
        self.assertFalse(self.check_plan({0: {100: 1, 101: big}})['remaining_rows'])
        self.assertTrue(self.check_plan({0: {101: big}})['remaining_rows'])

    def test_large_labels(self):
        label = 1 << 256
        self.assertFalse(self.check_plan({label: {label + 7: 1}})['remaining_rows'])

    def test_omitted_columns(self):
        rng = random.Random(918)
        for _ in range(100):
            a = {r: {c: rng.randrange(3) for c in range(6)} for r in range(4)}
            b = {r: dict(row, **{}) for r, row in a.items()}
            for r in b:
                b[r].update({c: rng.choice([0, 2, 5]) for c in range(6, 16)})
            self.assertEqual(set(self.check_plan(a)['remaining_rows']),
                             set(self.check_plan(b)['remaining_rows']))

    def test_input_unchanged(self):
        a = {0: {0: 1, 1: 2}, 1: {1: 1}}
        before = copy.deepcopy(a)
        self.check_plan(a)
        self.assertEqual(a, before)

    def test_reject_invalid_counts(self):
        for a in [None, [], {True: {}}, {-1: {}}, {0: []}, {0: {False: 1}},
                  {0: {0: True}}, {0: {0: -1}}, {0: {0: 1.0}}]:
            with self.assertRaises(ValueError):
                column_cancellation_plan(a)
            self.assertFalse(verify_stopping_set(a, [0]))

    def test_forged_pivot(self):
        a = {0: {0: 1}, 1: {0: 1}}
        bad = dict(schema='positive-column-peeling-v1', cancellations=[[0, 0]], remaining_rows=[1])
        self.assertFalse(verify_peeling_certificate(a, bad))

    def test_duplicate_rows_and_columns(self):
        a = {0: {0: 1}, 1: {1: 1}}
        for moves in [[[0, 0], [0, 0]], [[0, 0], [1, 0]]]:
            self.assertFalse(verify_peeling_certificate(a, dict(
                schema='positive-column-peeling-v1', cancellations=moves, remaining_rows=[])))

    def test_forged_residual(self):
        a = {0: {0: 1}}
        bad = dict(schema='positive-column-peeling-v1', cancellations=[], remaining_rows=[0])
        self.assertFalse(verify_peeling_certificate(a, bad))
        self.assertFalse(verify_stopping_set(a, [0]))

    def test_schema_strict(self):
        a = {0: {0: 1}}
        good = certificate(self.check_plan(a))
        for key, val in [('schema', 'wrong'), ('cancellations', [[True, 0]]),
                         ('remaining_rows', [99]), ('new_field', 1)]:
            bad = copy.deepcopy(good)
            bad[key] = val
            self.assertFalse(verify_peeling_certificate(a, bad))

    def test_negative_certificate_nonempty(self):
        self.assertFalse(verify_stopping_set({0: {}}, []))
        self.assertFalse(verify_stopping_set({0: {}}, [0, 0]))
        self.assertTrue(verify_stopping_set({0: {}}, [0]))

    def test_complete_requirement(self):
        a = {0: {0: 2}}
        self.assertFalse(verify_peeling_certificate(a, certificate(self.check_plan(a)),
                                                  require_complete=True))

    def test_callback_exceptions_propagate(self):
        def cancel():
            raise ValueError('user cancellation')
        a = {0: {0: 1}}
        good = certificate(column_cancellation_plan(a))
        for fn in [lambda: column_cancellation_plan(a, check=cancel),
                   lambda: verify_peeling_certificate(a, good, check=cancel),
                   lambda: replay_positive(a, [[0, 0]], check=cancel),
                   lambda: verify_stopping_set({0: {}}, [0], check=cancel)]:
            with self.assertRaisesRegex(ValueError, 'user cancellation'):
                fn()

    def test_native_full_success_and_no_fill(self):
        rng = random.Random(28341)
        for _ in range(1000):
            m, n = rng.randrange(1, 7), rng.randrange(1, 9)
            a = {r: {c: rng.randrange(3) for c in range(n)} for r in range(m)}
            fast, native = self.check_plan(a), capped_cancellation_plan(a)
            self.assertEqual(bool(fast['remaining_rows']), bool(native['remaining_rows']))
            if not native['remaining_rows']:
                self.assertEqual(native['stats']['entry_updates'], 0)

    def test_order_independent_residual(self):
        rng = random.Random(65741)
        for _ in range(200):
            a = {r: {c: rng.randrange(3) for c in range(7)} for r in range(6)}
            ids = list(a)
            rng.shuffle(ids)
            b = {i: dict(reversed(list(a[i].items()))) for i in ids}
            self.assertEqual(set(self.check_plan(a)['remaining_rows']),
                             set(self.check_plan(b)['remaining_rows']))

    def test_deferred_invalid(self):
        for k in [-1, True, 1.5]:
            with self.assertRaises(ValueError):
                deferred_plan({}, k)
        with self.assertRaises(ValueError):
            replay_with_passive({0: {}}, [0, 0], [])

    def test_passive_transport_matches_general_replay(self):
        rng = random.Random(72387)
        for _ in range(100):
            a = {r: {r: 1, 10: rng.randrange(3)} for r in range(5)}
            a[5] = {c: rng.randrange(3) for c in range(11)}
            moves = column_cancellation_plan({r: a[r] for r in range(5)})['cancellations']
            self.assertEqual(replay_with_passive(a, [5], moves), replay_positive(a, moves))

    def test_every_row_may_be_deferred(self):
        a = {0: {}, 1: {0: 2}}
        self.assertEqual(deferred_plan(a, 1)['status'], 'NO_PLAN_WITHIN_BUDGET')
        self.assertEqual(len(deferred_plan(a, 2)['deferred_rows']), 2)

    def test_incidence_bound(self):
        a = {r: {r: 1, 1000: 1} for r in range(1000)}
        plan = column_cancellation_plan(a)
        self.assertTrue(verify_peeling_certificate(a, certificate(plan)))
        self.assertEqual(plan['stats']['incidence_deletions'], 2000)
        self.assertLessEqual(plan['stats']['queue_pops'], 1001)


if __name__ == '__main__':
    unittest.main(verbosity=2)
