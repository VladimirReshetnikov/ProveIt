"""Maximum retained-work optimization, independent tree oracles and source cuts."""
from contextlib import ExitStack
from copy import deepcopy
from itertools import combinations
import random
import unittest
from unittest.mock import patch

from fastunknot.core_three_handle_reduction import _dual_moves, _raw_costs, reduce_core_three_handles
from fastunknot.core_three_handle_reduction_verify import replay_core_three_handles
from fastunknot.core_handlebody import column_cancellation_plan
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from tests.test_core_three_handles import BANK, EXTRA, geometry
from tests.test_normal_components import relabel


def exhaustive_best(ends, n, costs):
    best = None
    for selected in combinations(ends, n):
        seen = {None}
        while True:
            old = set(seen)
            for edge in selected:
                a, b = ends[edge]
                if a in seen: seen.add(b)
                if b in seen: seen.add(a)
            if seen == old: break
        if seen == {None, *range(n)}:
            weight = sum(costs[e] for e in selected)
            best = weight if best is None else max(best, weight)
    return best


class WeightedTopForestTests(unittest.TestCase):
    def test_400_small_multigraphs_against_all_spanning_trees(self):
        rng = random.Random(261012100)
        for trial in range(400):
            n = rng.randrange(6)
            ends = {e: [rng.choice([None, *range(n)]) for _ in range(2)]
                    for e in range(rng.randrange(11))}
            costs = {e: rng.randrange(7) * (1 << (512 if trial % 23 == 0 else 0)) for e in ends}
            best = exhaustive_best(ends, n, costs)
            plan = _dual_moves(ends, range(n), costs, lambda: None)
            if best is None:
                self.assertIsNone(plan)
                continue
            moves, remaining = plan
            self.assertEqual(sum(costs[m['two_handle']] for m in moves), best)
            self.assertEqual(remaining, set(ends) - {m['two_handle'] for m in moves})
            live = set(range(n))
            for m in moves:
                self.assertEqual([v for v in ends[m['two_handle']] if v in live], [m['three_handle']])
                live.remove(m['three_handle'])
            self.assertFalse(live)

    def test_source_replay_cost_and_unchanged_lower_charts(self):
        for c in [c for c in BANK if 'interior' in c['id']] + EXTRA:
            g = geometry(c); before = deepcopy(g)
            old, q = reduce_core_three_handles(g)
            new, p = reduce_core_three_handles(g, strategy='max_weight')
            costs = _raw_costs(g['core'], lambda: None)
            self.assertLessEqual(sum(costs[h] for h in p['surviving_two_handles']),
                                 sum(costs[h] for h in q['surviving_two_handles']))
            self.assertEqual(replay_core_three_handles(g, p), new)
            self.assertEqual(g, before)
            for key in ('handles0', 'handles1'): self.assertEqual(new['core'][key], old['core'][key])
            self.assertEqual(new['ports'], old['ports'])

    def test_two_new_loop_cuts_both_boundary_backends(self):
        for c in [c for c in EXTRA if c['id'] in ('interior_loop/empty', 'interior_loop/boundary_link')]:
            raw, rows = c['triangulation'], c['coordinates']
            self.assertEqual(normal_cut_handlebodies(raw, rows, top_forest='queue',
                                                   lower_forest='source')['status'], 'INCONCLUSIVE')
            for backend in ('masks', 'moments'):
                r = normal_cut_handlebodies(raw, rows, record_certificate=True, boundary_method=backend)
                self.assertEqual(r['status'], 'COMPLETE')
                self.assertEqual(r['census']['histogram'], [dict(genus=1, multiplicity=1)] if c['id'].endswith('/empty')
                                 else [dict(genus=0, multiplicity=1), dict(genus=1, multiplicity=1)])
                with ExitStack() as stack:
                    for name in ('_dual_moves', '_raw_costs', 'reduce_core_three_handles'):
                        stack.enter_context(patch('fastunknot.core_three_handle_reduction.'+name,
                                                  side_effect=AssertionError('planner called')))
                    self.assertTrue(verify_normal_cut_handlebodies(raw, rows, r['certificate']))
                bad = deepcopy(r['certificate'])
                bad['core_reduction']['cancellations'][0]['two_handle'] = True
                self.assertFalse(verify_normal_cut_handlebodies(raw, rows, bad))

    def test_scalar_multiplication_and_relabelled_loop_sources(self):
        c = next(c for c in BANK if c['id'] == 'interior_1_2/mixed')
        g = geometry(c); _, proof = reduce_core_three_handles(g, strategy='max_weight')
        rows = [[x * (1 << 16384) for x in row] for row in c['coordinates']]
        big = geometry(dict(c, coordinates=rows)); _, other = reduce_core_three_handles(big, strategy='max_weight')
        self.assertEqual(proof, other)
        self.assertEqual(_raw_costs(g['core'], lambda: None), _raw_costs(big['core'], lambda: None))
        rng = random.Random(261012101)
        c = next(c for c in EXTRA if c['id'] == 'interior_loop/empty')
        for _ in range(12):
            raw, rows = relabel(c['triangulation'], c['coordinates'], rng)
            g = geometry(dict(c, triangulation=raw, coordinates=rows))
            reduced, p = reduce_core_three_handles(g, strategy='max_weight')
            costs = _raw_costs(g['core'], lambda: None)
            ends = {r['two_handle']: r['ends'] for r in p['dual_endpoints']}
            self.assertEqual(sum(costs[m['two_handle']] for m in p['cancellations']),
                             exhaustive_best(ends, len(g['core']['handles3']), costs))
            self.assertEqual(replay_core_three_handles(g, p), reduced)

    def test_additive_optimum_does_not_imply_raw_cancellation(self):
        # An abstract incidence example, not an authenticated geometric core.
        rows = {0: {1: 1, 2: 1, 3: 1}, 1: {0: 1}, 2: {0: 1}}
        ends = {e: [None, 0] for e in rows}
        costs = {e: sum(row.values()) for e, row in rows.items()}
        moves, remaining = _dual_moves(ends, [0], costs, lambda: None)
        self.assertEqual(moves[0]['two_handle'], 0)
        self.assertTrue(column_cancellation_plan({e: rows[e] for e in remaining})['remaining_rows'])
        self.assertFalse(column_cancellation_plan({e: row for e, row in rows.items() if e != 1})['remaining_rows'])

    def test_invalid_modes_and_falsey_interruption(self):
        c = EXTRA[0]; g = geometry(c)
        for bad in (None, True, [], {}, 'maximum'):
            with self.assertRaises(ValueError): reduce_core_three_handles(g, strategy=bad)
            with self.assertRaises(ValueError): normal_cut_handlebodies(c['triangulation'], c['coordinates'], top_forest=bad)
        class Stop:
            def __bool__(self): return False
            def __call__(self): raise RuntimeError('interrupted')
        with self.assertRaisesRegex(RuntimeError, 'interrupted'):
            reduce_core_three_handles(g, strategy='max_weight', check=Stop())


if __name__ == '__main__': unittest.main()
