"""Independent exhaustive-subset controls for the color-mask packing DP."""
from copy import deepcopy
from itertools import combinations
import random
import unittest

from causal_research.colorful_packing import pack_colorful_candidates


def subset_oracle(candidates, coloring, budget, goal):
    """Evaluate every subset directly, without masks or dynamic programming."""
    feasible = []
    for size in range(len(candidates) + 1):
        for indices in combinations(range(len(candidates)), size):
            sources = [source for index in indices
                       for source in candidates[index]['footprint']]
            colors = [coloring[source] for source in sources]
            upward = sum(candidates[index]['upward'] for index in indices)
            if len(set(colors)) != len(colors) or upward > budget:
                continue
            actual_loss = sum(candidates[index]['loss'] for index in indices)
            objective = (-min(goal, actual_loss), upward)
            feasible.append((objective, indices, actual_loss, sources))
    best = min(row[0] for row in feasible)
    return dict(capped_loss=-best[0], upward=best[1],
                optimal_witnesses={row[1] for row in feasible if row[0] == best})


class ColorfulPackingTests(unittest.TestCase):
    def assert_oracle(self, candidates, coloring, budget, goal):
        saved = deepcopy((candidates, coloring))
        answer = pack_colorful_candidates(candidates, coloring,
                                          max_upward=budget, goal=goal)
        expected = subset_oracle(candidates, coloring, budget, goal)
        self.assertEqual((answer['capped_loss'], answer['upward']),
                         (expected['capped_loss'], expected['upward']))
        self.assertIn(tuple(answer['selected_indices']), expected['optimal_witnesses'])
        self.assertEqual((candidates, coloring), saved)
        # Reconstruct the returned witness directly from original items.
        chosen = answer['selected_indices']
        self.assertEqual(chosen, sorted(set(chosen)))
        sources = [source for index in chosen
                   for source in candidates[index]['footprint']]
        colors = [coloring[source] for source in sources]
        self.assertEqual(len(colors), len(set(colors)))
        actual_loss = sum(candidates[index]['loss'] for index in chosen)
        self.assertEqual(answer['actual_loss'], actual_loss)
        self.assertEqual(answer['capped_loss'], min(goal, actual_loss))
        self.assertEqual(answer['goal_reached'], actual_loss >= goal)
        self.assertEqual(answer['footprint'], sorted(sources))
        self.assertEqual(answer['upward'],
                         sum(candidates[index]['upward'] for index in chosen))
        self.assertEqual(answer['colors'], sorted(colors))
        labels = answer['color_labels']
        self.assertEqual(answer['color_mask'], sum(1 << labels.index(color)
                                                  for color in colors))
        self.assertLessEqual(answer['upward'], budget)
        return answer

    def test_original_indices_survive_discarded_items_and_zero_costs(self):
        candidates = [
            dict(footprint=[0, 1], upward=0, loss=99),  # same color: discard
            dict(footprint=[2], upward=3, loss=99),     # exceeds budget
            dict(footprint=[0], upward=0, loss=1, payload={'unchanged': [1]}),
            dict(footprint=[2], upward=0, loss=1),
            dict(footprint=[3], upward=1, loss=1),
        ]
        answer = self.assert_oracle(candidates, [0, 0, 1, 2], 1, 3)
        self.assertEqual(answer['selected_indices'], [2, 3, 4])
        self.assertEqual(answer['discarded_noncolorful'], [0])
        self.assertEqual(answer['discarded_over_budget'], [1])
        self.assertEqual(answer['actual_loss'], 3)

    def test_capped_goal_cost_and_witness_ties(self):
        candidates = [
            dict(footprint=[0], upward=2, loss=100),
            dict(footprint=[1], upward=1, loss=4),
            dict(footprint=[2], upward=1, loss=2),
            dict(footprint=[1, 2], upward=1, loss=3),
            dict(footprint=[3], upward=0, loss=1),
        ]
        for budget in range(4):
            for goal in range(7):
                self.assert_oracle(candidates, [0, 1, 2, 3], budget, goal)
        answer = self.assert_oracle(candidates, [0, 1, 2, 3], 3, 3)
        self.assertEqual(answer['selected_indices'], [1])
        self.assertEqual((answer['actual_loss'], answer['capped_loss']), (4, 3))

    def test_empty_family_zero_goal_and_noncolorful_negative(self):
        self.assert_oracle([], [], 0, 0)
        self.assert_oracle([], [0, 1], 7, 3)
        candidates = [dict(footprint=[0, 1], upward=0, loss=2)]
        answer = self.assert_oracle(candidates, [0, 0], 0, 2)
        self.assertFalse(answer['goal_reached'])
        self.assertEqual(answer['selected_indices'], [])
        candidates = [dict(footprint=[0], upward=0, loss=2)]
        self.assertEqual(self.assert_oracle(candidates, [0], 0, 0)
                         ['selected_indices'], [])

    def test_capping_does_not_claim_global_cardinality_optimization(self):
        # At mask {0,1}, profit 4 from items 1,2 dominates profit 3 from
        # item 0.  Both reach the goal after item 3, so retaining one best
        # value per mask/cost does not optimize the number of items.
        candidates = [dict(footprint=[0, 1], upward=0, loss=3),
                      dict(footprint=[0], upward=0, loss=2),
                      dict(footprint=[1], upward=0, loss=2),
                      dict(footprint=[2], upward=0, loss=2)]
        answer = self.assert_oracle(candidates, [0, 1, 2], 0, 5)
        self.assertEqual((answer['capped_loss'], answer['upward']), (5, 0))

    def test_color_labels_are_equality_classes_not_array_sizes(self):
        candidates = [dict(footprint=[0, 2], upward=1, loss=2),
                      dict(footprint=[1], upward=0, loss=1)]
        answer = self.assert_oracle(candidates, [10**12, 10**12, 7], 1, 3)
        self.assertEqual(answer['color_labels'], [7, 10**12])
        self.assertEqual(answer['capped_loss'], 2)

    def test_every_subset_of_deterministic_small_random_families(self):
        rng = random.Random(20261009)
        for case in range(96):
            source_count = rng.randrange(1, 9)
            color_count = rng.randrange(1, source_count + 1)
            coloring = [rng.randrange(color_count) for _ in range(source_count)]
            candidates = [dict(
                footprint=rng.sample(range(source_count),
                                     rng.randrange(1, min(4, source_count) + 1)),
                upward=rng.randrange(4), loss=rng.randrange(1, 8))
                for _ in range(rng.randrange(1, 10))]
            for budget, goal in ((0, 1), (2, 3), (4, 6), (3, 0)):
                with self.subTest(case=case, budget=budget, goal=goal):
                    self.assert_oracle(candidates, coloring, budget, goal)

    def test_two_geometric_gadgets_supply_disjoint_verified_items(self):
        from causal_research.fixtures import descent_gadgets
        from fastunknot.pachner_cover_search import search_pachner_cover
        from fastunknot.pachner_commitments_verify import inspect_pachner_endpoint

        fixture = descent_gadgets(2)
        raw, heights = fixture['triangulation'], fixture['heights']
        searched = search_pachner_cover(raw, heights, max_region_size=6,
            max_components=1, max_upward=1, max_nodes=None,
            collect_endpoints=True, seek_disc=False)
        self.assertEqual(searched['status'], 'COMPLETE_BOUNDED_COVER_FAMILY')
        candidates = []
        for index, proof in enumerate(searched['endpoints']):
            replay = inspect_pachner_endpoint(raw, heights, proof)
            self.assertIsNotNone(replay)
            loss = replay['downward_moves'] - replay['upward_moves']
            if loss > 0:
                # The allowed cover can contain surviving tetrahedra.  Use
                # the independently replayed actual footprint, not its cover.
                candidates.append(dict(
                    footprint=replay['consumed_initial_tetrahedra'],
                    upward=replay['upward_moves'], loss=loss,
                    endpoint_index=index))
        self.assertEqual(len(candidates), 6)
        self.assertTrue(all((item['upward'], item['loss'], len(item['footprint']))
                            == (1, 1, 6) for item in candidates))
        coloring = [source % 12 for source in range(len(raw['tetrahedra']))]
        answer = self.assert_oracle(candidates, coloring, 2, 2)
        self.assertTrue(answer['goal_reached'])
        self.assertEqual(len(answer['selected_indices']), 2)
        self.assertEqual((answer['upward'], answer['actual_loss']), (2, 2))
        self.assertEqual(answer['footprint'], list(range(1, 13)))
        self.assertEqual({tuple(candidates[index]['footprint'])
                          for index in answer['selected_indices']},
                         {tuple(range(1, 7)), tuple(range(7, 13))})
        # One coloring can lose all valid uncolored witnesses.  Such failure
        # remains scoped to that coloring; splitter completeness is separate.
        monochromatic = self.assert_oracle(candidates, [0] * 13, 2, 2)
        self.assertFalse(monochromatic['goal_reached'])

    def test_invalid_inputs_are_rejected_before_zero_goal_shortcut(self):
        good = [dict(footprint=[0], upward=0, loss=1)]
        bad_options = [dict(max_upward=True), dict(max_upward=-1),
                       dict(max_upward=1.5), dict(goal=True), dict(goal=-1),
                       dict(goal='1')]
        for options in bad_options:
            with self.subTest(options=options), self.assertRaises(ValueError):
                pack_colorful_candidates(good, [0],
                    **(dict(max_upward=1, goal=0) | options))
        for candidates in (None, {}, (good[0],), [None], [{}],
                           [dict(footprint=[0], upward=0)]):
            with self.subTest(candidates=candidates), self.assertRaises(ValueError):
                pack_colorful_candidates(candidates, [0], max_upward=1, goal=0)
        for coloring in (None, {}, (0,), [True], [-1], [1.5], ['0']):
            with self.subTest(coloring=coloring), self.assertRaises(ValueError):
                pack_colorful_candidates(good, coloring, max_upward=1, goal=0)
        alterations = [dict(footprint=[]), dict(footprint=(0,)),
                       dict(footprint=[True]), dict(footprint=[-1]),
                       dict(footprint=[1]), dict(footprint=[0.0]),
                       dict(footprint=[[0]]), dict(footprint=[0, 0]),
                       dict(upward=True), dict(upward=-1), dict(upward=1.5),
                       dict(loss=True), dict(loss=0), dict(loss=-1),
                       dict(loss=1.5)]
        for alteration in alterations:
            with self.subTest(alteration=alteration), self.assertRaises(ValueError):
                pack_colorful_candidates([good[0] | alteration], [0],
                                          max_upward=1, goal=0)


if __name__ == '__main__':
    unittest.main()
