"""Exact graph-model tests; none of these graphs asserts a 3-manifold source."""

from copy import deepcopy
from itertools import combinations, combinations_with_replacement, product
import random
import unittest
from unittest.mock import patch

from fastunknot.core_forest_exchange import plan_forest_exchange
from fastunknot.core_forest_exchange_verify import verify_forest_exchange


def _peels(rows):
    alive = set(rows)
    columns = {c for row in rows.values() for c in row}
    while alive:
        for c in columns:
            if sum(rows[r].get(c, 0) for r in alive) == 1:
                alive.remove(next(r for r in alive if rows[r].get(c, 0)))
                break
        else:
            return False
    return True


def _rank(vertices, edges):
    adjacency = {v: [] for v in vertices}
    for a, b in edges:
        adjacency[a].append(b)
        adjacency[b].append(a)
    seen, component_count = set(), 0
    for v in vertices:
        if v in seen:
            continue
        component_count += 1
        frontier = {v}
        while frontier:
            seen.update(frontier)
            frontier = {w for x in frontier for w in adjacency[x]} - seen
    return len(vertices) - component_count


def _row_edge(row):
    ends = [c for c, value in row.items() for _ in range(min(value, 2))]
    return tuple(ends + [-1] * (2 - len(ends)))


def _oracle(three, endpoints, rows):
    """Enumerate every dual spanning tree; return the least short-row nullity."""
    vertices = set(three) | {-1}
    forced = {r for r, row in rows.items() if sum(min(v, 2) for v in row.values()) > 2}
    columns = {c for row in rows.values() for c in row} | {-1}
    best, trees = None, []
    for chosen in combinations(rows, len(three)):
        selected = set(chosen)
        if not forced <= selected:
            continue
        dual = [tuple(endpoints[e]) + (-1,) * (2 - len(endpoints[e])) for e in selected]
        if _rank(vertices, dual) != len(three):
            continue
        retained = {r: row for r, row in rows.items() if r not in selected}
        rank = _rank(columns, [_row_edge(row) for row in retained.values()])
        nullity = len(retained) - rank
        assert (nullity == 0) == _peels(retained)
        best = nullity if best is None else min(best, nullity)
        trees.append((selected, nullity))
    return best, trees


def _from_pair(pair):
    row = {}
    for v in pair:
        if v != -1:
            row[v] = row.get(v, 0) + 1
    return row


class CoreForestExchangeTests(unittest.TestCase):
    def compare_with_oracle(self, three, endpoints, rows):
        before = deepcopy((three, endpoints, rows))
        result = plan_forest_exchange(three, endpoints, rows)
        self.assertTrue(verify_forest_exchange(
            three, endpoints, rows, result['certificate']), result)
        self.assertEqual((three, endpoints, rows), before)
        distance, _ = _oracle(three, endpoints, rows)
        self.assertEqual(result['status'] == 'COMPLETE', distance == 0)
        proof = result['certificate']
        if distance is not None and distance > 0:
            self.assertEqual(proof['kind'], 'short_row_rank_obstruction')
            self.assertEqual(proof['deficiency'], distance)
        if distance is None:
            self.assertIn(proof['kind'], ('boundary_disconnected', 'forced_long_cycle'))
        return result

    def test_exhaustive_small_graphs_and_rows(self):
        checked = 0
        # Both orientations of the size tradeoff; loops and parallel edges
        # are present. There are 6,175 labelled instances in each family.
        for three_count, column_count in ((1, 2), (2, 1)):
            three = list(range(three_count))
            dual_types = list(combinations_with_replacement([-1] + three, 2))
            row_types = list(combinations_with_replacement(
                [-1] + list(range(column_count)), 2))
            for edge_count in range(4):
                for pairs in product(product(dual_types, row_types), repeat=edge_count):
                    ends = {e: [v for v in pair[0] if v != -1]
                            for e, pair in enumerate(pairs)}
                    rows = {e: _from_pair(pair[1]) for e, pair in enumerate(pairs)}
                    self.compare_with_oracle(three, ends, rows)
                    checked += 1
        self.assertEqual(checked, 12350)

    def test_seeded_general_rows_and_forced_contraction(self):
        rng = random.Random(2026101219)
        for _ in range(1200):
            three = list(range(rng.randrange(4)))
            count, width = rng.randrange(9), rng.randrange(5)
            ends = {e: [v for v in (rng.choice([-1] + three),
                                    rng.choice([-1] + three)) if v != -1]
                    for e in range(count)}
            rows = {e: {c: value for c in range(width) if (value := rng.randrange(4))}
                    for e in range(count)}
            self.compare_with_oracle(three, ends, rows)

    def test_exchange_finds_an_alternative_to_stalled_greedy_tree(self):
        # Purely combinatorial example: no claim of geometric realizability.
        ends = {0: [0, 1], 1: [1], 2: [0]}
        rows = {0: {0: 1}, 1: {}, 2: {0: 2}}
        self.assertFalse(_peels({2: rows[2]}))  # dual tree {0, 1}
        result = self.compare_with_oracle([0, 1], ends, rows)
        self.assertEqual(result['certificate']['dual_forest'], [1, 2])
        self.assertGreater(result['stats']['recoloured_edges'], 0)

    def test_forced_long_rows_are_contracted_before_exchange(self):
        ends = {0: [0], 1: [0, 1], 2: [1]}
        rows = {0: {0: 1, 1: 1, 2: 1}, 1: {1: 1}, 2: {2: 1}}
        result = self.compare_with_oracle([0, 1], ends, rows)
        self.assertIn(0, result['certificate']['dual_forest'])
        self.assertEqual(result['stats']['forced_long_rows'], 1)

    def test_zero_rows_repeated_crossings_and_dual_loops(self):
        examples = [([], {0: []}, {0: {}}),
                    ([0], {0: [0, 0]}, {0: {1: 1}}),
                    ([0], {0: [0]}, {0: {1: 2}}),
                    ([], {0: []}, {0: {1: 2}}),
                    ([0], {0: [0], 1: [0]}, {0: {}, 1: {}})]
        for source in examples:
            self.compare_with_oracle(*source)

    def test_exact_positive_minimum_deficiency(self):
        ends = {e: [0] for e in range(5)}
        rows = {e: {0: 1} for e in range(5)}
        result = self.compare_with_oracle([0], ends, rows)
        proof = result['certificate']
        self.assertEqual(proof['deficiency'], 3)
        self.assertEqual(len(proof['unassigned_rows']), 3)
        self.assertEqual(len(proof['occurrence_forest']), 1)

    def test_general_peelable_rows_are_not_a_matroid(self):
        rows = {0: {2: 1}, 1: {1: 1, 2: 1},
                2: {0: 1, 1: 1}, 3: {0: 1, 1: 1, 2: 1}}
        smaller, larger = {2, 3}, {0, 1, 2}
        self.assertTrue(_peels({r: rows[r] for r in smaller}))
        self.assertTrue(_peels({r: rows[r] for r in larger}))
        for e in larger - smaller:
            self.assertFalse(_peels({r: rows[r] for r in smaller | {e}}))

    def test_restricted_strategy_refusal_can_still_be_raw_peelable(self):
        rows = {0: {0: 1, 1: 1, 2: 1}}
        self.assertTrue(_peels(rows))
        result = self.compare_with_oracle([], {0: []}, rows)
        self.assertEqual(result['certificate']['kind'], 'forced_long_cycle')
        self.assertNotIn('components', result)

    def test_binary_counts_and_labels_do_not_expand(self):
        huge = 1 << 16384
        source = ([huge + 1], {huge + 2: [huge + 1]}, {huge + 2: {huge + 3: huge}})
        result = self.compare_with_oracle(*source)
        self.assertEqual(result['status'], 'COMPLETE')

    def test_independent_verifier_never_calls_production(self):
        sources = [([0], {0: [0]}, {0: {}}),
                   ([0], {e: [0] for e in range(4)}, {e: {1: 1} for e in range(4)}),
                   ([0], {0: [0, 0]}, {0: {1: 1}}),
                   ([], {0: []}, {0: {0: 1, 1: 1, 2: 1}})]
        proofs = [plan_forest_exchange(*s)['certificate'] for s in sources]
        with patch('fastunknot.core_forest_exchange.plan_forest_exchange',
                   side_effect=AssertionError), \
             patch('fastunknot.core_forest_exchange._prepare', side_effect=AssertionError), \
             patch('fastunknot.core_forest_exchange._graphic_partition',
                   side_effect=AssertionError):
            for source, proof in zip(sources, proofs):
                self.assertTrue(verify_forest_exchange(*source, proof))

    def test_rejects_mutated_positive_and_rank_certificates(self):
        source = ([0, 1], {0: [0, 1], 1: [1], 2: [0]},
                  {0: {0: 1}, 1: {}, 2: {0: 2}})
        proof = plan_forest_exchange(*source)['certificate']
        changes = [('dual_forest', [0, 1]), ('dual_forest', [True, 2]),
                   ('two_three_cancellations', [[1, 1], [2, 1]]),
                   ('one_two_cancellations', []), ('one_two_cancellations', [[0, True]]),
                   ('schema', 'not-a-schema'), ('trusted_geometry', True)]
        for key, value in changes:
            forged = deepcopy(proof)
            forged[key] = value
            self.assertFalse(verify_forest_exchange(*source, forged))
        changed_source = deepcopy(source)
        changed_source[2][0][0] = 2
        self.assertFalse(verify_forest_exchange(*changed_source, proof))
        obstruction = ([0], {e: [0] for e in range(5)}, {e: {0: 1} for e in range(5)})
        proof = plan_forest_exchange(*obstruction)['certificate']
        for key, value in [('rows', []), ('ranks', [1, 2]), ('deficiency', 2),
                           ('unassigned_rows', []), ('occurrence_forest', [0, 1]),
                           ('two_three_cancellations', [])]:
            forged = deepcopy(proof)
            forged[key] = value
            self.assertFalse(verify_forest_exchange(*obstruction, forged))

    def test_invalid_source_and_cooperative_interruption(self):
        for source in [([True], {}, {}), ([0, 0], {}, {}),
                       ([0], {0: [0, 0, 0]}, {0: {}}),
                       ([0], {0: [1]}, {0: {}}),
                       ([0], {0: [0]}, {}),
                       ([0], {0: [0]}, {0: {0: -1}}),
                       ([0], {0: [0]}, {0: {0: True}})]:
            with self.assertRaises(ValueError):
                plan_forest_exchange(*source)
            self.assertFalse(verify_forest_exchange(*source, {}))
        class Stop(Exception):
            pass
        def stop():
            raise Stop
        with self.assertRaises(Stop):
            plan_forest_exchange([], {}, {}, check=stop)
        with self.assertRaises(Stop):
            verify_forest_exchange([], {}, {}, {}, check=stop)


if __name__ == '__main__':
    unittest.main()
