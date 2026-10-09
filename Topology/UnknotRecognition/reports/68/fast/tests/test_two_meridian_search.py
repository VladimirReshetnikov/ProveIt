"""Independent closure oracles, candidate completeness and frozen regressions."""
import importlib.util
import itertools
import json
from pathlib import Path
import random
import sys
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.geometry import ScanLimit
from fastunknot.two_meridian import (
    _Budget, _ProductivePairs, _SeedClosures, _model, _propagate, _rules,
    two_meridian_decide, verify_two_meridian_certificate,
)


ROOT = Path(__file__).resolve().parents[1]
UNCAPPED = dict(seconds=None, max_work=None, max_attempts=None)


def budget():
    return _Budget(lambda: None, None, None)


def fixed_point(crossings, seeds):
    """No queues, counters, stamps, incidence index or candidate filtering."""
    known = set(seeds)
    while True:
        updated = set(known)
        for over, u, v, _ in crossings:
            if over in known and u in known:
                updated.add(v)
            if over in known and v in known:
                updated.add(u)
        if updated == known:
            return known
        known = updated


def frozen_baseline():
    name = 'fastunknot._two_meridian_search_test_baseline'
    spec = importlib.util.spec_from_file_location(
        name, ROOT/'two_meridian_research/baseline_two_meridian.py')
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


class TwoMeridianSearchTests(unittest.TestCase):
    def check_system(self, n, crossings):
        rules, incident = _rules(n, crossings, budget())
        stamped = _SeedClosures(n, rules, incident, budget())
        candidates = _ProductivePairs.build(n, rules, budget())
        all_seeds = [seeds for k in (1, 2)
                     for seeds in itertools.combinations(range(n), k)]
        expected_first = None
        for seeds in all_seeds:
            known = fixed_point(crossings, seeds)
            dense = _propagate(n, rules, incident, seeds, budget())
            actual = stamped.propagate(seeds)
            self.assertEqual(actual, dense)
            self.assertEqual(set(stamped.reached), known)
            if len(known) == n and expected_first is None:
                expected_first = seeds
            if candidates is not None and len(seeds) == 2 and len(known) == n:
                self.assertIn(seeds, candidates.pairs)
        # Exercise reuse after the generation has advanced through every seed.
        actual_first = None
        for seeds in itertools.combinations(range(n), 1):
            if stamped.propagate(seeds)[1] == n:
                actual_first = seeds
                break
        if actual_first is None:
            pairs = (candidates.pairs if candidates is not None
                     else itertools.combinations(range(n), 2))
            for index, seeds in enumerate(pairs):
                if candidates is not None and candidates.excluded[index]:
                    self.assertLess(len(fixed_point(crossings, seeds)), n)
                    continue
                if stamped.propagate(seeds)[1] == n:
                    actual_first = seeds
                    break
                if candidates is not None:
                    candidates.exclude_closed(stamped, index, budget())
        self.assertEqual(actual_first, expected_first)

    def test_all_4096_four_arc_distinct_crossing_systems(self):
        n = 4
        triples = [(o, u, v, 1) for o in range(n)
                   for u, v in itertools.combinations(range(n), 2) if o not in (u, v)]
        self.assertEqual(len(triples), 12)
        for mask in range(1 << len(triples)):
            self.check_system(n, [t for j, t in enumerate(triples) if mask >> j & 1])

    def test_all_512_three_arc_systems_with_unary_rules(self):
        n = 3
        triples = [(o, u, v, 1) for o in range(n)
                   for u, v in itertools.combinations(range(n), 2)]
        self.assertEqual(len(triples), 9)
        for mask in range(1 << len(triples)):
            self.check_system(n, [t for j, t in enumerate(triples) if mask >> j & 1])

    def test_empty_small_and_random_degenerate_rule_systems(self):
        for n in range(4):
            self.check_system(n, [])
        # n=2 needs no first nonseed step; its sole seed pair must be retained.
        self.assertEqual(_ProductivePairs.build(2, [], budget()).pairs, [(0, 1)])
        rng = random.Random(2610081237)
        for _ in range(400):
            n = rng.randrange(1, 9)
            crossings = [tuple(rng.randrange(n) for _ in range(3)) +
                         (rng.choice((-1, 1)),) for _ in range(rng.randrange(0, 12))]
            self.check_system(n, crossings)

    def test_natural_fixtures_exact_certificate_and_first_pair(self):
        baseline = frozen_baseline()
        corpus = json.loads((ROOT/'two_meridian_research/corpus.json').read_text())
        closed_pruned = 0
        for row in corpus['cases']:
            d = Diagram.from_pd(row['pd'])
            old = baseline.two_meridian_decide(d, **UNCAPPED)
            new = two_meridian_decide(d, **UNCAPPED)
            self.assertEqual(new['status'], old['status'], row['name'])
            self.assertEqual(new.get('certificate'), old.get('certificate'), row['name'])
            self.assertEqual(new['statistics']['search_mode'], 'productive-prerequisites')
            closed_pruned += new['statistics']['closed_pairs_skipped']
            if new['status'] != 'INCONCLUSIVE':
                self.assertEqual(new['status'], row['expected'])
        self.assertGreater(closed_pruned, 0)
        gordian = next(row for row in corpus['cases'] if row['name'] == 'gordian')
        result = two_meridian_decide(Diagram.from_pd(gordian['pd']), seconds=None)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['reason'], 'no complete derivation from one or two seed meridians')
        self.assertLess(result['statistics']['attempts'], 416)
        self.assertLess(result['statistics']['work'], 100_000)
        self.assertEqual(result['statistics']['max_reached'], 5)

    def test_unary_active_planar_fallback_and_one_seed(self):
        baseline = frozen_baseline()
        checked_fallback = 0
        for strands in range(2, 9):
            d = Diagram.from_braid(strands, list(range(1, strands)))
            old, new = baseline.two_meridian_decide(d, **UNCAPPED), two_meridian_decide(d, **UNCAPPED)
            self.assertEqual(new['certificate'], old['certificate'])
            self.assertEqual(new['status'], 'UNKNOT')
            checked_fallback += new['statistics']['search_mode'] == 'all-pairs'
        self.assertGreater(checked_fallback, 0)

    def test_replay_is_search_independent_and_budget_boundaries(self):
        data = json.loads((ROOT/'examples/figure_eight.json').read_text())
        d = Diagram.from_json(data)
        full = two_meridian_decide(d, **UNCAPPED)
        with patch('fastunknot.two_meridian._SeedClosures.propagate',
                   side_effect=AssertionError('search called by verifier')):
            self.assertTrue(verify_two_meridian_certificate(d, full['certificate']))
        work = full['statistics']['work']
        self.assertEqual(two_meridian_decide(d, seconds=None, max_work=work)['certificate'],
                         full['certificate'])
        for cap in (0, 1, work - 1, work - full['statistics']['replay_work']):
            result = two_meridian_decide(d, seconds=None, max_work=cap)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', result)
            self.assertLessEqual(result['statistics']['work'], cap)
        for stop in (1, 15, 40, 70, 100, 130):
            calls = 0

            def cancel():
                nonlocal calls
                calls += 1
                if calls == stop:
                    raise ScanLimit('global cancellation')

            with self.assertRaises(ScanLimit):
                two_meridian_decide(d, check=cancel, **UNCAPPED)


if __name__ == '__main__':
    unittest.main()
