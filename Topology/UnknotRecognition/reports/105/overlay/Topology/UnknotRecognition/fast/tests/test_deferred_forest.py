"""Deferred primal forests on closed walks and authenticated native cuts."""
from copy import deepcopy
from itertools import combinations
import json
from pathlib import Path
import random
import unittest

from fastunknot.core_handlebody import (
    _forest, _occurrences, column_cancellation_plan, core_handlebody_certificate)
from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate
from fastunknot.core_three_handle_reduction import reduce_core_three_handles
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_surface_geometry import _prepare, _coordinates

ROOT = Path(__file__).parents[1]
BANK = json.loads((ROOT / 'marked_parallelity_research/corpus.json').read_text())['cases']
EXTRA = json.loads((ROOT / 'marked_parallelity_research/three_handle_corpus.json').read_text())['cases']


def source_core(case):
    p = _prepare(case['triangulation'], lambda: None)
    g = _parallelity_geometry(p, _coordinates(p, case['coordinates'], lambda: None),
                             lambda: None)
    return reduce_core_three_handles(g)[0]['core']


def abstract_core(n, edges, walks):
    """Closed graph walks only; these synthetic charts assert no manifold input."""
    rows = []
    for i, walk in enumerate(walks):
        cycle = []
        for v, e in walk:
            cycle.extend([dict(dimension=0, handle=v), dict(dimension=1, handle=e)])
        rows.append(dict(id=i, cycle=cycle))
    return dict(handles0=[dict(id=v) for v in range(n)],
                handles1=[dict(id=e, ends=list(pair)) for e, pair in enumerate(edges)],
                handles2=rows, handles3=[])


def forests(core):
    n = len(core['handles0'])
    size = len(_forest(core, lambda: None)[0])
    for chosen in combinations(range(len(core['handles1'])), size):
        component = list(range(n))
        for e in chosen:
            a, b = (component[v] for v in core['handles1'][e]['ends'])
            if a == b:
                break
            component = [min(a, b) if x in (a, b) else x for x in component]
        else:
            if all(component[h['ends'][0]] == component[h['ends'][1]]
                   for h in core['handles1']):
                yield chosen


class DeferredForestTests(unittest.TestCase):
    def test_two_vertex_closed_walk_strict_example(self):
        core = abstract_core(2, [(0, 1), (0, 1), (0, 1)], [
            [(0, 0), (1, 2), (0, 1), (1, 2)], [(0, 1), (1, 2)]])
        old = core_handlebody_certificate(core)
        new = core_handlebody_certificate(core, forest_strategy='deferred')
        self.assertEqual(old['status'], 'INCONCLUSIVE')
        self.assertEqual(new['status'], 'COMPLETE')
        self.assertEqual(new['certificate']['forest'], [1])
        self.assertEqual(new['certificate']['cancellations'], [[0, 0], [1, 2]])
        self.assertTrue(verify_core_handlebody_certificate(core, new['certificate']))

    def test_native_corpus_strict_coverage_and_old_checker(self):
        counts = [0, 0]
        improved = []
        for case in BANK + EXTRA:
            core = source_core(case)
            original = deepcopy(core)
            old = core_handlebody_certificate(core)
            new = core_handlebody_certificate(core, forest_strategy='deferred')
            self.assertEqual(core, original)
            for i, r in enumerate((old, new)):
                counts[i] += r['status'] == 'COMPLETE'
                if r['status'] == 'COMPLETE':
                    self.assertTrue(verify_core_handlebody_certificate(core, r['certificate']))
            if old['status'] == 'COMPLETE':
                self.assertEqual(new['status'], 'COMPLETE')
            elif new['status'] == 'COMPLETE':
                improved.append(case['id'])
        self.assertEqual(counts, [110, 118])
        self.assertEqual(improved, [
            'pilot/fibonacci_lst_04/0', 'pilot/fibonacci_lst_06/0',
            'pilot/fibonacci_lst_08/0', 'pilot/fibonacci_lst_10/0',
            'pilot/lst_4_9/0', 'pilot/finite_trefoil/0',
            'interior_loop/empty', 'interior_loop/boundary_link'])

    def test_exhaustive_forests_on_seeded_closed_walks(self):
        rng = random.Random(2026101201)
        examined = 0
        for _ in range(120):
            n = rng.randrange(1, 5)
            edges = [(v-1, v) for v in range(1, n)]
            edges += [(rng.randrange(n), rng.randrange(n))
                      for _ in range(rng.randrange(1, 5))]
            adjacency = {v: [] for v in range(n)}
            for e, (a, b) in enumerate(edges):
                adjacency[a].append((e, b))
                adjacency[b].append((e, a))
            walks = []
            for _ in range(rng.randrange(1, 5)):
                start = v = rng.randrange(n)
                walk = []
                for _ in range(rng.randrange(1, 5)):
                    e, w = rng.choice(adjacency[v])
                    walk.append((v, e))
                    v = w
                # The path edges connect consecutive labels and close the walk.
                while v != start:
                    w = v-1 if v > start else v+1
                    e = max(v, w)-1
                    walk.append((v, e))
                    v = w
                walks.append(walk)
            core = abstract_core(n, edges, walks)
            result = core_handlebody_certificate(core, forest_strategy='deferred')
            success = False
            for tree in forests(core):
                rows = _occurrences(core, tree, lambda: None)
                plan = column_cancellation_plan(rows)
                success |= not plan['remaining_rows']
                examined += 1
            self.assertEqual(result['status'] == 'COMPLETE', success)
            if success:
                self.assertTrue(verify_core_handlebody_certificate(core, result['certificate']))
        self.assertGreater(examined, 200)

    def test_repeated_bridge_and_loop_are_not_conflated(self):
        # A closed walk crosses the bridge twice and the loop once.
        core = abstract_core(2, [(0, 1), (1, 1)], [[(0, 0), (1, 1), (1, 0)]])
        r = core_handlebody_certificate(core, forest_strategy='deferred')
        self.assertEqual(r['certificate']['forest'], [0])
        self.assertEqual(r['certificate']['cancellations'], [[0, 1]])
        self.assertTrue(verify_core_handlebody_certificate(core, r['certificate']))
        bad = deepcopy(r['certificate'])
        bad['forest'] = [1]
        self.assertFalse(verify_core_handlebody_certificate(core, bad))
        bad = deepcopy(r['certificate'])
        bad['cancellations'] = [[0, 0]]
        self.assertFalse(verify_core_handlebody_certificate(core, bad))

    def test_invalid_strategy_and_interruption(self):
        core = abstract_core(1, [(0, 0)], [[(0, 0)]])
        with self.assertRaises(ValueError):
            core_handlebody_certificate(core, forest_strategy='unknown')
        def stop():
            raise RuntimeError('stopped')
        with self.assertRaisesRegex(RuntimeError, 'stopped'):
            core_handlebody_certificate(core, forest_strategy='deferred', check=stop)


if __name__ == '__main__':
    unittest.main()
