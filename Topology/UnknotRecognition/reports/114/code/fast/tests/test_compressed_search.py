"""Cross-check compressed discovery, graph multiplicities and resource limits."""
from collections import Counter
import json
import random
import subprocess
import sys
import unittest
from unittest.mock import patch

from benchmark_compressed_words import cases, ROOT
from fastunknot import Diagram, recognize
from fastunknot.compressed_words import WordArena
from fastunknot.compressed_search import compressed_certificate, _search
from fastunknot.group_certificate import (
    _Budget, _whitehead_graph, _whitehead_cut, _image, _reduce,
    group_decide, verify_group_certificate, GroupLimit)
from fastunknot.scan import ScanLimit


class CompressedSearchTests(unittest.TestCase):
    def test_random_dag_counts_graphs_and_cut_deltas(self):
        rng = random.Random(2687)
        for _ in range(250):
            arena, roots, words = WordArena(), [0], [[]]
            for _ in range(35):
                if rng.randrange(3) == 0:
                    word = [rng.choice([-3, -2, -1, 1, 2, 3])]
                    node = arena.from_word(word)
                else:
                    i, j = rng.randrange(len(roots)), rng.randrange(len(roots))
                    word, node = words[i]+words[j], arena.concat(roots[i], roots[j])
                words.append(word)
                roots.append(node)
            selected = [rng.randrange(len(roots)) for _ in range(8)]
            selected += [selected[-1]]  # Repeated roots and shared children count twice.
            budget = _Budget(lambda: None, 1000000, 10000000)
            explicit = [words[i] for i in selected]
            counts, graph = arena.summarize([roots[i] for i in selected], whitehead=True)
            self.assertEqual(arena.singletons([roots[i] for i in selected]),
                [sorted(g for g, count in Counter(map(abs, w)).items() if count == 1) for w in explicit])
            self.assertEqual(counts, Counter(abs(x) for w in explicit for x in w))
            self.assertEqual(graph, _whitehead_graph(explicit, budget))
            reduced = [_reduce(w, budget) for w in explicit]
            compressed = [arena.cyclic_reduce(roots[i]) for i in selected]
            _, graph = arena.summarize(compressed, whitehead=True)
            delta, a, subset = _whitehead_cut(graph, arena)
            if delta < 0:
                transformed = [_reduce((y for x in w for y in _image(x, a, subset)), budget)
                               for w in reduced]
                self.assertEqual(sum(map(len, transformed))-sum(map(len, reduced)), delta)

    def test_huge_shared_graph_and_elimination_never_expand(self):
        arena, n = WordArena(), 2**100
        block = arena.power(arena.from_word([1, 2]), n)
        with patch.object(arena, 'expand', side_effect=AssertionError('unexpected expansion')):
            counts, graph = arena.summarize([block, block, 0], whitehead=True)
            self.assertEqual(counts, {1: 2*n, 2: 2*n})
            self.assertEqual(graph, {1: {-2: 2*n}, -2: {1: 2*n},
                                    2: {-1: 2*n}, -1: {2: 2*n}})
            # A compressed abstract Z presentation, not a hard knot diagram.
            root = arena.concat(arena.letter(1), arena.power(arena.letter(2), n))
            roots, alive, moves = [root], {1, 2}, []
            self.assertTrue(_search(arena, roots, alive, moves, max_letters=4))
            self.assertEqual(moves, [dict(kind='eliminate', relation=0, generator=1)])
            self.assertEqual(alive, {2})

    def test_oversize_overlap_is_skipped_without_false_verdict(self):
        arena = WordArena()
        roots = [arena.power(arena.letter(g), 2**80) for g in (1, 2)]
        with patch.object(arena, 'expand', side_effect=AssertionError('unexpected expansion')):
            self.assertFalse(_search(arena, roots, {1, 2}, [], relator_moves=True, max_letters=10))
        self.assertEqual(arena.stats['overlap_skips'], 1)

    def test_real_knots_both_replayers_and_nontrivial_inputs(self):
        for name, d in cases():
            with self.subTest(name=name):
                certificate = compressed_certificate(d, relator_moves=True, max_work=10000000)
                self.assertIsNotNone(certificate)
                for compressed in (False, True):
                    self.assertTrue(verify_group_certificate(d, certificate,
                        compressed=compressed, max_work=10000000))
        for braid in ([1]*3, [1]*5, [1, -2]*2):
            d = Diagram.from_braid(2 if 2 not in map(abs, braid) else 3, braid)
            self.assertIsNone(compressed_certificate(d, relator_moves=True))

    def test_limits_cancellation_api_and_cli(self):
        _, d = next(cases())
        for options in ({'max_nodes': 0}, {'max_work': 0}, {'max_letters': 0}):
            with self.assertRaises(GroupLimit):
                compressed_certificate(d, **options)
            self.assertEqual(group_decide(d, compressed_search=True, **options)['status'], 'INCONCLUSIVE')
        for options in ({'max_nodes': -1}, {'stats': []}, {'relator_moves': 1}):
            with self.assertRaises(ValueError):
                compressed_certificate(d, **options)
        with self.assertRaises(ValueError):
            group_decide(d, compressed_search=1)
        with self.assertRaises(ValueError):
            recognize(d, group_compressed_search=1)
        def cancel():
            raise ScanLimit('global cancellation during compressed search')
        with self.assertRaises(ScanLimit):
            group_decide(d, compressed_search=True, check=cancel)
        result = recognize(Diagram.from_pd(d.pd), use_group=True,
                           group_compressed_search=True, group_seconds=None)
        self.assertEqual(result.evidence['group']['search_backend'], 'compressed-slp')
        self.assertEqual(result.evidence['group']['verification_backend'], 'compressed-slp')
        run = subprocess.run([sys.executable, '-B', '-m', 'fastunknot', 'recognize', '-',
            '--group-compressed-search', '--group-seconds', '2'],
            input=json.dumps({'pd': d.pd}), text=True, capture_output=True, cwd=ROOT)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout)['evidence']['group']['search_backend'], 'compressed-slp')


if __name__ == '__main__':
    unittest.main()
