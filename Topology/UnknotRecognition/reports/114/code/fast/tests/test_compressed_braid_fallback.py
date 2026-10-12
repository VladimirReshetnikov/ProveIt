"""Complete exceptional-factor fallback, source binding and independent replay."""
from copy import deepcopy
import random
import unittest
from unittest.mock import patch

from fastunknot.compressed_braid import recognize as native_recognize, verify, InvalidCertificate, CompressedLimit
from fastunknot.compressed_braid import cube
from fastunknot.compressed_braid.cube_verify import replay_rank
from fastunknot.compressed_braid.forest import summarize
from fastunknot.compressed_words import WordArena
from fastunknot.diagram import Diagram, DiagramError
from fastunknot.scan import khovanov_rank
from compressed_braid_research.families import sleeve


def recognize_cube(data, **options):
    """Keep the direct cube contract covered independently of adaptive reduction."""
    return native_recognize(data, use_fallback_reduction=False, **options)


def grammar(strands, word):
    rules, root = [['e']], 0
    for g in word:
        index = len(rules)
        rules.extend([['g', g], ['c', root, index]])
        root = index + 1
    return dict(strands=strands, rules=rules, root=root)


def join(left, right):
    rules, roots = [['e']], []
    for data, offset in ((left, 0), (right, left['strands'])):
        mapped = [0]
        for rule in data['rules'][1:]:
            if rule[0] == 'g':
                g = rule[1]
                new = ['g', (1 if g > 0 else -1) * (abs(g) + offset)]
            else:
                new = ['c', mapped[rule[1]], mapped[rule[2]]]
            mapped.append(len(rules))
            rules.append(new)
        roots.append(mapped[data['root']])
    rules.append(['c', *roots])
    roots = [len(rules)-1, len(rules)]
    rules.append(['g', left['strands']])
    rules.append(['c', *roots])
    return dict(strands=left['strands']+right['strands'], rules=rules, root=len(rules)-1)


UNKNOT = [1, 2, 3, 1, -1, 2, -2, 3, -3]
KNOT = [1, 2, -3] * 3


class ExceptionalCubeTests(unittest.TestCase):
    def test_both_verdicts_agree_with_independent_scanner(self):
        for word, status in ((UNKNOT, 'UNKNOT'), (KNOT, 'KNOTTED')):
            data = grammar(4, word)
            result = recognize_cube(data)
            self.assertEqual(result['status'], status)
            cert = result['certificate']
            self.assertEqual(cert['version'], 'compressed-singleton-forest-v2'
                             if status == 'UNKNOT' else 'compressed-singleton-forest-v3')
            child = cert['leaves'][0]['certificate']
            rank = khovanov_rank(Diagram.from_braid(4, word).pd)['reduced_rank']
            self.assertEqual(sum(child['homology']), rank)
            self.assertEqual(verify(data, cert), status)
            self.assertEqual(result['resources']['cube_generators'], 2*sum(child['dimensions']))

    def test_random_cubes_against_planar_scanner(self):
        rng = random.Random(261008492)
        checked = 0
        for _ in range(180):
            strands = rng.choice((3, 4, 5))
            word = [rng.choice((-1, 1))*rng.randrange(1, strands)
                    for _ in range(rng.randrange(strands-1, 10))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except DiagramError:
                continue
            data = grammar(strands, word)
            cert = cube.produce(data, summarize(data), max_crossings=10,
                                check=lambda: None, reserve=lambda size: None)
            expected = khovanov_rank(diagram.pd)['reduced_rank']
            self.assertEqual(sum(cert['homology']), expected, word)
            checked += 1
        self.assertGreaterEqual(checked, 25)

    def test_rank_transcripts_match_exhaustive_small_matrices(self):
        for bits in range(1 << 9):
            columns = [(bits >> (3*i)) & 7 for i in range(3)]
            span = {0}
            for col in columns:
                span |= {v ^ col for v in tuple(span)}
            rank, steps = cube.rank_trace(columns, lambda: None)
            self.assertEqual(rank, len(span).bit_length()-1)
            self.assertEqual(replay_rank(columns, 3, steps, lambda: None), rank)

    def test_rank_replay_rejects_nonspanning_and_dependent_witnesses(self):
        bad = [([1], [{'xor': [], 'pivot': -1}]),
               ([1, 1], [{'xor': [], 'pivot': 0}, {'xor': [], 'pivot': 0}]),
               ([1, 1], [{'xor': [], 'pivot': 0}, {'xor': [0, 0], 'pivot': -1}]),
               ([1], [{'xor': [1], 'pivot': 0}]),
               ([1], [{'xor': [], 'pivot': False}])]
        for cols, steps in bad:
            with self.assertRaises(InvalidCertificate):
                replay_rank(cols, 1, steps, lambda: None)

    def test_source_and_rank_mutations_rejected(self):
        data = grammar(4, KNOT)
        cert = recognize_cube(data)['certificate']
        for field, edit in (
                ('word', lambda x: [True] + x[1:]),
                ('word', lambda x: [-x[0]] + x[1:]),
                ('dimensions', lambda x: [True] + x[1:]),
                ('homology', lambda x: [x[0]+1] + x[1:]),
                ('differential_ranks', lambda x: [x[0]+1] + x[1:]),
                ('strands', lambda x: True),
                ('elimination', lambda x: x[:-1])):
            bad = deepcopy(cert)
            child = bad['leaves'][0]['certificate']
            child[field] = edit(child[field])
            with self.assertRaises(InvalidCertificate):
                verify(data, bad)
        bad = deepcopy(cert)
        bad['version'] = 'compressed-singleton-forest-v1'
        with self.assertRaises(InvalidCertificate):
            verify(data, bad)

    def test_replay_does_not_discover_rank_or_reduce_braids(self):
        data = grammar(4, UNKNOT)
        cert = recognize_cube(data)['certificate']
        with patch.object(cube, 'rank_trace', side_effect=AssertionError), \
             patch.object(cube, 'produce', side_effect=AssertionError), \
             patch.object(WordArena, 'lcp', side_effect=AssertionError):
            self.assertEqual(verify(data, cert), 'UNKNOT')

    def test_only_exceptional_factor_expands(self):
        data = join(sleeve(256), grammar(4, UNKNOT))
        expanded = []
        original = cube.expand_leaf
        def track(data, *args):
            expanded.append(data['strands'])
            return original(data, *args)
        with patch.object(cube, 'expand_leaf', side_effect=track), \
             patch.object(WordArena, 'expand', side_effect=AssertionError):
            result = recognize_cube(data)
        self.assertEqual(result['status'], 'UNKNOT')
        self.assertEqual(expanded, [4])
        self.assertEqual(verify(data, result['certificate']), 'UNKNOT')
        self.assertEqual(result['resources']['arenas'], 2)
        self.assertEqual(len(result['certificate']['leaves']), 2)

    def test_shared_generator_and_work_limits_cover_replay(self):
        data = join(grammar(4, UNKNOT), grammar(4, UNKNOT))
        full = recognize_cube(data)
        self.assertEqual(full['status'], 'UNKNOT')
        generators = full['resources']['cube_generators']
        work = full['resources']['work']
        self.assertEqual(recognize_cube(data, fallback_max_generators=generators, max_work=work)['status'], 'UNKNOT')
        for opts in (dict(fallback_max_generators=generators-1), dict(max_work=work-1)):
            limited = recognize_cube(data, **opts)
            self.assertEqual(limited['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', limited)
        with self.assertRaises(CompressedLimit):
            verify(data, full['certificate'], fallback_max_generators=0)

    def test_crossing_preflight_and_legacy_residual_proofs(self):
        data = grammar(4, KNOT)
        with patch.object(cube, 'produce', side_effect=AssertionError):
            result = recognize_cube(data, fallback_max_crossings=8)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['resources']['cube_generators'], 0)
        self.assertEqual(verify(data, result['certificate']), 'INCONCLUSIVE')
        self.assertEqual(result['certificate']['version'], 'compressed-singleton-forest-v1')
        for options in (dict(fallback_max_crossings=True), dict(fallback_max_generators=-1)):
            with self.assertRaises(ValueError):
                recognize_cube(data, **options)
        proof = recognize_cube(data)['certificate']
        with self.assertRaises(CompressedLimit):
            verify(data, proof, fallback_max_crossings=8)

    def test_empty_subgrammars_do_not_expand_exponentially(self):
        data = grammar(4, UNKNOT)
        empty = 0
        for _ in range(500):
            data['rules'].append(['c', empty, empty])
            empty = len(data['rules'])-1
        data['rules'].append(['c', data['root'], empty])
        data['root'] = len(data['rules'])-1
        self.assertEqual(cube.expand_leaf(data, len(UNKNOT), 12, lambda: None), UNKNOT)
        self.assertEqual(recognize_cube(data)['status'], 'UNKNOT')

    def test_huge_exceptional_factor_declines_before_expansion(self):
        data = grammar(4, UNKNOT)
        root = len(data['rules'])
        data['rules'].extend([['g', 1], ['g', -1], ['c', root, root+1]])
        root += 2
        for _ in range(1024):
            data['rules'].append(['c', root, root])
            root = len(data['rules'])-1
        data['rules'].append(['c', data['root'], root])
        data['root'] = len(data['rules'])-1
        with patch.object(cube, 'expand_leaf', side_effect=AssertionError):
            result = recognize_cube(data)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['resources']['cube_generators'], 0)
        self.assertTrue(result['verified'])

    def test_cancellation_inside_cube_propagates(self):
        class Cancelled(RuntimeError):
            pass
        data = grammar(4, UNKNOT)
        original = cube.resolution
        inside = False
        calls = 0
        def check():
            nonlocal calls
            if inside:
                calls += 1
                if calls == 7:
                    raise Cancelled
        def cancelled(strands, word, state, check):
            nonlocal inside
            inside = True
            try:
                return original(strands, word, state, check)
            finally:
                inside = False
        with patch.object(cube, 'resolution', side_effect=cancelled):
            with self.assertRaises(Cancelled):
                recognize_cube(data, check=check)
        self.assertEqual(calls, 7)


if __name__ == '__main__':
    unittest.main()
