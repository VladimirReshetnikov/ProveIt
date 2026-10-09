"""Primitive cocycles, native source proofs and sound portfolio fallbacks."""
from copy import deepcopy
from fractions import Fraction
import importlib.util
import json
import random
import subprocess
import sys
import tempfile
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed, CocycleLimit, _rank_one_kernel, _Budget
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_surface_geometry import _prepare, _coordinates, NormalOrbitError
from fastunknot.normal_disk_kernel import normal_compressing_disk_count
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_components import relabel


OPTIONS = dict(use_reduction=False, use_descending=False, use_seifert=False,
               use_braid=False, use_rational=False, use_factorization=False,
               use_modular=False, use_jones=False, use_alexander=False, use_r3=False,
               use_normal_seed=True, max_objects=20000)


class NormalSeedTests(unittest.TestCase):
    def test_sparse_kernel_against_dense_rational_rank_and_nullspace(self):
        rng = random.Random(261009463)
        for trial in range(240):
            dimension = rng.randrange(1, 10)
            matrix = [[rng.randrange(-4, 5) if rng.random() < .4 else 0
                       for _ in range(dimension)] for _ in range(rng.randrange(0, 14))]
            if trial == 239:
                matrix = [[(1 << 2000)*x for x in row] for row in matrix]
            dense = [[Fraction(x) for x in row] for row in matrix]
            pivots = []
            for column in range(dimension):
                selected = next((r for r in range(len(pivots), len(dense)) if dense[r][column]), None)
                if selected is None:
                    continue
                r = len(pivots)
                dense[r], dense[selected] = dense[selected], dense[r]
                coefficient = dense[r][column]
                dense[r] = [x/coefficient for x in dense[r]]
                for other in range(len(dense)):
                    if other != r:
                        factor = dense[other][column]
                        dense[other] = [a-factor*b for a, b in zip(dense[other], dense[r])]
                pivots.append(column)
            rows = [{i: x for i, x in enumerate(row) if x} for row in matrix]
            if dimension-len(pivots) != 1:
                with self.assertRaises(NormalOrbitError):
                    _rank_one_kernel(rows, dimension, _Budget(lambda: None, None))
                continue
            actual, _ = _rank_one_kernel(rows, dimension, _Budget(lambda: None, None))
            free = next(i for i in range(dimension) if i not in pivots)
            expected = [Fraction(0)]*dimension
            expected[free] = 1
            for r, pivot in enumerate(pivots):
                expected[pivot] = -dense[r][free]
            self.assertNotEqual(actual[free], 0)
            self.assertEqual([Fraction(x)/actual[free] for x in actual], expected)
            self.assertTrue(all(sum(x*y for x, y in zip(row, actual)) == 0 for row in matrix))

    def test_primitive_layered_meridians_and_cocycle_face_transitions(self):
        rng = random.Random(261009462)
        for n in (1, 2, 4, 8, 32):
            raw, _ = layered_torus(n)
            for source in (raw, relabel(raw, [[0]*7 for _ in range(n)], rng)[0]):
                seed = rank_one_cocycle_seed(source)
                self.assertEqual(seed['stats']['chords']-seed['stats']['pivots'], 1)
                p = _prepare(source, lambda: None)
                _coordinates(p, seed['coordinates'], lambda: None)
                for t, f, u, g, permutation in p['pairs']:
                    self.assertEqual(len({seed['heights'][u][permutation[v]]-seed['heights'][t][v]
                                          for v in range(4) if v != f}), 1)
                answer = normal_compressing_disk_count(source, seed['coordinates'])
                self.assertEqual(answer['compressing_disk_components'], 1)

    def test_source_proofs_replay_without_any_discovery_or_external_engine(self):
        for diagram in (Diagram.from_pd([]), Diagram.from_braid(2, [1]),
                        Diagram.from_braid(2, [-1]), Diagram.from_braid(5, [1, 2, 3, 4])):
            with patch('fastunknot.normal_seed.minimize_cocycle_span', side_effect=AssertionError):
                result = normal_seed_decide(diagram)
            self.assertEqual(result['status'], 'UNKNOT')
            self.assertEqual([s['stage'] for s in result['stages']], ['raw'])
            proof = json.loads(json.dumps(result['certificate']))
            with patch('fastunknot.normal_seed.normal_seed_decide', side_effect=AssertionError), \
                 patch('fastunknot.normal_cocycle.rank_one_cocycle_seed', side_effect=AssertionError), \
                 patch('fastunknot.cocycle_span.minimize_cocycle_span', side_effect=AssertionError), \
                 patch('fastunknot.diagram_exterior.diagram_exterior', side_effect=AssertionError), \
                 patch('fastunknot.normal_disk_kernel.normal_compressing_disk_count', side_effect=AssertionError):
                self.assertTrue(verify_normal_seed_certificate(diagram, proof))

    def test_minimum_pieces_does_not_mean_minimum_genus(self):
        diagram = Diagram.from_braid(2, [1, 1, -1])
        result = normal_seed_decide(diagram)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual([s['normal_pieces'] for s in result['stages']], [45, 43])
        self.assertEqual([s['compressing_discs'] for s in result['stages']], [0, 0])
        self.assertEqual(recognize(diagram, **OPTIONS).status, 'UNKNOT')
        trefoil = normal_seed_decide(Diagram.from_braid(2, [1, 1, 1]))
        self.assertEqual(trefoil['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', trefoil)

    def test_optimization_finds_a_disc_after_the_raw_seed_fails(self):
        diagram = Diagram.from_braid(4, [-1, 2, 1, -2, 3])
        result = normal_seed_decide(diagram)
        self.assertEqual(result['status'], 'UNKNOT')
        self.assertEqual([s['compressing_discs'] for s in result['stages']], [0, 1])
        self.assertEqual([s['normal_pieces'] for s in result['stages']], [194, 84])
        self.assertTrue(verify_normal_seed_certificate(diagram, result['certificate']))
        self.assertEqual(normal_seed_decide(diagram, optimize=False)['status'], 'INCONCLUSIVE')

    def test_certificate_source_geometry_coordinates_and_zero_count_are_checked(self):
        diagram = Diagram.from_braid(2, [1])
        proof = normal_seed_decide(diagram)['certificate']
        self.assertFalse(verify_normal_seed_certificate(Diagram.from_braid(2, [1, 1, 1]), proof))
        for field in proof:
            bad = deepcopy(proof); del bad[field]
            self.assertFalse(verify_normal_seed_certificate(diagram, bad))
        bad = deepcopy(proof); bad['coordinates'][0][0] += 1
        self.assertFalse(verify_normal_seed_certificate(diagram, bad))
        bad = deepcopy(proof); bad['triangulation']['tetrahedra'][0][0] = None
        self.assertFalse(verify_normal_seed_certificate(diagram, bad))
        raw = proof['triangulation']; zeros = [[0]*7 for _ in raw['tetrahedra']]
        valid_zero = normal_compressing_disk_count(raw, zeros, record_certificate=True)
        legacy = dict(schema='diagram-normal-disc-v1', input_pd=proof['input_pd'],
                      triangulation=raw, coordinates=proof['coordinates'],
                      disc_certificate=normal_compressing_disk_count(
                          raw, proof['coordinates'], record_certificate=True)['certificate'])
        self.assertTrue(verify_normal_seed_certificate(diagram, legacy))
        bad = dict(legacy, coordinates=zeros, disc_certificate=valid_zero['certificate'])
        self.assertFalse(verify_normal_seed_certificate(diagram, bad))
        valid_zero['certificate']['compressing_disk_components'] = True
        self.assertFalse(verify_normal_seed_certificate(diagram, bad))

    def test_shared_budget_and_false_valued_cancellation(self):
        diagram = Diagram.from_braid(2, [1])
        full = normal_seed_decide(diagram)
        for cap in (0, 1, 100, full['work']-1):
            result = normal_seed_decide(diagram, max_work=cap)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', result)
        self.assertEqual(normal_seed_decide(diagram, max_work=full['work'])['status'], 'UNKNOT')
        # Connectedness is now checked without interval-orbit cycles.
        self.assertEqual(normal_seed_decide(diagram, max_cycles=0)['status'], 'UNKNOT')
        raw = diagram_exterior(diagram)
        with self.assertRaises(CocycleLimit): rank_one_cocycle_seed(raw, max_work=0)
        class Stop:
            def __bool__(self): return False
            def __call__(self): raise RuntimeError('cancelled')
        with self.assertRaisesRegex(RuntimeError, 'cancelled'): normal_seed_decide(diagram, check=Stop())
        with self.assertRaisesRegex(RuntimeError, 'cancelled'):
            verify_normal_seed_certificate(diagram, full['certificate'], check=Stop())
        for options in ({'max_work': True}, {'optimize': 1}, {'max_cycles': -1}):
            with self.assertRaises(ValueError): normal_seed_decide(diagram, **options)

    def test_pipeline_positive_fallback_deadline_and_option_validation(self):
        source = Diagram.from_braid(2, [1])
        result = recognize(source, **OPTIONS)
        self.assertEqual(result.method, 'native-normal-cocycle')
        self.assertTrue(verify_normal_seed_certificate(source, result.evidence['normal_seed']['certificate']))
        self.assertNotIn('external-engine', result.to_json()['worst_case'])
        for word, expected in (([1, 1, -1], 'UNKNOT'), ([1, 1, 1], 'KNOTTED')):
            result = recognize(Diagram.from_braid(2, word), **OPTIONS)
            self.assertEqual(result.status, expected)
            self.assertEqual(result.evidence['normal_seed']['status'], 'INCONCLUSIVE')
        self.assertEqual(recognize(source, **OPTIONS, normal_seed_max_work=0).status, 'UNKNOT')
        self.assertEqual(recognize(source, **OPTIONS, seconds=0).status, 'UNKNOWN')
        for options in ({'use_normal_seed': 1}, {'normal_seed_optimize': 0}, {'normal_seed_max_work': -1}):
            with self.assertRaises(ValueError): recognize(source, **options)

    def test_command_line_flags(self):
        output = subprocess.check_output([sys.executable, '-B', '-m', 'fastunknot', 'recognize', '--help'], text=True)
        for flag in ('--normal-seed', '--normal-seed-max-work', '--normal-seed-no-optimize'):
            self.assertIn(flag, output)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'curl.json'
            diagram = Diagram.from_braid(2, [1])
            path.write_text(json.dumps({'pd': diagram.pd}))
            output = subprocess.check_output([sys.executable, '-B', '-m', 'fastunknot',
                'recognize', str(path), '--normal-seed', '--normal-seed-no-optimize',
                '--no-seifert', '--no-reduction', '--no-descending'], text=True)
            result = json.loads(output)
            self.assertEqual(result['method'], 'native-normal-cocycle')
            self.assertTrue(verify_normal_seed_certificate(diagram, result['evidence']['normal_seed']['certificate']))

    @unittest.skipUnless(importlib.util.find_spec('regina'), 'optional higher-rank and torsion controls')
    def test_higher_rank_rejected_and_rank_one_with_torsion_uses_exact_nonunit_pivots(self):
        import regina
        from normal_orbit_research.fixtures import export_triangulation
        high = regina.Example3.lst(1, 2)
        high.connectedSumWith(regina.Example3.s2xs1())
        self.assertEqual(high.homology().rank(), 2)
        with self.assertRaisesRegex(NormalOrbitError, 'Betti number one'):
            rank_one_cocycle_seed(export_triangulation(high))
        torsion = regina.Example3.lst(1, 2)
        torsion.connectedSumWith(regina.Example3.lens(2, 1))
        self.assertEqual(torsion.homology().rank(), 1)
        raw = export_triangulation(torsion)
        seed = rank_one_cocycle_seed(raw)
        self.assertGreater(seed['stats']['nonunit_pivots'], 0)
        _coordinates(_prepare(raw, lambda: None), seed['coordinates'], lambda: None)


if __name__ == '__main__':
    unittest.main()
