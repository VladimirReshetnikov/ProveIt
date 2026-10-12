"""Deferred forest proofs through the source-authenticated whole-cut wrapper."""
from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.bundle_boundary_kernel import bundle_boundary_kernel
from fastunknot.bundle_boundary_kernel_verify import replay_bundle_boundary_kernel
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from tests.test_normal_surface_orbits import relabel


class DeferredBoundaryKernelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = Path(__file__).parents[1]/'marked_parallelity_research'
        bank = json.loads((root/'corpus.json').read_text())['cases']
        extra = json.loads((root/'three_handle_corpus.json').read_text())['cases']
        ids = ('pilot/fibonacci_lst_08/0', 'pilot/fibonacci_lst_10/0',
               'interior_loop/empty')
        cls.cases = [next(c for c in bank+extra if c['id'] == name) for name in ids]
        cls.results = [normal_cut_handlebodies(c['triangulation'], c['coordinates'],
            forest_strategy='deferred', record_certificate=True) for c in cls.cases]

    def test_native_gains_and_literal_oracle(self):
        from marked_parallelity_research.audit_census import oracle
        for c, result in zip(self.cases, self.results):
            legacy = normal_cut_handlebodies(c['triangulation'], c['coordinates'])
            self.assertEqual(legacy['status'], 'INCONCLUSIVE')
            self.assertEqual(result['status'], 'COMPLETE')
            self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'],
                c['coordinates'], result['certificate']))
            self.assertEqual(result['census']['histogram'], oracle(c)['histogram'])
        self.assertEqual(self.results[0]['certificate']['kernel']['schema'],
                         'bundle-boundary-kernel-v3')

    def test_supplied_forest_is_checked_independently(self):
        c, result = self.cases[0], self.results[0]
        names = ('fastunknot.bundle_boundary_kernel.bundle_boundary_kernel',
                 'fastunknot.bundle_boundary_kernel._forest',
                 'fastunknot.bundle_boundary_kernel.column_cancellation_plan',
                 'fastunknot.core_handlebody.core_handlebody_certificate',
                 'fastunknot.normal_cut_handlebodies._census')
        proof = deepcopy(result['certificate'])
        proof['kernel']['forest'] = [hex(h) for h in proof['kernel']['forest']]
        with ExitStack() as stack:
            for name in names:
                stack.enter_context(patch(name, side_effect=AssertionError('producer called')))
            self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'],
                c['coordinates'], proof))

    def test_nonforests_and_invalid_pivots_are_rejected(self):
        c, result = self.cases[0], self.results[0]
        mutations = [
            lambda p: p['kernel']['forest'].pop(),
            lambda p: p['kernel']['forest'].append(p['kernel']['forest'][0]),
            lambda p: p['kernel']['forest'].__setitem__(0, True),
            lambda p: p['kernel']['forest'].__setitem__(0, -1),
            lambda p: p['kernel']['forest'].__setitem__(0, '0xno'),
            lambda p: p['kernel']['forest'].__setitem__(0, 10**9),
            lambda p: p['kernel']['cancellations'].pop(),
            lambda p: p['kernel']['cancellations'][0].__setitem__(1,
                p['kernel']['forest'][0]),
            lambda p: p['kernel'].update(schema='bundle-boundary-kernel-v2'),
        ]
        for mutate in mutations:
            proof = deepcopy(result['certificate'])
            mutate(proof)
            self.assertFalse(verify_normal_cut_handlebodies(c['triangulation'],
                c['coordinates'], proof))

    def test_budget_and_callback_contracts(self):
        c = self.cases[0]
        self.assertEqual(normal_cut_handlebodies(c['triangulation'], c['coordinates'],
            forest_strategy='deferred', max_cycles=0)['status'], 'INCONCLUSIVE')
        self.assertFalse(verify_normal_cut_handlebodies(c['triangulation'],
            c['coordinates'], self.results[0]['certificate'], max_operations=0))
        with self.assertRaises(ValueError):
            normal_cut_handlebodies(c['triangulation'], c['coordinates'],
                                   forest_strategy='invalid')
        with self.assertRaises(ValueError):
            bundle_boundary_kernel({}, {}, {}, forest_strategy='invalid')
        def stop():
            raise RuntimeError('stop')
        with self.assertRaisesRegex(RuntimeError, 'stop'):
            normal_cut_handlebodies(c['triangulation'], c['coordinates'],
                                   forest_strategy='deferred', check=stop)

    def test_direct_kernel_replay_and_binary_scaling(self):
        c, result = self.cases[0], self.results[0]
        proof = result['certificate']
        self.assertEqual(replay_bundle_boundary_kernel(proof['parallelity']['geometry'],
            proof['parallelity']['summary'], proof['boundary']['skeleton'],
            proof['kernel']), result['census'])
        rows = [[(1 << 128)*n for n in row] for row in c['coordinates']]
        scaled = normal_cut_handlebodies(c['triangulation'], rows,
            forest_strategy='deferred', record_certificate=True)
        self.assertEqual(scaled['status'], 'COMPLETE')
        self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'], rows,
                                                    scaled['certificate']))

    def test_relabelled_native_sources_replay(self):
        c = self.cases[0]
        rng = random.Random(26101271)
        for _ in range(3):
            raw, rows = relabel(c['triangulation'], c['coordinates'], rng)
            result = normal_cut_handlebodies(raw, rows,
                forest_strategy='deferred', record_certificate=True)
            self.assertEqual(result['status'], 'COMPLETE')
            self.assertEqual(result['census']['histogram'],
                             self.results[0]['census']['histogram'])
            self.assertTrue(verify_normal_cut_handlebodies(raw, rows, result['certificate']))


if __name__ == '__main__':
    unittest.main()
