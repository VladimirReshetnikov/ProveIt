#!/usr/bin/env python3
"""Finite semantic and strict encoding regressions; not formal proof objects."""
from __future__ import annotations
import importlib.util
from pathlib import Path
import random
import sys
import unittest

import kernel_metrics as k


class KernelMetricsTests(unittest.TestCase):
    def test_congruence_equivalence_all_relations_through_three(self):
        checks = 0
        for n in range(1, 4):
            for code in range(1 << (n*n)):
                self.assertEqual(k.evaluate(k.congruence(), n, code),
                                 k.evaluate(k.congruence(True), n, code))
                checks += 1
        self.assertEqual(checks, 530)

    def test_concrete_instance_corresponds_to_abstract_matrix(self):
        abstract, actual = k.templates(), k.templates(k.Mem(0, 1))
        for n in (1, 2):
            for code in range(1 << (n*n)):
                def hole(args): return bool(code & (1 << (args[0]*n + args[1])))
                for name in abstract:
                    self.assertEqual(k.evaluate(abstract[name], n, code, hole=hole),
                                     k.evaluate(actual[name], n, code), name)
                    self.assertNotIn('hole', k.metrics(actual[name])['operators'])

    def test_seeded_instances_against_direct_semantics(self):
        def direct(n, code, seed, mixed):
            def mem(x, y): return bool(code & (1 << (x*n+y)))
            def sub(x, b): return all(not mem(z, x) or mem(z, b) for z in range(n))
            local = all(any(all(not mem(x, y) or sub(y, b) or (mixed and mem(y, b))
                                for y in range(n)) for b in range(n)) for x in range(n))
            if not local: return True
            def starts(x, a):
                return x == a if seed == 'point' else sub(x, a) if seed == 'subset' else mem(x, a)
            return all(any(
                all(not ((starts(x, a) or mem(x, c)) and mem(x, y)) or mem(y, c)
                    for x in range(n) for y in range(n)) and
                all(not mem(y, c) or any(mem(x, y) for x in range(n)) for y in range(n))
                for c in range(n)) for a in range(n))
        variants = [(s, m, k.seeded(k.Mem(0, 1), seed=s, mixed=m))
                    for s in ('point', 'subset', 'member') for m in (False, True)]
        for n in range(1, 4):
            for code in range(1 << (n*n)):
                for seed, mixed, f in variants:
                    self.assertEqual(k.evaluate(f, n, code), direct(n, code, seed, mixed))

    def test_fresh_parameters_and_simultaneous_substitution(self):
        matrix = k.And(k.Mem(0, 2), k.All(3, k.Imp(k.Mem(3, 1), k.Mem(2, 3))))
        for name, f in k.templates(matrix).items():
            self.assertEqual(k.free_vars(f), set(), name)
        context = k.Context(matrix)
        x, y = context.fresh(), context.fresh()
        self.assertGreater(x, max(k.variables(matrix)))
        self.assertEqual(k.free_vars(context.at(x, y)), {x, y, 2})
        self.assertEqual(k.substitute(k.Mem(0, 1), {0: 1, 1: 0}), k.Mem(1, 0))
        capture = k.substitute(k.All(1, k.Mem(0, 1)), {0: 1})
        self.assertEqual(k.free_vars(capture), {1})
        self.assertNotEqual(capture.args[0], 1)
        with self.assertRaises(ValueError): k.subset(0, 1, 1)
        with self.assertRaises(ValueError): k.seeded(seed='unknown')

    def test_normalization_alpha_reuse_and_nand_semantics(self):
        rng = random.Random(20261016)
        def formula(depth):
            if not depth or rng.randrange(4) == 0:
                x, y = rng.randrange(4), rng.randrange(4)
                return rng.choice((k.Mem(x, y), k.Eq(x, y)))
            choice = rng.randrange(4)
            if choice == 0: return k.Not(k.Not(formula(depth-1)))
            if choice == 1: return k.Not(formula(depth-1))
            if choice == 2: return k.All(rng.randrange(4), formula(depth-1))
            return k.Imp(formula(depth-1), formula(depth-1))
        for _ in range(600):
            f = formula(4)
            n = rng.randrange(1, 4)
            code = rng.randrange(1 << (n*n))
            env = {v: rng.randrange(n) for v in range(4)}
            normalized = k.normalize(f)
            reused = k.alpha_reuse(normalized)
            self.assertEqual(k.alpha_key(normalized), k.alpha_key(reused))
            expected = k.evaluate(f, n, code, env)
            for variant in (normalized, reused, k.bottom_basis(f), k.to_nand(f)):
                self.assertEqual(expected, k.evaluate(variant, n, code, env))

    def test_roundtrips_and_explicit_payload_accounting(self):
        examples = [k.Mem(0, 1), k.Eq(0, 1),
                    *[k.alpha_reuse(k.normalize(f)) for f in k.templates(k.Mem(0, 1)).values()]]
        for f in examples:
            p = k.to_nand(f)
            self.assertEqual(k.from_rpn(k.rpn(p)), p)
            bits = k.serialize(p)
            self.assertEqual(k.deserialize(bits), p)
            m = k.encoding_metrics(f)
            self.assertEqual(m['total_bits'], len(bits))
            self.assertEqual(m['total_bits'], m['variable_payload_bits'] + m['opcode_bits'] + m['framing_bits'])
        with self.assertRaises(ValueError): k.to_nand(k.Hole(0, 1))
        with self.assertRaises(ValueError): k.to_nand(k.Bot())

    def test_strict_rejection(self):
        for tokens in (None, [], [['nand']], [['all', 0]], [['mem', True, 0]],
                       [['mem', -1, 0]], [['hole', 0, 1]], [['mem', 0, 1, 2]],
                       [['mem', 0, 1], ['mem', 1, 0]], [['all', 0, 1]]):
            with self.assertRaises(ValueError, msg=repr(tokens)): k.from_rpn(tokens)
        valid = k.serialize(k.Mem(0, 1))
        for bits in (None, '', '2', 'x', '0', '000', valid[:-1], valid+'0', '0'+k.gamma(1), '100111001010'):
            with self.assertRaises(ValueError, msg=repr(bits)): k.deserialize(bits)
        with self.assertRaises(ValueError): k.gamma(0)
        with self.assertRaises(ValueError): k.gamma(True)
        with self.assertRaises(ValueError): k.Mem(True, 0)

    def test_source02_raw_reference(self):
        root = Path(__file__).resolve().parents[4]
        source = root / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/02-seeded-formulas.py'
        spec = importlib.util.spec_from_file_location('delivered_seeded_metrics_reference', source)
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        ref = module.templates()
        ours = k.templates()
        names = {'Ext': 'Ext', 'CG_symmetric_MiraEsharp': 'EC', 'CP': 'CP', 'GIC': 'GIC',
                 'PSC_point_subset': 'PISI_open', 'PSC_point_mixed': 'PIBI',
                 'PSC_subset_mixed': 'SIBI', 'ISI_member_subset': 'ISI'}
        for a, b in names.items():
            self.assertEqual(k.metrics(k.bottom_basis(ours[a]))['nodes'],
                             sum(module.count(module.expand(ref[b])).values()), a)
        bottom = lambda name: k.metrics(k.bottom_basis(ours[name]))['nodes']
        self.assertEqual(bottom('Ext') + bottom('PSC_point_subset'), 65)
        self.assertEqual(bottom('Ext') + bottom('PSC_subset_subset'), 68)
        self.assertEqual(bottom('CG_symmetric_MiraEsharp') + bottom('PSC_subset_subset'), 79)
        self.assertEqual(k.metrics(ours['CG_oneway'])['nodes'], 17)
        self.assertEqual(k.metrics(k.bottom_basis(ours['CG_symmetric_MiraEsharp']))['nodes'], 27)


if __name__ == '__main__':
    unittest.main(verbosity=2)
