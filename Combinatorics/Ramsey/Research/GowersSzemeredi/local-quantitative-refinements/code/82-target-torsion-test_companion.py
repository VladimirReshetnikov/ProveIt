#!/usr/bin/env python3
"""Adversarial, standard-library tests for the public Report294 companion.

Run from the bundle root with ``python -B -m unittest discover -s tests -v``.
The suite also runs the checker in optimized, isolated, arbitrary-directory,
read-only, and write/network-audited subprocesses. No network is used.
"""
from __future__ import annotations

import sys
sys.dont_write_bytecode = True

import ast
from collections import Counter, defaultdict
from copy import deepcopy
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, islice, product
import json
from math import factorial
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from companion import exact_checks as check

SCRIPT = ROOT / 'companion' / 'exact_checks.py'
CERTIFICATE = SCRIPT.with_name('midpoint_certificate.json')
CERTIFICATE_SHA256 = 'cb053838d26497a2e52890e56f3b2c98202c7b1c04bcb6218059fac74db2570a'
EXPECTED_RELATIONS = (
    ((1, -2, 1), (1, 1, -2), (2, -1, -1)),
    ((1, -2, 1), (1, 1, 1), (2, -1, 2)),
    ((1, 1, -2), (1, 1, 1), (2, 2, -1)),
    ((2, -1, -1), (2, -1, 2), (4, -2, 1)),
    ((2, -1, -1), (2, 2, -1), (4, 1, -2)),
    ((2, -1, 2), (2, 2, -1), (4, 1, 1)),
)


def independent_energy(values, weights, rank, modulus=None):
    """Reference: four nested indices, with no checker geometry helpers."""
    pts = list(product((0, 1, 2), repeat=rank))
    retained = ordinary = Fraction(0)
    for a, b, c, d in product(range(len(pts)), repeat=4):
        if any((pts[a][j] + pts[b][j] - pts[c][j] - pts[d][j]) % 3
               for j in range(rank)):
            continue
        contribution = weights[a] * weights[b] * weights[c] * weights[d]
        ordinary += contribution
        defect = values[a] + values[b] - values[c] - values[d]
        if (defect == 0) if modulus is None else (defect % modulus == 0):
            retained += contribution
    return retained, ordinary


def invoke(*arguments, optimized=False, cwd=None, script=SCRIPT, env=None, isolated=True):
    command = [sys.executable, '-B', '-S']
    if isolated:
        command.append('-I')
    if optimized:
        command.append('-O')
    command.extend([str(script), *arguments])
    return subprocess.run(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, check=False, timeout=60)


class CertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.certificate = check.load_certificate(CERTIFICATE)

    def changed_record(self, index, field, value):
        data = dict(self.certificate)
        data['certificates'] = list(data['certificates'])
        data['certificates'][index] = dict(data['certificates'][index])
        data['certificates'][index][field] = value
        return data

    def test_canonical_certificate_and_digest(self):
        raw = CERTIFICATE.read_bytes()
        self.assertEqual(raw, check.canonical_bytes(self.certificate))
        self.assertEqual(sha256(raw).hexdigest(), CERTIFICATE_SHA256)
        self.assertLessEqual(len(raw), 300000)
        report = check.verify_midpoint_certificate(self.certificate)
        self.assertEqual(report['choices'], 729)
        self.assertEqual(report['certified_relation'], [6, 0, 0])
        self.assertEqual(report['maximum_absolute_integer_coefficient'], 6)

    def test_all_729_explicit_combinations_independently(self):
        records = self.certificate['certificates']
        self.assertEqual(len(records), 3**6)
        choices = [tuple(record['choice']) for record in records]
        self.assertEqual(Counter(choices), Counter(product(range(3), repeat=6)))
        self.assertEqual(tuple(tuple(tuple(v) for v in g)
                               for g in self.certificate['relations']), EXPECTED_RELATIONS)
        for record in records:
            with self.subTest(choice=record['choice']):
                choice = record['choice']
                columns = record['relation_columns']
                coefficients = record['integer_combination']
                self.assertEqual(columns, [list(EXPECTED_RELATIONS[j][choice[j]])
                                           for j in range(6)])
                self.assertTrue(all(type(c) is int and abs(c) <= 6 for c in coefficients))
                self.assertEqual([sum(coefficients[j] * columns[j][i]
                                      for j in range(6)) for i in range(3)], [6, 0, 0])

    def test_geometry_rebuilt_from_nine_source_lines(self):
        grid = {(i, j): ((i + (1 if j == 2 else 0)) % 3,
                         1 if j == 1 else 0, 1 if j == 2 else 0)
                for i in range(3) for j in range(3)}
        groups = []
        for slope in range(3):
            for offset in range(3):
                triple = [grid[((offset + slope*j) % 3, j)] for j in range(3)]
                options = []
                for selected in range(3):
                    row = tuple(2*triple[selected][k]
                                - triple[(selected+1) % 3][k]
                                - triple[(selected+2) % 3][k] for k in range(3))
                    first = next(v for v in row if v)
                    options.append(row if first > 0 else tuple(-v for v in row))
                groups.append(tuple(sorted(options)))
        self.assertEqual(tuple(sorted(set(groups))), EXPECTED_RELATIONS)
        expected_coverage = [EXPECTED_RELATIONS.index(g) for g in groups]
        self.assertEqual(check.midpoint_relations(), (EXPECTED_RELATIONS, expected_coverage))
        self.assertEqual(expected_coverage, [1, 1, 4, 2, 2, 3, 5, 0, 0])

    def test_malformed_top_level_and_schema(self):
        invalid = [None, [], (), 'certificate', 1, True, {},
                   {**self.certificate, 'extra': 0}]
        invalid.extend({k: v for k, v in self.certificate.items() if k != missing}
                       for missing in self.certificate)
        for value in invalid:
            with self.subTest(value_type=type(value).__name__):
                with self.assertRaises(ValueError):
                    check.verify_midpoint_certificate(value)
        for version in (None, True, False, '1', 1.0, Fraction(1), 0, 2, [], {}):
            with self.subTest(version=version):
                with self.assertRaises(ValueError):
                    check.verify_midpoint_certificate({**self.certificate, 'schema_version': version})

    def test_malformed_relations_and_wrong_geometry(self):
        for relations in (None, (), {}, self.certificate['relations'][:-1],
                          self.certificate['relations'] + [self.certificate['relations'][0]]):
            with self.subTest(relations_type=type(relations).__name__):
                with self.assertRaises(ValueError):
                    check.verify_midpoint_certificate({**self.certificate, 'relations': relations})
        for group in (None, (), {}, [], [[1, 2, 3]], [0, 1, 2]):
            data = deepcopy(self.certificate)
            data['relations'][0] = group
            with self.subTest(group=group):
                with self.assertRaises(ValueError):
                    check.verify_midpoint_certificate(data)
        for vector in ([1, 2], [1, 2, 3, 4], [True, -2, 1], [1.0, -2, 1],
                       [7, -2, 1], [1 << 512, -2, 1], 'abc'):
            data = deepcopy(self.certificate)
            data['relations'][0][0] = vector
            with self.subTest(vector=vector):
                with self.assertRaises(ValueError):
                    check.verify_midpoint_certificate(data)
        for row in ([0, -2, 1], [-1, 2, -1]):
            data = deepcopy(self.certificate)
            data['relations'][0][0] = row
            with self.assertRaisesRegex(RuntimeError, 'geometry'):
                check.verify_midpoint_certificate(data)
        data = deepcopy(self.certificate)
        data['relations'][0], data['relations'][1] = data['relations'][1], data['relations'][0]
        with self.assertRaisesRegex(RuntimeError, 'geometry'):
            check.verify_midpoint_certificate(data)

    def test_missing_extra_duplicate_and_reordered_records(self):
        records = self.certificate['certificates']
        for bad in (None, tuple(records), {}, records[:-1], records + [records[0]]):
            with self.subTest(record_type=type(bad).__name__):
                with self.assertRaises(ValueError):
                    check.verify_midpoint_certificate({**self.certificate, 'certificates': bad})
        duplicates = records[:-1] + [records[0]]
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            check.verify_midpoint_certificate({**self.certificate, 'certificates': duplicates})
        self.assertEqual(check.verify_midpoint_certificate(
            {**self.certificate, 'certificates': list(reversed(records))})['choices'], 729)

    def test_malformed_record_fields(self):
        first = self.certificate['certificates'][0]
        malformed = [None, [], (), 0, {**first, 'extra': 0}]
        malformed.extend({k: v for k, v in first.items() if k != missing} for missing in first)
        for bad in malformed:
            data = dict(self.certificate)
            data['certificates'] = [bad] + self.certificate['certificates'][1:]
            with self.subTest(record_type=type(bad).__name__):
                with self.assertRaises(ValueError):
                    check.verify_midpoint_certificate(data)

    def test_malformed_choice_vectors(self):
        for value in (None, {}, '000000', [0]*5, [0]*7, [-1]+[0]*5,
                      [3]+[0]*5, [True]+[0]*5, [0.0]+[0]*5, [Fraction(0)]+[0]*5):
            with self.subTest(value=value):
                with self.assertRaises(ValueError):
                    check.verify_midpoint_certificate(self.changed_record(0, 'choice', value))

    def test_malformed_columns_and_wrong_selected_column(self):
        columns = self.certificate['certificates'][0]['relation_columns']
        for value in (None, {}, tuple(columns), columns[:-1], columns + [columns[0]],
                      [None] + columns[1:], [[True, -2, 1]] + columns[1:],
                      [[7, -2, 1]] + columns[1:]):
            with self.subTest(value_type=type(value).__name__):
                with self.assertRaises(ValueError):
                    check.verify_midpoint_certificate(self.changed_record(0, 'relation_columns', value))
        altered = [list(EXPECTED_RELATIONS[0][1])] + columns[1:]
        with self.assertRaisesRegex(RuntimeError, 'wrong relation columns'):
            check.verify_midpoint_certificate(self.changed_record(0, 'relation_columns', altered))

    def test_malformed_integer_coefficients(self):
        for value in (None, {}, '000000', [0]*5, [0]*7, [7]+[0]*5,
                      [-7]+[0]*5, [True]+[0]*5, [0.0]+[0]*5,
                      [Fraction(0)]+[0]*5, [1 << 512]+[0]*5):
            with self.subTest(value=value):
                with self.assertRaises(ValueError):
                    check.verify_midpoint_certificate(self.changed_record(0, 'integer_combination', value))
        with self.assertRaisesRegex(RuntimeError, 'integer linear combination'):
            check.verify_midpoint_certificate(self.changed_record(0, 'integer_combination', [0]*6))

    def test_coefficient_mutation_in_every_one_of_729_records(self):
        for index, record in enumerate(self.certificate['certificates']):
            coefficients = list(record['integer_combination'])
            coefficients[0] += -1 if coefficients[0] == 6 else 1
            with self.subTest(index=index, choice=record['choice']):
                with self.assertRaisesRegex(RuntimeError, 'integer linear combination'):
                    check.verify_midpoint_certificate(
                        self.changed_record(index, 'integer_combination', coefficients))

    def test_input_is_not_mutated(self):
        before = check.canonical_bytes(self.certificate)
        check.verify_midpoint_certificate(self.certificate)
        self.assertEqual(check.canonical_bytes(self.certificate), before)


class BoundedJSONTests(unittest.TestCase):
    def load_bytes(self, payload):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'input.json'
            path.write_bytes(payload)
            return check.load_certificate(path)

    def test_duplicate_keys_at_any_level(self):
        for raw in (b'{"x":1,"x":2}', b'{"x":{"a":0,"a":1}}',
                    b'[{"choice":0,"choice":1}]', b'{"x":0,"\\u0078":1}'):
            with self.subTest(raw=raw):
                with self.assertRaisesRegex(ValueError, 'duplicate'):
                    self.load_bytes(raw)

    def test_rejects_all_noninteger_json_numbers(self):
        for token in ('0.0', '-0.0', '1.25', '1e0', '1E+2', '1e999',
                      '1e-999', 'NaN', 'Infinity', '-Infinity'):
            for raw in (token.encode('ascii'), ('{"number":' + token + '}').encode('ascii')):
                with self.subTest(raw=raw):
                    with self.assertRaises(ValueError):
                        self.load_bytes(raw)

    def test_integer_bit_and_digit_bounds(self):
        edge = (1 << 512) - 1
        for value in (0, 1, -1, edge, -edge):
            with self.subTest(value=value):
                self.assertEqual(self.load_bytes(str(value).encode('ascii')), value)
        for value in (1 << 512, -(1 << 512)):
            with self.assertRaises(ValueError):
                self.load_bytes(str(value).encode('ascii'))
        for raw in (b'1' * 161, b'-' + b'1' * 161, b'9' * 5000):
            with self.assertRaises(ValueError):
                self.load_bytes(raw)

    def test_size_utf8_syntax_and_nesting_bounds(self):
        self.assertEqual(self.load_bytes(b'0' + b' ' * 299999), 0)
        with self.assertRaisesRegex(ValueError, '300000'):
            self.load_bytes(b'0' + b' ' * 300000)
        for raw in (b'', b'\xff', b'\xc0\xaf', b'{', b'{}{}', b'[1,]',
                    b'[' * 2000 + b'0' + b']' * 2000):
            with self.subTest(prefix=raw[:10]):
                with self.assertRaises(ValueError):
                    self.load_bytes(raw)

    def test_explicit_json_depth_limit(self):
        self.assertEqual(self.load_bytes(b'['*16 + b'0' + b']'*16),
                         json.loads(b'['*16 + b'0' + b']'*16))
        for raw in (b'['*17 + b'0' + b']'*17,
                    b'{"x":'*17 + b'0' + b'}'*17):
            with self.assertRaises(ValueError):
                self.load_bytes(raw)

    def test_nesting_characters_inside_strings_are_not_depth(self):
        text = ('[{' * 2000) + '\\"' + ('}]' * 2000)
        self.assertEqual(self.load_bytes(json.dumps({'text': text}).encode('ascii')), {'text': text})

    def test_invalid_path_types(self):
        for path in (None, 1, True, [], {}, b'file.json'):
            with self.subTest(path=path):
                with self.assertRaises(ValueError):
                    check.load_certificate(path)

    def test_exact_canonical_serialization(self):
        data = {'z': (Fraction(2, 3), True, None), 'a': 'é'}
        self.assertEqual(check.canonical_bytes(data), b'{"a":"\\u00e9","z":["2/3",true,null]}\n')
        self.assertEqual(check.canonical_bytes({'b': 2, 'a': 1}),
                         check.canonical_bytes({'a': 1, 'b': 2}))
        for value in (0.0, float('nan'), float('inf'), {1: 'x'}, {False: 1}, set(), object()):
            with self.subTest(value_type=type(value).__name__):
                with self.assertRaises(ValueError):
                    check.canonical_bytes(value)


class ExactInterfaceTests(unittest.TestCase):
    def test_require_remains_active(self):
        check.require(True, 'valid')
        with self.assertRaisesRegex(RuntimeError, 'sentinel'):
            check.require(False, 'sentinel')
        for condition, message in ((1, 'x'), (0, 'x'), (None, 'x'), (True, 1)):
            with self.assertRaises(ValueError):
                check.require(condition, message)

    def test_exact_integer_and_rational_boundaries(self):
        edge = (1 << 512) - 1
        for value in (0, 1, -1, edge, -edge):
            self.assertEqual(check.integer(value), value)
            self.assertEqual(check.rational(value), Fraction(value))
        self.assertEqual(check.rational(Fraction(1, edge)), Fraction(1, edge))
        for value in (True, False, 1.0, '1', None, [], Fraction(1), 1 << 512, -(1 << 512)):
            with self.subTest(integer=value):
                with self.assertRaises(ValueError):
                    check.integer(value)
        for value in (True, False, 1.0, complex(1), '1', None, [],
                      1 << 512, Fraction(1, 1 << 512)):
            with self.subTest(rational=value):
                with self.assertRaises(ValueError):
                    check.rational(value)
        class IntegerSubclass(int):
            pass
        class FractionSubclass(Fraction):
            pass
        for value in (IntegerSubclass(1), FractionSubclass(1)):
            with self.assertRaises(ValueError):
                check.rational(value)

    def test_vector_validation(self):
        self.assertEqual(check.vector([1, -2, 3], 3, 3), (1, -2, 3))
        self.assertEqual(check.vector((1, -2, 3), 3, 3), (1, -2, 3))
        for value in (None, {}, iter([1, 2, 3]), [1, 2], [True, 2, 3],
                      [1.0, 2, 3], [4, 0, 0], [-4, 0, 0]):
            with self.assertRaises(ValueError):
                check.vector(value, 3, 3)
        for length in (True, 3.0, 0, -1, 33, 1 << 512):
            with self.assertRaises(ValueError):
                check.vector([1, 2, 3], length, 3)
        for bound in (True, 3.0, -1, 1 << 512):
            with self.assertRaises(ValueError):
                check.vector([1, 2, 3], 3, bound)

    def test_polynomial_coefficient_arithmetic(self):
        x, y = check.P('x'), check.P('y')
        self.assertEqual((x + y)**3, check.Polynomial({('x',)*3: 1,
            ('x', 'x', 'y'): 3, ('x', 'y', 'y'): 3, ('y',)*3: 1}))
        self.assertEqual((x + y)*(x - y), x*x - y*y)
        self.assertEqual((x + 1)/2, Fraction(1, 2)*x + Fraction(1, 2))
        self.assertEqual(2 - x, -x + 2)
        self.assertEqual(x**0, 1)
        self.assertEqual(check.Polynomial(), 0)
        self.assertNotEqual(x, True)
        self.assertNotEqual(check.Polynomial.constant(1), 1.0)
        self.assertNotEqual(x, object())
        self.assertEqual((x*x*y + 3*y).derivative('x'), 2*x*y)
        self.assertEqual((x*x*y + 3*y).derivative('y'), x*x + 3)
        self.assertEqual(x.derivative('z'), 0)
        self.assertEqual((x*x + 3*y).evaluate({'x': Fraction(2, 3), 'y': -2}), Fraction(-50, 9))
        self.assertEqual(check.Polynomial.constant(7).evaluate({}), Fraction(7))

    def test_polynomial_mapping_is_copied_and_immutable(self):
        original = {('x',): 1, ('y',): 0}
        p = check.Polynomial(original)
        original[('x',)] = 99
        self.assertEqual(dict(p.terms), {('x',): Fraction(1)})
        with self.assertRaises(TypeError):
            p.terms[('x',)] = 9
        with self.assertRaises(AttributeError):
            p.terms = {}

    def test_polynomial_constructor_rejects_malformed_terms(self):
        for value in ([], (), {1: 1}, {'x': 1}, {('y', 'x'): 1},
                      {(1,): 1}, {('x',)*17: 1}, {('',): 1}, {('a-b',): 1},
                      {('x'*21,): 1}, {('x',): True}, {('x',): 1.0},
                      {('x',): Fraction(1, 1 << 512)}):
            with self.subTest(value_type=type(value).__name__):
                with self.assertRaises(ValueError):
                    check.Polynomial(value)
        for name in (None, 1, True, '', 'a b', 'a-b', 'v'*21):
            with self.assertRaises(ValueError):
                check.P(name)
        with self.assertRaisesRegex(ValueError, '32 variables'):
            check.Polynomial({('v'+str(i),): 1 for i in range(33)})
        variables = ['v%02d' % i for i in range(20)]
        with self.assertRaisesRegex(ValueError, '12000'):
            check.Polynomial(dict.fromkeys(islice(combinations(variables, 5), 12001), 1))

    def test_polynomial_operation_resource_bounds(self):
        x = check.P('x')
        self.assertEqual(x**16, check.Polynomial({('x',)*16: 1}))
        with self.assertRaisesRegex(ValueError, 'degree'):
            (x**16) * x
        monomials = list(islice(combinations(['v%02d' % i for i in range(16)], 4), 1500))
        p = check.Polynomial(dict.fromkeys(monomials, 1))
        with self.assertRaisesRegex(ValueError, 'pair budget'):
            p*p
        left = check.Polynomial(dict.fromkeys(combinations(['a%02d' % i for i in range(16)], 2), 1))
        right = check.Polynomial(dict.fromkeys(combinations(['b%02d' % i for i in range(16)], 2), 1))
        with self.assertRaisesRegex(ValueError, '12000'):
            left*right
        with self.assertRaisesRegex(ValueError, '512'):
            check.Polynomial.constant((1 << 512) - 1)*2
        with self.assertRaisesRegex(ValueError, '512'):
            check.Polynomial.constant((1 << 512) - 1)+1

    def test_polynomial_rejects_inexact_operands_and_bad_powers(self):
        x = check.P('x')
        for bad in (True, False, 0.5, '1', None, [], complex(1)):
            for operation in (lambda: x + bad, lambda: x - bad,
                              lambda: x * bad, lambda: x / bad):
                with self.subTest(operand_type=type(bad).__name__):
                    with self.assertRaises(ValueError):
                        operation()
        for exponent in (-1, 17, True, 1.0, Fraction(1), '1', 1 << 512):
            with self.assertRaises(ValueError):
                x**exponent
        with self.assertRaises(ValueError):
            x/0
        with self.assertRaises(ValueError):
            x/x

    def test_polynomial_evaluation_rejects_wrong_variables_and_values(self):
        x = check.P('x')
        for values in ({}, {'x': 1, 'y': 2}, {'y': 1}, [], None,
                       {'x': True}, {'x': 1.0}, {'x': 1 << 512}):
            with self.subTest(values=values):
                with self.assertRaises(ValueError):
                    x.evaluate(values)
        with self.assertRaises(ValueError):
            (x*x).evaluate({'x': 1 << 300})
        with self.assertRaises(ValueError):
            x.derivative('not a variable')

    def test_partitions_and_rank_bounds(self):
        self.assertEqual(list(check.partitions(0)), [()])
        self.assertEqual(list(check.partitions(4, 2)), [(2, 2), (2, 1, 1), (1, 1, 1, 1)])
        ps = list(check.partitions(9))
        self.assertEqual(len(ps), 30)
        self.assertEqual(len(set(ps)), 30)
        self.assertTrue(all(sum(p) == 9 and tuple(sorted(p, reverse=True)) == p for p in ps))
        for n in (-1, 13, True, 1.0, '9'):
            with self.assertRaises(ValueError):
                list(check.partitions(n))
        for maximum in (0, 13, True, 1.0, '9'):
            with self.assertRaises(ValueError):
                list(check.partitions(9, maximum))
        for rank in (0, 4, -1, True, 2.0, '2', None):
            with self.assertRaises(ValueError):
                check.points(rank)
        for rank in (1, 2, 3):
            self.assertEqual(check.points(rank), tuple(product(range(3), repeat=rank)))


class EnergyTests(unittest.TestCase):
    def test_exhaustive_rank_one_against_four_index_reference(self):
        weights = (Fraction(1, 2), Fraction(2, 3), Fraction(5, 4))
        for values in product((-1, 0, 1), repeat=3):
            for modulus in (None, 2, 3):
                with self.subTest(values=values, modulus=modulus):
                    expected = independent_energy(values, weights, 1, modulus)
                    for method in ('quadruples', 'pairs'):
                        self.assertEqual(check.energies(values, weights, 1, modulus, method), expected)

    def test_rank_two_and_three_against_four_index_reference(self):
        cases = [([0, 0, 0, 2, 2, 2, -2, 1, 4],
                  [Fraction(i % 4, 3) for i in range(9)], 2, None),
                 ([i*i-7 for i in range(9)], [0, 1, 2, 0, 3, 1, 0, 2, 1], 2, 9),
                 ([(i*i + 2*i) % 7 - 3 for i in range(27)],
                  [Fraction(i % 3, 2) for i in range(27)], 3, 2)]
        for values, weights, rank, modulus in cases:
            with self.subTest(rank=rank, modulus=modulus):
                expected = independent_energy(values, weights, rank, modulus)
                self.assertGreater(expected[1], 0)
                self.assertLessEqual(expected[0], expected[1])
                for method in ('quadruples', 'pairs'):
                    self.assertEqual(check.energies(values, weights, rank, modulus, method), expected)

    def test_exact_invariances_and_degenerate_support(self):
        values = [0, 1, -2, 3, 1, 0, 8, -1, 2]
        weights = [Fraction(i % 3, 2) for i in range(9)]
        base = check.energies(values, weights)
        self.assertEqual(check.energies([v+17 for v in values], weights), base)
        self.assertEqual(check.energies([-3*v for v in values], weights), base)
        self.assertEqual(check.energies(values, [w*Fraction(2, 3) for w in weights]),
                         tuple(v*Fraction(2, 3)**4 for v in base))
        self.assertEqual(check.energies(values, [1]+[0]*8), (1, 1))
        self.assertEqual(check.energies(values, weights, modulus=1), (base[1], base[1]))
        self.assertEqual(check.energies(values, weights, modulus=9),
                         check.energies([v + 9*i for i, v in enumerate(values)], weights, modulus=9))
        for rank in (1, 2, 3):
            n = 3**rank
            self.assertEqual(check.energies([5]*n, [1]*n, rank, method='pairs'), (n**3, n**3))

    def test_invalid_energy_dimensions_and_scalar_types(self):
        values, weights = [0]*9, [1]*9
        for rank in (0, 4, True, 2.0, '2'):
            with self.assertRaises(ValueError):
                check.energies(values, weights, rank)
        for bad_values in (None, {}, range(9), [0]*8, [0]*10):
            with self.assertRaises(ValueError):
                check.energies(bad_values, weights)
        for bad_weights in (None, {}, range(9), [1]*8, [1]*10, [0]*9, [-1]+[1]*8):
            with self.assertRaises(ValueError):
                check.energies(values, bad_weights)
        for bad in (True, 0.0, '0', None, Fraction(0), 1 << 512):
            with self.subTest(value=bad):
                with self.assertRaises(ValueError):
                    check.energies([bad]+values[1:], weights)
        for bad in (True, 1.0, '1', None, 1 << 512, Fraction(1, 1 << 512)):
            with self.subTest(weight=bad):
                with self.assertRaises(ValueError):
                    check.energies(values, [bad]+weights[1:])
        for modulus in (0, -1, True, 1.0, Fraction(1), '2', 1 << 512):
            with self.assertRaises(ValueError):
                check.energies(values, weights, modulus=modulus)
        for method in ('', 'Pairs', 'unknown', None, 1, True, []):
            with self.assertRaises(ValueError):
                check.energies(values, weights, method=method)

    def test_histogram_validation_and_derivative_energy_identity(self):
        values = [0, 0, 0, 2, 2, 2, -2, 1, 4]
        for modulus, qs, retained in ((None, [41, 33, 33, 33], 361), (9, [45, 33, 33, 33], 369)):
            result = check.histograms(values, modulus)
            self.assertEqual([row['Q'] for row in result], qs)
            self.assertTrue(all(sum(row['multiplicities']) == 9 for row in result))
            self.assertEqual(81 + 2*sum(qs), retained)
            self.assertEqual(check.energies(values, [1]*9, modulus=modulus), (retained, 729))
        for bad in ([0]*8, [True]+[0]*8, [0.0]+[0]*8):
            with self.assertRaises(ValueError):
                check.histograms(bad)
        with self.assertRaises(ValueError):
            check.histograms(values, 0)

    def test_all_small_line_midpoint_formulas(self):
        for values in product(range(-2, 3), repeat=3):
            midpoint_count = sum(2*values[i] == values[(i+1) % 3] + values[(i+2) % 3]
                                 for i in range(3))
            self.assertEqual(check.energies(values, [1]*3, 1), (15 + 4*midpoint_count, 27))


class TheoremReceiptTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.receipt = check.run_checks()

    def test_complete_receipt_and_certificate_binding(self):
        r = self.receipt
        self.assertEqual((r['report'], r['schema_version'], r['status']), (294, 1, 'passed'))
        self.assertEqual(r['midpoint_certificate']['sha256'], CERTIFICATE_SHA256)
        self.assertEqual(set(r), {'report', 'schema_version', 'status', 'arithmetic', 'scope',
            'midpoint_certificate', 'cycle_case_coverage', 'normal_forms_and_line_test',
            'three_fiber_proof_algebra', 'reflection_proof_algebra', 'spike_energy_polynomials',
            'fourier_and_attainment'})
        def reject_inexact(value):
            self.assertNotIsInstance(value, (float, complex))
            if isinstance(value, dict):
                for child in value.values():
                    reject_inexact(child)
            elif isinstance(value, (tuple, list)):
                for child in value:
                    reject_inexact(child)
        reject_inexact(r)
        self.assertEqual(check.canonical_bytes(r), check.canonical_bytes(check.run_checks()))

    def test_exhaustive_cycle_case_counts(self):
        r = self.receipt['cycle_case_coverage']
        self.assertEqual(r['partitions_of_nine'], 30)
        self.assertEqual(r['partitions_above_35'],
                         [(9,), (8, 1), (7, 2), (7, 1, 1), (6, 3), (6, 2, 1), (6, 1, 1, 1), (5, 4)])
        expected = {(8, 1): (9, 9, 0, 0, 0), (7, 2): (36, 27, 9, 0, 0),
                    (7, 1, 1): (72, 54, 0, 18, 0), (6, 3): (84, 54, 0, 0, 30),
                    (5, 4): (126, 99, 27, 0, 0), (6, 2, 1): (252, 81, 54, 108, 9),
                    (6, 1, 1, 1): (504, 162, 0, 342, 0)}
        self.assertEqual(len(r['cycle_cases']), len(expected))
        for case in r['cycle_cases']:
            partition = case['partition']
            denominator = 1
            for count in partition:
                denominator *= factorial(count)
            self.assertEqual(case['assignments'], factorial(9)//denominator)
            actual = tuple(case.get(key, 0) for key in ('assignments', 'equal_values',
                           'doubling_injective_collapse', 'non_AP_cycle', 'structural_branch'))
            self.assertEqual(actual, expected[partition])
            self.assertEqual(actual[0], sum(actual[1:]))
        self.assertEqual(r['Q45_counts'], [(0, 0, 3), (0, 1, 2), (1, 1, 1)])
        self.assertEqual(r['Q41_5_4_counts'], [(0, 1, 3), (0, 2, 2), (1, 1, 2)])

    def test_all_27_affine_edge_normalizations(self):
        rows = self.receipt['cycle_case_coverage']['edge_configurations']
        self.assertEqual({row['edges'] for row in rows}, set(product(range(3), repeat=3)))
        self.assertEqual(sum(row['aligned'] for row in rows), 9)
        for row in rows:
            orientation, slope, offset = row['source_change']
            self.assertIn(orientation, (-1, 1))
            edges = row['edges']
            aligned = (edges[0] - 2*edges[1] + edges[2]) % 3 == 0
            self.assertEqual(row['aligned'], aligned)
            transformed = tuple((edges[j] - slope*j - offset) % 3 if orientation == 1
                                else (slope*j + offset - edges[j] - 1) % 3 for j in range(3))
            self.assertEqual(transformed, (2, 2, 2) if aligned else (2, 2, 1))

    def test_all_nine_aligned_midpoint_integer_combinations(self):
        rows = self.receipt['cycle_case_coverage']['aligned_midpoint_choices']
        triples = (((0, 1), (1, 2), (2, 0)), ((0, 0), (1, 2), (2, 1)))
        columns = [[tuple(3*t[k][i] - sum(p[i] for p in t) for i in range(2))
                    for k in range(3)] for t in triples]
        self.assertEqual({row['choice'] for row in rows}, set(product(range(3), repeat=2)))
        for row in rows:
            self.assertIn(row['relation'], ((3, 0), (6, 0), (0, 3)))
            actual = tuple(sum(row['coefficients'][j]*columns[j][row['choice'][j]][i]
                               for j in range(2)) for i in range(2))
            self.assertEqual(actual, row['relation'])

    def test_generic_normal_form_collision_factors_independently(self):
        r = self.receipt['normal_forms_and_line_test']
        self.assertEqual(r['generic_histogram_collision_factors'], [3, 6, 9])
        pts = list(product(range(3), repeat=2))
        values = dict(zip(pts, (0, 0, 0, 2, 2, 2, -2, 1, 4)))
        differences = set()
        for a, b in ((0, 1), (1, 0), (1, 1), (1, 2)):
            derivatives = {values[((x+a) % 3, (y+b) % 3)] - values[x, y] for x, y in pts}
            differences.update(abs(c-d) for c, d in combinations(derivatives, 2))
        self.assertEqual(differences, {3, 6, 9})
        self.assertEqual(r['line_always_retained'], 15)
        self.assertEqual(r['line_each_midpoint_adds'], 4)

    def test_three_fiber_sos_identity_and_attainment(self):
        r = self.receipt['three_fiber_proof_algebra']
        self.assertEqual(r['coefficient_identities'], 5)
        self.assertEqual(r['identical_fibers_coefficients'], [15, 27])
        x, y, z = map(check.P, ('x', 'y', 'z'))
        n = x**4 + y**4 + z**4 + 4*(x*x*y*y + x*x*z*z + y*y*z*z)
        squares = sum((a*a-b*b)**2 for a, b in ((x, y), (y, z), (z, x)))/2
        squares += Fraction(5, 2)*sum((a*b-b*c)**2 for a, b, c in ((x, y, z), (y, z, x), (z, x, y)))
        self.assertEqual(n - 5*x*y*z*(x+y+z), squares)
        self.assertEqual(check.energies([0, 0, 1], [1, 1, 1], 1), (15, 27))

    def test_reflection_exact_radicals_and_sharp_multiplicities(self):
        r = self.receipt['reflection_proof_algebra']
        self.assertEqual(r['coefficient_identities'], 14)
        self.assertEqual(len(set(r['identities'])), 14)
        self.assertEqual(r['u_squared_sqrt6_coordinates'], (-8, 6))
        self.assertEqual(r['N_u_sqrt6_coordinates'], (352, 192))
        self.assertEqual(r['k_squared_below_half_residual'], (1121, -456))
        self.assertEqual([row['skewness_squared'] for row in r['nine_atom_skewness']],
                         [Fraction(49, 8), Fraction(25, 14), Fraction(1, 2), Fraction(1, 20),
                          Fraction(1, 20), Fraction(1, 2), Fraction(25, 14), Fraction(49, 8)])
        for row in r['nine_atom_skewness']:
            k = row['positive_multiplicity']
            self.assertEqual(row['skewness_squared'], Fraction((9-2*k)**2, k*(9-k)))
        self.assertGreater(1121 - 456*Fraction(49, 20), 0)
        self.assertGreater(Fraction(49, 20)**2, 6)
        self.assertIn('fourth-power', r['rho_scope'])

    def test_spike_polynomials_against_both_energy_methods(self):
        r = self.receipt['spike_energy_polynomials']
        self.assertEqual(r['retained_coefficients'], [456, 0, 48, 0, 1])
        self.assertEqual(r['ordinary_coefficients'], [456, 224, 48, 0, 1])
        self.assertEqual(r['signed_coefficients'], [456, -224, 48, 0, 1])
        self.assertEqual(r['independent_pair_checks'], 3)
        for t in (0, 1, 2, 3, Fraction(1, 2)):
            for method in ('quadruples', 'pairs'):
                retained, ordinary = check.energies([1]+[0]*8, [t]+[1]*8,
                                                     modulus=2, method=method)
                for value, key in ((retained, 'retained_coefficients'),
                                   (ordinary, 'ordinary_coefficients'),
                                   (2*retained-ordinary, 'signed_coefficients')):
                    self.assertEqual(value, sum(c*t**i for i, c in enumerate(r[key])))

    def test_fourier_orthogonality_and_nonuniform_products(self):
        r = self.receipt['fourier_and_attainment']
        self.assertEqual(r['proof_algebra']['quotient_character_orthogonality_values'],
                         [[9, 0]] + [[0, 0]]*8)
        supplement = r['supplemental_rank_three']
        self.assertEqual(supplement['coefficientwise_fourier_identities'], 729)
        self.assertEqual(supplement['block_sizes'], [9, 9, 9])
        self.assertEqual(supplement['kernel_energy'], 33)
        self.assertEqual(independent_energy([0]*3, [1, 2, 0], 1), (33, 33))
        for key, expected in (('product_retained_coefficients', [456, 0, 48, 0, 1]),
                              ('product_ordinary_coefficients', [456, 224, 48, 0, 1]),
                              ('product_signed_coefficients', [456, -224, 48, 0, 1])):
            self.assertEqual(supplement[key], [33*c for c in expected])
        attainment = r['supplemental_three_fiber_product']
        self.assertEqual((attainment['retained'], attainment['ordinary']), (495, 891))
        self.assertEqual(Fraction(attainment['retained'], attainment['ordinary']), Fraction(5, 9))


class RuntimeContractTests(unittest.TestCase):
    def test_normal_optimized_and_hashseed_receipts_are_byte_identical(self):
        with tempfile.TemporaryDirectory() as directory:
            normal = invoke(cwd=directory)
            optimized = invoke(optimized=True, cwd=directory)
            other_seed = invoke(cwd=directory, isolated=False,
                                env={**os.environ, 'PYTHONHASHSEED': '987654'})
        for result in (normal, optimized, other_seed):
            self.assertEqual(result.returncode, 0, result.stderr.decode())
            self.assertEqual(result.stderr, b'')
        self.assertEqual(normal.stdout, optimized.stdout)
        self.assertEqual(normal.stdout, other_seed.stdout)
        self.assertEqual(normal.stdout, check.canonical_bytes(check.run_checks()))
        self.assertEqual(json.loads(normal.stdout)['status'], 'passed')
        self.assertEqual(normal.stdout.count(b'\n'), 1)

    def test_unknown_arguments_fail_closed_and_help_is_available(self):
        for arguments in (('--unknown',), ('--he',), ('--output', 'receipt.json'),
                          ('--certificate', 'other.json'), ('extra',)):
            with self.subTest(arguments=arguments):
                result = invoke(*arguments)
                self.assertEqual(result.returncode, 2)
                self.assertEqual(result.stdout, b'')
                self.assertIn(b'unrecognized arguments', result.stderr)
        result = invoke('--help')
        self.assertEqual(result.returncode, 0)
        self.assertIn(b'usage:', result.stdout)

    def test_production_ast_has_no_asserts_floats_cas_or_network_imports(self):
        allowed_imports = {'__future__', 'sys', 'argparse', 'collections', 'fractions',
                           'hashlib', 'itertools', 'json', 'pathlib', 'types'}
        forbidden_calls = {'assert', 'eval', 'exec', '__import__', 'float', 'complex',
                           'compile', 'breakpoint', 'input'}
        for path in sorted((ROOT / 'companion').glob('*.py')):
            tree = ast.parse(path.read_text(encoding='utf-8'), filename=path.name)
            for node in ast.walk(tree):
                with self.subTest(file=path.name, line=getattr(node, 'lineno', None)):
                    self.assertNotIsInstance(node, ast.Assert)
                    if isinstance(node, ast.Constant):
                        self.assertNotIsInstance(node.value, (float, complex))
                    if isinstance(node, ast.Import):
                        self.assertTrue(all(alias.name.split('.')[0] in allowed_imports for alias in node.names))
                    if isinstance(node, ast.ImportFrom):
                        self.assertIn(node.module.split('.')[0], allowed_imports)
                    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                        self.assertNotIn(node.func.id, forbidden_calls)

    def test_runtime_audit_rejects_writes_network_and_process_creation(self):
        code = r'''
import os, runpy, sys
sys.dont_write_bytecode = True
script = sys.argv[1]
sys.argv = [script]
def guard(event, args):
    if event == 'open':
        mode, flags = args[1], args[2]
        if isinstance(mode, str) and any(c in mode for c in 'wax+'):
            raise RuntimeError('unexpected file write')
        if isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND):
            raise RuntimeError('unexpected writable open')
    if event.startswith(('socket.', 'subprocess.', 'urllib.')):
        raise RuntimeError('unexpected external operation')
    if event in {'os.mkdir', 'os.remove', 'os.rename', 'os.rmdir', 'os.chmod', 'os.chown', 'os.link', 'os.symlink', 'os.truncate', 'os.system', 'os.exec', 'os.posix_spawn'}:
        raise RuntimeError('unexpected mutation or process creation')
sys.addaudithook(guard)
runpy.run_path(script, run_name='__main__')
'''
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run([sys.executable, '-B', '-I', '-S', '-c', code, str(SCRIPT)],
                cwd=directory, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertEqual(result.stdout, check.canonical_bytes(check.run_checks()))

    def test_read_only_copy_from_unrelated_read_only_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            package = root / 'bundle' / 'companion'
            package.mkdir(parents=True)
            for filename in ('__init__.py', 'exact_checks.py', 'midpoint_certificate.json'):
                shutil.copyfile(ROOT / 'companion' / filename, package / filename)
            elsewhere = root / 'elsewhere'
            elsewhere.mkdir()
            files = sorted(package.iterdir())
            before = {p.name: p.read_bytes() for p in files}
            try:
                for path in files:
                    path.chmod(0o444)
                for path in (package, package.parent, elsewhere):
                    path.chmod(0o555)
                for optimized in (False, True):
                    result = invoke(optimized=optimized, cwd=elsewhere, script=package / 'exact_checks.py')
                    self.assertEqual(result.returncode, 0, result.stderr.decode())
                    self.assertEqual(result.stdout, check.canonical_bytes(check.run_checks()))
                self.assertEqual({p.name: p.read_bytes() for p in package.iterdir()}, before)
                self.assertEqual(list(elsewhere.iterdir()), [])
                self.assertEqual(list(package.parent.iterdir()), [package])
            finally:
                for path in (package.parent, package, elsewhere):
                    path.chmod(0o755)
                for path in files:
                    path.chmod(0o644)

    def test_cli_rejects_noncanonical_and_mutated_certificate_copies(self):
        with tempfile.TemporaryDirectory() as directory:
            package = Path(directory) / 'companion'
            package.mkdir()
            shutil.copyfile(SCRIPT, package / 'exact_checks.py')
            certificate = check.load_certificate(CERTIFICATE)
            target = package / 'midpoint_certificate.json'
            for raw in (json.dumps(certificate, indent=1).encode('ascii'),
                        check.canonical_bytes({**certificate, 'schema_version': True})):
                target.write_bytes(raw)
                for optimized in (False, True):
                    result = invoke(optimized=optimized, cwd=directory, script=package / 'exact_checks.py')
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, b'')
            target.write_bytes(check.canonical_bytes(certificate))
            self.assertEqual(invoke(script=package / 'exact_checks.py', cwd=directory).returncode, 0)


if __name__ == '__main__':
    unittest.main()
