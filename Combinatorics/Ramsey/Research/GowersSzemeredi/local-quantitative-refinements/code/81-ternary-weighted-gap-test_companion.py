#!/usr/bin/env python3
"""Exact and adversarial tests; run directly under normal or optimized Python."""
import sys
sys.dont_write_bytecode = True
import ast
import copy
from fractions import Fraction
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / 'companion' / 'exact_checks.py'
spec = importlib.util.spec_from_file_location('report293_exact', CHECKER)
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)


class ExactCompanionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.upper, cls.certificate = checks.check_upper_bound()
        cls.certificate = checks.jsonable(cls.certificate)

    def reject_certificate(self, mutate):
        certificate = copy.deepcopy(self.certificate)
        mutate(certificate)
        with self.assertRaises((ValueError, RuntimeError)):
            checks.verify_lattice_certificate(certificate)

    def test_all_lattice_choices_and_counts(self):
        self.assertEqual(self.upper['midpoint_choices_checked'], 729)
        self.assertEqual(self.upper['distinct_lattices'], 8)
        self.assertEqual(self.upper['excluded_choices'], 693)
        self.assertEqual(self.upper['surviving_choices'], 36)
        counts = {tuple(map(tuple, row['claimed_column_basis'])): row['count']
                  for row in self.upper['relation_lattice_classes']}
        self.assertEqual(counts, {tuple(map(tuple, b)): n for b, n in checks.LATTICE_BASES})

    def test_all_unimodular_certificates(self):
        replay = checks.verify_lattice_certificate(self.certificate)
        self.assertEqual(replay['unimodular_identities'], 737)
        self.assertEqual(replay['records'], 729)

    def test_certificate_wrong_transform(self):
        self.reject_certificate(lambda c: c['records'][0]['U'][0].__setitem__(0, 99))

    def test_certificate_nonunimodular_transform(self):
        def mutate(c):
            c['records'][0]['U'][0] = [0]*6
        self.reject_certificate(mutate)

    def test_certificate_wrong_reduced_matrix(self):
        self.reject_certificate(lambda c: c['records'][0]['R'][0].__setitem__(0, 999))

    def test_certificate_wrong_input_generator(self):
        self.reject_certificate(lambda c: c['records'][0]['generators'][0].__setitem__(0, 999))

    def test_certificate_duplicate_choice(self):
        self.reject_certificate(lambda c: c['records'].__setitem__(1, copy.deepcopy(c['records'][0])))

    def test_certificate_missing_choice(self):
        self.reject_certificate(lambda c: c['records'].pop())

    def test_certificate_extra_choice(self):
        self.reject_certificate(lambda c: c['records'].append(copy.deepcopy(c['records'][0])))

    def test_certificate_bad_choice(self):
        for bad in (-1, 3, True, 0.0, '0'):
            with self.subTest(value=bad):
                self.reject_certificate(lambda c: c['records'][0]['choice'].__setitem__(0, bad))

    def test_certificate_bad_basis_index(self):
        for bad in (-1, 8, True, 0.0, '0'):
            with self.subTest(value=bad):
                self.reject_certificate(lambda c: c['records'][0].__setitem__('basis_index', bad))

    def test_certificate_wrong_basis(self):
        self.reject_certificate(lambda c: c['bases'][0]['claimed_column_basis'][0].__setitem__(0, 9))

    def test_certificate_unknown_and_missing_fields(self):
        self.reject_certificate(lambda c: c.__setitem__('unknown', 1))
        self.reject_certificate(lambda c: c['records'][0].pop('U'))
        self.reject_certificate(lambda c: c.__setitem__('schema_version', True))
        self.reject_certificate(lambda c: c.__setitem__('schema_version', 2))

    def test_certificate_noninteger_matrix(self):
        for value in (True, 1.0, '1', None, 1 << 4096):
            with self.subTest(value=type(value).__name__):
                self.reject_certificate(lambda c: c['records'][0]['U'][0].__setitem__(0, value))

    def test_certificate_wrong_dimensions(self):
        self.reject_certificate(lambda c: c['records'][0]['U'].pop())
        self.reject_certificate(lambda c: c['records'][0]['U'][0].pop())
        self.reject_certificate(lambda c: c['records'][0].__setitem__('U', []))

    def test_strict_json_parser(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'bad.json'
            for content in ('{"x":1,"x":2}', '{"x":NaN}', '{"x":Infinity}', '{'):
                path.write_text(content)
                with self.assertRaises(ValueError):
                    checks.load_certificate(path)
            path.write_bytes(b' '*2_000_001)
            with self.assertRaises(ValueError):
                checks.load_certificate(path)
        with self.assertRaises(ValueError):
            checks.load_certificate(None)

    def test_bundled_certificate_is_canonical(self):
        path = ROOT/'companion'/'lattice_certificate.json'
        self.assertEqual(path.read_bytes(), checks.canonical_bytes(self.certificate))
        self.assertEqual(checks.load_certificate(path), self.certificate)

    def test_matrix_exact_arithmetic(self):
        self.assertEqual(checks.determinant([[2,3],[5,7]]), -1)
        self.assertEqual(checks.determinant([[1,2],[2,4]]), 0)
        self.assertEqual(checks.multiply([[1,2]], [[3],[4]]), [[11]])
        for bad in ([], [[]], [[1],[1,2]], [[True]], [[1.0]], [[1]*17]):
            with self.assertRaises(ValueError):
                checks.matrix(bad)
        with self.assertRaises(ValueError):
            checks.determinant([[1,2]])
        with self.assertRaises(ValueError):
            checks.multiply([[1,2]], [[1,2]])

    def test_integer_lattice_not_rational_span(self):
        basis, u, reduced = checks.row_lattice([[2,0],[0,3],[4,3]])
        self.assertTrue(checks.member(basis, (4,6)))
        self.assertFalse(checks.member(basis, (1,0)))
        self.assertFalse(checks.member(basis, (0,1)))
        self.assertEqual(abs(checks.determinant(u)), 1)
        self.assertEqual(checks.multiply(u, [[2,0],[0,3],[4,3]]), reduced)

    def test_lattice_rank_deficiency_and_zero_rows(self):
        basis, u, reduced = checks.row_lattice([[2,4],[4,8],[0,0]])
        self.assertEqual(basis, ((2,4),))
        self.assertTrue(checks.member(basis, (6,12)))
        self.assertFalse(checks.member(basis, (6,11)))
        self.assertEqual(checks.row_lattice([[0,0],[0,0]])[0], ())

    def test_bad_membership_basis_rejected_before_early_exit(self):
        for bad in ([[2,0],[0,0]], [[2,0],[1,1]], [[-2,0]], [[0,1],[1,0]]):
            with self.assertRaises(ValueError):
                checks.member(bad, (1,0))
        with self.assertRaises(ValueError):
            checks.member([[1,0]], (0,))

    def test_all_branch_witnesses(self):
        expected = {'order_nine': (369,729), 'aligned_cap': (425,729),
                    'two_point': (1330,2322), 'cross_II': (1354,2322), 'cross_III': (1354,2322)}
        for name, energy in expected.items():
            row = self.upper['witnesses'][name]
            self.assertEqual((row['E_a'],row['E']), energy)
            self.assertEqual(checks.energies(row['values'],row['weights'],row['modulus'],'pairs'), energy)

    def test_generic_branch_and_runner_up(self):
        result = checks.check_generic_branch()
        self.assertEqual([x['retained'] for x in result['row_sum_residue_slices']], [87,87,187])
        self.assertEqual(result['E_a'], 361)
        self.assertEqual(result['runner_up_minus_cap'], '4/31347')

    def test_spike_polynomial_and_stationary_equation(self):
        self.assertEqual(self.upper['spike_N_coefficients'], [456,0,48,0,1])
        self.assertEqual(self.upper['spike_E_coefficients'], [456,224,48,0,1])
        self.assertEqual(self.upper['stationary_coefficients'], [456,0,-48,0,-3])
        self.assertEqual(self.upper['lambda_comparison_square_difference'], (27633,-11106))

    def test_stability_radical_identities(self):
        result = self.upper['stability_radicals']
        self.assertEqual(result['kappa_squared'], (1,Fraction(81,196)))
        self.assertEqual(result['c'], (Fraction(5,9),Fraction(-9,49)))
        self.assertGreater(result['c_strict_lower_bound'],0)
        self.assertLess(result['c_strict_upper_bound'],Fraction(1,2))

    def test_boundary_weights_and_fractional_weights(self):
        spike = [1]+[0]*8
        for weights in ([1]+[0]*8, [0]+[1]*8, [0,1]+[0]*7):
            retained, total = checks.energies(spike,weights,2)
            self.assertGreater(total, 0)
            self.assertEqual(retained,total)
        weights = [Fraction(i+1,7) for i in range(9)]
        for values, modulus in ((spike,2), (list(range(9)),None), (list(range(9)),9)):
            self.assertEqual(checks.energies(values,weights,modulus),
                             checks.energies(values,weights,modulus,'pairs'))

    def test_affine_addition_preserves_energy(self):
        spike = [1]+[0]*8
        embedded = [(3*spike[i]+2*x+4*y) % 6 for i,(x,y) in enumerate(checks.POINTS)]
        weights = list(range(1,10))
        self.assertEqual(checks.energies(spike,weights,2),checks.energies(embedded,weights,6))

    def test_energy_inputs_are_strict_and_exact(self):
        values, weights = [0]*9, [1]*9
        bad_weights = ([0]*9, [1]*8, [1]*8+[True], [1]*8+[1.0], [1]*8+[-1],
                       [1]*8+[float('nan')], [1]*8+[1<<256])
        for bad in bad_weights:
            with self.assertRaises(ValueError):
                checks.energies(values,bad,2)
        for bad in ([0]*8, [0]*8+[False], [0]*8+[0.0]):
            with self.assertRaises(ValueError):
                checks.energies(bad,weights,2)
        for bad in (0,-1,True,2.0):
            with self.assertRaises(ValueError):
                checks.energies(values,weights,bad)
        for bad in ('unknown',True,None):
            with self.assertRaises(ValueError):
                checks.energies(values,weights,2,bad)

    def test_derivative_exclusions_and_edge_coverage(self):
        self.assertEqual(len(self.upper['exceptional_edge_configurations']),27)
        self.assertEqual(sum(x['aligned'] for x in self.upper['exceptional_edge_configurations']),9)
        self.assertEqual(len(self.upper['high_Q_midpoint_branches']),9)
        self.assertEqual(sum(x['forces_delta_zero'] for x in self.upper['high_Q_midpoint_branches']),2)
        self.assertEqual(len(list(checks.partitions(9))),30)
        for bad in (-1,17,True,2.0):
            with self.assertRaises(ValueError):
                list(checks.partitions(bad))

    def test_all_binary_orbits_sanity_only(self):
        self.assertEqual(self.upper['binary_affine_complement_orbit_sizes'],
                         {'constant':2,'cut':24,'spike':18,'two_point':72,
                          'noncollinear_three':144,'line_plus_point':144,'cap':108})

    def test_polynomial_coefficient_identity_and_nonidentity(self):
        x, y = checks.Polynomial.variable('x'), checks.Polynomial.variable('y')
        self.assertEqual((x+y)**2,x*x+2*x*y+y*y)
        self.assertNotEqual((x+y)**2,x*x+x*y+y*y)
        self.assertEqual(((x+y)**2).evaluate({'x':Fraction(1,3),'y':Fraction(2,3)}),1)
        self.assertEqual(x-x,0)
        self.assertEqual((x/3)*3,x)
        self.assertEqual(x**0,1)

    def test_polynomial_invalid_inputs(self):
        for bad in ({('x',):1.0}, {('x',):True}, {('y','x'):1}, {('bad name',):1}, {('x',)*17:1}):
            with self.assertRaises(ValueError):
                checks.Polynomial(bad)
        x = checks.Polynomial.variable('x')
        for bad in (-1,17,True,1.0):
            with self.assertRaises(ValueError):
                x**bad
        for bad in (0,True,1.0):
            with self.assertRaises(ValueError):
                x/bad
        for bad in ({}, {'x':1.0}, {'x':1,'extra':1}):
            with self.assertRaises(ValueError):
                x.evaluate(bad)

    def test_unrestricted_spike_identities(self):
        report = checks.check_spike_lower_bound()
        self.assertEqual(report['free_centered_parameters'],7)
        self.assertEqual(report['number_of_coefficient_identities'],19)
        self.assertEqual(report['retained_unweighted_quadruples'],505)
        self.assertEqual(report['supplementary_signed_grid']['count'],2187)
        self.assertEqual(report['supplementary_signed_grid']['minimum_nonzero_slack'],24)

    def test_guards_are_not_python_asserts(self):
        tree = ast.parse(CHECKER.read_text())
        self.assertFalse(any(isinstance(node,ast.Assert) for node in ast.walk(tree)))
        with self.assertRaises(RuntimeError):
            checks.require(False,'adversarial failure')
        for bad in (0,1,[],None):
            with self.assertRaises(ValueError):
                checks.require(bad,'not a bool')

    def test_exact_json_rejects_unsupported_types(self):
        self.assertEqual(checks.jsonable(Fraction(2,3)),'2/3')
        for bad in (1.0, {1:'x'}, {1,2}):
            with self.assertRaises(ValueError):
                checks.jsonable(bad)

    def test_cli_deterministic_read_only_normal_and_optimized(self):
        before = {str(p.relative_to(ROOT)):p.read_bytes() for p in ROOT.rglob('*') if p.is_file()}
        outputs = []
        with tempfile.TemporaryDirectory() as directory:
            for optimized in (False,True):
                command = [sys.executable,'-I','-B','-X','int_max_str_digits=640']
                if optimized:
                    command.append('-O')
                command.append(str(CHECKER))
                process = subprocess.run(command,cwd=directory,capture_output=True,timeout=60,
                                         env={**os.environ,'PYTHONHASHSEED':'987' if optimized else '123'})
                self.assertEqual(process.returncode,0,process.stderr.decode())
                self.assertEqual(process.stderr,b'')
                outputs.append(process.stdout)
            self.assertEqual(list(Path(directory).iterdir()),[])
        self.assertEqual(outputs[0],outputs[1])
        result = json.loads(outputs[0])
        self.assertEqual(result['status'],'passed')
        self.assertEqual(result['certificate']['unimodular_identities'],737)
        after = {str(p.relative_to(ROOT)):p.read_bytes() for p in ROOT.rglob('*') if p.is_file()}
        self.assertEqual(before,after)

    def test_cli_rejects_unknown_arguments(self):
        process = subprocess.run([sys.executable,'-I','-B',str(CHECKER),'--output','forbidden.json'],
                                 capture_output=True,timeout=10)
        self.assertEqual(process.returncode,2)
        self.assertEqual(process.stdout,b'')
        self.assertIn(b'unrecognized arguments',process.stderr)


if __name__ == '__main__':
    unittest.main()
