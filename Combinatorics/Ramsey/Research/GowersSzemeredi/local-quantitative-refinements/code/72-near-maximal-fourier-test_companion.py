"""Exact arithmetic, hypotheses, provenance and optimized-mode regression tests."""
import sys
sys.dont_write_bytecode = True
import ast
from fractions import Fraction as Q
import importlib.util
import json
from itertools import product
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).absolute().parents[1]
spec = importlib.util.spec_from_file_location('report284_exact', ROOT/'companion/exact_checks.py')
c = importlib.util.module_from_spec(spec); spec.loader.exec_module(c)


class ParameterTests(unittest.TestCase):
    def test_low_dimensional_constants(self):
        self.assertEqual([c.parameters(d)[2] for d in range(1,5)],
                         [Q(1,180),Q(1,2040),Q(1,23760),Q(1,280800)])
        self.assertEqual([c.classical_parameters(k) for k in (2,3,4)],
                         [(5,Q(3,50),11),(54,Q(1,180),109),(3672,Q(1,12240),7345)])
        rows = c.check_constants()
        self.assertEqual(len(rows),30)
        self.assertEqual(rows[1]['epsilon_sym'],'1/4760')
        self.assertEqual(rows[3]['density_lower_expression'],'605/864')

    def test_parameters_reject_unbounded_or_inexact_inputs(self):
        for d in (False,True,0,31,-1,'2',Q(2),None):
            with self.subTest(d=d), self.assertRaises(ValueError): c.parameters(d)
        for k in (False,True,1,21,-1,'2',Q(2),None):
            with self.subTest(k=k), self.assertRaises(ValueError): c.classical_parameters(k)

    def test_recursive_budget_endpoints(self):
        rows = c.check_descent()
        self.assertEqual(len(rows),19)
        self.assertEqual(rows[0]['stages'],[])
        for row in rows[1:]:
            self.assertEqual(row['stages'][-1],dict(d=1,tau='1/20'))

    def test_cli_has_no_parameter_overrides(self):
        for argv in (['--help'],['--N','1000000000'],['30']):
            with self.assertRaises(SystemExit): c.main(argv)

    def test_live_guards_and_no_floating_arithmetic(self):
        tree = ast.parse((ROOT/'companion/exact_checks.py').read_text())
        self.assertFalse(any(isinstance(n,ast.Assert) for n in ast.walk(tree)))
        self.assertFalse(any(isinstance(n,ast.Constant) and type(n.value) in (float,complex) for n in ast.walk(tree)))
        self.assertFalse(any(isinstance(n,ast.Name) and n.id in ('cmath','random','float','complex') for n in ast.walk(tree)))
        with self.assertRaises(RuntimeError): c.require(False,'guard remains active')


class ExtensionTests(unittest.TestCase):
    def test_complete_and_zero_free_dense_domains(self):
        self.assertEqual(c.partial_extensions(1,2,{0:0}),(0,))
        self.assertEqual(c.partial_extensions(5,3,{1:0,2:0,3:0,4:0}),(0,))
        self.assertEqual(c.partial_extensions(6,3,{x:x%3 for x in range(6)}),(1,))
        self.assertIsNone(c.partial_extensions(2,2,{0:1,1:0}))

    def test_density_boundary_and_malformed_maps(self):
        for args in ((4,2,{1:0,2:0,3:0}),(7,2,{}),(2,4,{0:0,1:0}),
                     (2,2,{False:0,1:0}),(2,2,{0:0,1:3}),(2,2,[])):
            with self.subTest(args=args), self.assertRaises(ValueError): c.partial_extensions(*args)

    def test_exhaustive_small_dense_counts(self):
        self.assertEqual(c.check_dense_maps(),dict(nonzero_kernel_cases=780,
                          candidate_partial_maps=3353,partially_additive_maps=59))

    def test_sharp_support_and_generic_equality(self):
        out = c.check_support()
        self.assertEqual(out['nonzero_maps'],286)
        self.assertEqual(len(out['families']),10)
        self.assertEqual(out['generic_equality_examples'],8)

    def test_torsion_and_sign(self):
        self.assertEqual(len(c.check_torsion()),8)
        rows = c.check_polynomial()
        self.assertEqual(len(rows),11)
        self.assertEqual(sum(r['coefficient_increment_cases'] for r in rows),19265)
        self.assertIn(35,[r['N'] for r in rows])
        self.assertEqual(c.phase_difference((0,1,4,4,1),1,5),(4,1,3,0,2))


class CyclotomicTests(unittest.TestCase):
    def test_field_roots_and_orthogonality(self):
        for n in c.PHI:
            one = c.Cyclo(n,(1,))
            self.assertEqual(c.root(n,n),one)
            self.assertEqual(sum((c.root(n,j) for j in range(n)),c.Cyclo(n)),0)
            for j,k in product(range(n),repeat=2):
                self.assertEqual(c.root(n,j)*c.root(n,k),c.root(n,j+k))
                self.assertEqual(c.root(n,j).conjugate(),c.root(n,-j))
                self.assertEqual(c.root(n,j).norm_square(),one)
        i = c.root(4,1)
        self.assertEqual(i*i,-1)
        self.assertEqual((Q(3,5)*i+Q(4,5)).norm_square(),1)

    def test_constructor_and_operation_bounds(self):
        for args in ((True,()),(6,()),(3,[0]*65),(3,['1']),(3,[True]),(3,[1<<4097])):
            with self.subTest(args=args), self.assertRaises(ValueError): c.Cyclo(*args)
        for exponent in (True,Q(1),1000001,-1000001):
            with self.assertRaises(ValueError): c.root(3,exponent)
        with self.assertRaises(ValueError): c.root(3,1)+c.root(4,1)
        with self.assertRaises(ValueError): c.root(3,1)/0
        with self.assertRaises(ValueError): c.root(3,1)/True

    def test_constant_norms_and_direct_cube(self):
        for n in (2,3):
            f = tuple(c.Cyclo(n,(Q(1,2),)) for _ in range(n))
            for k in (1,2,3):
                expected = Q(1,2**(2**k))
                self.assertEqual(c.q_squared(f,k),expected)
                self.assertEqual(c.q_cube(f,k),expected)
            self.assertEqual(c.fourier(f)[0],Q(1,2))
            self.assertTrue(all(x == 0 for x in c.fourier(f)[1:]))

    def test_negative_transform_and_backward_positive_frequency(self):
        n = 5
        f = tuple(c.root(n,x*x) for x in range(n))
        for a in range(n):
            coeffs = c.fourier(c.difference(f,a))
            self.assertEqual(coeffs[(2*a)%n].norm_square(),1)
            self.assertTrue(all(z == 0 for r,z in enumerate(coeffs) if r != (2*a)%n))
        v = tuple(c.root(3,x*x*x) for x in range(3))
        for a,b in product(range(3),repeat=2):
            self.assertEqual(c.iterated(v,(a,b)),c.iterated(v,(b,a)))
            right = tuple(c.difference(v,a)[x]*c.difference(v,b)[(x-a)%3] for x in range(3))
            self.assertEqual(c.difference(v,(a+b)%3),right)


class RationalLiftTests(unittest.TestCase):
    def test_negative_binomial_integrality(self):
        self.assertEqual([c.integer_binomial(-3,j) for j in range(6)],
                         [1,-3,6,-10,15,-21])
        for x in (-128,-1,0,1,128):
            self.assertEqual(c.integer_binomial(x,0),1)
        self.assertEqual(c.integer_binomial(2,9),0)
        self.assertEqual(c.integer_binomial(-1,9),-1)

    def test_binomial_rejects_inexact_and_unbounded_inputs(self):
        for x in (True,False,Q(2),'2',None,2.0,-129,129):
            with self.subTest(x=x), self.assertRaises(ValueError): c.integer_binomial(x,2)
        for j in (True,Q(2),'2',None,2.0,-1,10):
            with self.subTest(j=j), self.assertRaises(ValueError): c.integer_binomial(2,j)

    def test_cubic_and_linear_coefficients(self):
        cubic = (Q(0),Q(5,12),Q(-3,8),Q(1,12))
        for construction in (c.rational_lift,c.newton_lift):
            self.assertEqual(construction(2,3,1),cubic)
            self.assertEqual(construction(7,1,-2),(Q(0),Q(-2,7)))
            self.assertEqual(construction(14,9,0),(Q(0),))
        self.assertEqual(c._poly_backward(c._poly_backward(cubic,1),1),(Q(-5,4),Q(1,2)))
        self.assertEqual(c._poly_value(cubic,1),Q(1,8))

    def test_independent_newton_at_domain_boundaries(self):
        for n,m,coefficient in product((2,14),(1,9),(-128,-1,0,1,128)):
            p = c.rational_lift(n,m,coefficient)
            self.assertEqual(p,c.newton_lift(n,m,coefficient))
            self.assertTrue(all(type(a) is Q for a in p))
            self.assertEqual(c._poly_add(c._poly_shift(p,n),c._poly_scale(p,-1)),
                             c._poly_scale(c._binomial_poly(m-1),coefficient))

    def test_lifts_reject_invalid_parameters(self):
        for construction in (c.rational_lift,c.newton_lift):
            for args in ((1,2,1),(15,2,1),(True,2,1),(Q(3),2,1),(3.0,2,1),
                         (3,0,1),(3,10,1),(3,True,1),(3,Q(2),1),(3,2,False),
                         (3,2,Q(1)),(3,2,1.0),(3,2,'1'),(3,2,-129),(3,2,129)):
                with self.subTest(construction=construction.__name__,args=args), self.assertRaises(ValueError):
                    construction(*args)

    def test_signed_zero_and_nonunit_increments(self):
        p = c.rational_lift(6,4,-2)
        for increments in ((-7,0,8),(-7,2,-3),(6,1,1),(0,0,0)):
            derivative = p
            for a in increments:
                derivative = c._poly_backward(derivative,a)
            slope = Q(-2,6)
            for a in increments:
                slope *= a
            self.assertEqual(derivative,c._poly_trim((derivative[0],slope)))
            values = tuple((Q(1),c._poly_value(p,x)) for x in range(6))
            expected = tuple((Q(1),c._poly_value(derivative,x)%1) for x in range(6))
            self.assertEqual(c.rational_differences(values,increments),expected)

    def test_point_increment_and_coefficient_representatives(self):
        p = c.rational_lift(2,3,1)
        values = tuple((Q(1),c._poly_value(p,x)) for x in range(2))
        alias = tuple((Q(1),c._poly_value(p,x-6)) for x in range(2))
        self.assertEqual(c.rational_differences(values,(1,1)),
                         c.rational_differences(alias,(-1,3)))
        changed = c.rational_lift(2,3,3)
        self.assertEqual((c._poly_value(changed,1)-c._poly_value(p,1))%1,Q(1,4))
        delta = c._poly_add(changed,c._poly_scale(p,-1))
        reduced = c._poly_add(delta,c._poly_scale(c._binomial_poly(3),-1))
        self.assertLessEqual(len(reduced),3)
        for x in range(-6,7):
            self.assertEqual((c._poly_value(delta,x)-c._poly_value(reduced,x)).denominator,1)

    def test_fixed_lift_diagnostic_counts_and_torsion(self):
        out = c.check_rational_lifts()
        self.assertEqual(out['counts'],dict(binomial_values=650,negative_binomial_identities=320,
            polynomials=510,integer_shift_values=18186,point_representative_checks=90930,
            signed_integer_derivatives=4590,cyclic_derivative_values=32886,
            increment_representative_checks=32130,lift_change_polynomials=1020,lift_change_values=5100))
        self.assertEqual(out['N2_cubic_coefficients'],['0','5/12','-3/8','1/12'])
        self.assertEqual(out['N2_cubic_second_difference'],['-5/4','1/2'])
        self.assertEqual(out['N2_c1_to_c3_phase_change_at_1'],'1/4')
        self.assertEqual(len(out['torsion_cases']),8)
        self.assertEqual(sum(row['top_order_tuples'] for row in out['torsion_cases']),2040)


class RationalEnergyTests(unittest.TestCase):
    def test_constant_and_zero_direct_cube(self):
        for n,amplitude in product((2,3),(Q(0),Q(1,2),Q(1))):
            values = ((amplitude,Q(1,7)),)*n
            for k in (1,2,3):
                expected = {Q(0):amplitude**(2**k)} if amplitude else {}
                self.assertEqual(c.rational_cube(values,k),expected)
                if k > 1:
                    self.assertEqual(c.rational_selected_energy(values,k-1,0),expected)

    def test_energy_with_zero_and_nonunit_amplitudes(self):
        n,d,coefficient = 3,2,1
        p = c.rational_lift(n,d+1,coefficient)
        values = ((Q(0),Q(1,7)),(Q(1,3),Q(2,7)),(Q(1),Q(3,7)))
        w = tuple((amplitude,phase-c._poly_value(p,x)) for x,(amplitude,phase) in enumerate(values))
        self.assertEqual(c.rational_selected_energy(values,d,coefficient),c.rational_cube(w,d+1))
        self.assertTrue(all(type(phase) is Q and type(weight) is Q
                            for phase,weight in c.rational_cube(w,d+1).items()))

    def test_direct_cube_does_not_use_derivative_algorithm(self):
        values = ((Q(1),Q(0)),(Q(1,2),Q(1,7)))
        expected = c.rational_cube(values,3)
        with patch.object(c,'_rational_differences',side_effect=RuntimeError('not a direct cube')):
            self.assertEqual(c.rational_cube(values,3),expected)

    def test_wrong_sign_is_actual_cyclotomic_counterexample(self):
        v = tuple(c.root(3,-x*x) for x in range(3))
        right = sum((c.fourier(c.difference(v,a))[a].norm_square() for a in range(3)),c.Cyclo(3))/3
        wrong = sum((c.fourier(c.difference(v,a))[(-a)%3].norm_square() for a in range(3)),c.Cyclo(3))/3
        self.assertEqual(right,1)
        self.assertEqual(wrong,Q(1,3))
        self.assertNotEqual(right,wrong)

    def test_rational_values_reject_malformed_and_inexact_inputs(self):
        invalid = (None,[],[(1,0)],[(1,0)]*15,[(1,0),1],[(1,0),(1,0,0)],
                   [(True,0),(1,0)],[(1,False),(1,0)],[(1.0,0),(1,0)],
                   [(1,0.0),(1,0)],[(1,'0'),(1,0)],[(3,0),(1,0)],
                   [(1,1<<257),(1,0)],[(1,Q(1,1<<257)),(1,0)])
        for values in invalid:
            for call in (lambda: c.rational_differences(values,(1,)),
                         lambda: c.rational_selected_energy(values,1,1),
                         lambda: c.rational_cube(values,2)):
                with self.subTest(values=values), self.assertRaises(ValueError): call()

    def test_increment_and_work_budget_guards(self):
        values = ((Q(1),Q(0)),)*2
        for increments in (None,'1',range(2),(True,),(Q(1),),(1.0,),(-129,),(129,),(1,)*9):
            with self.subTest(increments=increments), self.assertRaises(ValueError):
                c.rational_differences(values,increments)
        for d in (False,Q(1),1.0,0,5):
            with self.assertRaises(ValueError): c.rational_selected_energy(values,d,1)
        for coefficient in (False,Q(1),1.0,-129,129):
            with self.assertRaises(ValueError): c.rational_selected_energy(values,1,coefficient)
        for sign in (False,True,Q(1),1.0,0,2):
            with self.assertRaises(ValueError): c.rational_selected_energy(values,1,1,sign)
        for k in (False,Q(1),1.0,0,6):
            with self.assertRaises(ValueError): c.rational_cube(values,k)
        for size,order in ((7,1),(6,5)):
            with self.assertRaises(ValueError): c.rational_cube(values[:1]*size,order)
        with self.assertRaises(ValueError): c.rational_selected_energy(values[:1]*7,1,1)
        with self.assertRaises(ValueError): c.rational_selected_energy(values[:1]*6,4,1)

    def test_fractional_phase_representatives_and_empty_derivatives(self):
        values = ((Q(1,2),Q(-6,7)),(Q(1),Q(10,7)))
        canonical = ((Q(1,2),Q(1,7)),(Q(1),Q(3,7)))
        self.assertEqual(c.rational_differences(values,()),canonical)
        self.assertEqual(c.rational_differences(values,(-3,2)),c.rational_differences(canonical,(1,0)))
        self.assertEqual(c.rational_cube(values,3),c.rational_cube(canonical,3))

    def test_fixed_energy_families_and_descent(self):
        out = c.check_rational_energy()
        self.assertEqual(out['case_count'],64)
        self.assertEqual(len(out['cases']),64)
        self.assertEqual(sum(row['unit_input'] for row in out['cases']),32)
        self.assertEqual(out['wrong_sign_formal_mismatch_cases'],32)
        self.assertEqual(out['wrong_sign_cyclotomic_witness']['wrong_sign_energy'],'1/3')
        self.assertEqual(out['descent_k_range'],[2,30])
        self.assertEqual(out['positive_descent_stages'],406)


class SourceTests(unittest.TestCase):
    def test_pinned_sources(self):
        self.assertEqual(c.check_sources(),dict(snapshots=3,exact_sha256_and_git_blob_checks=True))

    def test_coherent_location_and_url_tampering_fails(self):
        for selected in ('Definitions.lean','Mathlib_Fourier_ZMod.lean','lake-manifest.json'):
            for field in ('repository','repository_path'):
                with self.subTest(source=selected,field=field), tempfile.TemporaryDirectory(prefix='report284-location-') as tmp:
                    root = Path(tmp)
                    for name in ('provenance/source_manifest.json','provenance/sources/Definitions.lean',
                                 'provenance/sources/Mathlib_Fourier_ZMod.lean','provenance/sources/lake-manifest.json'):
                        p = root/name; p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes((ROOT/name).read_bytes())
                    p = root/'provenance/source_manifest.json'
                    rows = json.loads(p.read_text())
                    row = next(r for r in rows if r['name'] == selected)
                    row[field] = ('other-owner/other-project' if field == 'repository' else 'different/source.lean')
                    row['url'] = 'https://github.com/'+row['repository']+'/blob/'+row['commit']+'/'+row['repository_path']
                    p.write_text(json.dumps(rows))
                    with patch.object(c,'ROOT',root):
                        with self.assertRaisesRegex(RuntimeError,'pinned source repository and path'):
                            c.check_sources()

    def test_modified_source_fails(self):
        with tempfile.TemporaryDirectory(prefix='report284-source-') as tmp:
            root = Path(tmp)
            for name in ('provenance/source_manifest.json','provenance/sources/Definitions.lean',
                         'provenance/sources/Mathlib_Fourier_ZMod.lean','provenance/sources/lake-manifest.json'):
                p = root/name; p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes((ROOT/name).read_bytes())
            with patch.object(c,'ROOT',root):
                c.check_sources()
                p = root/'provenance/sources/Definitions.lean'; p.write_bytes(p.read_bytes()+b'\n')
                with self.assertRaisesRegex(RuntimeError,'pinned source'): c.check_sources()


if __name__ == '__main__':
    unittest.main()
