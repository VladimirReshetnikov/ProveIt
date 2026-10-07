"""Report285 exact identities, mathematical boundaries, provenance, and live guards."""
import sys
sys.dont_write_bytecode = True
import ast
from contextlib import redirect_stdout
from fractions import Fraction as Q
import importlib.util
from io import StringIO
from itertools import product
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).absolute().parents[1]
spec = importlib.util.spec_from_file_location('report285_exact', ROOT/'companion/exact_checks.py')
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)


class ConstantsTests(unittest.TestCase):
    def test_low_degree_golden_constants(self):
        rows = [c.constants(d) for d in (2,3,4)]
        self.assertEqual([r['B'] for r in rows], [0,588,51688])
        self.assertEqual([r['Kstar'] for r in rows], [Q(5,2),Q(21),Q(170)])
        self.assertEqual([r['Hstar'] for r in rows], [Q(1),Q(600),Q(51788)])
        self.assertEqual([r['R'] for r in rows], [Q(121,32),Q(25023,256),Q(3759139,4096)])
        self.assertEqual([r['rho_squared'] for r in rows], [Q(1,14**2),Q(1,44**2),Q(1,171**2)])
        self.assertEqual([r['epsilon_entry'] for r in rows], [Q(1,100),Q(1,1000),Q(1,10000)])
        self.assertEqual([r['eta'] for r in rows], [Q(1),Q(1,180),Q(1,1800)])
        self.assertEqual(rows[1]['b_odd'],Q(13,64))
        self.assertEqual(rows[1]['b_even'],Q(21,64))

    def test_checked_range_and_low_degree_exceptions(self):
        rows = c.check_constants()
        self.assertEqual(len(rows),29)
        for row in rows:
            entry = row['epsilon_entry']
            if row['d'] in (2,3):
                self.assertGreater((6*entry)**2,row['radius_lower_squared'])
            else:
                self.assertLessEqual((6*entry)**2,row['radius_lower_squared'])
            self.assertLessEqual((6*entry)**2,row['rho_squared'])

    def test_exact_bounded_parameters(self):
        for value in (True,False,1,31,-1,Q(2),'2',None,2.0):
            with self.subTest(value=value), self.assertRaises(ValueError):
                c.constants(value)
        for value in (True,False,'1',None,1.0,1+0j,1 << (c.MAX_BITS+1),Q(1,1 << (c.MAX_BITS+1))):
            with self.subTest(value=type(value).__name__), self.assertRaises(ValueError):
                c.rational(value)
        self.assertEqual(c.rational(-2),Q(-2))
        self.assertEqual(c.rational(Q(1,3)),Q(1,3))

    def test_guards_survive_optimized_python(self):
        tree = ast.parse((ROOT/'companion/exact_checks.py').read_text())
        self.assertFalse(any(isinstance(n,ast.Assert) for n in ast.walk(tree)))
        self.assertFalse(any(isinstance(n,ast.Constant) and type(n.value) in (float,complex) for n in ast.walk(tree)))
        self.assertFalse(any(isinstance(n,ast.Name) and n.id in ('float','complex','cmath','random') for n in ast.walk(tree)))
        with self.assertRaisesRegex(RuntimeError,'active'):
            c.require(False,'active')


class GroupAndPhaseTests(unittest.TestCase):
    def test_group_laws_and_enumeration(self):
        for moduli in ((1,),(2,),(3,),(2,3),(2,2,2),(32,)):
            group = c.Group(moduli)
            self.assertEqual(group.points[0],(0,)*len(moduli))
            for x,y in product(range(group.n),repeat=2):
                self.assertEqual(group.sub[group.add[x][y]][y],x)
                self.assertEqual(group.add[x][group.neg[x]],0)
                self.assertEqual(group.sub[x][y],group.add[x][group.neg[y]])
        self.assertEqual(c.Group((2,3)).points,((0,0),(0,1),(0,2),(1,0),(1,1),(1,2)))

    def test_group_constructor_guards(self):
        for moduli in (None,2,(),(0,),(33,),(True,),(Q(2),),('2',),(2,2,2,2),(8,8),(1,1.0)):
            with self.subTest(moduli=moduli), self.assertRaises(ValueError):
                c.Group(moduli)
        with self.assertRaises(ValueError): c.group_input((2,))

    def test_backward_phase_sign_and_representatives(self):
        group = c.Group((3,))
        phase = (Q(0),Q(1,3),Q(1,3))
        self.assertEqual(c.phase_derivative(group,phase,1),(Q(1,3),Q(2,3),Q(0)))
        self.assertEqual(c.phases(group,(Q(-1),Q(4,3),Q(-2,3))),phase)
        for h,t in product(range(group.n),repeat=2):
            self.assertEqual(c.phase_derivative(group,c.phase_derivative(group,phase,h),t),
                             c.phase_derivative(group,c.phase_derivative(group,phase,t),h))
        self.assertTrue(c.phase_degree_at_most(group,phase,2))
        self.assertFalse(c.phase_degree_at_most(group,phase,1))
        self.assertTrue(c.phase_degree_at_most(group,(Q(1,7),)*3,0))

    def test_nonclassical_characteristic_two(self):
        group = c.Group((2,))
        for degree in (1,2,3,4):
            phase = (Q(0),Q(1,2**degree))
            self.assertTrue(c.phase_degree_at_most(group,phase,degree))
            self.assertFalse(c.phase_degree_at_most(group,phase,degree-1))
        # The fourth-root phase on Z/2 is quadratic but is not a character.
        self.assertEqual(c.phase_derivative(group,(Q(0),Q(1,4)),1),(Q(1,4),Q(3,4)))

    def test_phase_api_guards_and_work_budgets(self):
        group = c.Group((2,))
        for values in (None,(),(0,),(0,True),(0,0.0),(0,'0'),(0,Q(1,1 << (c.MAX_BITS+1)))):
            with self.subTest(values=type(values).__name__), self.assertRaises(ValueError): c.phases(group,values)
        for increment in (-1,2,True,Q(1),'1',None):
            with self.assertRaises(ValueError): c.phase_derivative(group,(0,0),increment)
        for degree in (-1,5,True,Q(2),'2',None):
            with self.assertRaises(ValueError): c.phase_degree_at_most(group,(0,0),degree)
        with self.assertRaises(ValueError): c.phase_degree_at_most(c.Group((32,)),(0,)*32,4)


class CocycleTests(unittest.TestCase):
    def test_integration_and_constant_normalization(self):
        group = c.Group((3,))
        phase = (Q(1,7),Q(1,7)+Q(1,3),Q(1,7)+Q(2,3))
        rows = tuple(c.phase_derivative(group,phase,h) for h in range(3))
        integrated = c.integrate_cocycle(group,rows)
        self.assertEqual(integrated,(Q(0),Q(1,3),Q(2,3)))
        forward_wrong = tuple(rows[x][0] for x in range(3))
        self.assertNotEqual(integrated,forward_wrong)
        self.assertEqual(rows[1],(Q(2,3),)*3)
        self.assertTrue(c.is_cocycle(group,rows))

    def test_exact_small_cocycle_correction_sign(self):
        group = c.Group((2,))
        phase = (Q(0),Q(1,8))
        exact = tuple(c.phase_derivative(group,phase,h) for h in range(2))
        theta = (Q(1,96),Q(1,48))
        rows = tuple(tuple((a+theta[h]) % 1 for a in exact[h]) for h in range(2))
        answer = c.correct_small_cocycle(group,rows)
        self.assertEqual(answer['b'],tuple(-t for t in theta))
        self.assertEqual(answer['integrated'],phase)
        self.assertEqual(answer['corrected'],exact)
        wrong = tuple(tuple((a-answer['b'][h]) % 1 for a in rows[h]) for h in range(2))
        self.assertFalse(c.is_cocycle(group,wrong))

    def test_lift_boundary_zero_defect_and_trivial_group(self):
        for group in (c.Group((1,)),c.Group((2,))):
            for value in (Q(-1,6),Q(0),Q(1,6)):
                rows = ((value,)*group.n,)*group.n
                answer = c.correct_small_cocycle(group,rows)
                self.assertEqual(answer['b'],(-value,)*group.n)
                self.assertEqual(answer['integrated'],(Q(0),)*group.n)
            for value in (Q(1,5),Q(-1,5),Q(1,2)):
                with self.assertRaisesRegex(ValueError,'exceeds'):
                    c.correct_small_cocycle(group,((value,)*group.n,)*group.n)

    def test_nonconstant_defects_and_false_cocycles_rejected(self):
        group = c.Group((3,))
        rows = ((0,0,0),(Q(1,12),0,0),(0,0,0))
        with self.assertRaisesRegex(ValueError,'constant in x'): c.correct_small_cocycle(group,rows)
        with self.assertRaisesRegex(ValueError,'exact translation'): c.integrate_cocycle(group,rows)
        with self.assertRaises(ValueError): c.integrate_cocycle(c.Group((2,)),((0,0),(Q(1,3),)*2))
        for rows in (None,(),((0,0),),((0,0),(0,True))):
            for function in (c.phase_rows,c.is_cocycle,c.integrate_cocycle,c.correct_small_cocycle):
                with self.subTest(function=function.__name__), self.assertRaises(ValueError):
                    function(c.Group((2,)),rows)


class CyclotomicTests(unittest.TestCase):
    def test_roots_multiplication_and_conjugation(self):
        for n in c.PHI:
            self.assertEqual(c.root(n,n),1)
            self.assertEqual(sum((c.root(n,j) for j in range(n)),c.Cyclo(n)),0)
            for j,k in product(range(n),repeat=2):
                self.assertEqual(c.root(n,j)*c.root(n,k),c.root(n,j+k))
            for j in range(n):
                self.assertEqual(c.root(n,j).conjugate(),c.root(n,-j))
                self.assertEqual(c.root(n,j).norm_square(),1)
        i = c.root(4,1)
        self.assertEqual(i*i,-1)
        self.assertEqual((Q(3,5)+Q(4,5)*i).norm_square(),1)
        self.assertEqual(1-i, c.Cyclo(4,(1,-1)))

    def test_actual_field_relations_are_not_formal_order(self):
        # Nonzero formal coefficients can evaluate to zero; signs of coefficients
        # therefore cannot certify the order of a cyclotomic real number.
        self.assertEqual(c.Cyclo(3,(1,1,1)),0)
        self.assertEqual(c.Cyclo(4,(1,0,1)),0)
        self.assertEqual(c.Cyclo(8,(1,0,0,0,1)),0)
        real_irrational = c.root(8,1)+c.root(8,-1)
        self.assertEqual(real_irrational,real_irrational.conjugate())
        with self.assertRaisesRegex(ValueError,'no formal positivity'): real_irrational.rational_real()
        with self.assertRaises(TypeError): real_irrational < 0
        self.assertEqual((real_irrational*real_irrational).rational_real(),Q(2))
        with self.assertRaises(ValueError): c.root(4,1).rational_real()

    def test_constructor_scalar_and_root_guards(self):
        for args in ((True,()),(1,()),(7,()),(3,()),(3,[0]*49),(3,['1']),(3,[True]),
                     (3,[1.0]),(3,[1 << (c.MAX_BITS+1)]),(3,[Q(1,1 << (c.MAX_BITS+1))])):
            if args == (3,()):
                self.assertEqual(c.Cyclo(*args),0)
            else:
                with self.subTest(args_type=type(args[1]).__name__), self.assertRaises(ValueError): c.Cyclo(*args)
        for value in (True,False,1.0,Q(1),'1',None,1000001,-1000001):
            with self.assertRaises(ValueError): c.root(3,value)
        for value in (True,0,0.0,'1',None):
            with self.assertRaises(ValueError): c.root(3,1)/value
        for value in (True,1.0,'1',None,c.root(4,1)):
            with self.assertRaises(ValueError): c.root(3,1)+value
        self.assertEqual(c.root(3,1).serialized(),['0','1'])

    def test_phase_evaluation_exact_denominators(self):
        group = c.Group((2,))
        self.assertEqual(c.evaluated_phases(group,(0,Q(1,4)),4),(c.Cyclo(4,(1,)),c.root(4,1)))
        with self.assertRaises(ValueError): c.evaluated_phases(group,(0,Q(1,3)),4)
        for conductor in (True,7,Q(4),'4',None):
            with self.assertRaises(ValueError): c.evaluated_phases(group,(0,0),conductor)


class CubeTests(unittest.TestCase):
    def test_constant_zero_and_unit_cube_values(self):
        for moduli in ((1,),(2,),(2,2)):
            group = c.Group(moduli)
            for a in (Q(0),Q(1,2),Q(1)):
                values = (c.Cyclo(4,(a,)),)*group.n
                for d in (1,2,3):
                    self.assertEqual(c.cube_average(group,values,d),a**(2**d))
        group = c.Group((2,))
        values = (c.Cyclo(4,(1,)),c.root(4,1))
        self.assertEqual(c.cube_average(group,values,2),Q(1,2))
        self.assertEqual(c.cube_average(group,values,3),1)

    def test_derivative_values_match_rational_phase_sign(self):
        group = c.Group((3,)); phase = (Q(0),Q(1,3),Q(1,3))
        values = c.evaluated_phases(group,phase,3)
        for h in range(group.n):
            self.assertEqual(c.derivative_values(group,values,h),
                             c.evaluated_phases(group,c.phase_derivative(group,phase,h),3))
        for increment in (-1,3,True,Q(1),'1'):
            with self.assertRaises(ValueError): c.derivative_values(group,values,increment)

    def test_character_fourier_and_energy(self):
        group = c.Group((2,3)); conductor = 6
        values = tuple(c.root(conductor,3*x+2*y) for x,y in group.points)
        coefficients = c.fourier(group,values)
        self.assertEqual(coefficients[4],1)
        self.assertEqual(sum((z.norm_square().rational_real() for z in coefficients),Q(0)),1)
        self.assertEqual(c.cube_average(group,values,2),1)
        with self.assertRaises(ValueError): c.fourier(c.Group((3,)),(c.Cyclo(4,(1,)),)*3)

    def test_values_mean_and_cube_budget_guards(self):
        group = c.Group((2,)); valid = (c.Cyclo(4,(1,)),)*2
        for values in (None,(),valid[:1],(0,0),(c.Cyclo(4),c.Cyclo(3))):
            for function in (c.values_input,c.fourier):
                with self.subTest(function=function.__name__), self.assertRaises(ValueError): function(group,values)
            with self.assertRaises(ValueError): c.cube_average(group,values,2)
        for values in (None,(),[0],[c.Cyclo(4)]*33,[c.Cyclo(4),c.Cyclo(3)]):
            with self.assertRaises(ValueError): c.mean(values)
        for d in (0,5,True,Q(2),'2',None):
            with self.assertRaises(ValueError): c.cube_average(group,valid,d)
            with self.assertRaises(ValueError): list(c.cube_indices(group,d))
        with self.assertRaises(ValueError): c.cube_budget(group,2,polynomial=1)
        with self.assertRaises(ValueError): c.cube_average(c.Group((32,)),(valid[0],)*32,4)
        with self.assertRaises(ValueError): c.cube_coefficients(c.Group((4,)),(valid[0],)*4,4)

    def test_convex_constant_and_zero_remainder_at_d2(self):
        group = c.Group((2,))
        for a in (Q(1,2),Q(3,4),Q(1)):
            values = (c.Cyclo(4,(a,)),)*2
            result = c.convex_certificate(group,values,3)
            self.assertEqual(result['v'],0)
            self.assertEqual(result['coefficients'],(a**8,)+(Q(0),)*8)
            self.assertEqual(result['remainder'],0)
        i = c.root(4,1)
        result = c.convex_certificate(group,(Q(3,5)+Q(4,5)*i,Q(3,5)-Q(4,5)*i),2)
        self.assertEqual(result['coefficients'],(Q(81,625),0,0,0,Q(256,625)))
        self.assertEqual(result['remainder'],0)

    def test_convex_disk_mean_and_order_guards(self):
        group = c.Group((2,)); one = c.Cyclo(4,(1,)); i = c.root(4,1)
        for values in ((one*Q(1,3),)*2,(one*2,one),(one+i,one-i),(one,one+i)):
            with self.assertRaises(ValueError): c.convex_certificate(group,values,3)
        for d in (1,5,True,Q(2),'2',None):
            with self.assertRaises(ValueError): c.convex_certificate(group,(one,one),d)
        with self.assertRaises(ValueError): c.convex_certificate(c.Group((4,)),(one,)*4,4)


class DiagnosticTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.results = c.run_all()

    def test_census_and_triple_law_golden_counts(self):
        rows = self.results['cube_geometry']['unimodular_and_circuit_census']
        self.assertEqual([r['triples'] for r in rows],[4,56,560,4960])
        self.assertEqual([r['ordinary'] for r in rows],[1,12,100,720])
        self.assertEqual([r['xor_zero'] for r in rows],[1,14,140,1240])
        laws = self.results['cube_geometry']['exact_joint_laws']
        self.assertEqual(len(laws),5)
        self.assertEqual(laws[-1],dict(group=[2,3],triples=56,outputs_each=216,multiplicity=6))

    def test_cocycles_and_good_set_coverage(self):
        rows = self.results['cocycle_integration']
        self.assertEqual(len(rows),6)
        self.assertEqual([r['exact_degree'] for r in rows],[2,3,2,2,2,2])
        self.assertTrue(all(r['wrong_sign_rejected'] for r in rows))
        self.assertIn([2,3],[r['group'] for r in rows])
        rows = self.results['good_set']
        self.assertEqual(len(rows),6)
        self.assertTrue(all(r['good_count'] == 19 and len(r['witnesses']) == 1 for r in rows))
        self.assertEqual(rows[0]['delta'],'519/2000000')

    def test_actual_polar_values_and_zero_coverage(self):
        rows = self.results['polar']
        self.assertEqual(len(rows),6)
        self.assertTrue(all(r['zero_count'] > 0 for r in rows))
        self.assertEqual(rows[2]['Qf'],'25/1024')
        self.assertEqual(rows[2]['Qrho'],'41/1024')
        self.assertEqual(rows[4]['Qv'],'2/9')
        for row in rows:
            self.assertLessEqual(1-Q(row['Qv']),2*Q(row['epsilon']))
            self.assertLessEqual(Q(row['amplitude_loss']),Q(row['epsilon']))

    def test_nontrivial_convex_taylor_and_fifth_moments(self):
        rows = self.results['convex']
        self.assertEqual(len(rows),7)
        self.assertEqual(rows[1]['tail'],'65536/390625')
        self.assertEqual(rows[4]['fifth'],'82458112/2562890625')
        self.assertEqual(rows[4]['tail'],'273104896/2562890625')
        self.assertEqual(rows[-1]['a'],'1/4')
        self.assertEqual(self.results['fifth_conjugations']['conjugation_choices'],32)
        self.assertGreater(Q(self.results['fifth_conjugations']['maximum_absolute_real']),0)
        # Missing the Taylor factor 1/5! would be visible on this exact nonzero tail.
        self.assertNotEqual(Q(rows[1]['tail']),120*Q(rows[1]['tail']))

    def test_near_extremizers_meet_the_final_main_threshold(self):
        rows = self.results['fourier_and_stability']['exact_near_extremizers']
        self.assertEqual(len(rows),3)
        self.assertEqual([r['degree'] for r in rows],[1,2,3])
        for row in rows:
            k = row['degree']+1
            self.assertLessEqual(Q(row['epsilon']),Q(1,10**k))
            self.assertLessEqual(Q(row['distance']),Q(row['main_bound']))
            self.assertLessEqual(Q(row['Qk']),Q(row['fidelity']))
        self.assertEqual(self.results['fourier_and_stability']['parseval_cases'][1]['Q2'],'1/3')

    def test_deterministic_json_and_finite_scope(self):
        self.assertEqual(self.results['status'],'PASS')
        self.assertEqual(self.results['report'],285)
        self.assertIn('finite',self.results['scope'])
        self.assertIn('no formal positivity',self.results['scope'])
        with patch.object(c,'run_all',return_value=self.results):
            first = StringIO(); second = StringIO()
            with redirect_stdout(first): self.assertEqual(c.main([]),0)
            with redirect_stdout(second): self.assertEqual(c.main(()),0)
        self.assertEqual(first.getvalue(),second.getvalue())
        self.assertEqual(json.loads(first.getvalue()),self.results)
        self.assertEqual(first.getvalue(),json.dumps(self.results,indent=2,sort_keys=True)+'\n')
        for arguments in (['--help'],['--d','30'],['30'],'',None):
            if arguments is None:
                continue
            with self.assertRaises(SystemExit): c.main(arguments)
        with self.assertRaises(ValueError): c.serialized(Q(1,2)+0.0)


class ProvenanceTests(unittest.TestCase):
    def copied_sources(self, root):
        for name in ('provenance/source_manifest.json','provenance/sources/source55_article.tex',
                     'provenance/sources/source55_audit.md'):
            path = root/name
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes((ROOT/name).read_bytes())

    def test_pinned_prior_source_boundaries(self):
        result = c.check_sources()
        self.assertEqual(result['snapshots'],2)
        self.assertTrue(result['exact_snapshot_sha256'])
        self.assertTrue(result['raw_audit_git_blob_verified'])
        self.assertIn('not bundled',result['boundary'])

    def test_raw_snapshot_tamper_rejected(self):
        for name in ('source55_article.tex','source55_audit.md'):
            with self.subTest(name=name), tempfile.TemporaryDirectory(prefix='report285-source-') as tmp:
                root = Path(tmp); self.copied_sources(root)
                path = root/'provenance/sources'/name
                path.write_bytes(path.read_bytes()+b'\n')
                with patch.object(c,'ROOT',root), self.assertRaisesRegex(RuntimeError,'snapshot bytes'):
                    c.check_sources()

    def test_coherent_manifest_retargeting_and_hash_tamper_rejected(self):
        for field in ('repository','repository_path','commit','sha256','archive_member','archive_git_blob_sha1','archive_sha256'):
            with self.subTest(field=field), tempfile.TemporaryDirectory(prefix='report285-manifest-') as tmp:
                root = Path(tmp); self.copied_sources(root)
                path = root/'provenance/source_manifest.json'
                rows = json.loads(path.read_text())
                rows[0][field] = 'changed'
                rows[0]['url'] = 'https://github.com/'+rows[0]['repository']+'/blob/'+rows[0]['commit']+'/'+rows[0]['repository_path']
                path.write_text(json.dumps(rows))
                with patch.object(c,'ROOT',root), self.assertRaisesRegex(RuntimeError,'pinned source identity'):
                    c.check_sources()

    def test_manifest_shape_and_order_rejected(self):
        for replacement in ({},[],[1,2]):
            with tempfile.TemporaryDirectory(prefix='report285-shape-') as tmp:
                root = Path(tmp); self.copied_sources(root)
                (root/'provenance/source_manifest.json').write_text(json.dumps(replacement))
                with patch.object(c,'ROOT',root), self.assertRaisesRegex(RuntimeError,'pinned source identity'):
                    c.check_sources()


if __name__ == '__main__':
    unittest.main()
