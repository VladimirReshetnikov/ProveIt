"""Independent enumeration and adversarial input tests for Report283."""
import sys
sys.dont_write_bytecode=True
import ast
from collections import Counter
from fractions import Fraction as F
import importlib.util
from itertools import product
import json
from math import gcd
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
ROOT=Path(__file__).absolute().parents[1]
SCRIPT=ROOT/'companion/exact_checks.py'
spec=importlib.util.spec_from_file_location('report283_checks',SCRIPT)
e=importlib.util.module_from_spec(spec);spec.loader.exec_module(e)


class Guards(unittest.TestCase):
    def test_no_assert_or_dynamic_code(self):
        tree=ast.parse(SCRIPT.read_text())
        self.assertFalse(any(isinstance(x,ast.Assert) for x in ast.walk(tree)))
        calls={x.func.id for x in ast.walk(tree) if isinstance(x,ast.Call) and isinstance(x.func,ast.Name)}
        self.assertFalse(calls & {'eval','exec','compile','float'})
        with self.assertRaises(RuntimeError):e.require(False,'must survive optimization')
        self.assertNotIn('set_int_max_str_digits(',SCRIPT.read_text())

    def test_integer_and_prime_guards(self):
        for x in (True,False,None,'2',2.0,-1,4097):
            with self.subTest(x=x),self.assertRaises(ValueError):e.integer(x,'x',2,4096)
        for p in (1,4,9,15,21,True,2.0):
            with self.subTest(p=p),self.assertRaises(ValueError):e.prime(p)
        self.assertEqual(e.prime(19),19)

    def test_model_and_power_caps(self):
        for args in ((2,9),(19,8),(4,2),(2,True)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.affine_histogram(*args)
        for args in ((2,8,F(1,100000)),(2,2,F(0)),(2,2,F(1)),(2,2,.5)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.alias_case(*args)
        for args in ((2,14,4),(19,4,2),(2,6,1),(4,5,4)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.strip_case(*args)

    def test_fixed_support_guards_and_independent_exponents(self):
        for r,n in ((6,72),(6,108),(6,216),(10,200),(10,400),(10,1000)):
            self.assertEqual(e.fixed_r_domain(r,n),(r,n))
        for args in ((1,16),(True,16),(33,99),(6,80),(2,80),(6,90),(6,False),(2,2048)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.fixed_support_affine(*args)
        self.assertEqual(e.fixed_r_domain(2,80,support=False),(2,80))
        for kw in ({'cap':True},{'cap':5000},{'support':1}):
            with self.subTest(kw=kw),self.assertRaises(ValueError):e.fixed_r_domain(2,16,**kw)
        self.assertEqual(e.prime_support(1000),(2,5))
        self.assertEqual(e.prime_support(648),(2,3))
        for n in (True,1,4097):
            with self.assertRaises(ValueError):e.prime_support(n)

    def test_full_strip_extra_hypotheses(self):
        # 72 and 108 pass the algebraic support checks but cannot use s=3.
        for args in ((6,72,3),(6,108,3),(6,36,2),(2,80,4),(10,200,True),
                     (10,200,13),(2,512,4),(32,4096,3)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.fixed_support_strip_case(*args)
        for n in (216,432,648):
            self.assertEqual(e.fixed_support_strip_case(6,n,3)['m'],n//216)
        for n in (200,400,1000):
            self.assertEqual(e.fixed_support_strip_case(10,n,2)['m'],n//100)

    def test_unknown_cli_option(self):
        proc=subprocess.run([sys.executable,'-I','-B',str(SCRIPT),'--N','999999'],capture_output=True,timeout=10)
        self.assertEqual(proc.returncode,2);self.assertIn(b'unrecognized arguments',proc.stderr)
        self.assertEqual(proc.stdout,b'')


class AffineAndCarrierTests(unittest.TestCase):
    def test_direct_all_coefficient_pairs(self):
        # Direct triples differ algorithmically from the companion's intercept histogram.
        for p,k in ((2,4),(2,5),(3,3),(5,2),(7,2),(11,2)):
            n=p**k; classmax=globalmax=0
            for slope in range(n):
                for offset in range(n):
                    counts=Counter(x%p for x in range(n) if (slope*x+offset)%n==x//p)
                    classmax=max(classmax,max(counts.values(),default=0))
                    globalmax=max(globalmax,sum(counts.values()))
            observed=e.affine_histogram(p,k)
            self.assertEqual(observed['per_class_max'],classmax)
            self.assertEqual(observed['global_max'],globalmax)
            self.assertEqual((classmax,globalmax),(1,p))

    def test_exact_modular_inverse_identity(self):
        for p,k,n in e.models():
            for slope in range(n):
                self.assertEqual(gcd(1-p*slope,n),1)
                self.assertEqual((1-p*slope)*pow(1-p*slope,-1,n)%n,1)

    def test_wrapping_and_nonproper_lengths(self):
        n,p,start=32,2,31
        points=[(start+p*j)%n for j in range(18)]
        self.assertIn(1,points);self.assertEqual(len(set(points)),16)
        self.assertEqual({x%p for x in points},{1})
        result=e.carrier_checks()
        self.assertEqual(result['carriers'],77328)
        self.assertEqual(result['wrapped_parameterizations'],38664)

    def test_direct_mixed_support_coefficient_pairs(self):
        for r,n in ((4,32),(6,36),(6,72),(6,108),(10,100),(10,200)):
            classmax=globalmax=0
            for slope in range(n):
                for offset in range(n):
                    counts=Counter(x%r for x in range(n) if (slope*x+offset)%n == x//r)
                    classmax=max(classmax,max(counts.values(),default=0))
                    globalmax=max(globalmax,sum(counts.values()))
            observed=e.fixed_support_affine(r,n)
            self.assertEqual((classmax,globalmax),(1,r))
            self.assertEqual(observed['global_max'],globalmax)
            self.assertEqual(observed['per_class_max'],classmax)
            self.assertEqual(observed['affine_maps_covered'],n*n)

    def test_large_independent_exponent_histogram(self):
        result=e.fixed_support_affine(10,1000)
        self.assertEqual((result['global_max'],result['per_class_max']),(10,1))
        self.assertEqual(result['inverse_equation_checks'],1000000)
        self.assertIn((6,72),e.mixed_models());self.assertIn((6,108),e.mixed_models())
        self.assertIn((10,400),e.mixed_models());self.assertIn((10,1000),e.mixed_models())
        for r,n in e.mixed_models():
            self.assertEqual(n%r,0)
            self.assertTrue(set(e.prime_support(n)) <= set(e.prime_support(r)))

    def test_total_floor_rows_may_leave_original_strip(self):
        r,n,m=6,72,1
        strip={r*j for j in range(m)}
        heights={0,1,n-1}; translate=n-1
        rows={((translate+h)%n):{x for x in range(n) if x//r == h%3}
              for h in heights}
        output={(x,y) for y,xs in rows.items() for x in xs}
        self.assertEqual(len(rows),len(heights))
        self.assertEqual(len(output),r*len(heights))
        self.assertTrue(any(x not in strip for x,y in output))
        self.assertTrue(all(len(xs) <= r for xs in rows.values()))
        # Restricting to any forced single residue class improves each row cap to 1.
        for residue in range(r):
            self.assertTrue(all(len({x for x in xs if x%r == residue}) <= 1 for xs in rows.values()))

    def test_outside_support_defeats_both_caps(self):
        result=e.outside_support_boundary()
        self.assertEqual(result['agreements'],[0,32,64])
        self.assertEqual(80%(2**4),0)
        self.assertEqual({x%2 for x in result['agreements']},{0})
        self.assertGreater(len(result['agreements']),2)
        self.assertEqual(gcd(2*3-1,80),5)
        with self.assertRaises(ValueError):e.fixed_support_affine(2,80)

    def test_nonprimepower_boundary(self):
        result=e.composite_boundary()
        self.assertEqual(result['agreements'],[0,4,8,12,16])
        self.assertEqual(gcd(2*5-1,18),9)
        self.assertGreater(len(result['agreements']),1)


class AliasTests(unittest.TestCase):
    def test_enumerated_kernel_and_signed_preimages(self):
        for p,k in ((2,6),(3,3),(5,2),(7,2)):
            n=p**k
            kernel={r for r in range(n) if p*r%n==0}
            self.assertEqual(kernel,{j*(n//p) for j in range(p)})
            for radius in range(5):
                cover={(nu*(n//p)+j)%n for nu in range(p) for j in range(-radius,radius+1)}
                preimages={r for r in range(n) for j in range(-radius,radius+1) if p*(r-j)%n==0}
                self.assertEqual(cover,preimages)

    def test_nonintegral_floor_and_duplicate_cover(self):
        case=e.alias_case(3,2,F(2,51))
        self.assertFalse(case['radius_integral'])
        self.assertEqual(case['K0'],4);self.assertEqual(case['q'],27)
        self.assertEqual(case['distinct_cover'],9)
        exact=e.alias_case(2,6,F(1,32))
        self.assertTrue(exact['radius_integral'])

    def test_mixed_alias_preimages_and_support_independence(self):
        for r,n in ((6,72),(6,108),(10,200),(10,400),(10,1000),(2,80)):
            kernel={freq for freq in range(n) if r*freq%n == 0}
            self.assertEqual(kernel,{nu*(n//r) for nu in range(r)})
            theta=F(2,16*r+3)
            result=e.fixed_r_alias_case(r,n,theta)
            radius=result['K0']
            direct={freq for freq in range(n) for j in range(-radius,radius+1)
                    if r*(freq-j)%n == 0}
            self.assertEqual(result['distinct_cover'],len(direct))
            self.assertEqual(result['q'],r*(2*radius+1))
            self.assertFalse(result['radius_integral'])

    def test_exact_annihilator_coefficient_all_phases_one(self):
        for r,n,m in ((2,32,2),(6,72,7),(6,216,1),(10,400,4),(10,1000,10),(2,80,5)):
            result=e.annihilator_case(r,n,m)
            phases=[[freq*x%n for x in range(0,r*m,r)]
                    for freq in range(0,n,n//r)]
            self.assertTrue(all(row == [0]*m for row in phases))
            self.assertEqual(result['exact_annihilator_coefficient'],n*m)
            self.assertEqual(result['phase_tests'],r*m)
        for args in ((6,72,17),(6,72,13),(6,72,0),(6,72,True),(6,80,1)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.annihilator_case(*args)

    def test_centered_norm_at_cut(self):
        self.assertEqual(e.centered(16,32),16)
        self.assertEqual(e.centered(-16,32),16)
        self.assertEqual(e.centered(31,32),1)
        with self.assertRaises(ValueError):e.centered(True,32)


class SubgroupTests(unittest.TestCase):
    def test_all_image_orders_and_centered_maxima(self):
        for r,n in [(p,n) for p,k,n in e.models()]+list(e.mixed_models()):
            for step in range(n):
                image={step*freq%n for freq in range(n) if r*freq%n == 0}
                order=len(image)
                self.assertEqual(order,r//gcd(r,step))
                # Independent subgroup equation and signed-residue representative.
                self.assertEqual(image,{x for x in range(n) if order*x%n == 0})
                signed=[x if 2*x <= n else x-n for x in image]
                self.assertEqual(max(map(abs,signed)),F(n*(order//2),order))
            result=e.subgroup_case(r,n)
            self.assertEqual(result['steps'],n)
            self.assertEqual(result['trivial_images'],n//r)

    def test_sharp_third_requires_strict_inequality(self):
        result=e.sharp_radius_checks()
        self.assertEqual(result['orders_checked'],127)
        self.assertEqual(result['sharp_radius'],'1/3')
        witness=result['weak_radius_counterexample']
        self.assertEqual(witness,dict(r=6,N=72,step=2,image=[0,24,48]))
        self.assertTrue(all(e.centered(x,72) <= F(72,3) for x in witness['image']))
        self.assertNotEqual(witness['step']%witness['r'],0)

    def test_divisibility_does_not_prescribe_selected_step(self):
        r,n,step=6,216,18
        self.assertEqual({step*nu*(n//r)%n for nu in range(r)},{0})
        self.assertNotEqual(step,r);self.assertGreater(gcd(step,n),1)
        for start in (0,1,n-1):
            carrier={(start+step*j)%n for j in range(n//gcd(step,n)+2)}
            self.assertEqual({x%r for x in carrier},{start%r})
        # The subgroup lemma itself does not need prime support.
        self.assertEqual(e.subgroup_case(2,80)['trivial_images'],40)


class FreimanAndCountTests(unittest.TestCase):
    def test_joint_dp_against_direct_ordered_tuples(self):
        for n,points,values,order in ((18,(0,2),(0,1),8),(18,(0,2),(0,1),9),(9,(0,3,6),(0,1,2),4),(5,(0,1,2),(3,2,4),5)):
            direct=Counter()
            for indices in product(range(len(points)),repeat=order):
                direct[(sum(points[j] for j in indices)%n,sum(values[j] for j in indices)%n)]+=1
            self.assertEqual(e.joint_sums(n,points,values,order),dict(direct))

    def test_binomial_coefficients_against_integer_convolution(self):
        for m in range(1,9):
            for order in range(1,10):
                counts=[1]
                for _ in range(order):
                    new=[0]*(len(counts)+m-1)
                    for i,c in enumerate(counts):
                        for j in range(m):new[i+j]+=c
                    counts=new
                self.assertEqual(counts,[e.interval_coefficient(m,order,t) for t in range(len(counts))])

    def test_full_group_fixed_height_normalization(self):
        for n in (2,3,5,7):
            sums=e.joint_sums(n,tuple(range(n)),(0,)*n,8)
            self.assertEqual(set(sums),{(x,0) for x in range(n)})
            self.assertEqual(set(sums.values()),{n**7})
            energy=sum(c*c for c in sums.values())
            self.assertEqual(energy,n**15)
            self.assertEqual(n**16*energy,n**31)

    def test_order_eight_boundary_and_order_nine_failure(self):
        eight=e.joint_sums(18,(0,2),(0,1),8)
        nine=e.joint_sums(18,(0,2),(0,1),9)
        for x in range(18):self.assertLessEqual(len({y for xx,y in eight if xx==x}),1)
        self.assertIn((0,0),nine);self.assertIn((0,9),nine)
        self.assertEqual(e.strip_case(2,5,4)['m'],2)

    def test_composite_strip_joint_convolution(self):
        for r,n,s in ((4,128,3),(6,432,3),(6,648,3),(10,400,2),(10,1000,2),(15,675,2)):
            result=e.fixed_support_strip_case(r,n,s)
            m=n//r**s
            self.assertLess(8*(m-1),n//r)
            self.assertEqual(result['m'],m)
            self.assertEqual(result['joint_states'],8*(m-1)+1)
            self.assertGreaterEqual(result['additive_energy']*n,m**16)
            self.assertEqual(result['annihilator']['exact_annihilator_coefficient'],n*m)

    def test_guards(self):
        for args in ((1,(0,),(0,),1),(5000,(0,),(0,),1),(5,[0],(0,),1),(5,(0,0),(0,1),1),
                     (5,(0,),(0,1),1),(5,(),(),1),(5,(0,),(True,),1),(5,(0,),(0,),10)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.joint_sums(*args)


class ScaleAndSourceTests(unittest.TestCase):
    def test_all_symbolic_identities(self):
        values=e.symbolic_checks()['identities']
        self.assertEqual(values['theta'],[-59,176])
        self.assertEqual(values['z_numerator_per_K'],[-227,576])
        self.assertEqual(values['b_over_Q13_half'],[-428432,252848])
        self.assertEqual(values['W_times_delta'],[92,-480])
        self.assertEqual(len(values),12)
        self.assertFalse(e.symbolic_checks()['huge_witness_evaluated'])

    def test_exact_floor_and_eight_threshold_pipelines(self):
        self.assertEqual(e.floor_checks()['exact_rational_cases'],20864)
        result=e.surrogate_threshold_checks()
        self.assertIn('not genuine source witnesses',result['scope'])
        self.assertEqual(len(result['cases']),6)
        self.assertTrue(all(x['eight_thresholds'] and x['six_budgets'] for x in result['cases']))

    def test_predecessor_floor_and_natural_boundary(self):
        result=e.predecessor_floor_checks()
        self.assertEqual(result['exact_rational_cases'],25024)
        self.assertEqual(result['length_branches'],47968)
        self.assertEqual(result['positive_width_branches'],16640)
        for x in (F(0),F(1,2),F(1),F(199,100),F(8),F(801,100),F(999,100)):
            m=x.numerator//x.denominator
            for lp in (m,m-1):
                if lp >= 0:
                    self.assertGreater(lp,x-2)
                    if x > 8:self.assertGreater(lp,x/2)
        # Properness alone gives no positivity; zero source lengths must be handled.
        self.assertEqual(F(199,100).numerator//100-1,0)

    def test_constant_separation_uses_only_exponent_margins(self):
        result=e.symbolic_checks()
        margin=result['c_less_than_d_over_eight']
        k=2**114
        self.assertEqual(margin['two_exponent_margin'],1+228*k-620036)
        self.assertEqual(margin['density_exponent_margin'],576*k-1843952)
        self.assertGreater(margin['two_exponent_margin'],0)
        self.assertGreaterEqual(margin['density_exponent_margin'],0)
        self.assertEqual(result['identities']['d_times_pi'],[-620031,1843952])
        self.assertEqual(result['identities']['d_over_eight_lower_using_pi_lt_four'],[-620036,1843952])
        self.assertTrue(all(not row['genuine_constants_evaluated'] for row in result['symbolic_density_examples']))
        self.assertEqual({row['r'] for row in result['symbolic_density_examples']},{2,3,4,5,6,10,11,12,15,19})

    def test_width_only_both_length_branches(self):
        result=e.surrogate_width_only_checks()
        self.assertEqual(result['case_count'],12)
        self.assertIn('toy constants',result['scope'])
        self.assertTrue(result['width_only'])
        self.assertEqual({row['length_branch'] for row in result['cases']},{'floor','predecessor'})
        for row in result['cases']:
            self.assertFalse(row['other_five_budgets_assumed'])
            self.assertTrue(row['positive_initial_length'])
            self.assertEqual(row['normalized_radius_strictly_below'],'1/4')
            u,w,beta=map(F,(row['u'],row['w'],row['beta']))
            self.assertGreater(u*w,beta);self.assertGreater(u,beta)

    def test_five_exact_byte_bindings(self):
        result=e.source_checks()
        self.assertEqual(result['verified_lean_snapshots'],5)
        self.assertEqual(result['commit'],e.COMMIT)
        self.assertFalse(result['lean_compiled'])
        self.assertFalse(result['remote_origin_reverified'])

    def test_mutated_source_or_manifest_rejected(self):
        original=(ROOT/'provenance/source_manifest.json').read_bytes()
        for mode in ('source','digest','url','duplicate','extra','schema','bytes-bool'):
            with self.subTest(mode=mode),tempfile.TemporaryDirectory(prefix='report283-source-') as tmp:
                root=Path(tmp);(root/'provenance/sources').mkdir(parents=True)
                for source in (ROOT/'provenance/sources').glob('*.lean'):
                    (root/'provenance/sources'/source.name).write_bytes(source.read_bytes())
                manifest=json.loads(original)
                if mode=='source':
                    path=root/'provenance/sources/Definitions.lean';path.write_bytes(path.read_bytes()+b'\n')
                elif mode=='digest':manifest['sources'][0]['sha256']='0'*64
                elif mode=='url':manifest['sources'][0]['verified_url']='https://example.invalid/source'
                elif mode=='duplicate':manifest['sources'][1]=manifest['sources'][0]
                elif mode=='extra':(root/'provenance/sources/extra.lean').write_text('extra')
                elif mode=='schema':manifest['schema']='wrong'
                else:manifest['sources'][0]['bytes']=True
                (root/'provenance/source_manifest.json').write_text(json.dumps(manifest))
                with patch.object(e,'ROOT',root),self.assertRaises(RuntimeError):e.source_checks()


if __name__=='__main__':
    unittest.main()
