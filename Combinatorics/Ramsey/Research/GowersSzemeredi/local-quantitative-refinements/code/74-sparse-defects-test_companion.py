"""Exact mathematical boundaries, failure controls, source pins and optimized replay."""
import sys
sys.dont_write_bytecode = True
import ast
import base64
from contextlib import redirect_stdout
from fractions import Fraction as Q
import hashlib
import importlib.util
from io import StringIO
from itertools import product
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).absolute().parents[1]
SPEC = importlib.util.spec_from_file_location('report286_exact',ROOT/'companion/exact_checks.py')
c = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(c)


class ExactInputTests(unittest.TestCase):
    def test_rational_types_and_bit_boundaries(self):
        self.assertEqual(c.rational(-2),Q(-2))
        self.assertEqual(c.rational(Q(1,3)),Q(1,3))
        self.assertEqual(c.rational((1 << c.MAX_BITS)-1),(1 << c.MAX_BITS)-1)
        self.assertEqual(c.rational(Q(1,(1 << c.MAX_BITS)-1)),Q(1,(1 << c.MAX_BITS)-1))
        for value in (True,False,'2',None,2.0,1j,1 << c.MAX_BITS,Q(1,1 << c.MAX_BITS)):
            with self.subTest(type=type(value).__name__), self.assertRaises(ValueError):
                c.rational(value)

    def test_ceil_negative_zero_and_positive(self):
        for value,expected in ((Q(-3,2),-1),(Q(-2),-2),(Q(0),0),(Q(1,3),1),(Q(3,2),2)):
            self.assertEqual(c.ceil_fraction(value),expected)
        with self.assertRaises(ValueError): c.ceil_fraction(True)

    def test_no_asserts_or_inexact_arithmetic(self):
        tree = ast.parse((ROOT/'companion/exact_checks.py').read_text())
        self.assertFalse(any(isinstance(node,ast.Assert) for node in ast.walk(tree)))
        self.assertFalse(any(isinstance(node,ast.Constant) and type(node.value) in (float,complex)
                             for node in ast.walk(tree)))
        self.assertFalse(any(isinstance(node,ast.Name) and node.id in ('float','complex','random')
                             for node in ast.walk(tree)))
        with self.assertRaisesRegex(RuntimeError,'live'): c.require(False,'live')

    def test_cli_rejects_all_inputs_before_work(self):
        for argv in (None,'',('x',),['--help'],['--size','1000000000'],{},42):
            with self.subTest(argv=argv):
                if argv is None:
                    with patch.object(sys,'argv',['check','unexpected']), self.assertRaises(SystemExit): c.main()
                else:
                    with self.assertRaises(SystemExit): c.main(argv)
        with patch.object(c,'run_all',return_value={'status':'sample'}):
            capture = StringIO()
            with redirect_stdout(capture): self.assertEqual(c.main([]),0)
            self.assertEqual(json.loads(capture.getvalue()),{'status':'sample'})


class ArithmeticTests(unittest.TestCase):
    def test_logarithm_endpoints_and_nested_enclosures(self):
        self.assertEqual(c.ln_unit_bounds(1),(Q(0),Q(0)))
        self.assertEqual(c.ln_integer_bounds(1),(Q(0),Q(0)))
        low1,high1 = c.ln_unit_bounds(2,1)
        low2,high2 = c.ln_unit_bounds(2,10)
        self.assertLess(low1,low2)
        self.assertLess(high2,high1)
        self.assertLessEqual(low2,high2)
        low,high = c.ln_integer_bounds(8,10)
        self.assertEqual((low,high),(3*low2,3*high2))
        for value in (0,Q(1,2),3,True,2.0,'2'):
            with self.assertRaises(ValueError): c.ln_unit_bounds(value)
        for terms in (0,129,True,Q(1),'1'):
            with self.assertRaises(ValueError): c.ln_unit_bounds(2,terms)
            with self.assertRaises(ValueError): c.ln_integer_bounds(2,terms)
        for value in (0,-1,True,Q(2),2.0,'2',1 << c.MAX_BITS):
            with self.assertRaises(ValueError): c.ln_integer_bounds(value)

    def test_threshold_golden_and_vacuous_boundaries(self):
        rows = c.check_thresholds()['examples']
        self.assertEqual([row['L0'] for row in rows],[12599,13486,28747,61042,896101,10735464])
        self.assertGreater(c.exact_L0(6,2),6)
        self.assertLessEqual(c.exact_L0(32768,2),16384)
        for args in ((5,2),(6,1),(6,3),(True,2),(6,True),(Q(6),2),(1 << 41,2)):
            with self.assertRaises(ValueError): c.exact_L0(*args)

    def test_coset_period_two_and_repeated_prefix(self):
        row = c.active_position_certificate(6,2,3,0,17)
        self.assertEqual(row['order'],2)
        self.assertEqual(row['coset_hits'],1)
        self.assertEqual(row['active_positions'],9)
        self.assertEqual(c.active_position_certificate(6,2,3,0,0)['active_positions'],0)
        self.assertEqual(c.active_position_certificate(6,2,3,0,c.MAX_PREFIX)['active_positions'],c.MAX_PREFIX//2)
        for N in range(6,19):
            for R in range(2,N//3+1):
                for delta in range(1,N):
                    for intercept in range(N):
                        length = 2*N+1
                        row = c.active_position_certificate(N,R,delta,intercept,length)
                        self.assertEqual(row['active_positions'],sum((intercept+delta*t) % N < R for t in range(length)))

    def test_active_certificate_rejects_noninterval_hypotheses(self):
        for args in ((5,2,1,0,1),(6,3,1,0,1),(6,2,0,0,1),(6,2,6,0,1),
                     (6,2,1,-1,1),(6,2,1,6,1),(6,2,1,0,-1),(6,2,1,0,c.MAX_PREFIX+1),
                     (True,2,1,0,1),(6,True,1,0,1),(6,2,True,0,1),(6,2,1,True,1),(6,2,1,0,True)):
            with self.assertRaises(ValueError): c.active_position_certificate(*args)

    def test_binomial_exact_rounding_and_empty_intervals(self):
        self.assertEqual(c.binomial_probability(2,2,0,0),Q(1,4))
        self.assertEqual(c.binomial_probability(2,2,0,2),1)
        self.assertEqual(c.binomial_probability(0,2,0,0),1)
        self.assertEqual(c.binomial_probability(0,2,1,0),0)
        self.assertEqual(c.binomial_probability(2,2,0,-1),0)
        for args in ((-1,2,0,0),(1025,2,0,0),(1,1,0,0),(1,65,0,0),
                     (1,2,-1,0),(1,2,3,0),(1,2,0,-2),(1,2,0,2),(True,2,0,0),(2,True,0,0)):
            with self.assertRaises(ValueError): c.binomial_probability(*args)

    def test_tail_certificates_are_exact_and_strict_endpoints(self):
        result = c.check_tails()
        self.assertEqual(result['cases'],105)
        for row in result['certificates']:
            probability = c.binomial_probability(row['trials'],row['R'],row['first'],row['last'])
            self.assertEqual(row['probability'],probability)
            self.assertLessEqual(probability,row['exponential_lower_base']**row['exponential_lower_power'])
            if row['event'] == 'symbol_lower':
                self.assertLess(row['last'],Q(7*row['L'],8*row['R']))
                self.assertGreaterEqual(row['last']+1,Q(7*row['L'],8*row['R']))
            else:
                numerator = 5 if row['event'] == 'symbol_upper' else 3
                threshold = Q(numerator*row['L'],4*row['R'])
                self.assertGreater(row['first'],threshold)
                self.assertLessEqual(row['first']-1,threshold)

    def test_cube_root_exact_and_irrational_certificates(self):
        for value in (Q(0),Q(1,8),Q(1),Q(8),Q(2),Q(7,3)):
            for bits in (0,1,24,64):
                lo,hi = c.cube_root_bounds(value,bits)
                self.assertLessEqual(lo**3,value)
                self.assertGreaterEqual(hi**3,value)
                self.assertLessEqual(hi-lo,Q(1,1 << bits))
        self.assertEqual(c.cube_root_bounds(Q(1,8)),(Q(1,2),Q(1,2)))
        for value in (-1,True,0.5,'1',None):
            with self.assertRaises(ValueError): c.cube_root_bounds(value)
        for bits in (-1,65,True,Q(1)):
            with self.assertRaises(ValueError): c.cube_root_bounds(2,bits)


class ListTests(unittest.TestCase):
    def test_nonunit_aliases_duplicates_and_outside_constants(self):
        word = (0,)*10+(1,)*10
        optimum = c.affine_list_coverage(40,2,0,2,word,((20,0),(20,1)))
        self.assertEqual(optimum['covered'],20)
        self.assertEqual(optimum['distinct_useful_constants'],(0,1))
        self.assertTrue(all(row['constant'] for row in optimum['restrictions']))
        duplicate = c.affine_list_coverage(40,2,0,2,word,((0,0),(20,0)))
        self.assertEqual(duplicate['covered'],10)
        self.assertEqual(duplicate['distinct_useful_constants'],(0,))
        outside = c.affine_list_coverage(40,2,0,2,word,((0,2),))
        self.assertEqual(outside['covered'],0)
        self.assertEqual(outside['distinct_useful_constants'],())
        self.assertIsNone(outside['restrictions'][0]['useful_value'])

    def test_singleton_zero_step_and_empty_list(self):
        row = c.affine_list_coverage(6,2,3,0,(1,),((3,4),))
        self.assertEqual(row['covered'],1)
        self.assertTrue(row['restrictions'][0]['constant'])
        self.assertEqual(c.affine_list_coverage(1,1,0,0,(0,),())['covered'],0)
        self.assertEqual(c.affine_list_coverage(1,1,0,0,(0,),((0,0),))['covered'],1)
        self.assertEqual(c.affine_list_coverage(2,1,0,1,(0,0),((0,0),)*64)['covered'],2)

    def test_reject_improper_or_malformed_lists(self):
        bad = ((6,2,0,0,(0,1),()),(6,2,0,2,(0,1,0,1),()),(6,2,0,1,(),()),
               (6,2,0,1,(2,),()),(6,2,0,1,(True,),()),(6,2,0,1,(0,),((6,0),)),
               (6,2,0,1,(0,),((0,),)),(6,2,0,1,(0,),((0,0,0),)),
               (6,2,0,1,(0,),((True,0),)),(6,2,0,1,(0,),((0,0),)*65),
               (6,2,0,1,iter((0,)),()),(6,2,0,1,(0,),iter(())),
               (257,2,0,1,(0,),()),(6,7,0,1,(0,),()),(6,2,6,1,(0,),()),(6,2,0,6,(0,),()))
        for args in bad:
            with self.subTest(args=repr(args)[:70]), self.assertRaises(ValueError): c.affine_list_coverage(*args)

    def test_small_lists_match_independent_pointwise_union(self):
        for N in (2,3,4,6):
            word = tuple(x % 2 for x in range(N))
            for a,b,c0,d in product(range(N),repeat=4):
                branches = ((a,b),(c0,d))
                row = c.affine_list_coverage(N,2,0,1,word,branches)
                expected = sum(any((alpha*x+beta) % N == word[x] for alpha,beta in branches) for x in range(N))
                self.assertEqual(row['covered'],expected)

    def test_subgroup_alphabet_failure(self):
        result = c.check_alphabet_boundary()
        self.assertEqual(result['words'],5440)
        self.assertEqual(result['balanced_words'],1266)


class EnergyTests(unittest.TestCase):
    @staticmethod
    def independent_four_index_energy(N,values,weights):
        return sum((weights[x]*weights[y]*weights[z]*weights[t]
                    for x,y,z,t in product(range(N),repeat=4)
                    if (x+y-z-t) % N == 0 and (values[x]+values[y]-values[z]-values[t]) % N == 0),Q(0))

    def test_ordered_quadruples_match_independent_enumeration(self):
        for N in (1,2,3,4,6):
            for values in ((0,)*N,tuple(x*x % N for x in range(N))):
                weights = tuple(Q(x+1,x+2) for x in range(N))
                self.assertEqual(c.respected_energy(N,values,weights),
                                 self.independent_four_index_energy(N,values,weights))

    def test_disjoint_families_noninterval_and_empty_support(self):
        for N,values,support in ((1,(0,),()),(4,(0,2,0,1),(1,3)),(6,(1,2,0,0,0,0),(0,1))):
            for weights in ((0,)*N,(1,)*N,tuple(Q(x+1,x+2) for x in range(N))):
                row = c.sparse_energy_certificate(N,values,weights,support)
                self.assertGreaterEqual(row['energy'],row['outside_energy']+row['inside_diagonal'])
                self.assertGreaterEqual(row['outside_energy']+row['inside_diagonal'],row['disjoint_lower'])
                self.assertGreaterEqual(row['disjoint_lower'],row['holder_lower'])
        self.assertEqual(c.sparse_energy_certificate(2,(0,0),(1,1),())['energy'],8)
        self.assertEqual(c.sparse_energy_certificate(2,(1,1),(1,1),(0,1))['outside_energy'],0)

    def test_empty_nonempty_and_constant_families(self):
        result = c.check_family_energy()
        self.assertEqual((result['empty_family'],result['single_map'],result['repeated_map'],result['constant_maps']),
                         (64,34,34,64))
        self.assertEqual(c.simultaneous_energy(1,(),(1,)),1)
        self.assertEqual(c.simultaneous_energy(2,((0,0),)*8,(1,1)),8)
        self.assertEqual(c.simultaneous_energy(4,((0,1,2,3),(0,2,0,2)),(1,)*4),64)

    def test_energy_input_guards(self):
        bad = ((0,(),()),(17,(0,)*17,(0,)*17),(True,(0,),(1,)),(2,(0,),(1,1)),
               (2,(0,0),(1,)),(2,(0,2),(1,1)),(2,(0,True),(1,1)),(2,(0,0),(1,-1)),
               (2,(0,0),(True,1)),(2,(0,0),(1.0,1)),(2,(0,0),(1,Q(1,1 << c.MAX_BITS))))
        for args in bad:
            with self.subTest(args=repr(args)[:70]), self.assertRaises(ValueError): c.respected_energy(*args)
        for support in ((0,0),(2,),(-1,),(True,),iter((0,)),tuple(range(17))):
            with self.assertRaises(ValueError): c.sparse_energy_certificate(2,(0,0),(1,1),support)
        with self.assertRaisesRegex(ValueError,'vanish'): c.sparse_energy_certificate(2,(1,0),(1,1),())
        for family in (((0,0),)*9,((0,),),((0,True),),iter(()),None):
            with self.assertRaises(ValueError): c.simultaneous_energy(2,family,(1,1))

    def test_holder_identity_and_sharp_equality(self):
        result = c.check_holder_identity()
        self.assertEqual(result['positive_factor_terms'],9)
        self.assertEqual(result['equality_example']['coefficient'],Q(8,27))
        for A,B,t in product((Q(0),Q(1,2),Q(1),Q(3)),repeat=3):
            lhs = (1+t)**3*(t**3*A**4+B**4)-t**3*(A+B)**4
            rhs = (t*A-B)**2*(t*t*(t*t+3*t+3)*A*A+2*t*(t*t+3*t+1)*A*B+(3*t*t+3*t+1)*B*B)
            self.assertEqual(lhs,rhs)
            self.assertGreaterEqual(lhs,0)


class CoverAndIdentityTests(unittest.TestCase):
    def test_cover_budget_boundaries(self):
        self.assertEqual(c.local_cover_ratio(0,2),0)
        self.assertEqual(c.local_cover_ratio(2,8),Q(5,16))
        self.assertEqual(c.local_cover_ratio(100,2),1)
        for args in ((-1,2),(True,2),(1.0,2),(1,0),(1,True),(1,1 << 41)):
            with self.assertRaises(ValueError): c.local_cover_ratio(*args)
        result = c.check_cover_ratios()
        self.assertEqual(result['total_area'],40)
        self.assertEqual(result['covered_mass_bound'],Q(25,2))
        self.assertEqual(result['prime_scale_margin'],Q(727,9))
        self.assertEqual(result['all_moduli_scale_margin'],Q(119,9))
        self.assertEqual(result['independent_line_cover_counts'],dict(qGamma=8,qDelta=1,QGamma=8,QDelta=1))

    def test_gamma_one_endpoint_finite_control(self):
        result = c.check_gamma_one_boundary()
        self.assertEqual([row['full_energy_words'] for row in result['rows']],[1,4,9,16,25])
        self.assertEqual(sum(row['words'] for row in result['rows']),3413)

    def test_general_dimensions_without_astronomical_evaluation(self):
        result = c.check_general_dimensions()
        self.assertEqual(len(result['dimensions']),32)
        for row in result['dimensions']:
            k = row['k']
            self.assertGreaterEqual(row['iteration_inner_exponent'],k+10)
            self.assertGreaterEqual(row['iteration_log2_lower'],row['target_log2_two_E'])
            self.assertEqual(row['global_arrangement_exponent'],17*k+15)
            self.assertEqual(row['fixed_side_arrangement_exponent'],16*k+15)
            self.assertEqual(row['cube_domain_exponent'],k+1)
        for row in result['boolean_rows']:
            self.assertEqual(row['alternating_sum'],0)
            self.assertEqual(row['remainder_coefficient'],1)
            self.assertEqual(row['vertices'],2**row['k'])
        for row in result['geometry_rows']:
            self.assertEqual(row['zero_fourier'],row['N']**(row['k']+1))
            self.assertEqual(row['deleted_slab_fraction'],Q(2,row['N']))
        self.assertEqual(c.dimension_certificate(32)['target_log2_two_E'],1+2**41)
        for k in (0,-1,33,True,Q(1),1.0,'1',None):
            with self.assertRaises(ValueError): c.dimension_certificate(k)

    def test_named_cube_arrangement_and_fourier_identities(self):
        result = c.check_named_identities()
        self.assertEqual(result['cube_identity_cases'],2025)
        for row in result['domain_rows']:
            self.assertEqual(row['good_pairs'],row['N']**2)
            self.assertEqual(row['arrangements_fixed_side'],row['N']**31)
            self.assertEqual(row['arrangements_global'],row['N']**32)
        self.assertEqual(result['arrangement_rows'][-1]['cross_section_completions'],32768)
        for row in result['spectrum_rows']:
            self.assertEqual(row['transform'],row['N']**2 if row['frequency'] == 0 else 0)


class ProvenanceTests(unittest.TestCase):
    def copy_sources(self,directory):
        target = Path(directory)/'package'
        shutil.copytree(ROOT/'provenance',target/'provenance')
        return target

    def test_raw_base64_and_git_pins(self):
        result = c.check_sources()
        self.assertEqual(result['snapshots'],5)
        self.assertEqual(result['raw_git_blob_hashes'],4)
        for row in c.EXPECTED_SOURCES:
            raw = (ROOT/'provenance/sources'/row['name']).read_bytes()
            self.assertEqual(hashlib.sha256(base64.b64encode(raw)).hexdigest(),row['canonical_base64_sha256'])

    def test_raw_corruption_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            target = self.copy_sources(directory)
            source = target/'provenance/sources/Definitions.lean'
            source.write_bytes(source.read_bytes()+b'\n')
            with patch.object(c,'ROOT',target), self.assertRaisesRegex(RuntimeError,'raw source'):
                c.check_sources()

    def test_coherent_retargeting_and_representation_changes_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            target = self.copy_sources(directory)
            source = target/'provenance/sources/Definitions.lean'
            raw = source.read_bytes()+b'\n'
            source.write_bytes(raw)
            manifest_path = target/'provenance/source_manifest.json'
            manifest = json.loads(manifest_path.read_bytes())
            row = manifest[0]
            row.update(bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),
                canonical_base64_sha256=hashlib.sha256(base64.b64encode(raw)).hexdigest(),
                git_blob_sha1=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(),
                commit='0'*40,url=row['url'].replace(row['commit'],'0'*40))
            manifest_path.write_text(json.dumps(manifest))
            with patch.object(c,'ROOT',target), self.assertRaisesRegex(RuntimeError,'manifest'):
                c.check_sources()
        with tempfile.TemporaryDirectory() as directory:
            target = self.copy_sources(directory)
            manifest_path = target/'provenance/source_manifest.json'
            manifest_path.write_bytes(manifest_path.read_bytes()+b'\n')
            with patch.object(c,'ROOT',target), self.assertRaisesRegex(RuntimeError,'manifest'):
                c.check_sources()

    def test_oversized_manifest_and_special_files_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            target = self.copy_sources(directory)
            manifest = target/'provenance/source_manifest.json'
            manifest.write_bytes(b' '*(32768+1))
            with patch.object(c,'ROOT',target), self.assertRaisesRegex(RuntimeError,'bounded'):
                c.check_sources()
        with tempfile.TemporaryDirectory() as directory:
            target = self.copy_sources(directory)
            source = target/'provenance/sources/Definitions.lean'
            source.unlink()
            source.symlink_to(ROOT/'provenance/sources/Definitions.lean')
            with patch.object(c,'ROOT',target), self.assertRaisesRegex(RuntimeError,'ordinary'):
                c.check_sources()
        with tempfile.TemporaryDirectory() as directory:
            target = self.copy_sources(directory)
            sources = target/'provenance/sources'
            shutil.rmtree(sources)
            sources.symlink_to(ROOT/'provenance/sources',target_is_directory=True)
            with patch.object(c,'ROOT',target), self.assertRaises(OSError): c.check_sources()
        with tempfile.TemporaryDirectory() as directory:
            target = self.copy_sources(directory)
            source = target/'provenance/sources/Definitions.lean'
            os.link(source,target/'alias')
            with patch.object(c,'ROOT',target), self.assertRaisesRegex(RuntimeError,'single-link'): c.check_sources()
        with tempfile.TemporaryDirectory() as directory:
            target = self.copy_sources(directory)
            source = target/'provenance/sources/Definitions.lean'
            source.unlink()
            os.mkfifo(source)
            with patch.object(c,'ROOT',target), self.assertRaisesRegex(RuntimeError,'ordinary'): c.check_sources()


class ReplayTests(unittest.TestCase):
    def test_normal_optimized_and_different_cwd_are_byte_identical(self):
        script = str(ROOT/'companion/exact_checks.py')
        with tempfile.TemporaryDirectory() as directory:
            normal = subprocess.run([sys.executable,'-B',script],cwd=directory,check=True,
                capture_output=True,timeout=180).stdout
            optimized = subprocess.run([sys.executable,'-O','-B',script],cwd=directory,check=True,
                capture_output=True,timeout=180).stdout
        self.assertEqual(normal,optimized)
        result = json.loads(normal)
        self.assertEqual(result['status'],'PASS')
        self.assertEqual(result['report'],286)
        self.assertEqual(result['lists']['lists'],1282400)
        self.assertEqual(result['lists']['optimizers'],{'1':4,'2':4})
        self.assertEqual(result['sparse_energy']['binary_weight_cases'],9664)
        self.assertEqual(result['sparse_energy']['rational_weight_cases'],15)
        self.assertEqual(result['sources']['snapshots'],5)


if __name__ == '__main__':
    unittest.main()
