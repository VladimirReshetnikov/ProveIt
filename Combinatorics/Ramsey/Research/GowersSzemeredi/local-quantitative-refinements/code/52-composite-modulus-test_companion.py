"""Independent finite-model and strict-interface regressions for Report280."""
import sys
sys.dont_write_bytecode=True
import ast
from collections import Counter
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import subprocess
import unittest
from unittest.mock import patch
ROOT=Path(__file__).absolute().parents[1]
COMPANION=ROOT/'companion/exact_checks.py'
spec=importlib.util.spec_from_file_location('report280_checks',COMPANION)
e=importlib.util.module_from_spec(spec);spec.loader.exec_module(e)


class ExponentTests(unittest.TestCase):
    def test_fixed_exponents(self):
        d=e.exponent_diagnostics()['integer_identities']
        self.assertEqual((d['delta'],d['lambda_'],d['epsilon']),(939,1072,1892))
        self.assertEqual(d['t'],1363892)
        self.assertEqual(d['Q134_log2'],d['t']+260)
        self.assertEqual(d['Q13_log2'],9437184)
        self.assertTrue(all(type(s) is str for s in e.symbolic_constants().values()))
        self.assertFalse(e.exponent_diagnostics()['huge_witness_evaluated'])

    def test_full_budget_symbolic_margins(self):
        d=e.budget_diagnostics()
        self.assertEqual(d['integer_identities']['cutoff'],763)
        self.assertEqual(d['integer_identities']['zeta_multiplier'],2531)
        self.assertEqual(d['integer_identities']['width_log2'],2951)
        self.assertEqual(d['rational_floor_cases'],15360)
        self.assertEqual(d['symbolic_margins'],['beta<sigma','sigma<u','2sigma<1','sigma<uw<1'])

    def test_guarded_small_power_only(self):
        self.assertEqual(e.pow2_small(0),1)
        self.assertEqual(e.pow2_small(30),1073741824)
        for value in (True,False,-1,31,128,1892,1363892,1.0,'1',None):
            with self.subTest(value=value),self.assertRaises(ValueError):e.pow2_small(value)
        tree=ast.parse(COMPANION.read_text())
        self.assertFalse(any(isinstance(n,ast.Assert) for n in ast.walk(tree)))
        calls={n.func.id for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name)}
        self.assertFalse(calls & {'eval','exec','compile','pow','float'})
        shifts=[n for n in ast.walk(tree) if isinstance(n,ast.BinOp) and isinstance(n.op,ast.LShift)]
        self.assertEqual(len(shifts),1)
        self.assertNotIn('set_int_max_str_digits(',COMPANION.read_text())
        with self.assertRaises(RuntimeError):e.require(False,'must survive -O')


class FreimanTests(unittest.TestCase):
    def test_convolution_against_direct_ordered_tuples(self):
        for modulus,points,values,order in ((7,(0,2),(0,1),8),(9,(0,3,6),(0,1,2),4),(5,(0,1,2),(2,1,3),5)):
            direct=Counter()
            for indices in product(range(len(points)),repeat=order):
                direct[(sum(points[i] for i in indices)%modulus,sum(values[i] for i in indices)%modulus)]+=1
            self.assertEqual(e.joint_sum_counts(modulus,points,values,order),dict(direct))
            diag=e.freiman_diagnostic(modulus,points,values,order)
            by_domain=Counter()
            for (x,y),n in direct.items():by_domain[x]+=n
            self.assertEqual(diag['additive_energy'],sum(v*v for v in by_domain.values()))

    def test_z18_detects_ninth_order_failure(self):
        self.assertTrue(e.freiman_diagnostic(18,(0,2),(0,1),8)['freiman'])
        self.assertFalse(e.freiman_diagnostic(18,(0,2),(0,1),9)['freiman'])
        self.assertEqual(e.joint_sum_counts(18,(0,2),(0,1),9)[(0,0)],1)
        self.assertEqual(e.joint_sum_counts(18,(0,2),(0,1),9)[(0,9)],1)

    def test_full_group_normalization(self):
        for n in (2,3,5):
            d=e.freiman_diagnostic(n,tuple(range(n)),(0,)*n,8)
            self.assertEqual(d['domain_counts'],(n**7,)*n)
            self.assertEqual(d['additive_energy'],n**15)
            self.assertEqual(d['fixed_height_arrangements'],n**31)

    def test_graph_and_order_caps(self):
        for args in ((1,(0,),(0,),1),(1025,(0,),(0,),1),(5,[0],(0,),1),
                     (5,(0,0),(0,1),1),(5,(0,),(1,2),1),(5,(True,),(0,),1),
                     (5,(0,),(5,),1),(5,(),(),1),(5,(0,),(0,),0),(5,(0,),(0,),10),
                     (5,(0,),(0,),True)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.joint_sum_counts(*args)
        with patch.object(e,'MAX_JOINT_STATES',1),self.assertRaises(ValueError):
            e.joint_sum_counts(5,(0,1),(0,1),1)


class AffineTests(unittest.TestCase):
    def test_against_direct_slopes_and_intercepts(self):
        for n,points,values in ((18,(0,2),(0,1)),(8,(0,1,2,3),(0,0,1,1)),(7,(0,1,2),(1,3,5))):
            expected=max(sum((a*x+b)%n==f for x,f in zip(points,values)) for a in range(n) for b in range(n))
            self.assertEqual(e.max_affine_agreement(n,points,values),expected)

    def test_prime_power_models_and_parity_caps(self):
        for row in ((2,5,2),(2,8,16),(3,4,3),(5,3,3),(7,3,3)):
            d=e.prime_power_model(*row)
            self.assertEqual(d['strip_max_agreement'],1)
            self.assertEqual(d['unit_interval_max_agreement'],row[0])
            self.assertTrue(d['order_eight'])

    def test_prime_power_parameter_caps(self):
        for args in ((True,5,2),(4,3,2),(11,2,1),(2,1,1),(2,11,1),(7,10,1),(2,5,17),(2,5,4),(2,5,0)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.prime_power_model(*args)

    def test_unit_condition_is_not_generic_composite_claim(self):
        # 2a-1 is a zero divisor at a=2 modulo 15; cancellation cannot be generalized blindly.
        self.assertEqual((3*5)%15,0)
        self.assertEqual(e.max_affine_agreement(15,(0,10),(0,5)),2)


class AliasAndCongruenceTests(unittest.TestCase):
    def test_aliases_by_explicit_preimages(self):
        for n in (18,32,64):
            for radius in (0,1,2):
                expected=set()
                for s in range(-radius,radius+1):
                    expected.update(r for r in range(n) if (2*r-2*s)%n==0)
                self.assertEqual(set(e.alias_set(n,radius)),expected)
        self.assertEqual(e.alias_set(18,0),(0,9))

    def test_alias_caps(self):
        for args in ((3,0),(17,1),(1025,1),(32,8),(32,-1),(32,True),(32,17)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.alias_set(*args)

    def test_exact_gcd_solutions(self):
        self.assertEqual(e.congruence_solutions(18,2,1),())
        self.assertEqual(e.congruence_solutions(18,2,2),(1,10))
        self.assertEqual(e.congruence_solutions(7,0,0),tuple(range(7)))
        self.assertEqual(e.congruence_solutions(7,0,1),())
        for n in range(2,20):
            for d in range(n):
                for out in range(n):
                    solutions=e.congruence_solutions(n,d,out)
                    self.assertEqual(solutions,tuple(a for a in range(n) if (d*a)%n==out))
        for args in ((65,1,1),(7,7,0),(7,0,7),(7,True,1)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.congruence_solutions(*args)

    def test_fixed_diagnostic_inventory(self):
        d=e.small_model_diagnostics()
        self.assertEqual(len(d['prime_power_models']),7)
        self.assertEqual(d['alias_models'],16)
        self.assertEqual(d['congruence_models'],4899)


class SourceTests(unittest.TestCase):
    def fixture(self):
        raw=b'precise\r\nsource\n'
        git=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        path='Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean'
        commit='a'*40
        row=dict(file='sources/Definitions.lean',repository_path=path,commit=commit,
                 bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),git_blob=git,
                 verified_url='https://github.com/VladimirReshetnikov/ProveIt/blob/'+commit+'/'+path)
        return raw,row

    def test_exact_byte_validation_and_line_endings(self):
        raw,row=self.fixture(); self.assertEqual(e.verify_source_bytes(raw,row),row['git_blob'])
        with self.assertRaises(RuntimeError): e.verify_source_bytes(raw.replace(b'\r\n',b'\n'),row)

    def test_corrupt_hashes_urls_and_unbounded_records_fail(self):
        raw,original=self.fixture()
        for change in ({'sha256':'0'*64},{'git_blob':'0'*40},{'bytes':len(raw)+1},
                       {'bytes':True},{'file':'../Definitions.lean'},
                       {'commit':'main'},{'verified_url':'https://example.com/file'},
                       {'repository_path':'somewhere/Definitions.lean'},{'extra':'unrequested'}):
            row=dict(original);row.update(change)
            with self.subTest(change=change),self.assertRaises((ValueError,RuntimeError)):
                e.verify_source_bytes(raw,row)

    def test_manifest_exact_inventory_and_duplicate_guards(self):
        raw,row=self.fixture()
        manifest=dict(schema='report280-curated-sources-v1',scope='test fixture',
                      sources=[row],unchanged_at_later_pins=[])
        files={'provenance/sources/Definitions.lean':raw}
        self.assertEqual(e.validate_source_manifest(manifest,files),(1,0))
        for mode in ('duplicate','missing','extra','later-missing','extra-key'):
            copy=json.loads(json.dumps(manifest));data=files.copy()
            if mode=='duplicate':copy['sources'].append(row)
            elif mode=='missing':data.clear()
            elif mode=='extra':data['provenance/sources/Extra.lean']=raw
            elif mode=='later-missing':copy['unchanged_at_later_pins']=[dict(row,file='sources/Extra.lean')]
            else:copy['unknown']='value'
            with self.subTest(mode=mode),self.assertRaises((ValueError,RuntimeError)):
                e.validate_source_manifest(copy,data)

    def test_frozen_source_inventory(self):
        result=e.source_diagnostics()
        self.assertEqual(result['verified_lean_snapshots'],5)
        self.assertEqual(result['unchanged_later_pin_checks'],0)
        self.assertEqual(result['provenance_files'],6)
        self.assertEqual(len(result['pins']),1)


class CommandTests(unittest.TestCase):
    def test_unknown_cli_option_is_rejected(self):
        result=subprocess.run([sys.executable,'-I','-B',str(COMPANION),'--modulus','999999999'],
                              capture_output=True,timeout=10)
        self.assertEqual(result.returncode,2)
        self.assertIn(b'unrecognized arguments',result.stderr)
        self.assertEqual(result.stdout,b'')


if __name__ == '__main__':
    unittest.main()
