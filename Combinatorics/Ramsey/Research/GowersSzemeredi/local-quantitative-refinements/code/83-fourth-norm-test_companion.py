#!/usr/bin/env python3
"""Adversarial standard-library tests for Report295; no packages/network needed."""
from __future__ import annotations
import sys
sys.dont_write_bytecode=True
import ast
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from companion import exact_checks as c
SCRIPT=ROOT/'companion'/'exact_checks.py'
CERT=SCRIPT.with_name('interval_certificate.json')


def invoke(script=SCRIPT,arguments=(),optimized=False,cwd=None):
    command=[sys.executable,'-I','-B','-S']
    if optimized: command.append('-O')
    return subprocess.run(command+[str(script),*arguments],cwd=cwd,stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE,timeout=60,check=False)


class PolynomialTests(unittest.TestCase):
    def test_all_general_formal_identities(self):
        labels=c.polynomial_checks()+c.spectral_algebra_checks()
        self.assertEqual(len(labels),54)
        self.assertEqual(len(set(labels)),54)

    def test_false_identity_is_rejected(self):
        x=c.P('x')
        with self.assertRaises(RuntimeError): c.verify_identity('changed coefficient',(x+1)**4,x**4+4*x**3+6*x*x+5*x+1)

    def test_formal_vs_sampled_nonidentity(self):
        x=c.P('x'); bad=x*(x-1)*(x-2)
        for i in range(3): self.assertEqual(bad.evaluate({'x':i}),0)
        with self.assertRaises(RuntimeError): c.verify_identity('vanishes on grid only',bad,0)

    def test_polynomial_derivative_substitution_coefficient(self):
        x,y=c.P('x'),c.P('y')
        p=(x+y)**4
        self.assertEqual(p.derivative('x'),4*(x+y)**3)
        self.assertEqual(c.substitute(p,'x',-y),0)
        self.assertEqual(c.coefficient(p,'x',2),6*y*y)

    def test_immutable_coefficient_map(self):
        p=c.P('x')
        with self.assertRaises(TypeError): p.terms[('x',)]=2

    def test_constructor_copies_input(self):
        data={('x',):F(1,2)}; p=c.Polynomial(data); data[('x',)]=4
        self.assertEqual(p.evaluate({'x':2}),1)

    def test_monomial_validation(self):
        for mon in (('y','x'),('not legal',),('x',)*33,('x'*25,),('x',2)):
            with self.subTest(mon=mon),self.assertRaises(ValueError): c.Polynomial({mon:1})

    def test_exact_types(self):
        for v in (True,False,0.1,'1/2',complex(1,0),None):
            with self.subTest(v=v),self.assertRaises(ValueError): c.rational(v)

    def test_budget_guards(self):
        with self.assertRaises(ValueError): c.rational(1<<16385)
        with self.assertRaises(ValueError): c.P('x')**33
        with self.assertRaises(ValueError): (c.P('x')**17)*(c.P('x')**16)
        with self.assertRaises(ValueError): c.P('x')/0
        with self.assertRaises(ValueError): c.P('x')**True

    def test_exact_evaluation_key_set(self):
        p=c.P('x')+1
        for value in ({},{'x':1,'y':2},{'x':1.0}):
            with self.assertRaises(ValueError): p.evaluate(value)

    def test_require_survives_optimization(self):
        with self.assertRaises(RuntimeError): c.require(False,'deliberate')
        with self.assertRaises(ValueError): c.require(1,'bad')


class IntervalTests(unittest.TestCase):
    def test_sqrt_square_certificates(self):
        for value in (F(0),F(1),F(2),F(4,9),F(1,10**90),F(10**40,7)):
            lo,hi=c.sqrt_bounds(value)
            self.assertLessEqual(lo*lo,value); self.assertLessEqual(value,hi*hi)
            self.assertLessEqual(hi-lo,F(1,10**65))

    def test_exact_square_collapses(self):
        self.assertEqual(c.sqrt_bounds(F(49,100)),(F(7,10),F(7,10)))
        self.assertEqual(c.sqrt_bounds(0),(0,0))

    def test_sqrt_rejects_invalid(self):
        for value in (-1,1.0,True,'2'):
            with self.subTest(value=value),self.assertRaises(ValueError): c.sqrt_bounds(value)
        for digits in (0,101,True,1.5):
            with self.assertRaises(ValueError): c.sqrt_bounds(2,digits)

    def test_signed_interval_arithmetic(self):
        a,b=c.Interval(-3,-2),c.Interval(4,5)
        self.assertEqual((a*b).bounds(),(-15,-8))
        self.assertEqual((a+b).bounds(),(1,3))
        self.assertEqual(a.reciprocal().bounds(),(F(-1,2),F(-1,3)))
        self.assertEqual((2-a).bounds(),(4,5))

    def test_zero_denominator_rejection(self):
        for a in (c.Interval(0),c.Interval(-1,1),c.Interval(0,2),c.Interval(-2,0)):
            with self.assertRaises(ValueError): a.reciprocal()
            with self.assertRaises(ValueError): c.Interval(1)/a

    def test_interval_boundary_rejection(self):
        with self.assertRaises(ValueError): c.Interval(2,1)
        with self.assertRaises(ValueError): c.Interval(-1,4).sqrt()
        with self.assertRaises(ValueError): c.Interval(0.5)
        x=c.Interval(1)
        with self.assertRaises(AttributeError): x._lo=3

    def test_outward_decimal_signed(self):
        self.assertEqual(c.decimal_bound(F(-1,3),2),'-0.34')
        self.assertEqual(c.decimal_bound(F(-1,3),2,True),'-0.33')
        self.assertEqual(c.decimal_bound(F(1,3),0),'0')
        self.assertEqual(c.decimal_bound(F(1,3),0,True),'1')
        self.assertEqual(c.decimal_bound(F(-1,1000),2,True),'0.00')

    def test_outward_decimal_invalid(self):
        for args in ((F(1,3),-1,False),(F(1,3),101,False),(F(1,3),2,1)):
            with self.assertRaises(ValueError): c.decimal_bound(*args)

    def test_unresolved_comparison_fails(self):
        for values in ({1:c.Interval(1,2),2:c.Interval(1,2)}, {1:c.Interval(1),2:c.Interval(1)}):
            with self.assertRaises(RuntimeError): c.unique_winner(values)

    def test_comparison_invalid(self):
        for values in ({},{True:c.Interval(1)},{1:1}):
            with self.assertRaises(ValueError): c.unique_winner(values)

    def test_strict_comparison_success(self):
        self.assertEqual(c.unique_winner({1:c.Interval(2,3),2:c.Interval(0,1)}),(1,F(1)))


class ReflectionTests(unittest.TestCase):
    def test_degenerate_orders(self):
        for n in (1,2):
            result=c.reflection_norm(n)
            self.assertEqual(result['norm'].bounds(),(1,1))
            self.assertEqual(result['candidate_m'],[])

    def test_candidate_locations(self):
        for n,expected in ((3,(1,)),(10,(1,)),(11,(1,2)),(27,(2,3)),(81,(7,8))):
            self.assertEqual(c.candidate_multiplicities(n),expected)

    def test_switch_and_large_examples(self):
        for n,m in [(n,1) for n in range(3,16)]+[(16,2),(27,3),(81,7)]:
            self.assertEqual(c.reflection_norm(n)['unique_winner'],m)

    def test_balanced_reflection(self):
        for n in (4,8,16,100):
            result=c.reflection_values(n,n//2)
            self.assertEqual(result['k'].bounds(),(0,0))
            self.assertEqual(result['norm_fourth'].bounds(),(1,1))

    def test_bad_split_and_order(self):
        for n,m in ((2,1),(3,0),(3,2),(3,True),(True,1),(4,2.0),(1000001,1)):
            with self.assertRaises(ValueError): c.reflection_values(n,m)
        for n in (0,-1,True,3.0,1000001):
            with self.assertRaises(ValueError): c.reflection_norm(n)

    def test_threshold_boundary(self):
        for n in (3,9,30,1000000):
            threshold=c.constant_threshold(n)
            self.assertGreater(threshold.lo,2)
            self.assertLess(threshold.hi,n)
        with self.assertRaises(ValueError): c.constant_threshold(2)

    def test_known_exact_fourth_norm(self):
        val=c.reflection_values(4,1)['norm_fourth']
        self.assertLessEqual(val.lo,4); self.assertGreaterEqual(val.hi,4)

    def test_finite_exhaustive_and_repeated_splits(self):
        result=c.supplemental_reflection_checks()
        self.assertEqual(len(result['maximizing_m']),98)
        self.assertEqual(result['finite_exhaustive_range'],[3,100])

    def test_n27_n81_strict_gap(self):
        gap=c.reflection_norm(27)['beta']-c.reflection_norm(81)['beta']
        self.assertGreater(gap.lo,F('0.0006789009254243884485970867865165191358'))
        self.assertLess(gap.hi,F('0.0006789009254243884485970867865165191359'))


class SpectralExampleTests(unittest.TestCase):
    def test_finite_character_and_energy_examples(self):
        result=c.finite_spectral_checks()
        self.assertEqual(len(result['point_spike_examples']),8)
        self.assertEqual(result['nonsplit_lift']['energy_multiplier'],27)

    def test_cyclotomic_orthogonality(self):
        self.assertEqual(c.character_sum([0,9,18],27),(0,)*18)
        self.assertEqual(c.character_sum([0,0,0],27),(3,)+(0,)*17)
        self.assertNotEqual(c.character_sum([0,9,17],27),(0,)*18)

    def test_bad_character_helpers(self):
        for exponents,conductor in (([0],2),([27],27),([True],3),([-1],3),([0.0],3)):
            with self.assertRaises(ValueError): c.character_sum(exponents,conductor)
        for moduli in ([3],(2,),(81,3),(),(True,)):
            with self.assertRaises(ValueError): c.finite_group(moduli)

    def test_parity_energy_small_independent_triples(self):
        # Independent ordered triple enumeration on C3 with actual rational weights.
        ws=[F(1,2),F(2),F(0)]
        E=Ea=F(0)
        for x in range(3):
            for y in range(3):
                for z in range(3):
                    w=(x+y-z)%3
                    term=ws[x]*ws[y]*ws[z]*ws[w]; E+=term
                    if ((x==0)+(y==0)-(z==0)-(w==0))%2==0: Ea+=term
        weights={(i,):c.Polynomial.constant(v) for i,v in enumerate(ws)}
        actualA,actualE,actualS=c.energy_polynomial((3,),weights,{(0,)})
        self.assertEqual(actualA,Ea); self.assertEqual(actualE,E)
        self.assertEqual(actualS,2*Ea-E)

    def test_energy_rejects_bad_input(self):
        with self.assertRaises(ValueError): c.energy_polynomial((3,),{},set())
        weights={(i,):c.Polynomial.constant(1) for i in range(3)}
        with self.assertRaises(ValueError): c.energy_polynomial((3,),weights,{(4,)})
        weights[(0,)]=1
        with self.assertRaises(ValueError): c.energy_polynomial((3,),weights,{(0,)})


class CertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls): cls.value,cls.digest=c.load_certificate(CERT)

    def test_regenerated_canonical_certificate(self):
        self.assertTrue(c.validate_certificate(self.value))
        self.assertEqual(CERT.read_bytes(),c.canonical_bytes(self.value))
        self.assertEqual(self.digest,sha256(CERT.read_bytes()).hexdigest())

    def test_mutated_winner_rejected(self):
        value=deepcopy(self.value); value['reflection_rows'][-1]['unique_winner']=8
        with self.assertRaises(RuntimeError): c.validate_certificate(value)

    def test_mutated_interval_rejected(self):
        value=deepcopy(self.value); value['beta27_minus_beta81'][0]='0.1'
        with self.assertRaises(RuntimeError): c.validate_certificate(value)

    def test_missing_or_unknown_field_rejected(self):
        value=deepcopy(self.value); del value['switches']
        with self.assertRaises(RuntimeError): c.validate_certificate(value)
        value=deepcopy(self.value); value['extra']=0
        with self.assertRaises(RuntimeError): c.validate_certificate(value)

    def test_bool_for_integer_rejected(self):
        value=deepcopy(self.value); value['reflection_rows'][0]['n']=True
        with self.assertRaises(RuntimeError): c.validate_certificate(value)

    def test_loader_rejects_malformed_types_and_structure(self):
        invalid=(b'{"x":1,"x":2}\n',b'{"x":1.5}\n',b'{"x":NaN}\n',b'{"x":Infinity}\n',
                 b'{"x":1234567890123}\n',b'{ bad json }\n',b'['*17+b'0'+b']'*17,
                 b'{"x":"\xff"}\n',b' '*100001,b'{ "x": 1 }\n')
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory)/'bad.json'
            for raw in invalid:
                p.write_bytes(raw)
                with self.subTest(raw=raw[:50]),self.assertRaises(ValueError): c.load_certificate(p)


class IntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.normal=invoke()
        if cls.normal.returncode: raise RuntimeError(cls.normal.stderr.decode())

    def test_optimized_byte_identical(self):
        result=invoke(optimized=True)
        self.assertEqual(result.returncode,0,result.stderr.decode())
        self.assertEqual(result.stdout,self.normal.stdout)

    def test_receipt_is_exact_canonical_json(self):
        value=json.loads(self.normal.stdout)
        self.assertEqual(value['status'],'PASS')
        self.assertEqual(value['formal_identity_count'],54)
        self.assertEqual(c.canonical_bytes(value),self.normal.stdout)
        self.assertNotIn(str(ROOT).encode(),self.normal.stdout)

    def test_arbitrary_working_directory(self):
        with tempfile.TemporaryDirectory() as directory: result=invoke(cwd=directory)
        self.assertEqual(result.returncode,0,result.stderr.decode())
        self.assertEqual(result.stdout,self.normal.stdout)

    def test_unknown_cli_argument(self):
        result=invoke(arguments=('--output','bad.json'))
        self.assertNotEqual(result.returncode,0)
        self.assertEqual(result.stdout,b'')

    def test_missing_certificate_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            script=Path(directory)/'exact_checks.py'; shutil.copyfile(SCRIPT,script)
            result=invoke(script)
        self.assertNotEqual(result.returncode,0)

    def test_formula_mutation_fails_in_optimized_run(self):
        with tempfile.TemporaryDirectory() as directory:
            script=Path(directory)/'exact_checks.py'
            source=SCRIPT.read_text()
            old='+6*d*h*r*r+3*K*(h+1)*r+K*d)'
            self.assertIn(old,source)
            script.write_text(source.replace(old,'+7*d*h*r*r+3*K*(h+1)*r+K*d)',1))
            shutil.copyfile(CERT,script.with_name(CERT.name))
            result=invoke(script,optimized=True)
        self.assertNotEqual(result.returncode,0)
        self.assertIn(b'stationary quintic identity',result.stderr)

    def test_read_only_and_no_network_audit(self):
        # Fail on any attempted write, subprocess, or network event, independent of chmod.
        wrapper="""import sys,runpy,os
sys.dont_write_bytecode=True
path=sys.argv[1]
sys.argv=[path]
def audit(event,args):
    if event=='open':
        mode=args[1]; flags=args[2]
        if (isinstance(mode,str) and any(x in mode for x in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise RuntimeError('write attempt blocked')
    if event.startswith(('socket.','subprocess.')) or event in ('os.system','os.remove','os.rename','os.mkdir','os.rmdir'):
        raise RuntimeError('external mutation/network attempt blocked')
sys.addaudithook(audit)
runpy.run_path(path,run_name='__main__')
"""
        with tempfile.TemporaryDirectory() as directory:
            d=Path(directory); script=d/SCRIPT.name; certificate=d/CERT.name
            shutil.copyfile(SCRIPT,script); shutil.copyfile(CERT,certificate)
            before={p.name:sha256(p.read_bytes()).hexdigest() for p in d.iterdir()}
            script.chmod(0o444); certificate.chmod(0o444); d.chmod(0o555)
            try:
                result=subprocess.run([sys.executable,'-I','-B','-S','-c',wrapper,str(script)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
                after={p.name:sha256(p.read_bytes()).hexdigest() for p in d.iterdir()}
            finally: d.chmod(0o755)
        self.assertEqual(result.returncode,0,result.stderr.decode())
        self.assertEqual(result.stdout,self.normal.stdout)
        self.assertEqual(before,after)

    def test_no_assert_float_external_imports_or_absolute_paths(self):
        tree=ast.parse(SCRIPT.read_text())
        imports=[]
        for node in ast.walk(tree):
            self.assertNotIsInstance(node,ast.Assert)
            if isinstance(node,ast.Constant):
                self.assertNotIsInstance(node.value,float)
                if isinstance(node.value,str): self.assertNotIn('/workspace/',node.value)
            if isinstance(node,ast.Import): imports.extend(n.name.split('.')[0] for n in node.names)
            if isinstance(node,ast.ImportFrom): imports.append(node.module.split('.')[0])
        self.assertTrue(set(imports)<={'__future__','sys','argparse','collections','fractions','hashlib','itertools','json','math','pathlib','types'})


if __name__=='__main__': unittest.main(verbosity=2)
