"""Independent exact identities, mutation tests and bounded diagnostic regressions."""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import ast
from copy import deepcopy
from fractions import Fraction
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).absolute().parents[1]
SCRIPT = ROOT / 'companion/exact_checks.py'
spec = importlib.util.spec_from_file_location('report296_checks', SCRIPT)
c = importlib.util.module_from_spec(spec); spec.loader.exec_module(c)


def invoke(script=SCRIPT, optimized=False, args=(), cwd=None):
    command = [sys.executable, '-I', '-B', '-X', 'int_max_str_digits=640']
    if optimized:
        command.append('-O')
    return subprocess.run(command+[str(script), *args], stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, cwd=cwd, timeout=30, check=False)


class SymbolicTests(unittest.TestCase):
    def test_independent_expanded_monomials(self):
        for d in (1, 2, 37, 2**42, 2**76):
            # These formulas expand directly, without calling checker arithmetic helpers.
            expected = {
                'a': (-71-d, 2+d), 'mu': (-59-d, 2+d),
                'b': (-20-2*(71+d)-12359*(72+d), (2+12359)*(2+d)),
                's': (-26-24718*(72+d), 24718*(2+d)),
                't': (-30-24718*(72+d), 24718*(2+d)),
                'beta': (-1-59-d-20-2*(71+d)-12359*(72+d), (3+12359)*(2+d)),
            }
            self.assertEqual(c.monomials(d), expected)

    def test_independent_ratio_degrees(self):
        old, new = c.monomials(2**76), c.monomials(2**42)
        delta = 2**76-2**42
        for name, degree in [('a',1), ('mu',1), ('t',24718), ('beta',12362)]:
            self.assertEqual(tuple(new[name][j]-old[name][j] for j in (0,1)),
                             (degree*delta, -degree*delta))

    def test_arithmetic_pairs_and_composition(self):
        self.assertEqual(c.multiply((-2,3),(5,-7)), (3,-4))
        self.assertEqual(c.quotient((-2,3),(5,-7)), (-7,10))
        self.assertEqual(c.power((-2,3),-5), (10,-15))
        for a in [(-2,3),(0,0),(8,-1)]:
            self.assertEqual(c.quotient(c.multiply(a,(5,7)),(5,7)),a)
            self.assertEqual(c.power(a,0),(0,0))

    def test_constants_and_sufficient_integer_inequalities(self):
        cert = c.symbolic_certificate(); k=cert['constants']; e=cert['source_exponents']
        self.assertEqual(k['partition_P3'], (1*2*3)**2 * 65536)
        self.assertEqual(k['quadratic_threshold_exponent'], 25378984)
        self.assertEqual(k['density_denominator'], 64000)
        self.assertEqual(k['interval_count_constant'], 12801)
        self.assertEqual(k['quadratic_size_degree'], 24718)
        self.assertEqual(k['local_count_two_loss'], 30)
        self.assertGreaterEqual(e['r_old'],e['r_fejer']+1)
        self.assertGreaterEqual(e['r_fejer'],1)
        self.assertLess(k['phase_loss'],k['phase_absorption_cube'])
        self.assertEqual(k['phase_absorption_cube'],64)
        self.assertEqual(k['localization_gain_floor'],4)

    def test_invalid_pair_types_and_limits(self):
        for v in (None, [], [1,2], (1,), (1,2,3), (True,1), (1.0,1),
                  (Fraction(1),1), (2**121,1), ('1',1)):
            with self.subTest(value=repr(v)[:50]), self.assertRaises(ValueError): c.pair(v)
        for v in (True, 1.0, Fraction(1), '1', 30001, -30001):
            with self.assertRaises(ValueError): c.power((1,2),v)
        for d in (0,-1,True,1.0,2**88+1):
            with self.assertRaises(ValueError): c.monomials(d)
        with self.assertRaises(ValueError): c.multiply((2**120,0),(1,0))
        with self.assertRaises(ValueError): c.power((2**120,0),2)

    def test_certificate_exact_and_unmutated(self):
        value=c.load_json(ROOT/'companion/certificate.json'); before=c.canonical_bytes(value)
        self.assertTrue(c.validate_certificate(value))
        self.assertEqual(before,c.canonical_bytes(value))
        self.assertEqual(value,c.symbolic_certificate())

    def test_certificate_mutation_of_every_numeric_leaf(self):
        original=c.symbolic_certificate()
        def paths(v,path=()):
            if type(v) is int:
                yield path
            elif type(v) is dict:
                for k,item in v.items(): yield from paths(item,path+(k,))
            elif type(v) is list:
                for k,item in enumerate(v): yield from paths(item,path+(k,))
        count=0
        for path in paths(original):
            value=deepcopy(original); node=value
            for k in path[:-1]: node=node[k]
            node[path[-1]]+=1
            with self.subTest(path=path), self.assertRaises(ValueError): c.validate_certificate(value)
            count+=1
        self.assertGreater(count,45)

    def test_certificate_wrong_types_and_schema(self):
        original=c.symbolic_certificate()
        for value in (None,[],{},True,{**original,'extra':1},
                      {**original,'schema_version':True}, {**original,'schema_version':1.0},
                      {**original,'commit':'0'*40}):
            with self.assertRaises(ValueError): c.validate_certificate(value)
        for missing in original:
            value={k:v for k,v in original.items() if k!=missing}
            with self.assertRaises(ValueError): c.validate_certificate(value)


class RationalTests(unittest.TestCase):
    def test_ceiling_reference_by_integer_search(self):
        for numerator in range(1,41):
            for denominator in range(1,21):
                x=Fraction(numerator,denominator)
                reference=next(n for n in range(1,42) if n>=x)
                self.assertEqual(c.ceil_positive(x),reference)
        self.assertEqual(c.ceil_positive(Fraction(81,10)),9)
        self.assertEqual(c.ceil_positive(Fraction(89,10)),9)

    def test_equal_counts_and_strictness(self):
        left,right=c.iteration_case(Fraction(3,2),2,64,256,7,7,4)
        self.assertLess(left,right)
        self.assertEqual(left,Fraction(3,2)*64**7)
        self.assertEqual(right,2*64**7)
        # Strict gain in count is allowed, not required.
        self.assertLess(*c.iteration_case(1,2,64,256,1,8,4))

    def test_weak_base_comparison_is_allowed(self):
        self.assertLess(*c.iteration_case(1,2,32,256,8,8,4))
        self.assertLess(*c.iteration_case(1,2,2,2,8,8,1))

    def test_invalid_iteration_hypotheses(self):
        good=[1,2,64,256,4,8,4]
        variants={0:[0,-1,2],1:[0,1],2:[0,-1,65],3:[0,1,255],
                  4:[0,9,129,True],5:[0,3,129,True],6:[0,-1,5]}
        for i, values in variants.items():
            for value in values:
                args=list(good);args[i]=value
                with self.subTest(index=i,value=value), self.assertRaises(ValueError): c.iteration_case(*args)

    def test_invalid_rationals_and_ceiling(self):
        for value in (True,1.0,'1',None,2**121,Fraction(1,2**121)):
            with self.assertRaises(ValueError): c.rational(value)
        for value in (0,-1,Fraction(-1,2)):
            with self.assertRaises(ValueError): c.ceil_positive(value)

    def test_exact_regression_inventory(self):
        self.assertEqual(c.regressions(),dict(ceiling_cases=990,equal_ceiling_cases=30,
            coefficient_cases=2970,maximum_cases=18,shared_maximum_cases=10,iteration_cases=480))


class JSONTests(unittest.TestCase):
    def read(self, raw):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'data.json';p.write_bytes(raw);return c.load_json(p)

    def test_duplicate_float_nonfinite_and_bad_encoding(self):
        for raw in (b'{"x":1,"x":2}',b'{"x":{"a":1,"a":2}}', b'{"x":1.0}',
                    b'{"x":NaN}',b'{"x":Infinity}',b'\xff',b'{',b'['*1000+b']'*1000,
                    b'['*2050+b']'*2050,b'{"x":'+b'1'*101+b'}'):
            with self.subTest(raw=raw[:35]), self.assertRaises(ValueError):self.read(raw)

    def test_noncanonical_and_oversize(self):
        for raw in (b'{"x":1}',b'{\r\n  "x": 1\r\n}\r\n',b' '* (c.MAX_BYTES+1)):
            with self.assertRaises(ValueError):self.read(raw)
        self.assertEqual(self.read(c.canonical_bytes({'x':1})),{'x':1})

    def test_leaf_aliases_and_nonregular_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);original=root/'data';original.write_bytes(b'{}\n')
            link=root/'link';link.symlink_to(original)
            with self.assertRaises(ValueError):c.read_bounded(link)
            hard=root/'hard';os.link(original,hard)
            with self.assertRaises(ValueError):c.read_bounded(original)
            fifo=root/'fifo';os.mkfifo(fifo)
            with self.assertRaises(ValueError):c.read_bounded(fifo)
            with self.assertRaises(ValueError):c.read_bounded(root)


class SourceAndCLITests(unittest.TestCase):
    def test_source_records_and_distinct_hash_scopes(self):
        result=c.verify_source_records()
        self.assertEqual(result['excerpt_records'],48)
        self.assertEqual(result['excerpt_lines'],133)
        self.assertEqual(result['full_file_identity_records'],34)
        self.assertFalse(result['full_files_refetched'])
        self.assertFalse(result['full_source_dependencies_compiled'])
        manifest=c.load_json(ROOT/'SOURCE_MANIFEST.json')
        self.assertEqual(len({x['repository_path'] for x in manifest['sources']}),34)
        for item in manifest['sources']:
            self.assertEqual(len(item['sha256']),64)
            self.assertEqual(len(item['git_blob_sha1']),40)
            self.assertEqual(item['commit'],c.COMMIT)
        values=c.load_json(ROOT/'source_excerpts.json')['excerpts']
        for e in values:
            self.assertEqual(hashlib.sha256(e['text'].encode()).hexdigest(),e['excerpt_sha256'])
            self.assertEqual(e['text'].count('\n'),e['end_line']-e['start_line']+1)
        theorem=next(e['text'] for e in values if e['name']=='natural_five_term_fejer')
        self.assertIn('HasNatAP A 5 := by',theorem)
        self.assertIn('fejer_cubic_function_discrepancy_bound',theorem)

    def test_edited_excerpt_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            for name in ('SOURCE_MANIFEST.json','source_excerpts.json'): shutil.copyfile(ROOT/name,root/name)
            data=c.load_json(root/'source_excerpts.json');data['excerpts'][0]['text']+='extra\n'
            (root/'source_excerpts.json').write_bytes(c.canonical_bytes(data))
            with self.assertRaisesRegex(RuntimeError,'hash mismatch'):c.verify_source_records(root)

    def test_data_pins_independently(self):
        self.assertEqual(len(c.DATA_PINS),3)
        for name,digest in c.DATA_PINS.items():
            self.assertEqual(hashlib.sha256((ROOT/name).read_bytes()).hexdigest(),digest)

    def test_normal_optimized_and_arbitrary_cwd(self):
        with tempfile.TemporaryDirectory() as temp:
            normal=invoke(cwd=temp);optimized=invoke(optimized=True,cwd=temp)
        self.assertEqual(normal.returncode,0,normal.stderr.decode())
        self.assertEqual(optimized.returncode,0,optimized.stderr.decode())
        self.assertEqual(normal.stdout,optimized.stdout)
        self.assertEqual(json.loads(normal.stdout)['status'],'passed')
        self.assertEqual(normal.stderr,b'');self.assertEqual(optimized.stderr,b'')
        self.assertEqual(invoke(args=('--unknown',)).returncode,2)

    def test_changed_data_fails_under_both_modes(self):
        for target in ('companion/certificate.json','SOURCE_MANIFEST.json','source_excerpts.json'):
            with tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp)/'source';shutil.copytree(ROOT,root)
                with (root/target).open('ab') as stream: stream.write(b' ')
                for optimized in (False,True):
                    result=invoke(root/'companion/exact_checks.py',optimized=optimized)
                    self.assertNotEqual(result.returncode,0)
                    self.assertIn(b'data pin mismatch',result.stderr)

    def test_guards_survive_optimization_and_no_external_execution(self):
        tree=ast.parse(SCRIPT.read_text())
        self.assertFalse(any(isinstance(n,ast.Assert) for n in ast.walk(tree)))
        forbidden={'subprocess','socket','urllib','requests','sympy','numpy','mpmath'}
        for node in ast.walk(tree):
            if isinstance(node,ast.Import):
                self.assertFalse(any(alias.name.split('.')[0] in forbidden for alias in node.names))
            if isinstance(node,ast.ImportFrom):
                self.assertNotIn((node.module or '').split('.')[0],forbidden)
        self.assertNotIn('eval(',SCRIPT.read_text())
        self.assertNotIn('exec(',SCRIPT.read_text())


if __name__=='__main__':
    unittest.main()
