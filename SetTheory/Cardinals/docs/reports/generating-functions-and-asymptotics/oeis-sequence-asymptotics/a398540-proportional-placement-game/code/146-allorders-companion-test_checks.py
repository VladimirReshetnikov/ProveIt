#!/usr/bin/env python3
"""Normal/-O-safe adversarial regression tests for the new Report146 companion."""
import argparse
import ast
import copy
from fractions import Fraction as Q
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import uuid

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent
spec = importlib.util.spec_from_file_location("report146_checks", ROOT / "checks.py")
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)
RAW = (ROOT / "fixture.json").read_bytes()
BASE = c.parse_json(RAW)


def nodes(value, path=()):
    yield path, value
    if type(value) is dict:
        for key, child in value.items():
            yield from nodes(child, path+(key,))
    elif type(value) is list:
        for key, child in enumerate(value):
            yield from nodes(child, path+(key,))


def at(value, path):
    for key in path:
        value = value[key]
    return value


def mutate(path, replacement):
    out = copy.deepcopy(BASE)
    at(out, path[:-1])[path[-1]] = replacement
    return out


def duplicate_json(value, target, path=()):
    if type(value) is dict:
        pairs = list(value.items())
        if path == target:
            pairs.insert(0, pairs[0])
        return "{" + ",".join(json.dumps(k)+":"+duplicate_json(v, target, path+(k,)) for k, v in pairs) + "}"
    if type(value) is list:
        return "["+",".join(duplicate_json(v, target, path+(i,)) for i, v in enumerate(value))+"]"
    return json.dumps(value)


class Checks(unittest.TestCase):
    def setUp(self):
        self.paths = []

    def tearDown(self):
        for p in reversed(self.paths):
            if p.is_symlink() or p.is_file() or p.exists() and not p.is_dir():
                p.unlink()
            elif p.is_dir():
                p.rmdir()

    def new_path(self, suffix=".json"):
        p = ROOT / ("test-"+uuid.uuid4().hex+suffix)
        self.paths.append(p)
        return p

    def cli(self, *args, cwd=None):
        command = [sys.executable, "-I"]
        if sys.flags.optimize:
            command.append("-O")
        return subprocess.run(command+[str(ROOT / "checks.py"), *args], capture_output=True,
                              text=True, cwd=cwd or ROOT, timeout=30)

    def expect_bad(self, data):
        with self.assertRaises(c.CheckError):
            c.validate_fixture(data)

    def test_01_good_fixture_and_reproducibility(self):
        a = c.verify_fixture(copy.deepcopy(BASE))
        b = c.verify_fixture(copy.deepcopy(BASE))
        self.assertEqual(a, b)
        self.assertEqual(a["status"], "passed")
        self.assertTrue(a["no_analytic_or_numerical_certification"])
        self.assertEqual(a["computed_kernel"]["third_x_constant"], "323/22680")
        self.assertEqual(a["computed_kernel"]["log_squared"], "0/1")

    def test_02_unknown_and_missing_keys_at_every_object_level(self):
        for path, value in nodes(BASE):
            if type(value) is dict:
                with self.subTest(path=path, attack="unknown"):
                    d = copy.deepcopy(BASE)
                    at(d, path)["unrecognized"] = None
                    self.expect_bad(d)
                with self.subTest(path=path, attack="missing"):
                    d = copy.deepcopy(BASE)
                    del at(d, path)[next(iter(value))]
                    self.expect_bad(d)

    def test_03_duplicate_keys_at_every_object_level(self):
        for path, value in nodes(BASE):
            if type(value) is dict:
                with self.subTest(path=path):
                    with self.assertRaises(c.CheckError):
                        c.parse_json(duplicate_json(BASE, path).encode("utf-8"))
        with self.assertRaises(c.CheckError):
            c.parse_json(b'{"schema":1,"\\u0073chema":2}')

    def test_04_bool_is_not_integer_at_any_integer_leaf(self):
        for path, value in nodes(BASE):
            if type(value) is int:
                for replacement in (True, False, float(value), str(value), None):
                    with self.subTest(path=path, replacement=replacement):
                        self.expect_bad(mutate(path, replacement))

    def test_05_all_container_types_are_closed(self):
        for path, value in nodes(BASE):
            if path and type(value) in (dict, list):
                with self.subTest(path=path):
                    self.expect_bad(mutate(path, None))
                    self.expect_bad(mutate(path, tuple(value)))
        for bad in ([], None, 1, True, "fixture"):
            self.expect_bad(bad)

    def test_06_canonical_rational_rejections(self):
        bad = ["1", "1/0", "2/4", "01/2", "-0/1", "-0/2", "0/2", "1/-2", " 1/2", "+1/2", "1/02",
               "1/2 ", "1.0/2", "1e1/2", "1_0/2", "9"*25+"/1", "1/"+"9"*25, True, 1, 1.0, None, [], {}]
        for value in bad:
            with self.subTest(value=value):
                self.expect_bad(mutate(("kernel", "p"), value))
        for value in ("0/1", "1/1", "-1/1", "-7/540", "999999999999999999999999/2"):
            self.assertIsInstance(c.rational(value, "test"), Q)

    def test_07_json_lexical_and_resource_rejections(self):
        for raw in (b"{", b"[] trailing", b"{\xff}", b"\xef\xbb\xbf{}", b"[NaN]", b"[Infinity]", b"[-Infinity]",
                    b"[0.5]", b"[1e2]", b"[1234567]", b"[-1234567]", b"["*25+b"0"+b"]"*25,
                    b"["+b"0,"*6100+b"0]", b" "*(c.MAX_BYTES+1)):
            with self.subTest(raw=raw[:50]):
                with self.assertRaises(c.CheckError):
                    c.parse_json(raw)
        # Structural braces inside a JSON string must not consume nesting depth.
        self.assertEqual(c.parse_json(json.dumps("{"*100+"\\\""+"}"*100).encode()), "{"*100+"\\\""+"}"*100)

    def test_08_fixture_resource_bounds(self):
        attacks = [(('log_models','n_max'),49), (('log_models','q_max'),7), (('log_models','a_max'),6),
                   (('inverse','unit_max'),25), (('inverse','tail_end'),41), (('inverse','models',0,'a'),-2),
                   (('inverse','models',0,'q'),7), (('moments','orders',9),13), (('moments','counts',9),365),
                   (('formal_inverse','R1',0,'powers',0),5), (('acceleration','max_J'),7),
                   (('signed_taylor','samples',0,'i'),48), (('signed_taylor','samples',0,'order'),9)]
        for path, value in attacks:
            with self.subTest(path=path):
                self.expect_bad(mutate(path, value))
        self.expect_bad(mutate(('signed_taylor','samples',0,'values'), ['1/1']*49))
        self.expect_bad(mutate(('formal_inverse','R1'), BASE['formal_inverse']['R1']*17))
        self.expect_bad(mutate(('inverse','models'), BASE['inverse']['models']*3))

    def test_09_sorted_unique_and_semantic_shape_requirements(self):
        self.expect_bad(mutate(('log_models','anchors',1), BASE['log_models']['anchors'][0]))
        self.expect_bad(mutate(('inverse','models',1), BASE['inverse']['models'][0]))
        self.expect_bad(mutate(('moments','orders',1), 1))
        self.expect_bad(mutate(('formal_inverse','R3'), list(reversed(BASE['formal_inverse']['R3']))))
        self.expect_bad(mutate(('formal_inverse','R1',0,'coefficient'),'0/1'))
        self.expect_bad(mutate(('synthetic_intervals',0,'a'), ['1/1','1/3']))
        self.expect_bad(mutate(('synthetic_intervals',0,'a'), ['1/3','1/1']))
        self.expect_bad(mutate(('synthetic_intervals',0,'C'), ['0/1','1/1']))
        self.expect_bad(mutate(('signed_taylor','samples',0,'values'), ['1/1']*16))
        self.expect_bad(mutate(('scope',), 'analytic proof'))
        self.expect_bad(mutate(('analytic_inputs',0), 'A1: numerically proved'))
        self.expect_bad(mutate(('formal_inverse','symbols',0), 'unknown'))

    def test_10_expected_values_have_real_semantics(self):
        paths = [('kernel', key) for key in BASE['kernel']]
        paths += [('log_models','anchors',i,'value') for i in range(len(BASE['log_models']['anchors']))]
        paths += [('signed_taylor','samples',i,'expected') for i in range(len(BASE['signed_taylor']['samples']))]
        paths += [('inverse','models',i,'critical_constant') for i in range(len(BASE['inverse']['models']))]
        paths += [('formal_inverse',name,i,'coefficient') for name in ('R1','R2','R3') for i in range(len(BASE['formal_inverse'][name]))]
        paths += [('synthetic_intervals',i,'expected',name,j) for i in range(2) for name in ('A','B','P') for j in range(2)]
        paths += [('acceleration','weights_J3',i) for i in range(5)]
        paths += [('acceleration','ratio',key) for key in BASE['acceleration']['ratio']]
        for path in paths:
            with self.subTest(path=path):
                wrong = c.rational(at(BASE,path),'original')+Q(1,1001)
                data = mutate(path, c.qstr(wrong))
                c.validate_fixture(data)  # The attack is schema-valid, but mathematically false.
                with self.assertRaises(c.CheckError):
                    c.verify_fixture(data)
        for i, count in enumerate(BASE['moments']['counts']):
            data = mutate(('moments','counts',i),count+1)
            c.validate_fixture(data)
            with self.assertRaises(c.CheckError):
                c.verify_fixture(data)

    def test_11_explicit_small_coefficient_and_boundary_checks(self):
        self.assertEqual(c.log_power_by_products(2,4), [Q(0),Q(0),Q(1),Q(1),Q(11,12)])
        self.assertEqual(c.model(1,1,4)[4], Q(-1,12))
        self.assertEqual(c.model(2,1,5)[5], Q(1,30))
        self.assertEqual(c.inverse_model(-1,1,4), [Q(-1,4),Q(-1,2),Q(-1,4),Q(-1,6),Q(-1,8)])
        K,n = 7,3
        h,y = c.model(-1,1,K+1),c.inverse_model(-1,1,K+1)
        finite=h[n-1]/(n+2)-2*(n+1)*sum((h[k]/((k+1)*(k+2)*(k+3)) for k in range(n,K+1)),Q(0))
        boundary=Q(n+1,K+2)*(h[K]/(K+3)-y[K+1])
        self.assertNotEqual(finite,y[n])
        self.assertEqual(finite-y[n],boundary)
        self.assertNotEqual(boundary,0)

    def test_12_formal_inverse_really_cancels(self):
        actual,residual4=c.solve_formal_inverse()
        self.assertEqual(len(actual),3)
        self.assertNotEqual(residual4,c.Polynomial())
        delta=c.sconstant(0,4)
        delta[1:4]=actual
        for value in c.root_residual(delta)[:4]:
            self.assertEqual(value,0)
        delta[3]=delta[3]+c.variable(6)
        self.assertNotEqual(c.root_residual(delta)[3],0)

    def test_13_cli_success_and_new_receipt(self):
        target=self.new_path()
        proc=self.cli('--output',target.name)
        self.assertEqual(proc.returncode,0,proc.stderr)
        self.assertEqual(target.read_text(),proc.stdout)
        result=json.loads(proc.stdout)
        self.assertEqual(result['python_optimization'],sys.flags.optimize)
        self.assertEqual(result['implementation_sha256'],hashlib.sha256((ROOT/'checks.py').read_bytes()).hexdigest())
        original=target.read_bytes()
        proc=self.cli('--output',target.name)
        self.assertNotEqual(proc.returncode,0)
        self.assertEqual(target.read_bytes(),original)
        self.assertEqual(proc.stdout,'')

    def test_14_cli_rejects_invalid_and_semantic_fixtures(self):
        for payload in (b'{"x":1,"x":2}',json.dumps(mutate(('kernel','p'),'2/3')).encode(),b'[NaN]'):
            target=self.new_path(); target.write_bytes(payload)
            output=self.new_path()
            proc=self.cli('--fixture',target.name,'--output',output.name)
            self.assertNotEqual(proc.returncode,0)
            self.assertFalse(output.exists())
            self.assertEqual(proc.stdout,'')

    def test_15_no_path_components_or_external_output(self):
        for name in ('../escape.json','/tmp/escape.json','nested/name.json','./name.json','a/../name.json',
                     'a\\b.json','..json','a.json/','a..json','a.json\x00','a.JSON','-a.json','a'*65+'.json'):
            for operation in (c.read_local,lambda v:c.write_local(v,b'{}\n')):
                with self.subTest(name=name):
                    with self.assertRaises((c.CheckError,OSError,ValueError)):
                        operation(name)
        proc=self.cli('--output','../escape.json')
        self.assertNotEqual(proc.returncode,0)
        proc=self.cli('--fixture','../fixture.json')
        self.assertNotEqual(proc.returncode,0)

    def test_16_symlink_regular_and_special_file_guards(self):
        target=self.new_path(); target.write_bytes(b'protected\n')
        link=self.new_path(); link.symlink_to(target.name)
        proc=self.cli('--output',link.name)
        self.assertNotEqual(proc.returncode,0)
        self.assertEqual(target.read_bytes(),b'protected\n')
        with self.assertRaises((c.CheckError,OSError)):
            c.read_local(link.name)
        dangling=self.new_path(); dangling.symlink_to('nonexistent-test-target.json')
        with self.assertRaises((c.CheckError,OSError)):
            c.write_local(dangling.name,b'{}')
        directory=self.new_path(); directory.mkdir()
        with self.assertRaises((c.CheckError,OSError)):
            c.read_local(directory.name)
        with self.assertRaises((c.CheckError,OSError)):
            c.write_local(directory.name,b'{}')
        fifo=self.new_path(); os.mkfifo(fifo)
        with self.assertRaises((c.CheckError,OSError)):
            c.read_local(fifo.name)
        oversized=self.new_path(); oversized.write_bytes(b' '*(c.MAX_BYTES+1))
        with self.assertRaises(c.CheckError):
            c.read_local(oversized.name)

    def test_17_symlink_directory_and_non_cwd_operation(self):
        directory=self.new_path(suffix=''); directory.mkdir()
        link=self.new_path(suffix=''); link.symlink_to(directory.name,target_is_directory=True)
        with self.assertRaises((c.CheckError,OSError)):
            c.secure_directory(link)
        with self.assertRaises((c.CheckError,OSError)):
            c.secure_directory(link/'child')
        with self.assertRaises(c.CheckError):
            c.secure_directory(ROOT/'..')
        proc=self.cli(cwd=directory)
        self.assertEqual(proc.returncode,0,proc.stderr)
        self.assertEqual(json.loads(proc.stdout)['status'],'passed')

    def test_18_no_assert_statements_and_cli_usage(self):
        for path in (ROOT/'checks.py',ROOT/'test_checks.py'):
            self.assertFalse(any(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(path.read_text()))))
        for args in (('--unknown',),('--output',),('--fixture',)):
            proc=self.cli(*args)
            self.assertNotEqual(proc.returncode,0)
        proc=self.cli('--help')
        self.assertEqual(proc.returncode,0)
        self.assertIn('finite exact algebra',proc.stdout)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="create a NEW JSON receipt in the companion directory")
    args=parser.parse_args()
    stream=io.StringIO()
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(Checks)
    result=unittest.TextTestRunner(stream=stream,verbosity=2).run(suite)
    receipt={"schema":"report146-adversarial-tests-v1","status":"passed" if result.wasSuccessful() else "failed",
             "python_optimization":sys.flags.optimize,"test_methods":result.testsRun,
             "failures":len(result.failures),"errors":len(result.errors),
             "checks_sha256":hashlib.sha256((ROOT/'checks.py').read_bytes()).hexdigest(),
             "test_code_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             "fixture_sha256":hashlib.sha256(RAW).hexdigest(),
             "scope":"finite exact and adversarial regression tests; not an analytic proof"}
    receipt["object_levels_tested"] = sum(type(v) is dict for p,v in nodes(BASE))
    receipt["integer_leaves_tested"] = sum(type(v) is int for p,v in nodes(BASE))
    payload=(json.dumps(receipt,indent=2,sort_keys=True)+"\n").encode("ascii")
    if args.output is not None:
        try:
            c.write_local(args.output,payload)
        except (c.CheckError,OSError) as exc:
            sys.stderr.write("test receipt failed: "+str(exc)+"\n")
            return 2
    sys.stdout.write(payload.decode("ascii"))
    if not result.wasSuccessful():
        sys.stderr.write(stream.getvalue())
    return 0 if result.wasSuccessful() else 1


if __name__=='__main__':
    raise SystemExit(main())
