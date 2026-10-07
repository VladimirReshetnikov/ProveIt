"""Independent exact expansions, adversarial inputs, mutation and read-only tests."""
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
spec = importlib.util.spec_from_file_location('report298_exact_checks', SCRIPT)
c = importlib.util.module_from_spec(spec); spec.loader.exec_module(c)


def invoke(script=SCRIPT, optimized=False, args=(), cwd=None):
    command = [sys.executable, '-I', '-B', '-X', 'int_max_str_digits=640']
    if optimized:
        command.append('-O')
    return subprocess.run(command+[str(script), *args], stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, cwd=cwd, timeout=30, check=False)


def clone_companion(destination):
    names = {*c.DATA_PINS, 'companion/exact_checks.py'}
    for name in names:
        path = destination/name; path.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(ROOT/name,path)
    return destination/'companion/exact_checks.py'


def fingerprint(root):
    return {p.relative_to(root).as_posix(): (p.stat().st_mode,p.stat().st_size,
            p.stat().st_mtime_ns,hashlib.sha256(p.read_bytes()).hexdigest())
            for p in root.rglob('*') if p.is_file()}


class ExactAlgebraTests(unittest.TestCase):
    def test_independent_geometric_expansions(self):
        g=c.monomials()['geometry_gamma']
        expected={
            'eta':[-4,32], 'theta':[-37-4*11//2,32*11//2],
            'theta_one':[-1882-59*10477,176*10477],
            'q_bound':[1882+59*10479,-176*10479],
            'Q':[1048576,-2097152], 'K':[114,-320],
            'spectrum_bound':[74+4*10,-32*10],
            'f':[-100,448], 'g':[-14-2*135,2*704], 'W':[135,-704],
        }
        self.assertEqual(g,expected)
        self.assertEqual(g['spectrum_bound'],g['K'])

    def test_independent_fejer_expansions(self):
        for d in (1,2,37,2**42,2**76):
            f=c.monomials(d)['fejer_x']
            expected={
                'alpha':[1,-1], 'a':[-69,-(d+2)], 'mu':[-57,-(d+2)],
                'b':[-20-2*69-70*12359,-(2+12359)*(d+2)],
                't':[-30-70*24718,-24718*(d+2)],
                'w':[-57-20-2*69-70*12359,-(3+12359)*(d+2)],
                'beta':[-1-57-20-2*69-70*12359,-(3+12359)*(d+2)],
            }
            self.assertEqual(f,expected)

    def test_monomial_operations_are_exact(self):
        self.assertEqual(c.multiply((-2,3),(5,-7)),(3,-4))
        self.assertEqual(c.power((-4,32),Fraction(11,2)),(-22,176))
        self.assertEqual(c.power((-2,3),0),(0,0))
        self.assertEqual(c.integral_pair((Fraction(6,2),-7)),[3,-7])
        with self.assertRaises(ValueError): c.integral_pair((Fraction(1,2),0))

    def test_bad_numeric_inputs_and_bounds(self):
        for value in (True,False,1.0,'1',None,2**120+1,-2**120-1):
            with self.assertRaises(ValueError): c.integer(value)
        for value in (True,1.0,'1',None,Fraction(1,2**121)):
            with self.assertRaises(ValueError): c.rational(value)
        for value in ([],[1,2],(1,),(1,2,3),(True,1),(1.0,2),(2**121,0)):
            with self.assertRaises(ValueError): c.pair(value)
        for value in (0,-1,True,1.0,2**76+1):
            with self.assertRaises(ValueError): c.monomials(value)
        with self.assertRaises(ValueError): c.power((1,1),2**76+1)
        with self.assertRaises(ValueError): c.power((2**120,1),2)
        with self.assertRaises(ValueError): c.multiply((2**120,0),(1,0))

    def test_sufficient_integer_checks_independently(self):
        checks=c.integer_checks()
        self.assertEqual(len(checks),106)
        for item in checks.values():
            if item['relation']=='=': self.assertEqual(item['left'],item['right'])
            elif item['relation']=='<': self.assertLess(item['left'],item['right'])
            else: self.assertLessEqual(item['left'],item['right'])
        self.assertEqual(checks['frequency_degree']['left'],89669903324)
        self.assertEqual(checks['beta_absorption']['left'],54368650971157718)
        self.assertEqual(checks['t_absorption']['left'],108710913663248398)
        self.assertEqual(checks['paper_label']['right'],16384)
        self.assertLess(337*2**67,2**76)
        self.assertLess(76,16384)  # Do not construct 2^16384 or any tower.

    def test_partition_square_is_retained(self):
        formulas=c.formula_ledger()
        self.assertEqual(formulas['fejer']['W_j'],'2^(2^(40*j^3+1))')
        self.assertEqual([40*j*j*j+1 for j in (1,2,3)],[41,321,1081])
        self.assertIn('2048^(q-1)',formulas['geometry']['R_q'])

    def test_totalized_q_zero_exactly(self):
        self.assertEqual(c.totalized_divide(7,0),0)
        for log_ratio in (0,3,100,Fraction(7,3),-4):
            self.assertEqual(c.pp_log_from_ratio_log(log_ratio,0),0)
        self.assertEqual(c.pp_log_from_ratio_log(3,Fraction(1,8)),24)
        self.assertEqual(c.pp_log_from_ratio_log(-3,Fraction(1,8)),0)
        with self.assertRaises(ValueError): c.pp_log_from_ratio_log(3,-1)

    def test_ceiling_exact_examples_not_a_continuous_proof(self):
        for numerator in range(0,41):
            for denominator in range(1,21):
                value=Fraction(numerator,denominator)
                reference=next(n for n in range(42) if n>=value)
                self.assertEqual(c.ceil_nonnegative(value),reference)
        with self.assertRaises(ValueError): c.ceil_nonnegative(-1)
        with self.assertRaises(ValueError): c.ceil_nonnegative(1.5)

    def test_square_log_reduction_on_exact_independent_inputs(self):
        # Algebraic regression only. The manuscript establishes the general identity.
        for f,g,e,log_c_inv in [(Fraction(1,2),Fraction(1,3),Fraction(1,4),7),
                               (Fraction(1,8),Fraction(2,5),Fraction(1,7),13)]:
            direct1=(2+f*log_c_inv)/(e*f)
            direct2=(1+g*(f*log_c_inv+2)/2)/(e*f*g/4)
            self.assertEqual(direct1,(2/f+log_c_inv)/e)
            self.assertEqual(direct2,(4/(f*g)+2*log_c_inv+4/f)/e)

    def test_formula_branch_coverage(self):
        f=c.formula_ledger()
        for name in ('density_recurrence','density_integer','square_scale','square_power'):
            self.assertIn(name,f['geometry']['G'])
        self.assertIn('ceil(I_q)',f['geometry']['density_recurrence'])
        self.assertIn('ceil(integer_budget_q)',f['geometry']['density_integer'])
        self.assertEqual(f['geometry']['k'],'ceil(K)')
        self.assertEqual(f['fejer']['n'],'ceil(8/beta)')
        self.assertIn('max{2,max{4,E}}',f['fejer']['U'])
        self.assertIn('F_graph',f['common_fourier']['F'])
        self.assertIn('G(x^(-D))',f['common_fourier']['F'])


class CertificateTests(unittest.TestCase):
    def test_certificate_matches_and_is_not_mutated(self):
        value=c.load_json(ROOT/'companion/certificate.json'); before=c.canonical_bytes(value)
        self.assertTrue(c.validate_certificate(value))
        self.assertEqual(before,c.canonical_bytes(value))
        self.assertEqual(value,c.symbolic_certificate())

    def test_every_numeric_and_formula_leaf_mutation_rejected(self):
        original=c.symbolic_certificate()
        def paths(value,path=()):
            if type(value) in (int,str): yield path
            elif type(value) is dict:
                for k,item in value.items(): yield from paths(item,path+(k,))
            elif type(value) is list:
                for k,item in enumerate(value): yield from paths(item,path+(k,))
        count=0
        for path in paths(original):
            value=deepcopy(original); node=value
            for k in path[:-1]: node=node[k]
            leaf=node[path[-1]];node[path[-1]]=leaf+1 if type(leaf) is int else leaf+' CORRUPTED'
            with self.subTest(path=path),self.assertRaises(ValueError):c.validate_certificate(value)
            count+=1
        self.assertGreater(count,400)

    def test_schema_and_bool_alias_rejected(self):
        original=c.symbolic_certificate()
        for value in (None,[],{},True,{**original,'extra':1},{**original,'schema_version':True},
                      {**original,'schema_version':1.0},{**original,'commit':'0'*40}):
            with self.assertRaises(ValueError):c.validate_certificate(value)
        for key in original:
            with self.assertRaises(ValueError):c.validate_certificate({k:v for k,v in original.items() if k!=key})

    def test_corrupted_formula_code_fails_both_modes(self):
        variants=[('power(half_a, 12359)','power(half_a, 12358)'),
                  ("'ceil(8/beta)'","'ceil(7/beta)'"),
                  ("'q_zero': 'u_0=theta_one^2/(16*0)=0; PP(C,D,0)=1'",
                   "'q_zero': 'u_0=1'"),
                  ('40*2**3+1,321','40*2**3,321')]
        for before,after in variants:
            with tempfile.TemporaryDirectory() as tmp:
                script=clone_companion(Path(tmp)/'source')
                text=script.read_text();self.assertIn(before,text);script.write_text(text.replace(before,after,1))
                for optimized in (False,True):
                    result=invoke(script,optimized=optimized)
                    self.assertNotEqual(result.returncode,0,(before,result.stdout))


class BoundedJsonTests(unittest.TestCase):
    def read_bytes(self,data):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'data.json';path.write_bytes(data)
            return c.load_json(path)

    def test_byte_parser_rejects_mutable_unbounded_or_nonbyte_inputs(self):
        for value in (bytearray(b'{}'),memoryview(b'{}'),'{}',None,True,b' '*(c.MAX_BYTES+1)):
            with self.assertRaises(ValueError):c.parse_json_bytes(value)
        self.assertEqual(c.parse_json_bytes(c.canonical_bytes({'x':1})),{'x':1})

    def test_valid_exact_json(self):
        self.assertEqual(self.read_bytes(c.canonical_bytes({'a':[1,-2,'text']})),{'a':[1,-2,'text']})

    def test_malformed_duplicate_float_noncanonical_oversized(self):
        examples=[b'{"a":1,"a":2}',b'{"x":1.0}',b'{"x":NaN}',b'{"x":Infinity}',
                  b'{"x":'+b'1'*41+b'}',b'{"x":'+str(2**120+1).encode()+b'}',
                  b'{}',b'\xff',b'{',b' '* (c.MAX_BYTES+1),
                  b'['*4097+b']'*4097]
        for data in examples:
            with self.subTest(start=data[:30]),self.assertRaises(ValueError):self.read_bytes(data)

    def test_excessive_depth_and_container_count(self):
        value=1
        for _ in range(18):value=[value]
        with self.assertRaisesRegex(ValueError,'depth'):self.read_bytes(c.canonical_bytes(value))
        with self.assertRaisesRegex(ValueError,'container'):self.read_bytes(c.canonical_bytes([[] for _ in range(4096)]))

    def test_leaf_symlink_hardlink_special_and_ancestor_symlink(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); directory=root/'directory';directory.mkdir()
            path=directory/'data';path.write_bytes(c.canonical_bytes({'x':1}))
            leaf=root/'leaf';leaf.symlink_to(path)
            with self.assertRaises(ValueError):c.read_bounded(leaf)
            ancestor=root/'alias';ancestor.symlink_to(directory,target_is_directory=True)
            with self.assertRaises(OSError):c.read_bounded(ancestor/'data')
            hard=root/'hard';os.link(path,hard)
            with self.assertRaises(ValueError):c.read_bounded(hard)
            with self.assertRaises(ValueError):c.read_bounded(path)
            fifo=root/'fifo';os.mkfifo(fifo)
            with self.assertRaises(ValueError):c.read_bounded(fifo)
            with self.assertRaises(ValueError):c.read_bounded(directory)
        for name in ('relative.json','/tmp/../tmp/data','//tmp/data'):
            with self.assertRaises(ValueError):c.read_bounded(name)


class SourceAndExecutionTests(unittest.TestCase):
    def test_source_records_and_distinct_authentication_scope(self):
        out=c.verify_source_records()
        self.assertEqual(out['full_file_identity_records'],50)
        self.assertEqual(out['excerpt_records'],56)
        self.assertEqual(out['excerpt_lines'],171)
        self.assertFalse(out['full_files_bundled'])
        self.assertFalse(out['full_files_refetched_or_authenticated_by_this_run'])
        data=c.load_json(ROOT/'source_excerpts.json')['excerpts']
        for entry in data:
            self.assertEqual(hashlib.sha256(entry['text'].encode()).hexdigest(),entry['excerpt_sha256'])
            self.assertEqual(entry['text'].count('\n'),entry['end_line']-entry['start_line']+1)
        lookup={e['name']:e['text'] for e in data}
        self.assertIn('HasNatAP A 5 := by',lookup['natural_five_term_fejer'])
        self.assertIn('fejer_cubic_function_discrepancy_bound',lookup['natural_five_term_fejer'])
        self.assertIn('def theorem_18_2',lookup['theorem_18_2'])
        spans=c.load_json(ROOT/'source_excerpts.json')['paper_formula_spans']
        self.assertEqual(len(spans),2)
        self.assertEqual(spans[0]['text'],r'a \uparrow(b \uparrow c)')
        self.assertEqual(spans[1]['text'],r'2 \uparrow 2 \uparrow \delta^{-1} \uparrow 2 \uparrow 2 \uparrow(k+9)')

    def test_edited_excerpt_hash_and_metadata_rejected(self):
        for field,newvalue in [('text','incorrect\n'),('start_line',0),('source_sha256','0'*64),('url','https://example.com/')]:
            with tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);clone_companion(root)
                value=c.load_json(root/'source_excerpts.json');value['excerpts'][0][field]=newvalue
                (root/'source_excerpts.json').write_bytes(c.canonical_bytes(value))
                with self.assertRaises(RuntimeError):
                    c.validate_source_records(c.load_json(root/'SOURCE_MANIFEST.json'),
                                              c.load_json(root/'source_excerpts.json'))

    def test_paper_math_span_corruption_rejected(self):
        for field,value in [('text','wrong'),('start_byte_zero_based',-1),
                            ('end_byte_exclusive',999),('source_line',1),
                            ('source_sha256','0'*64),('url','https://example.com/')]:
            with tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);clone_companion(root)
                data=c.load_json(root/'source_excerpts.json')
                data['paper_formula_spans'][0][field]=value
                (root/'source_excerpts.json').write_bytes(c.canonical_bytes(data))
                with self.assertRaises(RuntimeError):
                    c.validate_source_records(c.load_json(root/'SOURCE_MANIFEST.json'),
                                              c.load_json(root/'source_excerpts.json'))

    def test_data_pins_independently(self):
        self.assertEqual(len(c.DATA_PINS),4)
        for name,digest in c.DATA_PINS.items():
            self.assertEqual(hashlib.sha256((ROOT/name).read_bytes()).hexdigest(),digest)
        self.assertEqual(c.DATA_PINS['provenance/PROOF.md'],
                         '967e1b57b5823d5eff3282e48420ec64a35bd3562ca5bdfa19a21081dcb2358c')

    def test_normal_optimized_arbitrary_cwd_and_read_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'source';script=clone_companion(root)
            for path in root.rglob('*'):
                if path.is_file():path.chmod(0o444)
            for path in sorted(root.rglob('*'),reverse=True):
                if path.is_dir():path.chmod(0o555)
            root.chmod(0o555)
            before=fingerprint(root)
            try:
                normal=invoke(script,cwd=tmp);optimized=invoke(script,optimized=True,cwd=tmp)
                self.assertEqual(before,fingerprint(root))
            finally:
                root.chmod(0o755)
                for path in root.rglob('*'):
                    path.chmod(0o755 if path.is_dir() else 0o644)
        self.assertEqual(normal.returncode,0,normal.stderr.decode())
        self.assertEqual(optimized.returncode,0,optimized.stderr.decode())
        self.assertEqual(normal.stdout,optimized.stdout)
        out=json.loads(normal.stdout)
        self.assertEqual(out['status'],'passed');self.assertFalse(out['tower_values_evaluated'])
        self.assertEqual(normal.stderr,b'');self.assertEqual(optimized.stderr,b'')
        self.assertEqual(invoke(args=('--unknown',)).returncode,2)

    def test_real_file_replacement_after_pin_uses_original_snapshot(self):
        # A genuine filesystem interleaving, with no checker functions overridden.
        # Replacing both metadata files while the last pinned file is opened
        # reproduces the old pin-to-use window. An invalid commit on disk then
        # distinguishes using the original snapshot from parsing a replacement.
        runner = r'''import sys
sys.dont_write_bytecode=True
import importlib.util,json,pathlib,hashlib
root=pathlib.Path(sys.argv[1]); script=root/'companion/exact_checks.py'
spec=importlib.util.spec_from_file_location('snapshot_probe',script)
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
counts={pathlib.Path(name).name:0 for name in c.DATA_PINS}; replaced=[]
def interleave(event,args):
    if event!='open' or args[0] not in counts:
        return
    counts[args[0]]+=1
    if args[0]=='PROOF.md' and not replaced:
        manifest_path=root/'SOURCE_MANIFEST.json'
        manifest=json.loads(manifest_path.read_bytes())
        manifest['commit']='0'*40
        manifest['sources'][0]['sha256']='0'*64
        manifest['sources'][0]['git_blob_sha1']='0'*40
        manifest_path.write_bytes(c.canonical_bytes(manifest))
        excerpt_path=root/'source_excerpts.json'
        excerpts=json.loads(excerpt_path.read_bytes())
        excerpts['commit']='0'*40
        for entry in excerpts['excerpts']:
            if entry['repository_path']==manifest['sources'][0]['repository_path']:
                entry['source_sha256']='0'*64
        excerpt_path.write_bytes(c.canonical_bytes(excerpts));replaced.append(True)
sys.addaudithook(interleave)
result=c.main([])
summary={'result':result,'counts':counts,'replaced':bool(replaced),
         'manifest_on_disk_is_changed':hashlib.sha256((root/'SOURCE_MANIFEST.json').read_bytes()).hexdigest()!=c.DATA_PINS['SOURCE_MANIFEST.json']}
sys.stderr.write(json.dumps(summary)+'\n')
'''
        expected=invoke().stdout
        for optimized in (False,True):
            with tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp)/'source';clone_companion(root)
                command=[sys.executable,'-I','-B']
                if optimized:command.append('-O')
                result=subprocess.run(command+['-c',runner,str(root)],stdout=subprocess.PIPE,
                                      stderr=subprocess.PIPE,timeout=30,check=False)
            self.assertEqual(result.returncode,0,result.stderr.decode())
            self.assertEqual(result.stdout,expected)
            summary=json.loads(result.stderr)
            self.assertTrue(summary['replaced'])
            self.assertTrue(summary['manifest_on_disk_is_changed'])
            self.assertEqual(summary['result'],0)
            self.assertEqual(set(summary['counts'].values()),{1})

    def test_changed_data_fails_under_both_modes(self):
        for target in c.DATA_PINS:
            with tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp)/'source';script=clone_companion(root)
                with (root/target).open('ab') as stream:stream.write(b' ')
                for optimized in (False,True):
                    result=invoke(script,optimized=optimized)
                    self.assertNotEqual(result.returncode,0)
                    self.assertIn(b'data pin mismatch',result.stderr)

    def test_no_float_assert_network_eval_or_external_execution(self):
        source=SCRIPT.read_text();tree=ast.parse(source)
        self.assertFalse(any(isinstance(n,ast.Assert) for n in ast.walk(tree)))
        self.assertFalse(any(isinstance(n,ast.Constant) and isinstance(n.value,float) for n in ast.walk(tree)))
        forbidden={'subprocess','socket','urllib','requests','sympy','numpy','mpmath','ctypes'}
        for node in ast.walk(tree):
            if isinstance(node,ast.Import):
                self.assertFalse(any(alias.name.split('.')[0] in forbidden for alias in node.names))
            if isinstance(node,ast.ImportFrom):
                self.assertNotIn((node.module or '').split('.')[0],forbidden)
            if isinstance(node,ast.Call) and isinstance(node.func,ast.Name):
                self.assertNotIn(node.func.id,{'eval','exec','compile','__import__'})
        self.assertNotIn('Report296',source)


if __name__=='__main__':
    unittest.main()
