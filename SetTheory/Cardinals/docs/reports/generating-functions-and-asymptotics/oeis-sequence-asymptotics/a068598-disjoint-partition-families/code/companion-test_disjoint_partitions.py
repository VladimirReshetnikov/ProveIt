"""Exact, bounded API and CLI tests; checks remain active under Python -O."""
import ast
import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import disjoint_partitions as d

ROOT = Path(__file__).absolute().parent.parent
MODULE = Path(d.__file__).absolute()


class ExactTests(unittest.TestCase):
    def test_frozen_counts(self):
        actual = d.counts()
        self.assertEqual(actual, json.loads((ROOT/'data/counts.json').read_text()))
        self.assertEqual(actual['values'], list(map(str,d.SOURCE_TERMS[:25])))

    def test_frozen_full_verification(self):
        actual = d.verify()
        self.assertEqual(actual, json.loads((ROOT/'data/finite_checks.json').read_text()))
        self.assertEqual(sum(int(row['all_matchings_without_singleton']) for row in actual['matchings']),179455)
        self.assertEqual(actual['queens_extensions'][-1]['queens'],'92')

    def test_frozen_sources(self):
        self.assertEqual(d.sources(),json.loads((ROOT/'data/source_data.json').read_text()))
        self.assertEqual(len(d.sources()['values']),46)

    def test_maximal_not_maximum_or_all(self):
        n=8; edges=d._partitions(n); families=[]
        def rec(start,chosen,used):
            if all(used & d._mask(b) for b in edges):
                families.append(chosen)
            for j in range(start,len(edges)):
                mask=d._mask(edges[j])
                if not used & mask: rec(j+1,chosen+(edges[j],),used|mask)
        rec(0,(),0)
        self.assertEqual(len(families),3)
        self.assertEqual(sorted(map(len,families)),[2,3,4])
        self.assertTrue(all((8,) in family for family in families))
        self.assertEqual(d._enumerate(8)['all_matchings_without_singleton'],'11')

    def test_empty_and_two_part_codes(self):
        self.assertEqual(d._encode((),8),((),()))
        self.assertEqual(d._encode(((1,7),(2,6),(3,5)),8),((1,2,3),()))
        self.assertEqual(d.counts(0)['values'],['1'])
        self.assertEqual(d.verify(0,1,2)['matchings'],[])

    def test_parameter_validation(self):
        for bad in (True,False,1.0,'1',None,-1,25):
            with self.subTest(value=bad):
                with self.assertRaises(ValueError): d.counts(bad)
        for name,args in [('n',(-1,1,2)),('n',(25,1,2)),('queens',(1,0,2)),
                          ('queens',(1,9,2)),('round',(1,1,1)),('round',(1,1,100001))]:
            with self.subTest(name=name,args=args):
                with self.assertRaises(ValueError): d.verify(*args)
        for bad in (0,-1,True,2.0,'2',10**100+1):
            with self.assertRaises(ValueError): d.threshold(bad,0)
            with self.assertRaises(ValueError): d.integer_bounds(bad)

    def test_helper_work_caps(self):
        for method,values in [(d._partitions,(-1,46)),(d._recursive_partitions,(-1,25)),
                              (d._enumerate,(0,25)),(d._queen_permutations,(0,9)),
                              (d._clique_count,(0,19))]:
            for value in values:
                with self.assertRaises(ValueError): method(value)

    def test_exact_first_passage(self):
        self.assertEqual(d.threshold(1,0)['first_n'],0)
        self.assertEqual(d.threshold(2,6)['first_n'],6)
        self.assertEqual(d.threshold(3,8)['first_n'],8)
        self.assertEqual(d.threshold(4,8)['reached'],False)
        self.assertIsNone(d.threshold(10**100,24)['first_n'])
        vals=list(map(int,d.counts(24)['values']))
        for target in (2,3,4,8,75,76,888,1536,2535,4608):
            got=d.threshold(target,24)['first_n']
            self.assertEqual(got,next(i for i,x in enumerate(vals) if x>=target))

    def test_integer_brackets(self):
        self.assertEqual((d.integer_bounds(1)['lower_n'],d.integer_bounds(1)['upper_n']),(0,0))
        vals=list(map(int,d.counts(24)['values']))
        for target in range(2,4609):
            b=d.integer_bounds(target)
            first=next(i for i,x in enumerate(vals) if x>=target)
            self.assertLessEqual(b['lower_n'],first)
            self.assertGreaterEqual(b['upper_n'],first)
            k=b['factorial_k']; product=1
            for i in range(1,k+1): product*=2*i
            self.assertGreaterEqual(product,target)
            for n in range(2,b['lower_n']):
                self.assertLess(3**(n-1)*n**((n-2)//4),target)
        b=d.integer_bounds(10**100)
        self.assertLessEqual(b['lower_n'],b['upper_n'])
        self.assertLessEqual(b['factorial_k'],d.MAX_INVERSE_K)

    def test_fault_detection(self):
        bad=list(d.SOURCE_TERMS);bad[4]+=1
        with patch.object(d,'SOURCE_TERMS',tuple(bad)):
            with self.assertRaisesRegex(RuntimeError,'OEIS mismatch'):d.verify(4,1,2)
        with patch.object(d,'_recursive_partitions',return_value=()):
            with self.assertRaisesRegex(RuntimeError,'Partition generators disagree'):d.verify(1,1,2)
        with patch.object(d,'_clique_count',return_value=0):
            with self.assertRaisesRegex(RuntimeError,'Clique count mismatch'):d.verify(1,1,2)
        with self.assertRaises(RuntimeError):d._require(False,'deliberate fault')

    def test_production_has_no_assert_or_io_api(self):
        tree=ast.parse(MODULE.read_text())
        forbidden={'open','exec','eval','compile','input','__import__'}
        imports=set()
        for node in ast.walk(tree):
            self.assertNotIsInstance(node,ast.Assert)
            if isinstance(node,(ast.Import,ast.ImportFrom)):
                if isinstance(node,ast.Import): imports.update(x.name.split('.')[0] for x in node.names)
                else:imports.add(node.module.split('.')[0])
            if isinstance(node,ast.Call) and isinstance(node.func,ast.Name):
                self.assertNotIn(node.func.id,forbidden)
        self.assertLessEqual(imports,{'argparse','functools','itertools','json','re','sys'})

    def cli(self,args,optimized=False,cwd=None):
        cmd=[sys.executable,'-B']+(['-O'] if optimized else [])+[str(MODULE)]+args
        return subprocess.run(cmd,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=45)

    def test_cli_normal_optimized_identical_no_writes(self):
        with tempfile.TemporaryDirectory(prefix='report163-cli-') as directory:
            for args in (['counts'],['verify'],['sources'],['threshold','--value','888'],
                         ['bounds','--value',str(10**100)]):
                first=self.cli(args,cwd=directory);second=self.cli(args,True,cwd=directory)
                self.assertEqual(first.returncode,0,first.stderr)
                self.assertEqual(second.returncode,0,second.stderr)
                self.assertEqual(first.stdout,second.stdout)
                self.assertEqual(first.stderr,b'')
                self.assertEqual(json.dumps(json.loads(first.stdout),sort_keys=True,indent=2)+'\n',first.stdout.decode())
            self.assertEqual(list(Path(directory).iterdir()),[])

    def test_cli_invalid_tokens_and_caps(self):
        for token in ('-1','+1','01','1.0',' 1','1 ','١','９',str(10**101)):
            result=self.cli(['counts','--max-n',token])
            self.assertEqual(result.returncode,2,(token,result.stderr))
            self.assertEqual(result.stdout,b'')
        for args in (['counts','--max-n','25'],['verify','--queen-to','9'],
                     ['verify','--rounding-to','100001'],['bounds','--value','0'],
                     ['threshold','--value',str(10**100+1)],['sources','--output','out']):
            result=self.cli(args)
            self.assertEqual(result.returncode,2,result.stderr)
            self.assertEqual(result.stdout,b'')

    def test_failed_check_has_no_partial_json(self):
        with patch.object(sys,'argv',['disjoint_partitions.py','verify']), \
             patch.object(d,'verify',side_effect=RuntimeError('injected')), \
             contextlib.redirect_stdout(io.StringIO()) as out, \
             contextlib.redirect_stderr(io.StringIO()) as err:
            status=d.main()
        self.assertEqual(status,1)
        self.assertEqual(out.getvalue(),'')
        self.assertIn('injected',err.getvalue())


if __name__=='__main__':unittest.main()
