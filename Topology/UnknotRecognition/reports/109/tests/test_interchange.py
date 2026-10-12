import subprocess,sys,unittest
from pathlib import Path
from ordered_kernel.jsonio import dumps,loads,parse_input
from ordered_kernel import *
from integration.native_adapter import optimize_retained_occurrences

class InterchangeTests(unittest.TestCase):
    def test_large_roundtrip(self):
        obj={'cost':1<<16384,'nested':[-(1<<2000),1]}
        self.assertEqual(loads(dumps(obj)),obj)
    def test_duplicate_json(self):
        with self.assertRaises(ValueError):loads('{"a":1,"a":2}')
    def test_duplicate_rows(self):
        with self.assertRaises(ValueError):parse_input({'schema':'occurrence-matrix-v1','rows':[{'id':0,'entries':[]},{'id':0,'entries':[]}]})
    def test_duplicate_columns(self):
        with self.assertRaises(ValueError):parse_input({'schema':'occurrence-matrix-v1','rows':[{'id':0,'entries':[[1,1],[1,2]]}]})
    def test_cli(self):
        path=Path(__file__).resolve().parents[1]/'examples'/'weighted_block.json'
        p=subprocess.run([sys.executable,'-m','ordered_kernel',str(path)],capture_output=True,text=True,check=True)
        obj=loads(p.stdout);self.assertEqual(obj['cost'],2)
        self.assertEqual(obj['deferred_rows'],[1]);self.assertEqual(obj['residual_count_rows'][0]['entries'],[[1,2]])
    def test_adapter_keeps_deferred(self):
        a={0:{0:1,1:1},1:{0:1,1:2}}
        x=optimize_retained_occurrences(a)
        self.assertEqual(x['status'],'PARTIAL_MATRIX_KERNEL')
        self.assertEqual(set(x['retained_two_handle_ids']),set(x['saturated_retained_occurrences']))
    def test_adapter_refusal(self):
        a={0:{0:1},1:{0:1},2:{0:1}}
        x=optimize_retained_occurrences(a,method='ordered',limits=Limits(max_work=0))
        self.assertEqual(x['status'],'INCONCLUSIVE')

if __name__=='__main__':unittest.main()
