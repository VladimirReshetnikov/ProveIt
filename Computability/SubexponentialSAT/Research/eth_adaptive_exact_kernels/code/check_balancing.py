from pathlib import Path
from fractions import Fraction as F
from itertools import product
import json,sys,unittest,random
from sparse_balancing import balance,prepare

COUNTS={}
class Checks(unittest.TestCase):
    def test_exhaustive_outputs(self):
        cases=steps=0
        fixtures=[[[v[0],v[1]],[v[2],v[3]]] for v in product(range(3),repeat=4)]
        fixtures += [[],[[],[]],[[0,0,0]],[[0],[3],[0]],[[3,0,2],[0,1,0],[2,1,3]]]
        for adj in fixtures:
            for Q in (1,2,3,5):
                for h in (2,8):
                    refs=[balance(adj,Q,h,m,certificate=True) for m in ('cubic','dense','sparse')]
                    for out in refs[1:]:
                        for key in ('row_labels','column_labels','loads','initial','final','steps'):
                            self.assertEqual(refs[0][key],out[key],(adj,Q,h,key))
                    result=refs[-1]
                    direct=[[0]*Q for _ in range(Q)]
                    for i,row in enumerate(adj):
                        for j,w in enumerate(row):direct[result['row_labels'][i]][result['column_labels'][j]]+=w
                    self.assertEqual(direct,result['loads'])
                    steps+=len(result['steps']);cases+=1
        COUNTS['three_method_graph_cases']=cases;COUNTS['identical_step_certificates']=steps

    def test_completion_enumeration(self):
        cases=0
        for adj in ([[1,1],[1,0]],[[2,0,1],[0,1,2]],[[0,0],[0,0]]):
            for Q in (2,3):
                out=balance(adj,Q,3,'sparse',certificate=True)
                z=prepare(adj,Q,3);q=z['q'];n=len(adj[0]);prefix=[]
                for j,step in enumerate(out['steps']):
                    expected=[]
                    for b in range(Q):
                        total=F(0)
                        for tail in product(range(Q),repeat=n-j-1):
                            labels=prefix+[b]+list(tail);loads=[[0]*Q for _ in range(Q)]
                            for i,row in enumerate(adj):
                                for k,w in enumerate(row):loads[out['row_labels'][i]][labels[k]]+=w
                            total+=sum((q**v for row in loads for v in row),F(0))
                        expected.append(total/(Q**(n-j-1)))
                    self.assertEqual(expected,step['scores'])
                    self.assertEqual(min(range(Q),key=lambda b:(expected[b],b)),step['selected'])
                    prefix.append(step['selected']);cases+=1
        COUNTS['direct_completion_steps']=cases

    def test_random_sparse(self):
        rng=random.Random(20261027);cases=0
        for Q in (2,4,8,16):
            for repeat in range(8):
                adj=[[rng.randrange(1,4) if rng.random()<.16 else 0 for _ in range(7)] for _ in range(6)]
                a=balance(adj,Q,4,'dense',certificate=True);b=balance(adj,Q,4,'sparse',certificate=True)
                for key in ('row_labels','column_labels','loads','initial','final','steps'):self.assertEqual(a[key],b[key])
                self.assertLessEqual(b['stats']['score_terms'],a['stats']['score_terms']);cases+=1
        COUNTS['random_sparse_cases']=cases

    def test_rejection(self):
        for args in (([[1]],0,8),([[1]],2,1),([[1]],2.0,8),([[1,2],[3]],2,8),([[-1]],2,8),([[1.0]],2,8)):
            with self.assertRaises(ValueError):balance(*args)
        with self.assertRaises(ValueError):balance([[1]],2,method='typo')
        COUNTS['negative_controls']=7

if __name__=='__main__':
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(Checks))
    out={'success':result.wasSuccessful(),'methods':result.testsRun,'optimization':sys.flags.optimize,'counts':COUNTS,
         'scope':'Exact component equivalence, not full SAT verification.'}
    target=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent.parent/'results/balancing_checks.json'
    target.write_text(json.dumps(out,indent=2)+'\n');sys.exit(not result.wasSuccessful())
