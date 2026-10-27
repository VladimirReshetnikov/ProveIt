"""Finite exact component checks. Does not validate a complete SAT algorithm."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json, math, sys, unittest
from refinement import *

COUNTS={}
class Checks(unittest.TestCase):
    def test_matching_potential(self):
        fixtures=[[(0,0),(0,0),(1,0),(1,1),(2,1)],
                  [(0,0),(0,1),(1,1),(1,2),(2,2),(2,0)],
                  [(0,0),(1,1),(2,2)],[(0,0),(0,1),(0,2)]]
        cases=[(e,N,l) for e in fixtures for N in (2,3) for l in (1,2,4)]
        for counts in product(range(3), repeat=4):
            e=[(j//2,j%2) for j,c in enumerate(counts) for _ in range(c)]
            cases.append((e,2,2))
        vertices=0;thresholds=0
        for e,N,l in cases:
            z=label_graph(e,N,l)
            self.assertLessEqual(z['initial'], F(1,8))
            self.assertLessEqual(z['final'],z['initial'])
            vals=[z['initial']]+z['trace']
            self.assertTrue(all(b<=a for a,b in zip(vals,vals[1:])))
            vertices+=len(z['trace'])
            self.assertEqual(sum(map(sum,z['loads'])),len(e))
            for g,h in zip(z['groups'],z['thresholds']):
                self.assertEqual(len({x for x,y in g}),len(g))
                self.assertEqual(len({y for x,y in g}),len(g))
                for a in range(N):
                    for b in range(N):
                        load=sum(z['assignment']['L',x]==a and z['assignment']['R',y]==b for x,y in g)
                        self.assertLess(load,h);thresholds+=1
            if e:
                bound=F(l+1,l)*F(len(e),N*N)+2*len(z['groups'])*l*z['tau']
                self.assertLess(max(map(max,z['loads'])),bound)
        COUNTS['packing_graph_cases']=len(cases)
        COUNTS['exact_conditional_average_checks']=vertices
        COUNTS['matching_class_threshold_checks']=thresholds

    def test_exact_log_budget(self):
        self.assertEqual(log_interval_positive(2,8),log_interval_positive(F(2),8))
        cases=list(range(1,513))+[1000,4096,10000]
        for lam in cases:
            a=exact_budget(lam)
            self.assertLessEqual(54**(20*a),1<<lam)
            self.assertGreater(54**(20*(a+1)),1<<lam)
        COUNTS['certified_budget_direct_power_cases']=len(cases)

    def test_schedule(self):
        cases=[2,10,100,1000,10**6,10**9,10**12,10**15,10**18,10**24]
        data=[]
        for lam in cases:
            z=schedule(lam)
            self.assertGreaterEqual(18**z['depth'],lam)
            if z['depth']:self.assertLess(18**(z['depth']-1),lam)
            if z['U']>0:
                self.assertLessEqual(sum(z['u']),z['U'])
                self.assertLessEqual(max(z['a']),z['budget']-z['k']**2)
                for d,u in enumerate(z['u']):
                    prev=z['a'][d-1] if d else 0
                    self.assertEqual(z['a'][d]-u,prev+z['gap'])
            data.append(z)
        COUNTS['schedule_cases']=len(cases)
        COUNTS['schedule_records']=data

    def test_precision(self):
        cases=nodes=0
        for a in range(1,9):
            for u in range(1,a+1):
                for M in range(u,20):
                    z=precision(M,a,u,7);cases+=1
                    self.assertGreater(z['total_conditions'],z['degree'])
                    for row in z['rows']:
                        i=row['i'];q=row['q'];D=row['D'];h=z['h'];nodes+=1
                        loss=D*sum((F(j,2**j)*(q-h*max(0,u-i-j)) for j in range(1,a-i+1)),F(0))
                        self.assertEqual(loss,row['loss'])
                        self.assertGreater(row['precision'],7)
                        self.assertLessEqual(loss,6*h*D)
                        self.assertLessEqual(row['precision'],7+6*h*D+3*M*(a+1))
        COUNTS['taper_parameter_cases']=cases;COUNTS['loss_sum_cases']=nodes

    def test_mode_count(self):
        cases=0
        def rec(weights,p,j):
            if j==len(weights):return 1
            return sum(rec(weights,p-e*weights[j],j+1) for e in range((p-1)//weights[j]+1))
        for p in range(1,23):
            for c in (1,2):
                weights=[mode_weight(b) for b in range(p) if mode_weight(b)<p for _ in range(c)]
                self.assertEqual(weighted_count(p,c),rec(weights,p,0));cases+=1
        COUNTS['partition_count_cases']=cases

    def test_negative_controls(self):
        for args in ((0,1,1,1),(1,1,2,1),(1,1,1,0)):
            with self.assertRaises(ValueError):precision(*args)
        with self.assertRaises(ValueError):schedule(1)
        with self.assertRaises(ValueError):exact_budget(0)
        with self.assertRaises(ValueError):mode_weight(-1)
        with self.assertRaises(ValueError):exact_budget(1,0)
        with self.assertRaises(ValueError):log_interval_positive(2,0)
        with self.assertRaises(ValueError):log_interval_positive(2.0,8)
        # Wrong label average must be detected, not silently accepted.
        groups,tau,hs=packing_data([(0,0)],2,2)
        parent=potential(groups,hs,2,2,{})
        wrong=potential(groups,hs,2,2,{('L',0):0})/2
        self.assertNotEqual(parent,wrong)
        COUNTS['negative_controls']=10

if __name__=='__main__':
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(Checks)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    out=dict(success=result.wasSuccessful(),test_methods=result.testsRun,
             python=sys.version,optimization=sys.flags.optimize,
             scope='Finite exact components only; no complete SAT solver, formal proof, or timing comparison.',counts=COUNTS)
    output=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent.parent/'results'/'verification.json'
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(out,indent=2)+'\n')
    sys.exit(0 if result.wasSuccessful() else 1)
