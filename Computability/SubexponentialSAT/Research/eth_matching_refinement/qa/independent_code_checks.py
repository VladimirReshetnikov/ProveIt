"""Independent finite component checks; not end-to-end SAT or proof validation."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'code'))
import refinement as r

COUNTS = {}

class IndependentChecks(unittest.TestCase):
    def test_exhaustive_multigraph_coloring(self):
        cases = 0
        for multiplicities in product(range(4), repeat=6):
            edges = [(i // 3, i % 3) for i, n in enumerate(multiplicities) for _ in range(n)]
            groups = r.color_matchings(edges)
            self.assertEqual(Counter(e for g in groups for e in g), Counter(edges))
            for g in groups:
                self.assertEqual(len(set(x for x, _ in g)), len(g))
                self.assertEqual(len(set(y for _, y in g)), len(g))
            if edges:
                degree = max(max(Counter(x for x, _ in edges).values()),
                             max(Counter(y for _, y in edges).values()))
                self.assertLessEqual(len(groups), 2 * degree - 1)
            else:
                self.assertEqual(groups, [])
            cases += 1
        COUNTS['exhaustive_multigraphs'] = cases

    def test_potential_against_full_completion_enumeration(self):
        edges = [(0,0),(0,0),(0,1),(1,0),(1,1)]
        vertices = [('L',0),('L',1),('R',0),('R',1)]
        checks = 0
        for labels, lam in product((2,3),(1,2,4)):
            groups, tau, hs = r.packing_data(edges, labels, lam)
            t = F(lam+1, lam)
            for values in product(range(-1, labels), repeat=len(vertices)):
                partial = {v: a for v, a in zip(vertices, values) if a != -1}
                missing = [v for v in vertices if v not in partial]
                direct = F(0)
                for completion in product(range(labels), repeat=len(missing)):
                    assignment = {**partial, **dict(zip(missing, completion))}
                    for g,h in zip(groups,hs):
                        loads = Counter((assignment['L',x],assignment['R',y]) for x,y in g)
                        direct += sum((t**(loads[a,b]-h) for a,b in product(range(labels), repeat=2)), F(0))
                direct /= labels**len(missing)
                self.assertEqual(r.potential(groups,hs,labels,lam,partial),direct)
                checks += 1
        COUNTS['enumerated_partial_assignment_checks'] = checks

    def test_nonvacuous_thresholds_and_ties(self):
        cases = [( [(i,i) for i in range(m)], labels, lam)
                 for m,labels,lam in [(24,2,1),(40,2,2),(64,2,4),(24,3,1)]]
        cases += [([(i,i) for i in range(32)]*2,2,1),
                  ([(i,i) for i in range(32)] + [(i,(i+1)%32) for i in range(32)],2,1)]
        tie_checks = 0
        for edges,labels,lam in cases:
            z = r.label_graph(edges,labels,lam)
            self.assertTrue(all(h <= len(g) for g,h in zip(z['groups'],z['thresholds'])))
            self.assertLessEqual(z['initial'], F(1,8))
            self.assertLessEqual(z['final'], z['initial'])
            partial = {}
            for vertex in sorted(z['assignment']):
                vals = [r.potential(z['groups'],z['thresholds'],labels,lam,{**partial,vertex:a}) for a in range(labels)]
                self.assertEqual(z['assignment'][vertex], vals.index(min(vals)))
                partial[vertex] = z['assignment'][vertex]
                tie_checks += 1
            for g,h in zip(z['groups'],z['thresholds']):
                loads = Counter((partial['L',x],partial['R',y]) for x,y in g)
                self.assertLess(max(loads.values()),h)
        for edges in ([], [(0,0)], [(0,0)]*10):
            z=r.label_graph(edges,1,1)
            self.assertEqual(z['loads'],[[len(edges)]])
            self.assertTrue(all(a == 0 for a in z['assignment'].values()))
        COUNTS['nonvacuous_packing_cases'] = len(cases)
        COUNTS['explicit_minimum_label_checks'] = tie_checks
        COUNTS['empty_or_single_label_cases'] = 3

    def test_budget_threshold_boundaries(self):
        cases=0
        for divisor in (1,7,20,53):
            for a in range(1,101):
                # bit_length locates the two integer lambdas bracketing each exact crossing.
                power=54**(divisor*a)
                upper_lam=power.bit_length()
                self.assertEqual(r.exact_budget(upper_lam-1,divisor),a-1)
                self.assertEqual(r.exact_budget(upper_lam,divisor),a)
                cases+=2
        COUNTS['direct_power_budget_boundary_cases']=cases

    def test_schedule_boundaries(self):
        cases=0
        lambdas={2,10**6,10**9,10**12,10**24}
        lambdas.update(18**d+offset for d in range(1,13) for offset in (-1,0,1))
        for lam,root_constant in product(sorted(lambdas),(1,2,7,100)):
            z=r.schedule(lam,root_constant)
            self.assertGreaterEqual(18**z['depth'],root_constant*lam)
            self.assertLess(18**(z['depth']-1),root_constant*lam)
            self.assertEqual(z['gap'],6*r.ceil_log2(lam))
            self.assertEqual(z['U'],z['budget']-(z['depth']+1)*z['gap']-z['k']**2)
            self.assertEqual(z['basic_guard'],z['U']>0 and min(z['u'])>=2)
            self.assertEqual(z['u'],[8*max(z['U'],0)//9**(d+1) for d in range(z['depth']+1)])
            for d,(u,a) in enumerate(zip(z['u'],z['a'])):
                self.assertEqual(a-(z['a'][d-1] if d else 0),u+z['gap'])
            if z['U']>0:
                self.assertLessEqual(sum(z['u']),z['U'])
                self.assertLessEqual(z['a'][-1],z['budget']-z['k']**2)
            else:
                self.assertFalse(z['basic_guard'])
            cases+=1
        COUNTS['schedule_boundary_cases']=cases

    def test_precision_minimality_and_mode_polynomial(self):
        cases=rows=0
        for a in range(1,17):
            for u in range(1,a+1):
                for M,p in product(sorted({u,u+1,2*u,31}),(1,2,23)):
                    z=r.precision(M,a,u,p)
                    mass=z['total_conditions']//z['h']
                    self.assertGreater(z['h']*mass,z['degree'])
                    self.assertLessEqual((z['h']-1)*mass,z['degree'])
                    for row in z['rows']:
                        i,q,D=row['i'],row['q'],row['D']
                        loss=D*sum((F(j,2**j)*(q-z['h']*max(0,u-i-j)) for j in range(1,a-i+1)),F(0))
                        self.assertEqual(row['loss'],loss)
                        self.assertEqual(row['precision'],p+loss+(q-1)*(a-i+1))
                        rows+=1
                    cases+=1
        partitions=0
        for precision,colors in product(range(1,36),range(4)):
            polynomial={0:1}
            for b in range(precision):
                # Independent v_2(b!) formula, without bit_count.
                valuation=sum(b//2**j for j in range(1,b.bit_length()+1))
                weight=1+b+2*valuation
                self.assertEqual(r.mode_weight(b),weight)
                for _ in range(colors):
                    new=Counter()
                    for old_degree,coefficient in polynomial.items():
                        for exponent in range((precision-1-old_degree)//weight+1):
                            new[old_degree+exponent*weight]+=coefficient
                    polynomial=dict(new)
            self.assertEqual(r.weighted_count(precision,colors),sum(polynomial.values()))
            partitions+=1
        COUNTS['independent_precision_parameters']=cases
        COUNTS['independent_precision_rows']=rows
        COUNTS['generating_polynomial_mode_cases']=partitions

    def test_integer_log_helper_regression(self):
        # This fails on the initial helper because integer division produces float.
        lower,upper=r.log_interval_positive(2,32)
        self.assertIsInstance(lower,F)
        self.assertIsInstance(upper,F)
        certified_lower,certified_upper=r.log_interval_positive(F(2),64)
        self.assertLessEqual(lower,certified_lower)
        self.assertGreaterEqual(upper,certified_upper)
        COUNTS['integer_log_helper_regression']=1

if __name__=='__main__':
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(IndependentChecks))
    out={'success':result.wasSuccessful(),'test_methods':result.testsRun,'optimization':sys.flags.optimize,
         'scope':'Independent finite component checks, not a complete SAT solver or formal proof.', 'counts':COUNTS}
    path=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('independent-code-checks.json')
    path.write_text(json.dumps(out,indent=2)+'\n')
    sys.exit(not result.wasSuccessful())
