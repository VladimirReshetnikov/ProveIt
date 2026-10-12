"""Forced-difference contraction, original-model lifting and adaptive bypass."""
import json
import random
import unittest
from unittest.mock import patch
from fastunknot.cocycle_euler_flow import _minimize_difference, _minimize_difference_full
from fastunknot.cocycle_euler_verify import verify_difference_optimum
from fastunknot.integer_codec import json_safe


class EulerQuotientTests(unittest.TestCase):
    def test_random_forced_groups_against_full_network(self):
        rng = random.Random(261009520)
        for _ in range(240):
            n = rng.randrange(2,14);initial=[rng.randrange(-20,21) for _ in range(n)]
            groups=[rng.randrange(4) for _ in range(n)]
            constraints=[]
            for g in sorted(set(groups)):
                vs=[v for v in range(n) if groups[v]==g]
                for a,b in zip(vs,vs[1:]+vs[:1]):
                    constraints.append([a,b,initial[b]-initial[a]])
            for _ in range(2*n):
                a,b=rng.randrange(n),rng.randrange(n)
                constraints.append([a,b,initial[b]-initial[a]+rng.randrange(6)])
            edges=[[rng.randrange(n),rng.randrange(n),rng.randrange(-30,31),rng.randrange(5)] for _ in range(3*n)]
            # Reversed and parallel terms exercise aggregate-flow splitting.
            a,b,c,w=edges[0];edges.extend([[a,b,c,w],[b,a,-c,w]])
            old=_minimize_difference_full(n,edges,constraints,initial,lambda:None)
            new=_minimize_difference(n,edges,constraints,initial,lambda:None)
            self.assertEqual(old['certificate']['objective'],new['certificate']['objective'])
            self.assertTrue(verify_difference_optimum(n,edges,constraints,new['certificate']))
            self.assertLessEqual(new['stats']['quotient_nodes'],n)

    def test_one_way_tightness_is_not_equality_and_singletons_bypass(self):
        result=_minimize_difference(2,[[0,1,1,3]],[[0,1,0]],[0,0],lambda:None)
        self.assertEqual(result['certificate']['objective'],0)
        self.assertFalse(result['stats']['contracted'])
        self.assertEqual(result['stats']['quotient_nodes'],2)
        self.assertEqual(result['certificate']['potential'][1]-result['certificate']['potential'][0],-1)
        with self.assertRaises(ValueError):
            _minimize_difference(2,[],[[0,1,-1]],[0,0],lambda:None)

    def test_cycle_family_linear_lift_and_large_binary_gauge(self):
        for n in (8,16,32,1500):
            scale=(1<<20000) if n==1500 else 1
            initial=[v*scale for v in range(n)]
            edges=[[0,v,1-initial[v],1] for v in range(1,n)]
            constraints=[[v,(v+1)%n,initial[(v+1)%n]-initial[v]] for v in range(n)]
            work=[0]
            def tick():work[0]+=1
            result=_minimize_difference(n,edges,constraints,initial,tick)
            c=result['certificate']
            self.assertEqual(c['objective'],n-1)
            self.assertEqual(result['stats']['quotient_nodes'],1)
            self.assertEqual(result['stats']['augmentations'],0)
            self.assertLess(work[0],100*n)
            self.assertTrue(verify_difference_optimum(n,edges,constraints,json.loads(json.dumps(json_safe(c)))))
            if n<100:
                old=_minimize_difference_full(n,edges,constraints,initial,lambda:None)
                self.assertEqual(old['certificate']['objective'],c['objective'])
                self.assertEqual(old['stats']['augmentations'],n-1)

    def test_lift_gate_rejects_corruption_and_cancellation_propagates(self):
        edges=[[0,1,2,3],[1,2,1,2]];constraints=[[0,1,0],[1,0,0],[1,2,0],[2,1,0]]
        def cancel():raise RuntimeError('cancelled')
        with self.assertRaisesRegex(RuntimeError,'cancelled'):
            _minimize_difference(3,edges,constraints,[0,0,0],cancel)
        with patch('fastunknot.cocycle_euler_quotient.verify_difference_optimum',return_value=False):
            with self.assertRaisesRegex(ArithmeticError,'original-model replay'):
                _minimize_difference(3,edges,constraints,[0,0,0],lambda:None)
        result=_minimize_difference(3,edges,constraints,[0,0,0],lambda:None)
        bad=dict(result['certificate'],constraint_flows=[0]*len(constraints))
        self.assertFalse(verify_difference_optimum(3,edges,constraints,bad))

if __name__=='__main__':unittest.main()
