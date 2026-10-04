"""Regression and independent differential tests for the speed-up."""
from __future__ import annotations
import copy
import importlib.util
import itertools
import json
from pathlib import Path
import random
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'fast'))
sys.path.insert(0, str(ROOT/'tools'))
from fastunknot import Diagram, khovanov_rank, recognize, verify_rejection
from fastunknot.alexander import alexander_polynomial, evaluate
from fastunknot.jones import jones_evaluations, JonesLimit, verify_jones_witness
from fastunknot.modular import PRIME, alexander_witness, verify_alexander_witness, determinant_mod
from fastunknot.ordering import scan_order, best_scan_order
from fastunknot.scan import compose, inverse, clear_caches, cache_info, _compose_geometry
from fastunknot.simplify import descending_start, simplify
from fastunknot.splitting import decompose
from reference import one_component, brute_jones, reference_reduced_rank, trefoil_sum

# Load the untouched supplied package under an isolated name.
spec = importlib.util.spec_from_file_location('baseline_fastunknot', ROOT/'baseline/fastunknot/__init__.py',
    submodule_search_locations=[str(ROOT/'baseline/fastunknot')])
baseline = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = baseline
spec.loader.exec_module(baseline)
from baseline_fastunknot import scan as oldscan
from baseline_fastunknot.simplify import descending_start as olddescending


def random_diagrams(count, seed=401, max_n=9):
    rng = random.Random(seed)
    while count:
        strands = rng.choice([2, 3, 4, 5])
        word = [rng.choice([-1, 1])*rng.randrange(1,strands) for _ in range(rng.randrange(1,max_n+1))]
        if one_component(strands, word):
            yield Diagram.from_braid(strands,word), word
            count -= 1


class OptimizationTests(unittest.TestCase):
    def test_incremental_order_exactly_matches_baseline(self):
        for d,_ in random_diagrams(70, max_n=20):
            for i in range(d.crossings):
                self.assertEqual(scan_order(d.pd,i), oldscan.scan_order(d.pd,i))
            self.assertEqual(best_scan_order(d.pd,tries=4), oldscan.best_scan_order(d.pd,tries=4))

    def test_linear_descending_exactly_matches_baseline(self):
        for d,_ in random_diagrams(100, max_n=20):
            self.assertEqual(descending_start(d), olddescending(d))
            self.assertEqual(descending_start(d.mirror()), olddescending(d.mirror()))

    def test_jones_against_independent_state_sum(self):
        for d,word in random_diagrams(100, max_n=9):
            self.assertEqual(d.writhe(), -sum(1 if g>0 else -1 for g in word))
            result=jones_evaluations(d)
            self.assertEqual(result['normalized'], brute_jones(d), word)
            self.assertEqual(jones_evaluations(d,order=list(reversed(range(d.crossings))))['normalized'],
                             result['normalized'])
            rank=reference_reduced_rank(d)
            if rank==1:
                self.assertEqual(result['normalized'],[1,1])

    def test_even_port_rotations_and_label_permutations(self):
        rng=random.Random(591)
        for d,_ in random_diagrams(50,max_n=9):
            reference=jones_evaluations(d)['normalized']
            pd=[list(row[2:]+row[:2]) if rng.randrange(2) else list(row) for row in d.pd]
            rng.shuffle(pd)
            labels=list(range(2*d.crossings));rng.shuffle(labels)
            other=Diagram.from_pd([[labels[e]+100 for e in row] for row in pd])
            self.assertEqual(other.writhe(),d.writhe())
            self.assertEqual(jones_evaluations(other)['normalized'],reference)
            self.assertEqual(alexander_polynomial(other),alexander_polynomial(d))

    def test_modular_alexander_and_certificate_safety(self):
        for d,_ in random_diagrams(100,max_n=12):
            w=alexander_witness(d)
            if w:
                self.assertNotEqual(alexander_polynomial(d),[1])
                self.assertTrue(verify_alexander_witness(d,w))
                bad=dict(w,minor_determinant=(w['minor_determinant']+1)%PRIME)
                self.assertFalse(verify_alexander_witness(d,bad))
            if alexander_polynomial(d)==[1]:
                self.assertIsNone(w)
        self.assertEqual(determinant_mod([[0,2],[3,4]]),PRIME-6)
        self.assertEqual(determinant_mod([]),1)
        self.assertEqual(determinant_mod([[1,2],[2,4]]),0)
        with self.assertRaises(ValueError):determinant_mod([[1]],15)

    def test_rejection_replay_and_tampering(self):
        for name in ('trefoil','conway','kinoshita_terasaka','torus_3_5'):
            d=Diagram.from_json(json.loads((ROOT/'fast/examples'/f'{name}.json').read_text()))
            result=recognize(d).to_json()
            self.assertTrue(verify_rejection(d,result),name)
            bad=copy.deepcopy(result)
            bad['evidence']['witness']['prime']=15
            self.assertFalse(verify_rejection(d,bad))
            self.assertFalse(verify_rejection(Diagram.from_pd([]),result))
            self.assertFalse(verify_rejection(d,{'status':'KNOTTED'}))
            for malformed in (None, [], 1, 'invalid', {'status':'KNOTTED', 'evidence':[]},
                              {'status':'KNOTTED', 'evidence':{'witness':None}}):
                self.assertFalse(verify_rejection(d, malformed))
            self.assertFalse(verify_alexander_witness(d, []))
            self.assertFalse(verify_jones_witness(d, []))
        # R2 moves occur before the eventual trefoil witness.
        d=Diagram.from_braid(2,[1,1,1,1,-1])
        result=recognize(d).to_json()
        self.assertTrue(result['evidence']['reidemeister_trace'])
        self.assertTrue(verify_rejection(d,result))
        result['evidence']['reidemeister_trace'][0]['crossings']=[999]
        self.assertFalse(verify_rejection(d,result))

    def test_markowitz_lifo_dense_and_factored_agree(self):
        for d,word in random_diagrams(45,seed=225,max_n=8):
            reference=reference_reduced_rank(d)
            for pivot in ('lifo','markowitz'):
                direct=khovanov_rank(d.pd,pivot=pivot,factor_connected=False,check_d_squared=True)
                factored=khovanov_rank(d.pd,pivot=pivot,check_d_squared=True)
                self.assertEqual(direct['reduced_rank'],reference,word)
                self.assertEqual(factored['by_degree'],direct['by_degree'],word)

    def test_nonhomogeneous_unit_inverse_and_multiplication(self):
        rng=random.Random(844)
        for r in range(1,7):
            arcs=[frozenset((2*i,2*i+1)) for i in range(r)]
            matching=frozenset(arcs)
            monomials=[frozenset(arcs[i] for i in range(r) if mask>>i&1) for mask in range(1<<r)]
            for _ in range(20):
                f=frozenset(m for m in monomials if rng.randrange(2))|{frozenset()}
                g=frozenset(m for m in monomials if rng.randrange(2))
                self.assertEqual(compose(f,inverse(f,matching),matching,matching,matching),{frozenset()})
                self.assertEqual(compose(f,g,matching,matching,matching),
                                 _compose_geometry(f,g,matching,matching,matching))

    def test_connected_sum_compact_rank_and_degrees(self):
        for k in range(1,5):
            d=trefoil_sum(k)
            leaves,cuts=decompose(d)
            self.assertEqual(len(leaves),k)
            self.assertEqual(sorted(i for f in leaves for i in f.indices),list(range(3*k)))
            factored=khovanov_rank(d.pd,check_d_squared=True)
            direct=khovanov_rank(d.pd,factor_connected=False)
            self.assertEqual(factored['by_degree'],direct['by_degree'])
            self.assertEqual(factored['reduced_rank'],3**k)
        for k in (8,20,50):
            result=khovanov_rank(trefoil_sum(k).pd,max_objects=18)
            self.assertEqual(result['reduced_rank'],3**k)
            self.assertEqual(result['stats']['factor_count'],k)
            self.assertLessEqual(result['stats']['max_objects_before_elimination'],18)

    def test_budgets_and_bad_orders(self):
        d=Diagram.from_braid(3,[1,2]*5)
        for order in ([0], list(range(d.crossings-1))+[0], list(range(1,d.crossings+1)),
                      [False]+list(range(1,d.crossings))):
            with self.assertRaises(ValueError):khovanov_rank(d.pd,order=order)
            with self.assertRaises(ValueError):jones_evaluations(d,order=order)
        with self.assertRaises(JonesLimit):jones_evaluations(d,max_states=1)
        result=recognize(d,use_alexander=False,max_jones_states=1)
        self.assertEqual(result.status,'KNOTTED')
        self.assertEqual(result.method,'reduced-khovanov-F2-scan')
        self.assertIn('jones_filter_skipped',result.evidence)
        for bad in (-1,float('inf'),float('nan')):
            with self.assertRaises(ValueError):recognize(d,seconds=bad)
        self.assertEqual(recognize(d,seconds=0).status,'UNKNOWN')
        self.assertEqual(recognize(d,use_alexander=False,use_jones=False,max_objects=1).status,'UNKNOWN')
        self.assertEqual(recognize(d,use_modular=False,use_jones=False).method,'alexander-polynomial')

    def test_caches_are_bounded_and_clearable(self):
        clear_caches()
        d=Diagram.from_braid(2,[1]*3)
        khovanov_rank(d.pd)
        info=cache_info()
        for value in info.values():
            self.assertIsNotNone(value['maxsize'])
            self.assertLessEqual(value['currsize'],value['maxsize'])
        clear_caches()
        self.assertTrue(all(value['currsize']==0 for value in cache_info().values()))

if __name__=='__main__':unittest.main()
