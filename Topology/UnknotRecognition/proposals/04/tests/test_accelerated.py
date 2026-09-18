from __future__ import annotations
import copy
import importlib.util
import itertools
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'fast'))
from fastunknot import Diagram, DiagramError, recognize, khovanov_rank
from fastunknot import scan
from fastunknot.alexander import alexander_polynomial
from fastunknot.factor import (connected_sum, decompose, verify_decomposition,
                               close_cut, factored_khovanov_rank)
from fastunknot.jones import bracket_evaluation, verify_obstruction
from fastunknot.simplify import descending_start
from fastunknot.verify import verify_result
from reference_cube import reference_reduced_rank, one_component

# Import the unchanged baseline under a different package name in this process.
spec = importlib.util.spec_from_file_location(
    'baseline_fastunknot', ROOT / 'baseline/fastunknot/__init__.py',
    submodule_search_locations=[str(ROOT / 'baseline/fastunknot')])
base = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = base
spec.loader.exec_module(base)
from baseline_fastunknot import scan as oldscan
from baseline_fastunknot.simplify import descending_start as olddescending


def load(name):
    return Diagram.from_json(json.loads((ROOT / 'fast/examples' / name).read_text()))


def random_diagrams(count, seed=71, maximum=9):
    rng = random.Random(seed)
    for _ in range(count):
        while True:
            strands = rng.randint(2, 5)
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randint(strands - 1, maximum))]
            if one_component(strands, word):
                yield Diagram.from_braid(strands, word)
                break


def brute_bracket(d, a, modulus):
    """Independent full state sum on 4n darts, no frontier/glue code."""
    n = d.crossings
    ai = pow(a, -1, modulus)
    delta = (-a*a-ai*ai) % modulus
    if not n:
        return delta
    alpha = d.alpha()
    value = 0
    for state in range(1 << n):
        parent = list(range(4*n))
        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x
        def union(x,y):
            parent[find(x)] = find(y)
        for x,y in enumerate(alpha):
            union(x,y)
        for i in range(n):
            pairs = ((0,3),(1,2)) if state >> i & 1 else ((0,1),(2,3))
            for x,y in pairs:
                union(4*i+x,4*i+y)
        circles = len({find(i) for i in range(4*n)})
        value += pow(a,n-2*state.bit_count(),modulus)*pow(delta,circles,modulus)
    return value % modulus


def normalized(e):
    delta = (-(e.a**2) - pow(e.a,-2,e.modulus)) % e.modulus
    return e.bracket * pow(delta,-1,e.modulus) * pow(-e.a**3,-e.writhe,e.modulus) % e.modulus


def matchings(points):
    if not points:
        yield frozenset()
        return
    x = points[0]
    for i,y in enumerate(points[1:],1):
        rest = points[1:i]+points[i+1:]
        for m in matchings(rest):
            yield m | {frozenset((x,y))}


def random_morphism(a,b,rng):
    keys = sorted(set(oldscan.circles(a,b).values()), key=sorted)
    return {frozenset(keys[i] for i in range(len(keys)) if bits >> i & 1)
            for bits in range(1 << len(keys)) if rng.randrange(2)}


class AlgebraTests(unittest.TestCase):
    def test_all_128_three_arc_units(self):
        m=frozenset(frozenset((2*i,2*i+1)) for i in range(3))
        keys=sorted(m,key=sorted)
        monomials=[frozenset(keys[i] for i in range(3) if b>>i&1) for b in range(8)]
        for mask in range(128):
            f={frozenset()} | {monomials[i+1] for i in range(7) if mask>>i&1}
            self.assertEqual(scan.inverse(f,m),oldscan.inverse(f,m))
            self.assertEqual(scan.compose(f,f,m,m,m),{frozenset()})

    def test_1200_morphism_compositions(self):
        rng=random.Random(41)
        def planar(m):
            arcs=[tuple(sorted(pair)) for pair in m]
            return not any(a<c<b<d or c<a<d<b for a,b in arcs for c,d in arcs)
        choices=[m for m in matchings(tuple(range(6))) if planar(m)]
        for _ in range(1200):
            a,b,c=(rng.choice(choices) for _ in range(3))
            f,g=random_morphism(a,b,rng),random_morphism(b,c,rng)
            self.assertEqual(scan.compose(f,g,a,b,c),oldscan.compose(f,g,a,b,c))

    def test_immutable_composition_cache(self):
        m=frozenset((frozenset((0,1)),)); one={frozenset()}
        first=scan.compose(one,one,m,m,m); first.clear()
        self.assertEqual(scan.compose(one,one,m,m,m),one)

    def test_bounded_caches(self):
        for info in scan.cache_info().values():
            self.assertIsNotNone(info['maxsize'])
            self.assertLessEqual(info['currsize'],info['maxsize'])

    def test_60_scan_baseline_and_pivot_comparisons(self):
        for d in random_diagrams(60,maximum=9):
            a=oldscan.khovanov_rank(d.pd)
            b=scan.khovanov_rank(d.pd,check_d_squared=True)
            c=scan.khovanov_rank(d.pd,pivot_strategy='stack')
            self.assertEqual(a['by_degree'],b['by_degree'])
            self.assertEqual(b['by_degree'],c['by_degree'])

    def test_independent_cubes_80_random_diagrams(self):
        for d in random_diagrams(80,seed=19,maximum=8):
            self.assertEqual(scan.khovanov_rank(d.pd)['reduced_rank'],reference_reduced_rank(d))

    def test_independent_cubes_named(self):
        for name in ('conway.json','kinoshita_terasaka.json','hard_unknot_8.json','torus_3_5.json'):
            d=load(name)
            self.assertEqual(scan.khovanov_rank(d.pd)['reduced_rank'],reference_reduced_rank(d))

    def test_supplied_36_crossing_stress_with_d_squared(self):
        d=Diagram.from_json(json.loads((ROOT/'benchmarks/inputs/five_braid_36.json').read_text()))
        r=khovanov_rank(d.pd,check_d_squared=True,seconds=30)
        self.assertEqual(r['reduced_rank'],2949)
        # Independent integer Alexander determinant agrees here; determinant
        # equality is a check, not a general formula for Khovanov rank.
        from fastunknot.alexander import evaluate
        self.assertEqual(abs(evaluate(alexander_polynomial(d),-1)),2949)


class JonesTests(unittest.TestCase):
    def test_100_independent_state_sums(self):
        for d in random_diagrams(100,seed=21,maximum=8):
            for a,mod in ((2,1000000007),(3,101),(2,15)):
                ev=bracket_evaluation(d,a=a,modulus=mod,max_states=None)
                self.assertEqual(ev.bracket,brute_bracket(d,a,mod))

    def test_no_false_positives_on_small_unknots(self):
        for d in random_diagrams(100,seed=25,maximum=8):
            if reference_reduced_rank(d)==1:
                self.assertFalse(bracket_evaluation(d).obstructs_unknot)

    def test_order_relabel_rotation_and_mirror(self):
        rng=random.Random(55)
        for d in random_diagrams(40,seed=29,maximum=9):
            ev=bracket_evaluation(d)
            rows=[list(row[2:]+row[:2]) if rng.randrange(2) else list(row) for row in d.pd]
            rng.shuffle(rows)
            changed=Diagram.from_pd([[100-7*x for x in row] for row in rows])
            self.assertEqual(normalized(ev),normalized(bracket_evaluation(changed)))
            self.assertEqual(d.writhe(),changed.writhe())
            self.assertEqual(alexander_polynomial(d),alexander_polynomial(changed))
            self.assertEqual(normalized(bracket_evaluation(d.mirror())),
                             normalized(bracket_evaluation(d,a=pow(2,-1,1000000007))))
            order=list(range(d.crossings));rng.shuffle(order)
            self.assertEqual(ev.bracket,bracket_evaluation(d,order=order).bracket)

    def test_reidemeister_two_and_braid_relation(self):
        rng=random.Random(57)
        for d in random_diagrams(20,seed=37,maximum=7):
            # Direct state-sum equality under local R2 reductions already
            # follows here from comparing to the reduced diagram.
            from fastunknot.simplify import simplify
            reduced,_=simplify(d)
            self.assertEqual(normalized(bracket_evaluation(d)),
                             normalized(bracket_evaluation(reduced)))
        for suffix in ([1],[2],[1,1,1],[2,2,2]):
            a=Diagram.from_braid(3,[1,2,1]+list(suffix))
            b=Diagram.from_braid(3,[2,1,2]+list(suffix))
            self.assertEqual(normalized(bracket_evaluation(a)),normalized(bracket_evaluation(b)))

    def test_named_obstructions(self):
        for name in ('conway.json','kinoshita_terasaka.json','trefoil.json','figure_eight.json'):
            ev=bracket_evaluation(load(name));self.assertTrue(ev.obstructs_unknot)
            self.assertTrue(verify_obstruction(load(name),ev.to_json()))
        for name in ('unknot.json','unknot_braid40.json','hard_unknot_8.json'):
            self.assertFalse(bracket_evaluation(load(name)).obstructs_unknot)

    def test_zero_delta_and_nonprime_modulus(self):
        d=load('trefoil.json')
        ev=bracket_evaluation(d,a=1,modulus=2)
        self.assertEqual(ev.bracket,0)
        self.assertFalse(ev.obstructs_unknot)
        self.assertEqual(bracket_evaluation(d,a=2,modulus=15).bracket,brute_bracket(d,2,15))

    def test_equality_is_inconclusive(self):
        d=load('trefoil.json')
        self.assertFalse(bracket_evaluation(d,a=1,modulus=2).obstructs_unknot)
        self.assertEqual(recognize(d,use_jones=False,use_alexander=False).status,'KNOTTED')

    def test_tampering(self):
        d=load('conway.json'); ev=bracket_evaluation(d).to_json()
        for key in ('bracket','unknot_bracket','writhe'):
            bad=copy.deepcopy(ev);bad[key]+=1
            self.assertFalse(verify_obstruction(d,bad))
        bad=copy.deepcopy(ev);bad['order']=bad['order'][:-1]
        self.assertFalse(verify_obstruction(d,bad))


class DecompositionTests(unittest.TestCase):
    def test_trefoil_powers_and_degree_convolution(self):
        t=load('trefoil.json');d=Diagram.from_pd([])
        for k in range(1,5):
            d=connected_sum(d,t)
            factors,e=decompose(d)
            self.assertEqual(len(factors),k)
            self.assertEqual(factors,verify_decomposition(d,e))
            fact=factored_khovanov_rank(d)
            self.assertEqual(fact['reduced_rank'],3**k)
            self.assertEqual(fact['by_degree'],khovanov_rank(d.pd)['by_degree'])

    def test_mixed_connected_sums(self):
        ds=list(random_diagrams(12,seed=7,maximum=6))
        for a,b in zip(ds[::2],ds[1::2]):
            joined=connected_sum(a,b)
            fact=factored_khovanov_rank(joined)
            self.assertEqual(fact['reduced_rank'],reference_reduced_rank(a)*reference_reduced_rank(b))
            self.assertEqual(fact['by_degree'],khovanov_rank(joined.pd)['by_degree'])

    def test_conway_power_without_expansion(self):
        t=load('conway.json');d=Diagram.from_pd([])
        for _ in range(12):d=connected_sum(d,t)
        r=factored_khovanov_rank(d)
        self.assertEqual(r['reduced_rank'],33**12)
        self.assertEqual(sum(r['by_degree'].values()),2*33**12)
        self.assertTrue(all(f['crossings']==11 for f in r['factors']))
        self.assertEqual(recognize(d).status,'KNOTTED')

    def test_all_unknot_factors(self):
        d=connected_sum(load('hard_unknot_8.json'),load('hard_unknot_8.json'))
        r=recognize(d,use_reduction=False,use_descending=False)
        self.assertEqual(r.status,'UNKNOT')
        self.assertEqual(r.method,'connected-sum')
        self.assertTrue(verify_result(d,r.to_json()))

    def test_bad_partitions_and_tampering(self):
        d=connected_sum(load('trefoil.json'),load('figure_eight.json'))
        factors,ev=decompose(d)
        bad=copy.deepcopy(ev);bad['cuts'][0]['left_crossings']=[]
        with self.assertRaises(ValueError):verify_decomposition(d,bad)
        bad=copy.deepcopy(ev);bad['leaf_ids']=bad['leaf_ids'][:-1]
        with self.assertRaises(ValueError):verify_decomposition(d,bad)
        with self.assertRaises(ValueError):close_cut(d,{0},(0,1))

    def test_empty_circle(self):
        d=Diagram.from_pd([])
        self.assertEqual(factored_khovanov_rank(d)['reduced_rank'],1)


class SafetyTests(unittest.TestCase):
    def test_heap_equals_original_greedy(self):
        for d in random_diagrams(90,seed=22,maximum=12):
            for start in range(d.crossings):
                self.assertEqual(scan.scan_order(list(d.pd),start),oldscan.scan_order(list(d.pd),start))

    def test_linear_descending_equals_original(self):
        for d in random_diagrams(300,seed=9,maximum=14):
            self.assertEqual(descending_start(d),olddescending(d))

    def test_invalid_orders(self):
        d=load('trefoil.json')
        for order in ([],[0,1],[0,1,1],[0,1,2,3],[-1,0,1],[True,0,2]):
            for function in (lambda:khovanov_rank(d.pd,order=order),
                             lambda:bracket_evaluation(d,order=order)):
                with self.assertRaises(ValueError):function()
        with self.assertRaises(DiagramError):khovanov_rank([[0,1,2,3]])

    def test_resource_limits(self):
        d=load('conway.json')
        self.assertEqual(recognize(d,seconds=0).status,'UNKNOWN')
        self.assertEqual(recognize(d,use_jones=False,max_objects=1).status,'UNKNOWN')
        self.assertEqual(recognize(d,jones_max_states=1).status,'KNOTTED')
        with self.assertRaises(scan.ScanLimit):bracket_evaluation(d,max_states=1)
        with self.assertRaises(scan.ScanLimit):factored_khovanov_rank(d,seconds=0)
        for budget in (-1,float('nan'),float('inf')):
            with self.assertRaises(ValueError):recognize(d,seconds=budget)
            with self.assertRaises(ValueError):khovanov_rank(d.pd,seconds=budget)
        for ceiling in (0,-1,False,1.5):
            with self.assertRaises(ValueError):recognize(d,max_objects=ceiling)

    def test_argument_validation(self):
        d=load('conway.json')
        for budget in (-1,float('nan'),float('inf')):
            with self.assertRaises(ValueError):verify_result(d,{},seconds=budget)
        for tries in (0,-1,False,1.5):
            with self.assertRaises(ValueError):scan.best_scan_order(list(d.pd),tries=tries)
        self.assertEqual(scan.best_scan_order([],tries=0),[])

    def test_result_verification(self):
        for path in (ROOT/'fast/examples').glob('*.json'):
            d=Diagram.from_json(json.loads(path.read_text()));r=recognize(d).to_json()
            self.assertTrue(verify_result(d,r))
            bad=copy.deepcopy(r);bad['status']='KNOTTED' if r['status']=='UNKNOT' else 'UNKNOT'
            self.assertFalse(verify_result(d,bad))
        d=connected_sum(load('conway.json'),load('trefoil.json'))
        r=recognize(d).to_json();self.assertTrue(verify_result(d,r))
        r['evidence']['factor_results'][0]['factor_index']=100
        self.assertFalse(verify_result(d,r))

    def test_cli_new_features(self):
        env=dict(os.environ,PYTHONPATH=str(ROOT/'fast'))
        cmd=[sys.executable,'-m','fastunknot']
        d=str(ROOT/'fast/examples/conway.json')
        out=subprocess.run(cmd+['jones',d],env=env,capture_output=True,text=True)
        self.assertEqual(out.returncode,0)
        self.assertTrue(json.loads(out.stdout)['obstructs_unknot'])
        out=subprocess.run(cmd+['recognize',d,'--seconds','0'],env=env,capture_output=True,text=True)
        self.assertEqual(out.returncode,3)
        self.assertEqual(json.loads(out.stdout)['status'],'UNKNOWN')

if __name__=='__main__':unittest.main()
