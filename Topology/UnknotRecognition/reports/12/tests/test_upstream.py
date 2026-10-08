from __future__ import annotations
import itertools, json, pathlib, random, unittest
from unknot_frobenius.adapters import accelerated_planar_class, install_on_empty_scan
from unknot_frobenius.kernel import CompiledPlan, contract_reference
from reference.upstream.planar import Planar
from reference.upstream.algebra import BitAlgebra
from reference.upstream.scan_fast import FastScan
from reference.legacy.fastunknot import scan as legacy
from reference.legacy.fastunknot.diagram import Diagram, DiagramError

ROOT=pathlib.Path(__file__).resolve().parents[1]

def matchings(labels):
    if not labels:
        yield ()
        return
    a=labels[0]
    for j in range(1,len(labels),2):
        for inside in matchings(labels[1:j]):
            for outside in matchings(labels[j+1:]):
                yield tuple(sorted(((a,labels[j]),)+inside+outside))

def fset(m): return frozenset(frozenset(pair) for pair in m)

def decode_planar(alg,a,b,f):
    owner,k=alg.basis(a,b)
    keys=tuple(frozenset(p for p in owner if owner[p]==i) for i in range(k))
    return {frozenset(keys[j] for j in range(k) if (s>>j)&1) for s in range(1<<k) if (f>>s)&1}

def run_scan(pd, *, accelerated=False, force=False, debug=False, seconds=20):
    from time import monotonic
    if not pd:
        return {0:2}, {}, {}
    order=legacy.best_scan_order(list(pd),tries=min(len(pd),12))
    scan=FastScan(max_objects=100000,deadline=monotonic()+seconds)
    if accelerated:
        install_on_empty_scan(scan,minimum_pairs=0 if force else 64,method="fast" if force else "auto")
    for index in order:
        scan.add_crossing(tuple(pd[index]))
        if debug: scan.check_d_squared()
    scan.total_rank()
    return scan.ranks_by_degree(),scan.stats,getattr(scan.algebra,'kernel_stats',{})

class UpstreamTests(unittest.TestCase):
    def test_all_small_matching_triples_and_monomials(self):
        count=0
        for n in range(4):
            alg=Planar(shape_cache=False)
            ms=list(matchings(tuple(range(2*n))))
            ids=[alg.intern(m) for m in ms]
            for a,b,c in itertools.product(ids,repeat=3):
                plan=alg.compose_plan(a,b,c)
                cp=CompiledPlan.from_plan(None if plan is None else tuple(x[:4] for x in plan[0]))
                ka,kb=alg.basis(a,b)[1],alg.basis(b,c)[1]
                for u in range(1<<ka):
                    for v in range(1<<kb):
                        f,g=1<<u,1<<v
                        result=cp.apply(f,g,method='fast')
                        self.assertEqual(result,alg.compose(a,b,c,f,g))
                        # Independent, older set-based cobordism implementation.
                        expected=legacy.compose(decode_planar(alg,a,b,f),decode_planar(alg,b,c,g),
                                                fset(alg.pairs[a]),fset(alg.pairs[b]),fset(alg.pairs[c]))
                        self.assertEqual(decode_planar(alg,a,c,result),expected)
                        count+=1
        self.assertEqual(count,2245)

    def test_all_four_arc_triples_random_polynomials(self):
        rng=random.Random(90313)
        alg=Planar(shape_cache=False)
        ids=[alg.intern(m) for m in matchings(tuple(range(8)))]
        fast=accelerated_planar_class(Planar)(shape_cache=False,minimum_pairs=0,method='fast')
        for a in ids: self.assertEqual(fast.intern(alg.pairs[a]),a)
        for a,b,c in itertools.product(ids,repeat=3):
            f=rng.getrandbits(1<<alg.basis(a,b)[1]);g=rng.getrandbits(1<<alg.basis(b,c)[1])
            self.assertEqual(fast.compose(a,b,c,f,g),alg.compose(a,b,c,f,g))

    def test_upstream_bit_algebra(self):
        rng=random.Random(522)
        alg=BitAlgebra()
        ms=[fset(m) for m in matchings(tuple(range(8)))]
        for _ in range(300):
            a,b,c=[rng.choice(ms) for _ in range(3)]
            f=rng.getrandbits(1<<len(alg.basis(a,b).keys));g=rng.getrandbits(1<<len(alg.basis(b,c).keys))
            cp=CompiledPlan.from_plan(alg.plan(a,b,c))
            self.assertEqual(cp.apply(f,g,method='fast'),alg.compose(f,g,a,b,c))

    def test_existing_examples(self):
        for name in ['trefoil','figure_eight','hard_unknot_8','conway','kinoshita_terasaka','torus_3_5']:
            with self.subTest(name=name):
                pd=Diagram.from_json(json.loads((ROOT/'examples'/f'{name}.json').read_text())).pd
                ordinary,_,_=run_scan(pd,debug=True)
                self.assertEqual(run_scan(pd,accelerated=True,force=True,debug=True)[0],ordinary)
                self.assertEqual(run_scan(pd,accelerated=True)[0],ordinary)
                # Original archive oracle, with a different cancellation policy.
                self.assertEqual(legacy.khovanov_rank(pd,seconds=20)['by_degree'],ordinary)

    def test_seeded_random_braids(self):
        rng=random.Random(123691)
        tested=0
        while tested<40:
            strands=rng.randrange(2,5);n=rng.randrange(strands-1,11)
            word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(n)]
            try: pd=Diagram.from_braid(strands,word).pd
            except DiagramError: continue
            ordinary,_,_=run_scan(pd,debug=True)
            self.assertEqual(run_scan(pd,accelerated=True,force=True,debug=True)[0],ordinary)
            self.assertEqual(legacy.khovanov_rank(pd,seconds=20)['by_degree'],ordinary)
            tested+=1

    def test_adapter_safety_and_stage_reset(self):
        scan=FastScan()
        alg=install_on_empty_scan(scan,minimum_pairs=0)
        m=alg.intern(((0,1),(2,3)))
        alg.compose(m,m,m,7,11)
        self.assertTrue(alg.component_plans)
        alg.stage(frozenset(),(0,1,2,3))
        self.assertFalse(alg.component_plans)
        scan.add_crossing((0,1,2,3))
        with self.assertRaises(ValueError): install_on_empty_scan(scan)
        scan=FastScan();install_on_empty_scan(scan)
        def stop(): raise TimeoutError('polling test')
        scan.hook=stop
        with self.assertRaises(TimeoutError): scan.add_crossing((0,1,2,3))

class RankFormulaTests(unittest.TestCase):
    def test_linearized_ranks(self):
        rng=random.Random(915)
        for _ in range(100):
            c=rng.randrange(1,4);masks=[[0]*c for _ in range(3)]
            for axis in range(3):
                for k in range(rng.randrange(5)):
                    masks[axis][rng.randrange(c)]|=1<<k
            plan=tuple((masks[0][j],masks[1][j],masks[2][j],rng.randrange(3)) for j in range(c))
            cp=CompiledPlan.from_plan(plan)
            pivots={}
            for u in range(1<<len(cp.left_owner)):
                for v in range(1<<len(cp.right_owner)):
                    col=contract_reference(plan,1<<u,1<<v)
                    while col:
                        top=col.bit_length()-1
                        if top not in pivots:
                            pivots[top]=col;break
                        col^=pivots[top]
            self.assertEqual(len(pivots),cp.linearized_rank())
