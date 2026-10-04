"""Independent algebra, state-sum, mutation and regression tests."""
from __future__ import annotations
import itertools
import json
from pathlib import Path
import random
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot import Diagram, DiagramError, recognize, khovanov_rank
from fastunknot.algebra import Algebra
from fastunknot import geometry as reference
from fastunknot.jones import jones_obstruction, verify_obstruction, FilterLimit, PRIME, A_VALUE
from fastunknot.modular import numeric_minor, determinant_mod, alexander_obstruction
from fastunknot.alexander import alexander_matrix, alexander_polynomial, evaluate
from fastunknot.ordering import scan_order, best_scan_order
from fastunknot.decompose import visible_factors
from fastunknot.simplify import simplify
from baseline.fastunknot import scan as old_scan
from benchmarks.common import connected_sum, sum_family
from test_fastunknot import reference_reduced_rank, one_component


def noncrossing(points):
    if not points:
        yield frozenset()
        return
    first = points[0]
    for j in range(1, len(points), 2):
        for a in noncrossing(points[1:j]):
            for b in noncrossing(points[j+1:]):
                yield a | b | {frozenset((first, points[j]))}


def dense_bracket(diagram):
    """Independent 2^n state sum; no frontier transitions or compiled surfaces."""
    n, p, a = diagram.crossings, PRIME, A_VALUE
    delta = (-a*a-pow(a, -2, p)) % p
    if not n:
        return delta
    result = 0
    for state in range(1 << n):
        parent = list(range(2*n))
        def root(v):
            while parent[v] != v:
                v = parent[v]
            return v
        for i, (a0, b, c, d) in enumerate(diagram.pd):
            for x, y in (((a0, d), (b, c)) if state >> i & 1 else ((a0, b), (c, d))):
                parent[root(x)] = root(y)
        circles = len({root(i) for i in range(2*n)})
        result = (result + pow(a, n - 2 * state.bit_count(), p)*pow(delta, circles, p)) % p
    return result


class CompiledAlgebraTests(unittest.TestCase):
    def test_all_composition_basis_entries_through_six_ends(self):
        engine = Algebra()
        for size in (0, 2, 4, 6):
            matchings = list(noncrossing(list(range(size))))
            for a, b, c in itertools.product(matchings, repeat=3):
                for tf in range(1 << len(engine.basis(a, b).keys)):
                    f = 1 << tf
                    for tg in range(1 << len(engine.basis(b, c).keys)):
                        g = 1 << tg
                        expected = reference.compose(engine.decode(f,a,b),engine.decode(g,b,c),a,b,c)
                        self.assertEqual(engine.decode(engine.compose(f,g,a,b,c),a,c), expected)

    def test_all_units_are_involutions(self):
        engine = Algebra()
        m = next(noncrossing(list(range(6))))
        for f in range(1, 256, 2):
            decoded = engine.decode(f,m,m)
            self.assertEqual(reference.compose(decoded,decoded,m,m,m), {frozenset()})
            self.assertEqual(engine.compose(f,f,m,m,m),1)

    def test_crossing_maps_against_explicit_surfaces(self):
        rng = random.Random(91)
        for word in ([1,2]*4, [1,-2,3,-2,1,3,2], [1,-2,1,-2], [1]):
            d = Diagram.from_braid(max(map(abs,word))+1, word)
            states, points = {frozenset()}, frozenset()
            for slots in d.pd:
                engine = Algebra()
                new = set()
                states_list = sorted(states,key=repr)
                for a in states_list:
                    for b in states_list:
                        count = 1 << len(engine.basis(a,b).keys)
                        f = rng.randrange(1 << count)
                        for i in (0,1):
                            _,_,actual = engine.crossing_entries(a,b,f,i,i,points,slots)
                            gs,gt,expected = reference.crossing_entries(
                                a,b,engine.decode(f,a,b),i,i,points,slots)
                            decoded = {(ls,lt):engine.decode(value,gs.matching,gt.matching)
                                       for ls,lt,value in actual}
                            self.assertEqual(decoded,expected)
                    for i in (0,1):
                        g = engine.gluing(a,i,points,slots)
                        new.add(g.matching)
                points,states = g.points,new


class InvariantTests(unittest.TestCase):
    def test_jones_against_dense_state_sum(self):
        rng = random.Random(92)
        for _ in range(100):
            while True:
                s = rng.choice((3,4))
                w = [rng.choice((-1,1))*rng.randrange(1,s) for _ in range(rng.randrange(3,9))]
                if one_component(s,w): break
            d = Diagram.from_braid(s,w)
            order = list(range(d.crossings));rng.shuffle(order)
            self.assertEqual(jones_obstruction(d,order=order)['bracket'],dense_bracket(d))

    def test_pd_rotation_relabeling_and_writhe(self):
        rng = random.Random(93)
        for word in ([1,2]*4,[1,-2,1,-2],[1,-2,3,-2,1,3,2],[1]):
            d = Diagram.from_braid(max(map(abs,word))+1,word)
            p, j, w = alexander_polynomial(d),jones_obstruction(d)['normalized_jones'],d.writhe()
            for _ in range(10):
                rows = [row[2:]+row[:2] if rng.randrange(2) else row for row in d.pd]
                rng.shuffle(rows)
                labels = list(range(2*d.crossings));rng.shuffle(labels)
                q = Diagram.from_pd([[100+7*labels[x] for x in row] for row in rows])
                self.assertEqual(q.writhe(),w)
                self.assertEqual(alexander_polynomial(q),p)
                self.assertEqual(jones_obstruction(q)['normalized_jones'],j)

    def test_numeric_fox_matrix_matches_symbolic(self):
        for name in ('conway','kinoshita_terasaka','figure_eight','torus_3_5','hard_unknot_8'):
            d=Diagram.from_json(json.loads((ROOT/'examples'/f'{name}.json').read_text()))
            symbolic = alexander_matrix(d)
            for t in (-1,2):
                expected = [[evaluate(entry,t)%PRIME for entry in row[:-1]] for row in symbolic[:-1]]
                self.assertEqual(numeric_minor(d,t),expected)
            if name in ('conway','kinoshita_terasaka','hard_unknot_8'):
                self.assertFalse(alexander_obstruction(d)['obstruction'])

    def test_reidemeister_and_braid_relation(self):
        for word in ([1,-2,1,-2],[1,2],[1,2]*4):
            d = Diagram.from_braid(3,word)
            j = jones_obstruction(d)['normalized_jones']
            for curl in (3,-3):
                self.assertEqual(jones_obstruction(Diagram.from_braid(4,word+[curl]))['normalized_jones'],j)
            self.assertEqual(jones_obstruction(Diagram.from_braid(3,word+[1,-1]))['normalized_jones'],j)
        # Braid relation inside closures that are knots.
        for tail in ([1],[2],[1,1,1],[2,2,2]):
            a,b = Diagram.from_braid(3,[1,2,1]+tail),Diagram.from_braid(3,[2,1,2]+tail)
            self.assertEqual(jones_obstruction(a)['normalized_jones'],jones_obstruction(b)['normalized_jones'])

    def test_witness_replay_and_tamper(self):
        d=Diagram.from_json(json.loads((ROOT/'examples/conway.json').read_text()))
        witness=jones_obstruction(d)
        self.assertTrue(verify_obstruction(d,witness))
        bad=dict(witness,bracket=witness['bracket']+1)
        self.assertFalse(verify_obstruction(d,bad))
        self.assertFalse(verify_obstruction(Diagram.from_braid(2,[1]),witness))
        with self.assertRaises(FilterLimit):jones_obstruction(d,max_states=0)
        result=recognize(d,use_alexander=False,jones_max_states=0)
        self.assertEqual(result.method,'reduced-khovanov-F2-scan')
        self.assertEqual(result.status,'KNOTTED')


class ScannerTests(unittest.TestCase):
    def test_orders_exactly_match_upstream(self):
        rng=random.Random(94)
        for _ in range(50):
            while True:
                s=rng.randrange(2,6)
                word=[rng.choice((-1,1))*rng.randrange(1,s) for _ in range(rng.randrange(2,25))]
                if one_component(s,word):break
            d=Diagram.from_braid(s,word)
            for start in (0,d.crossings//2,d.crossings-1):
                self.assertEqual(scan_order(d.pd,start),old_scan.scan_order(d.pd,start))
            self.assertEqual(best_scan_order(d.pd,12),old_scan.best_scan_order(d.pd,12))

    def test_connected_sum_degree_convolution(self):
        for k in range(1,5):
            d=sum_family(k,Diagram)
            product=khovanov_rank(d.pd)
            raw=khovanov_rank(d.pd,factor=False)
            self.assertEqual(product['reduced_rank'],3**k)
            self.assertEqual(product['by_degree'],raw['by_degree'])
        for k in (10,50):
            d=sum_family(k,Diagram)
            self.assertEqual(khovanov_rank(d.pd)['reduced_rank'],3**k)
        a=Diagram.from_braid(2,[1]*3);b=Diagram.from_braid(3,[1,-2,1,-2])
        d=connected_sum(a,b,Diagram)
        self.assertEqual(khovanov_rank(d.pd)['reduced_rank'],15)
        self.assertEqual(reference_reduced_rank(d),15)

    def test_conway_sum_family(self):
        block=Diagram.from_json(json.loads((ROOT/'examples/conway.json').read_text()))
        d=connected_sum(block,block,Diagram)
        raw=khovanov_rank(d.pd,factor=False)
        factored=khovanov_rank(d.pd)
        self.assertEqual(raw['by_degree'],factored['by_degree'])
        self.assertEqual(factored['reduced_rank'],33**2)
        d=connected_sum(d,block,Diagram)
        self.assertEqual(simplify(d)[0].crossings,33)
        self.assertEqual(alexander_polynomial(d),[1])
        self.assertEqual(recognize(d).status,'KNOTTED')
        fallback=recognize(d,use_jones=False)
        self.assertTrue(fallback.evidence['khovanov']['factorized'])
        self.assertEqual(fallback.evidence['khovanov']['reduced_rank'],33**3)

    def test_exhaustive_short_three_braids_against_cube(self):
        for n in (2,4):
            for word in itertools.product((-2,-1,1,2),repeat=n):
                if not one_component(3,word):continue
                d=Diagram.from_braid(3,word)
                self.assertEqual(khovanov_rank(d.pd,factor=False)['reduced_rank'],reference_reduced_rank(d),word)

    def test_fresh_random_cubes_both_pivots_and_d_squared(self):
        rng=random.Random(20260918)
        for k in range(100):
            while True:
                s=rng.choice((3,4,5))
                word=[rng.choice((-1,1))*rng.randrange(1,s) for _ in range(rng.randrange(4,10))]
                if one_component(s,word):break
            d=Diagram.from_braid(s,word)
            expected=reference_reduced_rank(d)
            for pivot in ('lifo','markowitz'):
                self.assertEqual(khovanov_rank(d.pd,pivot=pivot,factor=False,
                                 check_d_squared=(k<20))['reduced_rank'],expected,word)
            self.assertEqual(recognize(d).status,'UNKNOT' if expected==1 else 'KNOTTED')

    def test_cli_replays_unreduced_witness(self):
        import subprocess,tempfile
        block=Diagram.from_json(json.loads((ROOT/'examples/conway.json').read_text()))
        d=connected_sum(block,Diagram.from_braid(2,[1]),Diagram)
        witness=recognize(d,use_reduction=False).to_json()
        self.assertEqual(witness['method'],'jones-mod-prime')
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)
            (path/'diagram.json').write_text(json.dumps(d.to_json()))
            (path/'witness.json').write_text(json.dumps(witness))
            p=subprocess.run([sys.executable,'-m','fastunknot','verify-jones',
                str(path/'diagram.json'),str(path/'witness.json')],cwd=ROOT,
                capture_output=True,text=True,check=True)
            self.assertTrue(json.loads(p.stdout)['verified'])

    def test_bad_orders_and_limits(self):
        d=Diagram.from_braid(2,[1]*3)
        for order in ([],[0,0,2],[0,1,3],[0,1],[0,1,True]):
            with self.assertRaises(ValueError):khovanov_rank(d.pd,order=order)
            with self.assertRaises(ValueError):jones_obstruction(d,order=order)
        for kwargs in ({'seconds':0},{'max_objects':1,'use_alexander':False,'use_jones':False}):
            self.assertEqual(recognize(d,**kwargs).status,'UNKNOWN')
        self.assertEqual(recognize(d,max_objects=1).status,'KNOTTED')
        with self.assertRaises(ValueError):recognize(d,seconds=-1)
        with self.assertRaises(ValueError):recognize(d,max_objects=-1)


if __name__=='__main__':unittest.main()
