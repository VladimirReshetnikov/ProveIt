"""Independent cube tests plus differential tests of the optimized algebra.

Small full-cube Jones evaluation below deliberately does not use the scan's
matchings, gluing, surface algebra, or Gaussian cancellation.
"""
import copy
import itertools
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize, khovanov_rank
from fastunknot import optimized_algebra as opt, reference_algebra as ref
from fastunknot.alexander import alexander_polynomial
from fastunknot.decompose import connected_sum, connected_sum_factors, verify_decomposition
from fastunknot.jones import normalized_bracket_mod, PRIME, A_VALUE
from fastunknot.scan import ScanComplex, ScanLimit
from fastunknot.simplify import simplify
from test_fastunknot import reference_reduced_rank

EXAMPLES = Path(__file__).resolve().parents[1] / 'examples'

def example(name):
    return Diagram.from_json(json.loads((EXAMPLES / (name + '.json')).read_text()))

def random_knots(seed, count, maximum=9):
    rng = random.Random(seed)
    result = []
    while len(result) < count:
        strands = rng.randint(2, 4)
        word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                for _ in range(rng.randint(1, maximum))]
        try:
            result.append(Diagram.from_braid(strands, word))
        except ValueError:
            pass
    return result

def cube_bracket(diagram, a=A_VALUE):
    """Exhaust all 2^n smoothings using an independent edge-label union-find."""
    n, p = diagram.crossings, PRIME
    if not n:
        return 1
    delta = -(a*a + pow(a, -2, p)) % p
    answer = 0
    for state in range(1 << n):
        parent = list(range(2*n))
        def find(x):
            while parent[x] != x:
                x = parent[x]
            return x
        for i, row in enumerate(diagram.pd):
            pairs = ((0, 3), (1, 2)) if (state >> i) & 1 else ((0, 1), (2, 3))
            for j, k in pairs:
                parent[find(row[j])] = find(row[k])
        loops = len({find(j) for j in range(2*n)})
        exponent = n - 2 * state.bit_count()
        answer += pow(a, exponent, p) * pow(delta, loops-1, p)
    return answer * pow(-a**3 % p, -diagram.writhe(), p) % p

def matchings(points):
    if not points:
        yield frozenset()
        return
    a = points[0]
    for index in range(1, len(points), 2):
        b = points[index]
        for left in matchings(points[1:index]):
            for right in matchings(points[index+1:]):
                yield left | right | {frozenset((a, b))}

def morphisms(a, b):
    keys = list(set(ref.circles(a,b).values()))
    terms = [frozenset(keys[j] for j in range(len(keys)) if mask >> j & 1)
             for mask in range(1 << len(keys))]
    return terms

class JonesTests(unittest.TestCase):
    def test_independent_full_cube_120(self):
        for d in random_knots(190926, 120):
            with self.subTest(pd=d.pd):
                self.assertEqual(normalized_bracket_mod(d)['value'], cube_bracket(d))

    def test_all_supplied_examples_full_cube(self):
        for path in EXAMPLES.glob('*.json'):
            d = Diagram.from_json(json.loads(path.read_text()))
            if d.crossings <= 12:
                self.assertEqual(normalized_bracket_mod(d)['value'], cube_bracket(d))

    def test_rotated_rows_preserve_writhe_and_invariants(self):
        rng = random.Random(712)
        for d in random_knots(713, 40):
            rotated = Diagram.from_pd([row[2:]+row[:2] if rng.randrange(2) else row
                                       for row in d.pd])
            self.assertEqual(d.writhe(), rotated.writhe())
            self.assertEqual(normalized_bracket_mod(d)['value'],
                             normalized_bracket_mod(rotated)['value'])
            self.assertEqual(alexander_polynomial(d), alexander_polynomial(rotated))

    def test_crossing_order_and_relabeling(self):
        rng = random.Random(901)
        for d in random_knots(902, 30):
            expected = normalized_bracket_mod(d)['value']
            order = list(range(d.crossings)); rng.shuffle(order)
            self.assertEqual(normalized_bracket_mod(d,order=order)['value'], expected)
            labels = list(range(2*d.crossings)); rng.shuffle(labels)
            rows = [tuple(100 + labels[x]*7 for x in d.pd[i]) for i in order]
            self.assertEqual(normalized_bracket_mod(Diagram.from_pd(rows))['value'], expected)

    def test_reidemeister_reductions_60(self):
        for d in random_knots(200,60):
            reduced, _ = simplify(d)
            self.assertEqual(normalized_bracket_mod(d)['value'],
                             normalized_bracket_mod(reduced)['value'])

    def test_many_curls_and_canceling_braid_pairs(self):
        for n in range(1, 16):
            for sign in (-1,1):
                d = Diagram.from_braid(n+1, [sign*j for j in range(1,n+1)])
                self.assertEqual(normalized_bracket_mod(d)['value'],1)
        d = example('trefoil')
        expected = normalized_bracket_mod(d)['value']
        for k in range(8):
            d = Diagram.from_braid(2,[1]*3+[1,-1]*k)
            self.assertEqual(normalized_bracket_mod(d)['value'], expected)

    def test_braid_third_reidemeister_relation(self):
        rng = random.Random(313)
        checked = 0
        while checked < 25:
            tail = [rng.choice((-2,-1,1,2)) for _ in range(5)]
            try:
                left = Diagram.from_braid(3, [1,2,1] + tail)
                right = Diagram.from_braid(3, [2,1,2] + tail)
            except ValueError:
                continue
            self.assertEqual(normalized_bracket_mod(left)['value'],
                             normalized_bracket_mod(right)['value'])
            checked += 1

    def test_mirror_relation(self):
        for d in random_knots(321, 30):
            mirror = Diagram.from_pd([row[1:]+row[:1] for row in d.pd])
            self.assertEqual(mirror.writhe(), -d.writhe())
            self.assertEqual(normalized_bracket_mod(mirror)['value'],
                             cube_bracket(d, pow(A_VALUE,-1,PRIME)))

    def test_cap_is_not_a_verdict(self):
        d = example('conway')
        self.assertFalse(normalized_bracket_mod(d,max_states=1)['completed'])
        r = recognize(d,jones_max_states=1)
        self.assertEqual(r.status,'KNOTTED')
        self.assertEqual(r.method,'reduced-khovanov-F2-scan')

    def test_equality_is_not_an_unknot_verdict(self):
        with patch('fastunknot.recognize.normalized_bracket_mod',
                   return_value={'completed':True, 'value':1}):
            r = recognize(example('conway'))
        self.assertEqual(r.status,'KNOTTED')
        self.assertEqual(r.method,'reduced-khovanov-F2-scan')

    def test_filter_limits(self):
        d = example('trefoil')
        for budget in (0,-1,True,1.5):
            with self.assertRaises(ValueError): normalized_bracket_mod(d,max_states=budget)
        with self.assertRaises(ScanLimit): normalized_bracket_mod(d,deadline=0)

class AlgebraTests(unittest.TestCase):
    def test_composition_differential_6000(self):
        rng = random.Random(2335)
        ms = list(matchings(tuple(range(6))))
        self.assertEqual(len(ms),5)
        for _ in range(6000):
            a,b,c = [rng.choice(ms) for _ in range(3)]
            f = frozenset(t for t in morphisms(a,b) if rng.randrange(2))
            g = frozenset(t for t in morphisms(b,c) if rng.randrange(2))
            self.assertEqual(opt.compose(f,g,a,b,c), ref.compose(set(f),set(g),a,b,c))

    def test_every_unit_on_three_arcs_is_self_inverse(self):
        m = next(matchings(tuple(range(6))))
        terms = morphisms(m,m)
        nonempty = [t for t in terms if t]
        for mask in range(1 << len(nonempty)):
            f = frozenset([frozenset()] + [t for j,t in enumerate(nonempty) if mask>>j&1])
            self.assertEqual(opt.inverse(f,m), ref.inverse(set(f),m))
            self.assertEqual(opt.compose(f,f,m,m,m), opt.ONE)

    def test_crossing_entries_differential(self):
        # Four old boundary labels, zero to four glued to this crossing.
        rng = random.Random(833)
        ms = list(matchings(tuple(range(4))))
        for slots in ((4,5,6,7),(0,4,5,6),(0,1,4,5),(0,1,2,4),(0,1,2,3)):
            for a,b in itertools.product(ms,repeat=2):
                for si,ti in ((0,0),(1,1),(0,1)):
                    f=frozenset(t for t in morphisms(a,b) if rng.randrange(2))
                    _,_,got=opt.crossing_entries(a,b,f,si,ti,frozenset(range(4)),slots)
                    _,_,wanted=ref.crossing_entries(a,b,set(f),si,ti,frozenset(range(4)),slots)
                    self.assertEqual(got,wanted)
                    self.assertTrue(all(isinstance(value,frozenset) for value in got.values()))

    def test_caches_are_bounded_and_clearable(self):
        for data in opt.cache_statistics().values():
            self.assertEqual(data['maxsize'],16384)
            self.assertLessEqual(data['currsize'],16384)
        opt.clear_caches()
        self.assertTrue(all(data['currsize']==0 for data in opt.cache_statistics().values()))

class RankAndDecompositionTests(unittest.TestCase):
    def test_dense_cube_tail_variants_35(self):
        rng = random.Random(591)
        for d in random_knots(592,35,8):
            expected = reference_reduced_rank(d)
            result = []
            for tail in (1,2,3):
                order = list(range(d.crossings));rng.shuffle(order)
                r=khovanov_rank(d.pd,order=order,tail_crossings=tail,check_d_squared=True)
                self.assertEqual(r['reduced_rank'],expected)
                result.append(r['by_degree'])
            self.assertEqual(result[0],result[1]);self.assertEqual(result[1],result[2])

    def test_connected_sum_convolution_and_certificates(self):
        for a,b in [('trefoil','trefoil'),('trefoil','figure_eight'),
                    ('figure_eight','figure_eight'),('trefoil','unknot')]:
            d=connected_sum(example(a),example(b))
            factored=khovanov_rank(d.pd)
            raw=khovanov_rank(d.pd,decompose=False,check_d_squared=True)
            self.assertEqual(factored['by_degree'],raw['by_degree'])
            self.assertEqual(factored['reduced_rank'],reference_reduced_rank(d))
            factors,cert=connected_sum_factors(d)
            self.assertEqual(verify_decomposition(d,cert),factors)

    def test_many_factors_and_memoization(self):
        trefoil=example('trefoil'); d=Diagram.from_pd([])
        for _ in range(16): d=connected_sum(d,trefoil)
        r=khovanov_rank(d.pd)
        self.assertEqual(r['reduced_rank'],3**16)
        self.assertEqual(r['stats']['factor_count'],16)
        self.assertEqual(r['stats']['distinct_factor_computations'],1)
        self.assertEqual(len(verify_decomposition(d,r['decomposition'])),16)

    def test_tampered_certificate_rejected(self):
        d=connected_sum(example('trefoil'),example('figure_eight'))
        _,cert=connected_sum_factors(d)
        bad=copy.deepcopy(cert);bad['nodes'][0]['cut_edges']=[0,0]
        with self.assertRaises(ValueError):verify_decomposition(d,bad)
        bad=copy.deepcopy(cert);bad['nodes'][0]['children']=[1,1]
        with self.assertRaises(ValueError):verify_decomposition(d,bad)
        bad=copy.deepcopy(cert);bad['nodes'].append({'pd':[],'factor':999})
        with self.assertRaises(ValueError):verify_decomposition(d,bad)

    def test_invalid_orders_rejected(self):
        d=example('trefoil')
        for order in ([],[0,1],[0,1,1],[0,1,3],[0,1,True]):
            with self.assertRaises(ValueError):khovanov_rank(d.pd,order=order)

    def test_resource_results_and_bad_limits(self):
        d=example('trefoil')
        self.assertEqual(recognize(d,seconds=0).status,'UNKNOWN')
        r=recognize(d,use_alexander=False,use_jones=False,max_objects=1)
        self.assertEqual(r.status,'UNKNOWN')
        for kw in ({'seconds':-1},{'seconds':float('nan')},{'tail_crossings':0},
                   {'max_objects':True},{'max_objects':0}):
            with self.assertRaises(ValueError):khovanov_rank(d.pd,**kw)

    def test_completed_complex_cannot_be_extended(self):
        d=Diagram.from_braid(2,[1]); c=ScanComplex();c.add_crossing(d.pd[0])
        with self.assertRaises(ValueError):c.add_crossing(d.pd[0])

if __name__=='__main__': unittest.main()
