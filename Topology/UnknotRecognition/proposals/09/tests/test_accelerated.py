"""Independent state sums, differential tests, and resource/error regressions."""
import itertools
import json
import random
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot import Diagram, DiagramError, recognize, alexander_polynomial
from fastunknot import scan
from fastunknot.alexander import evaluate
from fastunknot.jones import jones_residue, join_matching, JonesLimit
from fastunknot.determinant_filter import determinant_residue
from fastunknot.factors import (connected_sum, diagram_factors, split_once,
                               replay_factor_certificate)
from fastunknot.ordering import scan_order, best_scan_order
from fastunknot.simplify import descending_start
from baseline_fastunknot import scan as old_scan
from baseline_fastunknot.simplify import descending_start as old_descending
from test_legacy import reference_reduced_rank, one_component


def example(name):
    return Diagram.from_json(json.loads((ROOT/'examples'/f'{name}.json').read_text()))


def random_knots(count, seed=912, max_n=8):
    rng = random.Random(seed)
    result = []
    while len(result) < count:
        s = rng.randint(2, 4)
        word = [rng.choice((-1, 1))*rng.randrange(1, s) for _ in range(rng.randint(1, max_n))]
        if one_component(s, word):
            result.append(Diagram.from_braid(s, word))
    return result


def cube_jones(diagram, modulus, a):
    """Independent 2^n full-state DSU calculation; no frontier code is used."""
    n = diagram.crossings
    if not n:
        return 1
    ai = pow(a, -1, modulus)
    delta = (-a*a-ai*ai) % modulus
    bracket = 0
    for state in range(1 << n):
        parents = list(range(2*n))
        def find(e):
            while parents[e] != e:
                e = parents[e]
            return e
        for k, row in enumerate(diagram.pd):
            pairs = ((0, 3), (1, 2)) if state >> k & 1 else ((0, 1), (2, 3))
            for u, v in pairs:
                parents[find(row[u])] = find(row[v])
        circles = len({find(e) for e in range(2*n)})
        weight = pow(a, n-2*state.bit_count(), modulus)
        bracket = (bracket + weight*pow(delta, circles-1, modulus)) % modulus
    return bracket*pow(-a**3, -diagram.writhe(), modulus) % modulus


def planar_matchings(points):
    if not points:
        yield frozenset()
        return
    a = points[0]
    for k in range(1, len(points), 2):
        for left in planar_matchings(points[1:k]):
            for right in planar_matchings(points[k+1:]):
                yield left | right | {frozenset((a, points[k]))}


class JonesTests(unittest.TestCase):
    def test_all_examples(self):
        for path in (ROOT/'examples').glob('*.json'):
            d = Diagram.from_json(json.loads(path.read_text()))
            j = jones_residue(d)
            if d.crossings <= 11:
                self.assertEqual(j['residue'], cube_jones(d, j['modulus'], j['A']), path.name)
        for name in ('unknot', 'hard_unknot_8', 'grid_scrambled_unknot', 'unknot_braid40'):
            self.assertEqual(jones_residue(example(name))['residue'], 1)
        for name in ('conway', 'kinoshita_terasaka', 'trefoil', 'figure_eight', 'torus_3_5'):
            self.assertTrue(jones_residue(example(name))['obstructs'])

    def test_random_dense_state_sums(self):
        rng = random.Random(1200)
        for d in random_knots(80):
            order = list(range(d.crossings))
            rng.shuffle(order)
            for p, a in ((1000000007, 2), (101, 3)):
                self.assertEqual(jones_residue(d, modulus=p, a=a, order=order)['residue'],
                                 cube_jones(d, p, a))

    def test_modular_collision_is_inconclusive(self):
        # At A=1 (mod 5), normalized Jones of ANY knot is 1. No unknot verdict.
        d = example('trefoil')
        self.assertEqual(jones_residue(d, modulus=5, a=1)['residue'], 1)
        self.assertFalse(jones_residue(d, modulus=5, a=1)['obstructs'])

    def test_reidemeister_and_markov(self):
        for s, word in [(2, [1]*3), (3, [1, -2, 1, -2]), (3, [1, 2])]:
            d = Diagram.from_braid(s, word)
            value = jones_residue(d)['residue']
            for sign in (-1, 1):
                changed = [sign] + word + [-sign]
                self.assertEqual(jones_residue(Diagram.from_braid(s, changed))['residue'], value)
                stabilized = Diagram.from_braid(s+1, word+[sign*s])
                self.assertEqual(jones_residue(stabilized)['residue'], value)
                cancellation = word[:1]+[sign, -sign]+word[1:]
                self.assertEqual(jones_residue(Diagram.from_braid(s, cancellation))['residue'], value)
        self.assertEqual(jones_residue(Diagram.from_braid(3, [1,2,1,1]))['residue'],
                         jones_residue(Diagram.from_braid(3, [2,1,2,1]))['residue'])

    def test_mirror(self):
        for d in random_knots(30, seed=988):
            p = 1000000007
            self.assertEqual(jones_residue(d.mirror())['residue'],
                             jones_residue(d, a=pow(2,-1,p))['residue'])

    def test_join_matches_old_glue(self):
        rng = random.Random(827)
        for d in random_knots(30):
            order = list(range(d.crossings))
            rng.shuffle(order)
            points = frozenset()
            m = frozenset()
            for index in order:
                s = rng.randrange(2)
                old = old_scan.glue(m, s, points, d.pd[index])
                new, closed = join_matching(tuple(sorted(tuple(sorted(pair)) for pair in m)),
                                            d.pd[index], s)
                self.assertEqual(old.matching, frozenset(frozenset(pair) for pair in new))
                self.assertEqual(old.closed, closed)
                points, m = old.points, old.matching

    def test_limits_and_ring_validation(self):
        d = example('conway')
        with self.assertRaises(JonesLimit):
            jones_residue(d, max_states=1)
        with self.assertRaises(JonesLimit):
            jones_residue(d, max_transitions=1)
        for options in ({'modulus': 4, 'a': 2}, {'modulus': 17, 'a': 2}, {'max_states': 0},
                        {'modulus': 0}, {'a': 0}):
            with self.assertRaises(ValueError):
                jones_residue(d, **options)


class PolynomialAndOrderingTests(unittest.TestCase):
    def test_determinant_matches_polynomial(self):
        for d in random_knots(100, seed=571, max_n=12):
            r = determinant_residue(d)
            value = evaluate(alexander_polynomial(d), -1) % r['modulus']
            self.assertIn(r['residue'], (value, -value % r['modulus']))

    def test_half_turn_pd_invariance(self):
        rng = random.Random(29)
        for d in random_knots(60, seed=811, max_n=10):
            rows = [row[2:]+row[:2] if rng.randrange(2) else row for row in d.pd]
            rotated = Diagram.from_pd(rows)
            self.assertEqual(d.writhe(), rotated.writhe())
            self.assertEqual(alexander_polynomial(d), alexander_polynomial(rotated))
            self.assertEqual(jones_residue(d)['residue'], jones_residue(rotated)['residue'])

    def test_fast_order_is_identical(self):
        for d in random_knots(80, max_n=20):
            for start in range(d.crossings):
                self.assertEqual(scan_order(d.pd, start), old_scan.scan_order(d.pd, start))
            self.assertEqual(best_scan_order(d.pd, tries=min(d.crossings,12)),
                             old_scan.best_scan_order(d.pd, tries=min(d.crossings,12)))

    def test_linear_descending_exact_dart(self):
        rng = random.Random(90)
        for d in random_knots(100, max_n=20):
            rows = [row[2:]+row[:2] if rng.randrange(2) else row for row in d.pd]
            d = Diagram.from_pd(rows)
            self.assertEqual(descending_start(d), old_descending(d))


class AlgebraAndRankTests(unittest.TestCase):
    def test_composition_against_original(self):
        rng = random.Random(826)
        def morph(a,b):
            keys = list(set(old_scan.circles(a,b).values()))
            terms = [frozenset(k for k in keys if rng.randrange(2)) for _ in range(5)]
            return set(terms)
        for size in (0,2,4,6,8):
            matchings = list(planar_matchings(tuple(range(size))))
            for _ in range(100):
                a,b,c = (rng.choice(matchings) for _ in range(3))
                f,g = morph(a,b),morph(b,c)
                self.assertEqual(scan.compose(f,g,a,b,c), old_scan.compose(f,g,a,b,c))

    def test_unit_self_inverse(self):
        rng = random.Random(171)
        for size in range(1,7):
            m = frozenset(frozenset((2*i,2*i+1)) for i in range(size))
            for _ in range(20):
                f = {frozenset()}
                for _ in range(20):
                    f.add(frozenset(pair for pair in m if rng.randrange(2)))
                self.assertEqual(scan.inverse(f,m), f)
                self.assertEqual(old_scan.compose(f,f,m,m,m), {frozenset()})

    def test_raw_scanner_matches_cube_and_baseline(self):
        rng = random.Random(3)
        for d in random_knots(55, seed=490, max_n=8):
            order = list(range(d.crossings)); rng.shuffle(order)
            actual = scan.khovanov_rank(d.pd, order=order, check_d_squared=True)
            old = old_scan.khovanov_rank(d.pd, order=order)
            self.assertEqual(actual['by_degree'], old['by_degree'])
            self.assertEqual(actual['reduced_rank'], reference_reduced_rank(d))

    def test_caches_released(self):
        scan.khovanov_rank(example('conway').pd)
        for func in (scan.glue,scan.circles,scan._compose_plan,scan._compose_cached,
                     scan._crossing_entries_cached):
            self.assertEqual(func.cache_info().currsize, 0)
        with self.assertRaises(scan.ScanLimit):
            scan.khovanov_rank(example('conway').pd, max_objects=6)
        self.assertEqual(scan.glue.cache_info().currsize, 0)

    def test_order_validation(self):
        d = example('trefoil')
        for order in ([0,0,1], [0,1], [0,1,3], [0,1,True]):
            with self.assertRaises(ValueError):
                scan.khovanov_rank(d.pd, order=order)
            with self.assertRaises(ValueError):
                jones_residue(d, order=order)


class FactorTests(unittest.TestCase):
    def test_known_factors(self):
        for count in (2,3,6,12):
            d = connected_sum([example('trefoil')]*count)
            leaves, certificate = diagram_factors(d)
            self.assertEqual([p.crossings for p in leaves], [3]*count)
            r = scan.khovanov_rank(d.pd)
            self.assertEqual(r['reduced_rank'], 3**count)
            self.assertEqual(sum(r['by_degree'].values()), 2*3**count)

    def test_degreewise_kunneth(self):
        for pieces in ((example('trefoil'), example('figure_eight')),
                       (example('trefoil'), example('trefoil').mirror()),
                       (example('hard_unknot_8'), example('trefoil'))):
            d = connected_sum(pieces)
            fast = scan.khovanov_rank(d.pd)
            raw = scan.khovanov_rank(d.pd, factor=False)
            self.assertEqual(fast['by_degree'], raw['by_degree'])
            if d.crossings <= 8:
                self.assertEqual(fast['reduced_rank'], reference_reduced_rank(d))

    def test_relabelled_reordered_cuts(self):
        rng = random.Random(124)
        d = connected_sum([example('trefoil'), example('figure_eight'), example('trefoil')])
        for _ in range(12):
            rows = list(d.pd); rng.shuffle(rows)
            rows = [r[2:]+r[:2] if rng.randrange(2) else r for r in rows]
            renamed = Diagram.from_pd(rows)
            pieces,_ = diagram_factors(renamed)
            self.assertEqual(sorted(x.crossings for x in pieces), [3,3,4])
            self.assertEqual(scan.khovanov_rank(renamed.pd)['reduced_rank'], 45)

    def test_no_spurious_split(self):
        for name in ('trefoil','figure_eight','conway','kinoshita_terasaka','torus_3_5'):
            self.assertIsNone(split_once(example(name)))

    def test_explicit_order_bypasses_factors(self):
        d = connected_sum([example('trefoil')]*2)
        r = scan.khovanov_rank(d.pd, order=list(range(d.crossings)))
        self.assertNotIn('factors',r)
        self.assertEqual(r['reduced_rank'],9)


class PipelineTests(unittest.TestCase):
    def test_new_default_methods(self):
        self.assertEqual(recognize(example('conway')).method,'modular-jones')
        self.assertEqual(recognize(example('trefoil')).method,'modular-determinant')
        self.assertEqual(recognize(example('hard_unknot_8'), use_reduction=False,
                                   use_descending=False).status,'UNKNOT')

    def test_cap_falls_back(self):
        r = recognize(example('conway'), max_jones_states=1)
        self.assertEqual(r.status,'KNOTTED')
        self.assertEqual(r.method,'reduced-khovanov-F2-scan')
        self.assertIn('jones_filter_inconclusive',r.evidence)

    def test_global_limits_do_not_guess(self):
        d=example('conway')
        self.assertEqual(recognize(d,seconds=0).status,'UNKNOWN')
        self.assertEqual(recognize(d,use_alexander=False,use_jones=False,max_objects=2).status,'UNKNOWN')
        # A ceiling on the unused homology backend does not disable a valid Jones proof.
        self.assertEqual(recognize(d,use_alexander=False,max_objects=2).status,'KNOTTED')
        for options in ({'seconds':-1},{'seconds':float('nan')},{'max_objects':0}):
            with self.assertRaises(ValueError):
                recognize(d,**options)

    def test_random_decisions_against_cube(self):
        for d in random_knots(80,seed=711,max_n=8):
            expected = 'UNKNOT' if reference_reduced_rank(d)==1 else 'KNOTTED'
            self.assertEqual(recognize(d).status,expected)

    def test_cli_new_options(self):
        def run(*args):
            return subprocess.run([sys.executable,'-m','fastunknot',*args], cwd=ROOT,
                                  text=True,capture_output=True)
        path=str(ROOT/'examples'/'conway.json')
        r=run('recognize',path,'--max-objects','2')
        self.assertEqual(r.returncode,0)
        self.assertEqual(json.loads(r.stdout)['method'],'modular-jones')
        r=run('recognize',path,'--no-jones','--no-alexander','--max-objects','2')
        self.assertEqual(r.returncode,3)
        r=run('khovanov',path,'--seconds','0')
        self.assertEqual(r.returncode,3)
        r=run('recognize',path,'--seconds','-1')
        self.assertEqual(r.returncode,2)
        r=run('jones',path)
        self.assertEqual(json.loads(r.stdout)['residue'],619646344)


class CertificateTests(unittest.TestCase):
    def test_replay_factor_certificate(self):
        for factors in ([example('trefoil')]*8,
                        [example('trefoil'), example('figure_eight'), example('trefoil').mirror()],
                        [example('conway')]):
            d = connected_sum(factors)
            leaves, certificate = diagram_factors(d)
            restored = replay_factor_certificate(d, certificate)
            self.assertEqual([x.pd for x in leaves], [x.pd for x in restored])

    def test_reject_tampered_certificate(self):
        import copy
        d = connected_sum([example('trefoil')]*3)
        _, certificate = diagram_factors(d)
        altered = copy.deepcopy(certificate)
        altered['cut_edges'][0] = -1
        with self.assertRaises(ValueError):
            replay_factor_certificate(d, altered)
        altered = copy.deepcopy(certificate)
        altered['crossing_sets'][0][0] = 999
        with self.assertRaises(ValueError):
            replay_factor_certificate(d, altered)
        with self.assertRaises(ValueError):
            replay_factor_certificate(d, {'leaf': 0, 'crossings': 1})


if __name__=='__main__':
    unittest.main()
