"""Independent validation of the filters, algebra, ordering and integration."""
from __future__ import annotations
import copy
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import random
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / 'reference')]
import baseline_fastunknot as baseline
from baseline_fastunknot import scan as original_scan
from baseline_fastunknot.simplify import descending_start as original_descending
from fastunknot import Diagram, DiagramError, alexander_polynomial, khovanov_rank, recognize
from fastunknot import scan
from fastunknot.filters import (MODULUS, attach, bracket_obstruction,
                               determinant_obstruction, sparse_determinant, verify_obstruction)
from fastunknot.recognize import verify_modular_result
from test_fastunknot import reference_reduced_rank, one_component


def samples(count=100, seed=20260918, maximum=9):
    rng = random.Random(seed)
    found = 0
    while found < count:
        strands = rng.choice([2, 3, 4, 5])
        word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                for _ in range(rng.randrange(max(1, strands - 1), maximum + 1))]
        if one_component(strands, word):
            found += 1
            yield Diagram.from_braid(strands, word)


def exhaustive_small():
    for length in (2, 4):
        for word in product((-2, -1, 1, 2), repeat=length):
            if one_component(3, word):
                yield Diagram.from_braid(3, word)


def cube_bracket(diagram, a=Fraction(2)):
    """Independent global state sum using a fresh edge DSU for every state."""
    n = diagram.crossings
    delta = -a*a - 1/(a*a)
    if not n:
        return delta
    answer = 0
    for state in range(1 << n):
        parents = list(range(2*n))
        def find(x):
            while parents[x] != x:
                parents[x] = parents[parents[x]]
                x = parents[x]
            return x
        for i, (u, v, w, x) in enumerate(diagram.pd):
            pairs = ((u, x), (v, w)) if state >> i & 1 else ((u, v), (w, x))
            for p, q in pairs:
                parents[find(p)] = find(q)
        circles = len({find(i) for i in range(2*n)})
        answer += a**(n - 2*state.bit_count()) * delta**circles
    return answer


def normalized_bracket(diagram, a=2):
    result = bracket_obstruction(diagram, modulus=None, value=a)
    scaled = int(result['scaled_bracket_hex'], 16)
    target = int(result['unknot_scaled_hex'], 16)
    return Fraction(scaled, target)


def noncrossing(points):
    if not points:
        yield frozenset()
        return
    for k in range(1, len(points), 2):
        for left in noncrossing(points[1:k]):
            for right in noncrossing(points[k+1:]):
                yield left | right | {frozenset((points[0], points[k]))}


def monomials(a, b):
    keys = sorted(set(original_scan.circles(a, b).values()), key=lambda x: tuple(sorted(x)))
    return [frozenset(keys[j] for j in range(len(keys)) if mask >> j & 1)
            for mask in range(1 << len(keys))]


class OrderingAndPreprocessing(unittest.TestCase):
    def test_greedy_order_exact_equivalence(self):
        for d in samples(100, maximum=20):
            for start in range(d.crossings):
                self.assertEqual(scan.scan_order(d.pd, start), original_scan.scan_order(d.pd, start))
            self.assertEqual(scan.best_scan_order(d.pd, tries=12),
                             original_scan.best_scan_order(d.pd, tries=12))

    def test_descending_exact_equivalence(self):
        from fastunknot.simplify import descending_start
        for d in list(exhaustive_small()) + list(samples(150, maximum=25)):
            self.assertEqual(descending_start(d), original_descending(d))

    def test_oriented_writhe_and_pd_rotations(self):
        rng = random.Random(77)
        found_old_bug = False
        for d in samples(100, maximum=12):
            rows = list(d.pd)
            for i in range(len(rows)):
                if rng.randrange(2):
                    rows[i] = rows[i][2:] + rows[i][:2]
            rng.shuffle(rows)
            rotated = Diagram.from_pd(rows)
            self.assertEqual(d.writhe(), rotated.writhe())
            self.assertEqual(d.writhe(), -d.mirror().writhe())
            self.assertEqual(alexander_polynomial(d), alexander_polynomial(rotated))
            self.assertEqual(alexander_polynomial(rotated),
                             baseline.alexander_polynomial(baseline.Diagram.from_pd(rows)))
            if baseline.Diagram.from_pd(rows).writhe() != d.writhe():
                found_old_bug = True
            self.assertEqual(normalized_bracket(d), normalized_bracket(rotated))
        self.assertTrue(found_old_bug)

    def test_order_validation_and_budget_validation(self):
        d = Diagram.from_braid(2, [1]*3)
        for order in ([], [0,1,1], [0,1,3], [False,1,2]):
            with self.assertRaises(ValueError):
                khovanov_rank(d.pd, order=order)
            with self.assertRaises(ValueError):
                bracket_obstruction(d, order=order)
        with self.assertRaises(ValueError):
            scan.best_scan_order(d.pd, tries=0)
        with self.assertRaises(ValueError):
            scan.scan_order(d.pd, start=10)
        for seconds in (-1, float('nan'), float('inf')):
            with self.assertRaises(ValueError):
                recognize(d, seconds=seconds)
        with self.assertRaises(DiagramError):
            recognize(Diagram(((0,1,2,3),)))


class CompiledAlgebra(unittest.TestCase):
    def test_all_six_point_basis_compositions(self):
        matches = list(noncrossing(tuple(range(6))))
        self.assertEqual(len(matches), 5)
        for a, b, c in product(matches, repeat=3):
            for f, g in product(monomials(a,b), monomials(b,c)):
                self.assertEqual(scan.compose({f},{g},a,b,c),
                                 original_scan.compose({f},{g},a,b,c))

    def test_random_eight_point_combinations_and_associativity(self):
        rng = random.Random(791)
        matches = list(noncrossing(tuple(range(8))))
        for _ in range(250):
            a,b,c,d = rng.choices(matches,k=4)
            f = {m for m in monomials(a,b) if rng.randrange(2)}
            g = {m for m in monomials(b,c) if rng.randrange(2)}
            h = {m for m in monomials(c,d) if rng.randrange(2)}
            self.assertEqual(scan.compose(f,g,a,b,c), original_scan.compose(f,g,a,b,c))
            self.assertEqual(scan.compose(scan.compose(f,g,a,b,c),h,a,c,d),
                             scan.compose(f,scan.compose(g,h,b,c,d),a,b,d))

    def test_all_units_through_three_arcs(self):
        for arcs in range(4):
            m = frozenset(frozenset((2*i,2*i+1)) for i in range(arcs))
            terms = monomials(m,m)
            for mask in range(1 << len(terms)):
                f = {terms[j] for j in range(len(terms)) if mask >> j & 1}
                if frozenset() not in f:
                    continue
                self.assertEqual(scan.inverse(f,m), f)
                self.assertEqual(scan.compose(f,f,m,m,m), {frozenset()})
                self.assertEqual(original_scan.inverse(f,m), f)

    def test_cached_values_are_not_mutable_aliases(self):
        a,b = list(noncrossing(tuple(range(4))))
        f,g = {frozenset()}, {frozenset()}
        expected = scan.compose(f,g,a,b,a)
        returned = scan.compose(f,g,a,b,a)
        returned.clear()
        self.assertEqual(scan.compose(f,g,a,b,a), expected)
        args = (frozenset(),frozenset(),{frozenset()},0,1,frozenset(),(0,1,2,3))
        expected = scan.crossing_entries(*args)[2]
        returned = scan.crossing_entries(*args)[2]
        for value in returned.values():
            value.clear()
        self.assertEqual(scan.crossing_entries(*args)[2], expected)
        scan.clear_caches()
        for fn in (scan.circles,scan.glue,scan._compose_cached,scan._crossing_entries_cached):
            self.assertEqual(fn.cache_info().currsize,0)
            self.assertIsNotNone(fn.cache_info().maxsize)


class ObstructionTests(unittest.TestCase):
    def test_independent_cube_bracket_exhaustive_and_random(self):
        diagrams = list(exhaustive_small()) + list(samples(120, maximum=9)) + [Diagram.from_pd([])]
        for d in diagrams:
            q = cube_bracket(d)
            exact = bracket_obstruction(d, modulus=None)
            self.assertEqual(Fraction(int(exact['scaled_bracket_hex'],16),
                                     2**exact['scale_exponent']), q)
            modular = bracket_obstruction(d)
            self.assertEqual(modular['bracket_residue'],
                             q.numerator * pow(q.denominator,-1,MODULUS) % MODULUS)

    def test_transition_against_cobordism_glue(self):
        rng = random.Random(37)
        for d in samples(40, maximum=10):
            order = list(range(d.crossings))
            rng.shuffle(order)
            states, points = {()}, frozenset()
            for i in order:
                new = set()
                for m in states:
                    frozen = frozenset(frozenset(p) for p in m)
                    for smoothing in (0,1):
                        actual, closed = attach(m,d.pd[i],smoothing)
                        ref = original_scan.glue(frozen,smoothing,points,d.pd[i])
                        self.assertEqual(frozenset(frozenset(p) for p in actual),ref.matching)
                        self.assertEqual(closed,ref.closed)
                        new.add(actual)
                states = new
                points = frozenset(e for p in next(iter(states)) for e in p)

    def test_integer_modular_mirror_and_arbitrary_order(self):
        rng = random.Random(5)
        for d in samples(75, maximum=12):
            order = list(range(d.crossings))
            rng.shuffle(order)
            a = bracket_obstruction(d)
            b = bracket_obstruction(d,order=order)
            self.assertEqual(a['bracket_residue'],b['bracket_residue'])
            inv = pow(2,-1,MODULUS)
            mirror = bracket_obstruction(d.mirror(),value=inv)
            self.assertEqual(a['bracket_residue'],mirror['bracket_residue'])
            self.assertEqual(a['unknot_residue'],mirror['unknot_residue'])

    def test_reidemeister_three_and_markov_stabilization(self):
        for suffix in ([1],[-1],[2],[-2],[1,2,1],[-2,-1,2]):
            left, right = [1,2,1]+list(suffix), [2,1,2]+list(suffix)
            if not one_component(3,left):
                continue
            d,e = Diagram.from_braid(3,left),Diagram.from_braid(3,right)
            self.assertEqual(normalized_bracket(d),normalized_bracket(e))
            for sign in (-1,1):
                stabilized = Diagram.from_braid(4,left+[sign*3])
                self.assertEqual(normalized_bracket(d),normalized_bracket(stabilized))

    def test_modular_determinant_matches_full_polynomial(self):
        from fastunknot.alexander import evaluate
        for d in list(exhaustive_small()) + list(samples(200, maximum=16)):
            residue = determinant_obstruction(d)['minor_residue']
            expected = evaluate(alexander_polynomial(d),-1) % MODULUS
            self.assertIn(residue,(expected,(-expected)%MODULUS))

    def test_sparse_determinant_against_permutation_formula(self):
        from itertools import permutations
        rng=random.Random(808)
        for n in range(6):
            for _ in range(20):
                a=[[rng.randrange(-5,6) for _ in range(n)] for _ in range(n)]
                determinant=0
                for perm in permutations(range(n)):
                    sign=(-1)**sum(perm[i]>perm[j] for i in range(n) for j in range(i+1,n))
                    term=sign
                    for i,j in enumerate(perm): term*=a[i][j]
                    determinant+=term
                self.assertEqual(sparse_determinant([dict(enumerate(row)) for row in a]),
                                 determinant%MODULUS)

    def test_equal_values_and_budget_exhaustion_never_prove_unknot(self):
        d=Diagram.from_braid(2,[1]*3)
        # delta=0 at A=2 modulo 17 makes every nonempty closed bracket vanish.
        collision=bracket_obstruction(d,modulus=17)
        self.assertTrue(collision['complete'])
        self.assertFalse(collision['detected'])
        self.assertNotIn('status',collision)
        for kwargs in ({'max_states':0},{'max_states':1},{'max_transitions':0}):
            r=bracket_obstruction(d,**kwargs)
            self.assertFalse(r['complete'])
            self.assertFalse(r['detected'])
        with self.assertRaises(ValueError): bracket_obstruction(d,modulus=16,value=2)
        with self.assertRaises(ValueError): bracket_obstruction(d,modulus=None,value=1)

    def test_witness_verification_and_tampering(self):
        for name in ('trefoil','conway','torus_3_5'):
            d=Diagram.from_json(json.loads((ROOT/'examples'/f'{name}.json').read_text()))
            result=recognize(d).to_json()
            self.assertTrue(verify_modular_result(d,result))
            bad=copy.deepcopy(result)
            obstruction=bad['evidence']['obstruction']
            key='minor_residue' if obstruction['kind']=='modular-determinant' else 'bracket_residue'
            obstruction[key]+=1
            self.assertFalse(verify_modular_result(d,bad))
            self.assertFalse(verify_modular_result(Diagram.from_pd([]),result))
            exact={'kind':'integer-bracket',**bracket_obstruction(d,modulus=None)}
            self.assertTrue(verify_obstruction(d,exact))
        self.assertFalse(verify_modular_result(d,{}))


class IntegrationTests(unittest.TestCase):
    def test_independent_cube_on_alexander_trivial_fixtures(self):
        for name in ('conway', 'kinoshita_terasaka'):
            d = Diagram.from_json(json.loads((ROOT/'examples'/f'{name}.json').read_text()))
            self.assertEqual(reference_reduced_rank(d), 33)
            self.assertEqual(khovanov_rank(d.pd)['reduced_rank'], 33)

    def test_connected_sum_family_exact_bracket(self):
        from tools.families import connected_power
        d = Diagram.from_json(json.loads((ROOT/'examples/conway.json').read_text()))
        point = Fraction(970142522911, 65536)
        for k in range(1, 6):
            power = connected_power(d, k)
            result = bracket_obstruction(power, modulus=None, order=range(power.crossings))
            actual = Fraction(int(result['scaled_bracket_hex'], 16),
                              int(result['unknot_scaled_hex'], 16))
            self.assertEqual(actual, point**k)
            self.assertTrue(result['detected'])

    def test_connected_sum_rank_and_reproducible_fixture(self):
        from tools.families import connected_power
        d = Diagram.from_json(json.loads((ROOT/'examples/conway.json').read_text()))
        power = connected_power(d, 2)
        fixture = Diagram.from_json(json.loads((ROOT/'examples/conway_sum_2.json').read_text()))
        self.assertEqual(power.pd, fixture.pd)
        self.assertEqual(khovanov_rank(power.pd)['reduced_rank'], 1089)

    def test_independent_cube_rank_and_original_graded_backend(self):
        for d in samples(80,maximum=8):
            actual=khovanov_rank(d.pd,check_d_squared=True)
            original=baseline.khovanov_rank(d.pd)
            self.assertEqual(actual['reduced_rank'],reference_reduced_rank(d))
            self.assertEqual(actual['by_degree'],original['by_degree'])
            self.assertEqual(actual['rank'],original['rank'])

    def test_verdicts_exhaustive_and_random(self):
        for d in list(exhaustive_small())+list(samples(80,maximum=8)):
            expected='UNKNOT' if reference_reduced_rank(d)==1 else 'KNOTTED'
            result=recognize(d)
            self.assertEqual(result.status,expected)
            # Force both the old pipeline and the optimized unfiltered backend.
            forced=recognize(d,use_alexander=False,use_jones=False,
                             use_reduction=False,use_descending=False)
            self.assertEqual(forced.status,expected)
            self.assertFalse(result.to_json()['quasipolynomial_guarantee'])

    def test_all_filter_ablation_and_resource_paths(self):
        d=Diagram.from_json(json.loads((ROOT/'examples/conway.json').read_text()))
        self.assertEqual(recognize(d,max_objects=1).status,'KNOTTED')
        self.assertEqual(recognize(d,max_objects=1,use_alexander=False,use_jones=False).status,'UNKNOWN')
        self.assertEqual(recognize(d,seconds=0).status,'UNKNOWN')
        self.assertEqual(recognize(d,jones_max_transitions=0).status,'KNOTTED')
        self.assertEqual(recognize(d,jones_max_transitions=0).method,'reduced-khovanov-F2-scan')
        trefoil=Diagram.from_braid(2,[1]*3)
        r=recognize(trefoil,use_modular=False,use_jones=False)
        self.assertEqual(r.method,'alexander-polynomial')
        for limit in (-1,0):
            with self.assertRaises(ValueError): recognize(d,max_objects=limit)

    def test_cli_new_commands_and_exit_codes(self):
        def run(*args):
            return subprocess.run([sys.executable,'-m','fastunknot',*args],cwd=ROOT,
                                  capture_output=True,text=True)
        self.assertEqual(run('bracket','examples/conway.json','--integer').returncode,0)
        self.assertEqual(run('khovanov','examples/conway.json','--max-objects','1').returncode,3)
        self.assertEqual(run('recognize','examples/conway.json','--seconds','-1').returncode,2)
        import tempfile
        with tempfile.TemporaryDirectory() as tmp:
            output=str(Path(tmp)/'result.json')
            self.assertEqual(run('recognize','examples/conway.json','--output',output).returncode,0)
            self.assertEqual(run('verify','examples/conway.json',output).returncode,0)
            self.assertEqual(run('verify','examples/trefoil.json',output).returncode,4)


if __name__=='__main__': unittest.main()
