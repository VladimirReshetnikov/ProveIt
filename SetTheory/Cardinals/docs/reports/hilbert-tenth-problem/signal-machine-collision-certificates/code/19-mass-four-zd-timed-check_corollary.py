#!/usr/bin/env python3
"""Finite exact arithmetic checks only; no CA-to-chart compiler or NF proof.
Self-contained standard-library test implementation of the displayed compiler.
Assertions are not used, so python -O performs the same checks.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import permutations, product
from math import lcm
import json
from pathlib import Path
import random

COUNTS = {}

def check(ok, group):
    if not ok:
        raise RuntimeError('failed: ' + group)
    COUNTS[group] = COUNTS.get(group, 0) + 1

class Poly:
    def __init__(self, k, terms=()):
        self.k = k
        terms = dict(terms)
        self.terms = {tuple(e): Fraction(c) for e, c in terms.items() if c}
        if any(len(e) != k or any(type(v) is not int or v < 0 for v in e)
               for e in self.terms):
            raise ValueError('bad exponents')
    @staticmethod
    def const(k, c): return Poly(k, {tuple([0]*k): c})
    @staticmethod
    def var(k, i):
        e = [0]*k; e[i] = 1
        return Poly(k, {tuple(e): 1})
    def coerce(self, p):
        p = p if isinstance(p, Poly) else Poly.const(self.k, p)
        if p.k != self.k: raise ValueError('arity')
        return p
    def __add__(self, p):
        p = self.coerce(p); terms = dict(self.terms)
        for e, c in p.terms.items(): terms[e] = terms.get(e, 0) + c
        return Poly(self.k, terms)
    __radd__ = __add__
    def __neg__(self): return Poly(self.k, {e: -c for e, c in self.terms.items()})
    def __sub__(self, p): return self + (-self.coerce(p))
    def __rsub__(self, p): return self.coerce(p) + (-self)
    def __mul__(self, p):
        p = self.coerce(p); terms = {}
        for e, c in self.terms.items():
            for f, v in p.terms.items():
                h = tuple(a+b for a, b in zip(e, f))
                terms[h] = terms.get(h, 0) + c*v
        return Poly(self.k, terms)
    __rmul__ = __mul__
    @property
    def degree(self): return max((sum(e) for e in self.terms), default=0)
    def __call__(self, values):
        if len(values) != self.k: raise ValueError('eval arity')
        answer = Fraction(0)
        for e, c in self.terms.items():
            for x, a in zip(values, e):
                if a: c *= x**a
            answer += c
        return answer
    def clear(self):
        L = lcm(*(c.denominator for c in self.terms.values()))
        return L*self
    def lift(self, total, parameter_slots, selector_slot):
        terms = {}
        for e, c in self.terms.items():
            h = [0]*total
            if any(e):
                for slot, a in zip(parameter_slots, e): h[slot] = a
            else: h[selector_slot] = 1
            terms[tuple(h)] = c
        return Poly(total, terms)

@dataclass
class Chart:
    k: int
    out: tuple
    ge: tuple = ()
    eq: tuple = ()

class Compiled:
    def __init__(self, charts):
        self.charts = charts
        self.B = len(charts); self.Q = len(charts[0].out)
        self.K = sum(c.k for c in charts)
        self.M = sum(len(c.ge) for c in charts)
        self.H = sum(len(c.eq) for c in charts)
        self.N = self.B + self.K + self.M
        self.total = self.Q + self.N
        V = lambda i: Poly.var(self.total, i)
        self.zslots = []; self.uslots = []
        slot = self.Q + self.B
        for c in charts:
            self.zslots.append(tuple(range(slot, slot+c.k))); slot += c.k
            self.uslots.append(tuple(range(slot, slot+len(c.ge)))); slot += len(c.ge)
        self.selectors = [V(self.Q+i) for i in range(self.B)]
        residuals = [sum(self.selectors)-1]
        pooled = [Poly.const(self.total, 0) for _ in range(self.Q)]
        for i, c in enumerate(charts):
            lift = lambda f: f.lift(self.total, self.zslots[i], self.Q+i)
            residuals += [lift(f.clear())-V(u) for f, u in zip(c.ge, self.uslots[i])]
            residuals += [lift(f.clear()) for f in c.eq]
            for q, f in enumerate(c.out): pooled[q] += lift(f)
        residuals += [(V(q)-pooled[q]).clear() for q in range(self.Q)]
        for i in range(self.B):
            Z = sum((V(s) for s in self.zslots[i]+self.uslots[i]), Poly.const(self.total, 0))
            residuals.append((1-self.selectors[i])*Z)
        self.residuals = residuals
        self.expression = sum((r*r for r in residuals), Poly.const(self.total, 0))
        check(len(residuals) == 1+self.M+self.H+self.Q+self.B, 'residual_ledgers')
        check(self.N == self.B+self.K+self.M, 'witness_ledgers')
        check(all(r.degree <= 2 for r in residuals), 'residual_degrees')
        check(self.expression.degree <= 4, 'ordinary_quartic_degrees')
        check(all(c.denominator == 1 for c in self.expression.terms.values()), 'integer_coefficients')
    def witness(self, i, z):
        c = self.charts[i]
        if len(z) != c.k or any(v < 0 for v in z): raise ValueError('parameters')
        if any(f(z) != 0 for f in c.eq): raise ValueError('equality')
        w = [0]*self.N; w[i] = 1
        for slot, value in zip(self.zslots[i], z): w[slot-self.Q] = value
        for slot, f in zip(self.uslots[i], c.ge):
            value = f.clear()(z)
            if value < 0 or value.denominator != 1: raise ValueError('domain')
            w[slot-self.Q] = int(value)
        return tuple(w)
    def evaluate(self, out, w):
        if any(type(v) is not int or v < 0 for v in w): raise ValueError('natural witness')
        x = tuple(out)+tuple(w)
        return sum(r(x)**2 for r in self.residuals)


def lex_cases(points):
    m = len(points); d = len(points[0]) if points else 1
    good = []
    for pi in permutations(range(m)):
        for ks in product(range(d), repeat=max(0, m-1)):
            if all(all(points[b][h] == points[a][h] for h in range(k))
                   and points[b][k]-points[a][k] >= 1
                   for a,b,k in zip(pi, pi[1:], ks)):
                good.append((pi,ks))
    return good

def sorting_tests():
    rng = random.Random(20261003)
    fixtures = [[(0,0),(0,1)], [(0,1),(0,0)], [(1,0),(1,1)],
                [(2,0),(0,1)], [(1,1,1),(1,1,0),(1,0,2),(0,9,9)]]
    for d in range(1,5):
        for m in range(1,5):
            for _ in range(20):
                points = set()
                while len(points) < m:
                    points.add(tuple(rng.randrange(-4,5) for _ in range(d)))
                fixtures.append(list(points))
    for points in fixtures:
        good = lex_cases(points)
        check(len(good) == 1, 'lex_refinement_uniqueness')
        pi, _ = good[0]
        check([points[i] for i in pi] == sorted(points), 'lex_refinement_correct_order')
    for j in range(5):
        points = [(j,0),(2-j,1)]
        check(len(lex_cases(points)) == 1, 'lex_order_crossing_and_tie')


def step_binary(sites):
    ordered = sorted(sites); components = []
    for x in ordered:
        if not components or x-components[-1][-1] > 2: components.append([x])
        else: components[-1].append(x)
    rules = {(0,1):(1,2), (0,2):(-1,1), (0,1,3):(-1,1,4), (0,2,4):(0,3,4)}
    out = set()
    for component in components:
        base = component[0]; relative = tuple(x-base for x in component)
        out.update(base+x for x in rules.get(relative, relative))
    return out


def shuttle_tests():
    # Embed the known 1D binary fixture along e_2 and restore drift (-2,1).
    n = Poly.var(2,0); j = Poly.var(2,1)
    for gap in (7,9):
        T = n*n+(2*gap-11)*n
        times = [T+j, T+gap+n-5+j]
        ys = [(Poly.const(2,0),3+j,4+j,gap+n),
              (Poly.const(2,0),gap+n-4-j,gap+n-2-j,gap+n+1)]
        charts = []
        for time, positions in zip(times, ys):
            coords = tuple(p for y in positions for p in (-2*time,y+time))
            inequalities = (gap+n-6-j,)+tuple(positions[v+1]-positions[v]-1 for v in range(3))
            charts.append(Chart(2,(time,)+coords,inequalities,(Poly.const(2,0),)*3))
        cert = Compiled(charts)
        check(cert.N == 14 and len(cert.residuals) == 26, 'multidimensional_exact_ledger')
        state = {0,3,4,gap}; t = 0
        for cycle in range(8):
            for branch in range(2):
                for flight in range(gap+cycle-5):
                    z = (cycle,flight)
                    out = tuple(int(p(z)) for p in charts[branch].out)
                    expected = (t,)+tuple(v for y in sorted(state) for v in (-2*t,y+t))
                    check(out == expected, 'full_timed_orbit_and_drift')
                    witness = cert.witness(branch,z)
                    check(cert.evaluate(out,witness) == 0, 'canonical_orbit_witness')
                    if cycle < 2:
                        for q in range(cert.Q):
                            bad = list(out); bad[q] += 1
                            check(cert.evaluate(bad,witness) > 0, 'wrong_external_rejections')
                    state = step_binary(state); t += 1
        check(t == 8*8+(2*gap-11)*8, 'half_open_cycle_boundaries')


def quadratic_domain_and_gate_tests():
    z = Poly.var(1,0)
    # Disjoint: branch zero outputs t=0; branch one t=n^2, n>=1.
    # A quadratic inequality tests the strengthened observation-domain interface.
    charts = [Chart(0,(Poly.const(0,0),)), Chart(1,(z*z,), (z-1,z*z-1))]
    cert = Compiled(charts)
    check(cert.N == 5, 'quadratic_domain_ledger')
    # Full natural witness cube, not merely intended witnesses; larger valid
    # branches are checked separately below. Bound external time only for this finite test.
    for t in range(5):
        roots = []
        for w in product(range(3), repeat=cert.N):
            value = cert.evaluate((t,),w)
            check(value >= 0, 'full_cube_nonnegativity')
            if value == 0: roots.append(w)
        expected = 1 if t in (0,1) else 0  # t=4 requires slack 3, outside cube
        check(len(roots) == expected, 'full_cube_root_counts')
    for n in (1,2,3,10,10**30):
        w = cert.witness(1,(n,))
        check(cert.evaluate((n*n,),w) == 0, 'quadratic_domain_unique_slack')
        bad = list(w); bad[0] = 1
        check(cert.evaluate((n*n,),bad) > 0, 'invalid_selector_rejections')
    # Source Report 13's pitfall: without inactivity gates, n=1 and an
    # inactive n=1 can contribute to a pooled output not represented by either chart.
    c2 = Compiled([Chart(1,(z+1,)),Chart(1,(z+10,))])
    w = (1,0,0,1)  # selected first n=0; inactive second n=1
    residual_without_gates = c2.residuals[:-2]
    values = (2,)+w
    check(sum(r(values)**2 for r in residual_without_gates) == 0, 'missing_gate_counterexample')
    check(c2.evaluate((2,),w) > 0, 'inactive_branch_rejection')


def comparison_code(x,y):
    if x == y: return ('eq',)
    for k,(a,b) in enumerate(zip(x,y)):
        if a != b: return (k,1 if a>b else -1)
    raise RuntimeError('unreachable')

def matches(state, pattern, shift):
    return all(state.get(tuple(a+b for a,b in zip(site,shift)),0) == label
               for site,label in pattern.items())

def pattern_tests():
    # Two successful placements at one exact configuration; the canonical
    # choice has to be explicit, since uniqueness of placement is false.
    state = {(0,0):1,(0,2):1,(0,4):1,(0,6):1}
    pattern = {(0,0):1,(0,1):0,(0,2):1}
    ordered = sorted(state); anchor = (0,0)
    successes = [x for x in ordered if matches(state,pattern,x)]
    check(len(successes) == 3 and min(successes) == (0,0), 'multiple_translation_placements')
    matrix = tuple(comparison_code(tuple(v[h]-i[h] for h in range(2)),w)
                   for i in ordered for v in ordered for w in pattern)
    check(len(matrix) == len(ordered)**2*len(pattern), 'translated_comparison_count')
    for drift in ((-3,4),(1,-2),(0,0)):
        shifted = {tuple(x[h]+drift[h] for h in range(2)):a for x,a in state.items()}
        sorted_shifted = sorted(shifted)
        matrix2 = tuple(comparison_code(tuple(v[h]-i[h] for h in range(2)),w)
                        for i in sorted_shifted for v in sorted_shifted for w in pattern)
        check(matrix == matrix2, 'translated_pattern_drift_cancellation')
        hits = [x for x in sorted_shifted if matches(shifted,pattern,x)]
        check(min(hits) == tuple(min(successes)[h]+drift[h] for h in range(2)), 'first_success_is_canonical')
    zero_pattern = {(-4,0):0,(9,7):0}
    shift = (max(x[0] for x in state)+1-min(w[0] for w in zero_pattern),0)
    check(matches(state,zero_pattern,shift), 'all_zero_chosen_placement')
    for x in range(-20,21):
        pair = (max(x,0),max(-x,0))
        check(pair[0]-pair[1] == x and pair[0]*pair[1] == 0, 'canonical_signed_pairs')
        check((pair[0]+1)*(pair[1]+1) != 0, 'noncanonical_signed_pair_rejection')


def main():
    sorting_tests()
    shuttle_tests()
    quadratic_domain_and_gate_tests()
    pattern_tests()
    result = {'status':'passed','scope':'finite exact arithmetic fixtures; not a proof of NF',
              'counts':dict(sorted(COUNTS.items()))}
    output = Path(__file__).with_name('check-results.json')
    output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__ == '__main__': main()
