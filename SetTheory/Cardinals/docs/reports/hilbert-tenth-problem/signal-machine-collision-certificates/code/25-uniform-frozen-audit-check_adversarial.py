#!/usr/bin/env python3
"""Independent arithmetic adversaries; no imported programs or saved schedules.

These are finite abstract-section and compiler tests, not a CA compiler and not
a proof of the all-rules dynamics. The direct oracle advances one time at a time.
"""
from collections import Counter
from hashlib import sha256
from itertools import product
from pathlib import Path
import json
import sympy as sp

HERE = Path(__file__).resolve().parent
counts = Counter()


def partial_sums(xs):
    answer = [0]
    for x in xs:
        answer.append(answer[-1] + x)
    return answer


def witness_at_step(step, g, left, clock, periods, prefixes, word, shifts):
    """One actual abstract section edge, with every elapsed time retained."""
    s = step % len(word)
    flight = (s + 1) * g + 3
    for elapsed in range(flight + prefixes[s]):
        if elapsed < flight:
            j, r = divmod(elapsed, periods[s])
            descriptor = (s, g, left, 'flight', r, j)
        else:
            descriptor = (s, g, left, 'prefix', elapsed - flight)
        yield clock + elapsed, descriptor


def chart_edge(d, left0, n, s, word, shifts, periods, prefixes):
    cs, es = partial_sums(word), partial_sums(shifts)
    delta, shift = cs[-1], es[-1]
    alphas = list(range(1, len(word) + 1))
    betas = [3 + p for p in prefixes]
    A = sum(alphas)
    B = sum(a * c + b for a, c, b in zip(alphas, cs, betas))
    base = n * (A * d + B) + A * delta * n * (n - 1) // 2
    base += sum(alphas[i] * (d + n * delta + cs[i]) + betas[i]
                for i in range(s))
    g = d + n * delta + cs[s]
    left = left0 + n * shift + es[s]
    flight = alphas[s] * g + 3
    for r in range(periods[s]):
        j = 0
        while r + periods[s] * j < flight:
            yield base + r + periods[s] * j, (s, g, left, 'flight', r, j)
            j += 1
    for v in range(prefixes[s]):
        yield base + flight + v, (s, g, left, 'prefix', v)


def section_tests():
    N = 12
    for m in range(1, 5):
        for word in product(range(-2, 3), repeat=m):
            cs = partial_sums(word)
            delta, b = cs[-1], min(cs)
            shifts = tuple((2 * i - m) for i in range(m))
            periods = tuple(i % 3 + 2 for i in range(m))
            prefixes = tuple(i % 3 for i in range(m))
            for d in range(N + 1, N + 10):
                left0 = 7 - 3 * d
                # Direct oracle: no accelerated cycle count or clock formula.
                direct = {}
                step, g, left, clock = 0, d, left0, 0
                indefinitely_live = delta >= 0 and d + b > N
                while g > N and (not indefinitely_live or step < 7 * m):
                    for time, descriptor in witness_at_step(
                            step, g, left, clock, periods, prefixes, word, shifts):
                        assert time not in direct
                        direct[time] = descriptor
                    s = step % m
                    clock += (s + 1) * g + 3 + prefixes[s]
                    g += word[s]
                    left += shifts[s]
                    step += 1
                    assert step < 1000
                # Closed chart construction, with the final endpoint included.
                if delta < 0:
                    a = -delta
                    K = max(0, -((-(d + b - N)) // a))
                elif indefinitely_live:
                    K = 7
                else:
                    K = 0
                charts = {}
                for n in range(K):
                    for s in range(m):
                        for time, descriptor in chart_edge(
                                d, left0, n, s, word, shifts, periods, prefixes):
                            assert time not in charts, ('duplicate', word, d, time)
                            charts[time] = descriptor
                if not indefinitely_live:
                    first_fail = next(s for s in range(1, m + 1)
                                      if d + K * delta + cs[s] <= N)
                    assert d + K * delta > N
                    assert all(d + K * delta + cs[s] > N
                               for s in range(first_fail))
                    for s in range(first_fail):
                        for time, descriptor in chart_edge(
                                d, left0, K, s, word, shifts, periods, prefixes):
                            assert time not in charts
                            charts[time] = descriptor
                    # Exact bounded reset geometry and the first reset time.
                    assert step == K * m + first_fail
                    assert g == d + K * delta + cs[first_fail]
                    assert N + min(word) < g <= N
                    assert left == left0 + K * sum(shifts) + sum(shifts[:first_fail])
                    assert max(charts) + 1 == clock
                    # A normalized, fixed reset template: two prefix states,
                    # then a translated period-three tail. No extra prehistory
                    # parameter appears in this additive composition.
                    for elapsed in range(23):
                        if elapsed < 2:
                            state = ('reset-prefix', g, elapsed, left)
                        else:
                            n, r = divmod(elapsed - 2, 3)
                            state = ('reset-tail', g, r, left + 2 * n)
                        assert clock + elapsed not in charts
                        charts[clock + elapsed] = state
                        direct[clock + elapsed] = state
                    counts['bounded_reset_cases'] += 1
                assert charts == direct, (word, d)
                assert sorted(charts) == list(range(len(charts)))
                counts['abstract_section_cases'] += 1
                counts['individual_times_compared'] += len(charts)
    # Explicit counterexamples to tempting weaker guards, not to the note.
    assert partial_sums((-3,)) == [0, -3]
    assert 12 > 10 and 12 - 3 <= 10  # Final endpoint cannot be omitted.
    assert 13 > 10 and 13 - 5 + 6 > 10 and 13 - 5 <= 10
    # Start and final endpoint do not suffice: (-5,+6) fails internally.
    counts['rejected_incomplete_guard_variants'] = 2


def first_contact_tests():
    # Enumerate first proximity of several synchronized phase pairs. The
    # independent oracle checks each chronological time, not candidate minima.
    def phase_candidate(A, drift, width):
        if drift == 0:
            return 0 if abs(A) <= width else None
        lower, upper = sorted((sp.Rational(-width-A, drift),
                               sp.Rational(width-A, drift)))
        k = max(0, int(sp.ceiling(lower)))
        return k if k <= upper else None
    for P in range(1, 5):
        for gap in range(-30, 31):
            for drift in range(-4, 5):
                candidates = []
                for r in range(P):
                    # Two monitored site pairs per phase; holes are allowed.
                    for pair in range(2):
                        A = gap + 3*r + 7*pair
                        k = phase_candidate(A, drift, 2)
                        if k is not None:
                            candidates.append((r+P*k, r, pair, k))
                selected = min(candidates) if candidates else None
                brute = None
                for t in range(250):
                    k, r = divmod(t, P)
                    pairs = [pair for pair in range(2)
                             if abs(gap+3*r+7*pair+drift*k) <= 2]
                    if pairs:
                        brute = (t, r, min(pairs), k)
                        break
                assert selected == brute
                counts['synchronized_first_contact_cases'] += 1
    # False hull contact for a compact three-mass phase with a large hole.
    sites, probe, radius = [0, 20, 21], 10, 2
    assert min(sites)-radius <= probe <= max(sites)+radius
    assert not any(abs(probe-v) <= radius for v in sites)
    counts['rejected_hull_contact_variants'] = 1


def compiler_tests():
    # Two disjoint congruence charts with a genuinely quadratic input term.
    # Private X copies, unique input quotient, one free chart parameter.
    x, t, v = sp.symbols('x t v')
    e0,e1,X0,X1,u0,u1,n0,n1 = sp.symbols('e0 e1 X0 X1 u0 u1 n0 n1')
    ws = (e0,e1,X0,X1,u0,u1,n0,n1)
    residuals = [e0+e1-1, X0-e0*x, X1-e1*x,
                 X0-2*u0, X1-2*u1-e1,
                 (1-e0)*(X0+u0+n0), (1-e1)*(X1+u1+n1),
                 t-(X0**2+X0*n0+n0**2+X1**2+X1*n1+n1**2+e1),
                 v-(X0+n0+X1-n1)]
    C = sp.Poly(sum(r*r for r in residuals), x,t,v,*ws)
    assert C.total_degree() == 4
    assert max(sp.Poly(r,x,t,v,*ws).total_degree() for r in residuals) == 2
    # The naive input-dependent constant lift has an actual degree-six square.
    naive = t-(x*n0+n0**2+e0*x*x)
    assert sp.Poly(naive**2,x,t,n0,e0).total_degree() == 6
    counts['symbolic_quartic_degree_checks'] += 2
    for external_x in range(5):
        fibers = Counter()
        # Every natural selector value >1 is excluded by the selector residual;
        # include 2 explicitly, and exhaust private-variable boxes including
        # invalid inactive values. Residual zero tests avoid huge expansions.
        for a,b in product(range(3), repeat=2):
            for A,B,U,V,N,M in product(range(5), repeat=6):
                counts['compiler_witness_tuples_checked'] += 1
                if a+b != 1 or A != a*external_x or B != b*external_x:
                    continue
                if A-2*U or B-2*V-b:
                    continue
                if (1-a)*(A+U+N) or (1-b)*(B+V+M):
                    continue
                out_t = A*A+A*N+N*N+B*B+B*M+M*M+b
                out_v = A+N+B-M
                fibers[out_t,out_v] += 1
        expected = {}
        for n in range(5):
            expected[external_x**2+external_x*n+n*n+(external_x%2),
                     external_x+n if external_x%2==0 else external_x-n] = 1
        assert dict(fibers) == expected
        counts['compiler_external_input_cases'] += 1
    counts['compiler_empty_or_singleton_outputs'] = 25


def congruence_tests():
    for denominator in range(1, 7):
        for modulus in range(1, 7):
            for value in range(-100, 101):
                if value % denominator:
                    continue
                for rho in range(modulus):
                    lhs = (value // denominator) % modulus == rho
                    rhs = (value-denominator*rho) % (denominator*modulus) == 0
                    assert lhs == rhs
                    counts['denominator_inside_congruence_cases'] += 1
    assert 2 % 2 == 0 and (2//2) % 2 != 0
    counts['rejected_lcm_only_congruence_variants'] = 1


def main():
    section_tests()
    first_contact_tests()
    compiler_tests()
    congruence_tests()
    result = {'status':'PASS', 'scope':'Independent finite arithmetic adversaries; not a CA compiler or an all-rules verification',
              'counts':dict(counts), 'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
              'executed_upstream_programs':False, 'executed_saved_schedules':False}
    (HERE/'CHECK-RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
