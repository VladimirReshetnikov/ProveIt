"""Reproducible finite checks; no finite test establishes an infinite theorem."""
from __future__ import annotations
import itertools
import json
import math
from pathlib import Path
import platform
import random
from fractions import Fraction as F
from collections import Counter

from equilibria import (
    prefix_data, periodic_normalizer, finite_defect_normalizer,
    transition_row, single_defect_mass, decode_rational_mass,
    threshold_witness, certificate_residuals, compact_witness, compact_residuals, thue_morse,
    ReversibleCounterLift, Instruction, State,
)

ROOT = Path(__file__).resolve().parents[1]
COUNTS: Counter[str] = Counter()

def check(condition: bool, category: str) -> None:
    COUNTS[category] += 1
    if not condition:
        raise AssertionError(f"Check failed in {category}, number {COUNTS[category]}")

def rational(x: F) -> dict[str, str]:
    return {"numerator": str(x.numerator), "denominator": str(x.denominator)}

def words(n: int):
    return itertools.product((0, 1), repeat=n)

def main() -> None:
    (ROOT / 'results').mkdir(exist_ok=True)
    rng = random.Random(20260930)
    for n in range(9):
        for bits in words(n):
            data = prefix_data(bits)
            lo, hi = data.interval
            z0 = periodic_normalizer(bits, (0,))
            z1 = periodic_normalizer(bits, (1,))
            defects = [i for i, b in enumerate(bits) if b]
            check(z0 == finite_defect_normalizer(defects), 'defect identity')
            check(lo == 1 / z0 and hi == 1 / z1, 'sharp endpoints')
            check(hi - lo <= F(2, 3 * (1 << n)), 'prefix width')
            check(F(1, 2) <= lo <= hi <= F(3, 4), 'mass range')
            for nxt in (0, 1):
                l2, h2 = prefix_data(bits + (nxt,)).interval
                check(lo <= l2 <= h2 <= hi, 'nested intervals')
            if n:
                w = F(1)
                for i, b in enumerate(bits):
                    next_w = w * F(2 - b, 4)
                    row = transition_row(i, b)
                    check(sum(row.values()) == 1 and min(row.values()) > 0,
                          'stochastic rows')
                    check(w * row[i + 1] == next_w / 2, 'detailed balance')
                    check(data.W[i + 1] == (4 ** (i + 1)) * next_w,
                          'scaled weight recurrence')
                    w = next_w
            for a, v in ((1, 2), (3, 5), (2, 3), (3, 4), (5, 8)):
                for direction in ('lower', 'upper'):
                    wt = threshold_witness(data, a, v, direction)
                    yes = lo > F(a, v) if direction == 'lower' else hi < F(a, v)
                    check((wt is not None) == yes, 'threshold acceptance')
                    if wt is not None:
                        rs = certificate_residuals(bits, a, v, direction, wt)
                        check(len(rs) == 4 * n + 4 and all(r == 0 for r in rs),
                              'canonical certificate')
                        check(len(wt) == 3 * n + 4, 'witness count')
                        cw = compact_witness(data, a, v, direction)
                        if cw is None:
                            raise AssertionError('compact/full inconsistency')
                        cr = compact_residuals(bits, a, v, direction, cw)
                        check(len(cw) == n+1 and len(cr) == 2*n+1 and not any(cr),
                              'compact certificate')
                        for name in cw:
                            badc = cw.copy()
                            badc[name] += 1
                            check(any(compact_residuals(bits, a, v, direction, badc)),
                                  'compact mutation rejected')
                        # Each individual coordinate is forced: perturb it alone.
                        for name in wt:
                            bad = wt.copy()
                            bad[name] += 1
                            check(any(certificate_residuals(bits, a, v, direction, bad)),
                                  'single-coordinate mutation rejected')
    for pre_n in range(5):
        for per_n in range(1, 5):
            for pre in words(pre_n):
                for per in words(per_n):
                    alpha = 1 / periodic_normalizer(pre, per)
                    decoded = decode_rational_mass(alpha, max_steps=None)
                    check(decoded is not None, 'rational decoder accepts')
                    if decoded is None:
                        raise AssertionError('unreachable')
                    check(1 / periodic_normalizer(*decoded) == alpha,
                          'rational decoder round trip')
    for q in range(1, 50):
        for p in range(q + 1):
            alpha = F(p, q)
            decoded = decode_rational_mass(alpha, max_steps=None)
            if decoded is not None:
                check(1 / periodic_normalizer(*decoded) == alpha,
                      'rational membership sweep')
    for t in range(101):
        a = single_defect_mass(t)
        check(a == 1 / finite_defect_normalizer([t]), 'halting formula')
        check(a - F(1, 2) == F(1, 2 * ((1 << (t + 2)) - 1)),
              'halting separation')
        check(a.denominator == (1 << (t + 2)) - 1, 'reduced denominator')
    check(decode_rational_mass(F(5, 8)) is None, 'gap nonmembership')

    # Countdown, including zero; halt is entered after n+1 transitions.
    countdown = ReversibleCounterLift((Instruction('dec', 0, 0, 1),
                                      Instruction('halt')), 1)
    for n in range(21):
        tr = countdown.forward_trace(State(0, (n,)), n + 7)
        check(countdown.backward(tr[0]) is None, 'root has no predecessor')
        for s, nxt in zip(tr, tr[1:]):
            check(countdown.backward(nxt) == s, 'counter forward backward')
            check(nxt.history > s.history, 'strict history growth')
        ds = [i for i, s in enumerate(tr) if countdown.defect(s)]
        check(ds == [n + 1], 'unique fresh halt')
    loop = ReversibleCounterLift((Instruction('inc', 0, 0),), 1)
    tr = loop.forward_trace(State(0, (0,)), 100)
    check(all(loop.defect(s) == 0 for s in tr), 'nonhalting example')
    for s, nxt in zip(tr, tr[1:]):
        check(loop.backward(nxt) == s, 'loop inverse')

    # Exact Poincare checks on reflecting finite truncations.
    # The theorem is stronger (constant 1/delta < 24), and is proved in text.
    for n in range(2, 18):
        for trial in range(20):
            bs = tuple(rng.randrange(2) for _ in range(n))
            weights = [F(1)]
            for b in bs:
                weights.append(weights[-1] * F(2 - b, 4))
            z = sum(weights)
            pi = [w/z for w in weights]
            f = [rng.randrange(-12, 13) for _ in pi]
            mean = sum(p*x for p, x in zip(pi, f))
            var = sum(p*(x-mean)**2 for p, x in zip(pi, f))
            energy = sum(pi[i+1] * F(1, 2) * (f[i+1]-f[i])**2
                         for i in range(n))
            check(var <= 24 * energy, 'exact finite Poincare')

    # Symbolic quartic generation: all parameters, including bits, remain free.
    import sympy as sp
    N = 3
    B = sp.symbols(f'b0:{N}')
    W = sp.symbols(f'W0:{N+1}')
    S = sp.symbols(f'S0:{N+1}')
    Q = sp.symbols(f'Q0:{N+1}')
    a, v, eta = sp.symbols('a v eta')
    rs = [W[0]-1, S[0]-1, Q[0]-1]
    for i in range(N):
        rs += [B[i]*(B[i]-1), W[i+1]-(2-B[i])*W[i],
               S[i+1]-4*S[i]-W[i+1], Q[i+1]-4*Q[i]]
    rs += [v*Q[N]-a*(S[N]+W[N])-1-eta]
    poly = sp.Poly(sum(r*r for r in rs), *B, a, v, *W, *S, *Q, eta)
    check(poly.total_degree() == 4, 'symbolic quartic degree')
    check(len(rs) == 16, 'symbolic residual count')
    example_bits = (0, 1, 0)
    data = prefix_data(example_bits)
    assignment = threshold_witness(data, 1, 2, 'lower')
    if assignment is None:
        raise AssertionError('chosen example should certify')
    sub = {str(s): s for s in poly.gens}
    val = poly.as_expr().subs({sub[k]: x for k, x in assignment.items()} |
                             {B[i]: b for i, b in enumerate(example_bits)} |
                             {a: 1, v: 2})
    check(val == 0, 'expanded polynomial example')
    (ROOT / 'results/quartic_N3.txt').write_text(str(poly.as_expr())+'\n')
    (ROOT / 'results/quartic_N3.json').write_text(json.dumps({
        'horizon': N, 'direction': 'lower', 'degree': poly.total_degree(),
        'witness_count': len(W)+len(S)+len(Q)+1,
        'residual_count': len(rs), 'monomial_count': len(poly.terms()),
        'variables': [str(s) for s in poly.gens],
        'residuals': [str(r) for r in rs],
        'terms': [{'exponents': list(exps), 'coefficient': int(c)}
                  for exps, c in poly.terms()],
        'example': {'bits': example_bits, 'a': 1, 'v': 2,
                    'assignment': assignment}
    }, indent=2)+'\n')

    # Compact presentation, with W0, S and Q eliminated algebraically.
    compact_W = [sp.Integer(1)] + list(W[1:])
    compact_S = sum(4**(N-i)*compact_W[i] for i in range(N+1))
    crs = []
    for i in range(N):
        crs += [B[i]*(B[i]-1), compact_W[i+1]-(2-B[i])*compact_W[i]]
    crs += [v*4**N-a*(compact_S+compact_W[N])-1-eta]
    cp = sp.Poly(sum(r*r for r in crs), *B, a, v, *W[1:], eta)
    check(cp.total_degree() == 4 and len(crs) == 2*N+1, 'compact symbolic degree count')
    ca = compact_witness(data, 1, 2, 'lower')
    check(cp.as_expr().subs({sp.Symbol(k): x for k,x in ca.items()} |
                           {B[i]: b for i,b in enumerate(example_bits)} |
                           {a:1, v:2}) == 0, 'compact expanded example')
    (ROOT/'results/compact_quartic_N3.txt').write_text(str(cp.as_expr())+'\n')
    (ROOT/'results/compact_quartic_N3.json').write_text(json.dumps({
        'horizon':N, 'degree':cp.total_degree(), 'witness_count':N+1,
        'residual_count':len(crs), 'monomial_count':len(cp.terms()),
        'variables':[str(x) for x in cp.gens], 'residuals':[str(x) for x in crs],
        'example': {'bits':example_bits, 'a':1,'v':2,'assignment':ca}
    },indent=2)+'\n')
    tm = prefix_data(thue_morse(i) for i in range(80))
    lo, hi = tm.interval
    examples = {
        'thue_morse_80': {'lower': rational(lo), 'upper': rational(hi),
                         'width': rational(hi-lo),
                         'display_only': float((lo+hi)/2)},
        'single_defects': [{'T': t, 'mass': rational(single_defect_mass(t))}
                           for t in [0,1,2,5,10,20]],
        'factorial_defects': [{'last_stage': s,
                              'Z': rational(finite_defect_normalizer(
                                  math.factorial(k+2) for k in range(s+1)))}
                             for s in range(5)],
        'countdown_n3': [{'pc': s.pc, 'counters': s.counters,
                         'history': s.history, 'defect': countdown.defect(s)}
                        for s in countdown.forward_trace(State(0,(3,)),7)],
    }
    (ROOT / 'results/examples.json').write_text(json.dumps(examples, indent=2)+'\n')
    report = {'seed': 20260930, 'python': platform.python_version(),
              'sympy': sp.__version__, 'passed': True,
              'total_checks': sum(COUNTS.values()), 'counts': dict(sorted(COUNTS.items())),
              'not_verified_by_testing': [
                  'infinite-state spectral gap and stationary limits',
                  'universal machine semantics', 'arithmetical-hierarchy completeness',
                  'irrationality or transcendence', 'MRDP compiler or Lean theorem'],
              'symbolic_example': {'horizon': N, 'degree': poly.total_degree(),
                                   'monomials': len(poly.terms())},
              'compact_symbolic_example': {'horizon':N, 'degree':cp.total_degree(),
                                          'witnesses':N+1,'residuals':len(crs),
                                          'monomials':len(cp.terms())}}
    (ROOT / 'verification/checks.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
