"""Run exact finite checks and write a machine-readable verification report.

Run from any directory: python /path/to/code/verify.py
Tests are NOT formal proofs of the infinite or computability-theoretic claims.
"""
from __future__ import annotations
import itertools
import json
import math
import platform
import time
from fractions import Fraction
from pathlib import Path
import sympy as s
from holonomic import Holonomic, HF, Guarded, X
from ordinals import Ordinal

checks = []
start = time.perf_counter()


def check(name, condition, detail=''):
    success = bool(condition)
    checks.append({'name': name, 'passed': success, 'detail': detail})
    if not success:
        raise AssertionError(name)
    print('PASS', name, flush=True)


def rejects(name, function, exception=ValueError):
    try:
        function()
    except exception:
        check(name, True)
    else:
        check(name, False)


def run():
    zero = Holonomic.constant(0)
    one = Holonomic.constant(1)
    exponential = Holonomic([X, -1], [1])
    expminus = Holonomic([X, 1], [1])
    factorial = Holonomic([X, -(X+1)**2], [1])
    geometric = Holonomic([X, -(X+1)], [1])
    sine = Holonomic([X*(X-1), 0, 1], [0, 1])
    cosine = Holonomic([X*(X-1), 0, 1], [1, 0])

    check('factorial coefficients through index 24',
          all(factorial.coefficient(n) == math.factorial(n) for n in range(25)))
    check('exponential coefficients through index 24',
          all(exponential.coefficient(n) == s.Rational(1, math.factorial(n)) for n in range(25)))
    check('geometric coefficients through index 24',
          all(geometric.coefficient(n) == 1 for n in range(25)))
    check('negative input coefficient index means zero', factorial.coefficient(-1) == 0)
    check('empty jet with no singular indices selects zero', Holonomic([X+1], []).is_zero)
    rejects('missing exceptional index is rejected', lambda: Holonomic([X*(X-3)], [0, 0]))
    rejects('incompatible exceptional jet is rejected', lambda: Holonomic([X*(X-3)], [0, 1, 0, 1]))
    rejects('zero initial Euler polynomial is rejected', lambda: Holonomic([0, X], []))
    rejects('floating-point coefficient is rejected', lambda: Holonomic([X], [1.0]), TypeError)
    delayed = Holonomic([X*(X-17)], [0]*17+[1])
    check('delayed nonzero term is found at exceptional index 17',
          not delayed.is_zero and delayed.valuation == 17)
    check('delayed coefficient continuation is zero', all(delayed.coefficient(n) == 0 for n in range(18,25)))

    identity_product = exponential*expminus
    check('certified exp(t)*exp(-t)=1', identity_product.equal(one),
          'Computed product annihilator and finite jet, not a fixed-prefix comparison')
    check('certified sin(t)^2+cos(t)^2=1', (sine*sine+cosine*cosine).equal(one))
    tseries = Holonomic.monomial(1)
    check('certified geometric inverse identity', ((one-tseries)*geometric).equal(one))
    difference = geometric-exponential
    check('first two exact cancellations, then leading coefficient 1/2',
          difference.valuation == 2 and difference.leading_coefficient == s.Rational(1,2))
    product = factorial*exponential
    check('computed product certificate matches independent convolution through index 18',
          all(product.coefficient(n) == sum(s.Rational(math.factorial(j), math.factorial(n-j))
                                            for j in range(n+1)) for n in range(19)))
    check('sum identity uses distinct input equations', (exponential+expminus).equal(2*cosine) is False,
          'The even exponential sum is not twice the ordinary cosine series')

    tf = HF.monomial(1)
    invt3 = HF.monomial(-3)
    frac = HF.of(one)/(HF.of(one)-tf)
    check('fraction equals geometric series', frac.equal(HF.of(geometric)))
    check('negative Laurent exponents and coefficients',
          invt3.valuation == -3 and invt3.coefficient(-3) == 1 and invt3.coefficient(-2) == 0)
    rational = invt3*frac
    check('shifted geometric fraction has exact Laurent coefficients',
          rational.valuation == -3 and all(rational.coefficient(n) == 1 for n in range(-3,9)))
    shifted_numerator = HF.of(Holonomic.monomial(3))
    shifted_denominator = HF.of(Holonomic.monomial(2))
    check('fraction valuation subtracts numerator and denominator orders',
          (shifted_numerator/shifted_denominator).equal(tf))
    rejects('zero fraction denominator is rejected', lambda: HF(one, zero), ZeroDivisionError)
    rejects('inverse of zero is rejected', lambda: HF.of(0).inverse(), ZeroDivisionError)

    UE = Guarded(0, {1: HF.of(exponential)})
    UEminus = Guarded(0, {1: HF.of(expminus)})
    U2 = Guarded(0, {2: HF.of(1)})
    check('omnific infinite-product identity (U*E)*(U*Eminus)=U^2', (UE*UEminus).equal(U2))
    tail = Guarded(0, {1: HF.of(difference)})
    check('guarded difference leading monomial', tail.leading == ((1,-2),s.Rational(1,2)))
    check('guarded difference is positive', tail.sign == 1)
    dominated = Guarded(0, {1: HF.of(1), 2: -HF.monomial(100)})
    check('higher block dominates regardless of finite offset', dominated.sign == -1)
    check('guarded integer and additive inverse', (UE+(-UE)+7).equal(Guarded(7)))
    rejects('nonintegral guarded constant rejected', lambda: Guarded(s.Rational(1,2)), TypeError)
    rejects('nonpositive guarded power rejected', lambda: Guarded(0, {0: HF.of(1)}))

    # Exhaustive finite models of the mind-change coding. No halting oracle
    # and no claim of testing the infinite completeness theorems.
    finite_encodings = 0
    for d in range(1,6):
        for count in range(d+1):
            for times in itertools.combinations(range(8), count):
                blocks = [(j+1,n,1 if j % 2 == 0 else -1) for j,n in enumerate(times)]
                actual_sign = 0 if not blocks else blocks[-1][2]
                approximation = [False]
                for stage in range(1,10):
                    seen = [b for b in blocks if b[1] < stage]
                    approximation.append(bool(seen and max(seen)[2] > 0))
                changes = sum(a != b for a,b in zip(approximation, approximation[1:]))
                if not (changes <= d and approximation[-1] == (count % 2 == 1)
                        and (actual_sign > 0) == (count % 2 == 1)):
                    raise AssertionError(('mind-change finite instance', d, times))
                finite_encodings += 1
    check('finite dominance encodings: parity, sign, and mind-change bound', True,
          f'{finite_encodings} exhaustive finite event schedules, d=1..5, time positions 0..7')

    # More general signs and delayed discoveries: one arbitrary spike per block.
    priority_tests = 0
    for d in range(1,5):
        for raw in itertools.product((None,(0,1),(0,-1),(2,1),(2,-1)), repeat=d):
            approximations = [False]
            for stage in range(1,5):
                seen = [(k,item) for k,item in enumerate(raw) if item is not None and item[0] < stage]
                approximations.append(bool(seen and seen[-1][1][1] > 0))
            final = [item for item in raw if item is not None]
            expected = bool(final and final[-1][1] > 0)
            changes = sum(a != b for a,b in zip(approximations, approximations[1:]))
            if approximations[-1] != expected or changes > d:
                raise AssertionError(('priority upper-bound instance', raw))
            priority_tests += 1
    check('finite arbitrary-sign priority upper bounds', True,
          f'{priority_tests} finite block assignments, d=1..4')

    zero_o, one_o, two_o = (Ordinal.natural(n) for n in range(3))
    omega = one_o.omega_power()
    omega2 = two_o.omega_power()
    omegaomega = omega.omega_power()
    check('canonical ordinal comparison', zero_o < one_o < two_o < omega < omega2 < omegaomega)
    check('ordinary ordinal addition is not natural addition',
          one_o.ordinal_add(omega) == omega and one_o.natural_add(omega) != omega)
    check('natural addition commutes', one_o.natural_add(omega) == omega.natural_add(one_o))
    op1 = omega.natural_add(one_o)
    expected_square = Ordinal(((two_o,1),(one_o,2),(zero_o,1)))
    check('natural ordinal polynomial square', op1.natural_mul(op1) == expected_square)
    check('ordinary ordinal sum absorbs lower terms', op1.ordinal_add(omega2) == omega2)
    rejects('noncanonical ordinal exponent ordering rejected',
            lambda: Ordinal(((zero_o,1),(one_o,1))))
    rejects('zero ordinal coefficient rejected', lambda: Ordinal(((one_o,0),)))

    # Fixed finite initial segment of midpoint embedding for KB order.
    sequences = [()]
    for length in range(1,5):
        sequences.extend(itertools.product(range(3), repeat=length))
    def kb_less(a,b):
        for x,y in zip(a,b):
            if x != y:
                return x < y
        return len(a) > len(b)
    embedding = {}
    for a in sequences:
        lower = [value for b,value in embedding.items() if kb_less(a,b)]
        upper = [value for b,value in embedding.items() if not kb_less(a,b)]
        lo = max(lower, default=Fraction(1))
        hi = min(upper, default=Fraction(2))
        embedding[a] = (lo+hi)/2
    # Direction audit below independently tests every pair, not only neighbors.
    check('dyadic midpoint embedding respects reverse KB order',
          all((embedding[a] > embedding[b]) == kb_less(a,b)
              for a,b in itertools.permutations(sequences,2)),
          f'{len(sequences)} nodes; {len(sequences)*(len(sequences)-1)} ordered comparisons')
    check('midpoint exponents stay dyadic in (1,2)',
          all(1 < value < 2 and value.denominator & (value.denominator-1) == 0
              for value in embedding.values()))
    return {'factorial_certificate': factorial.summary(),
            'exponential_product_certificate': identity_product.summary(),
            'cancellation_certificate': difference.summary(),
            'finite_change_schedules': finite_encodings,
            'finite_priority_assignments': priority_tests,
            'dyadic_embedding_nodes': len(sequences)}


if __name__ == '__main__':
    detail = {}
    error = None
    try:
        detail = run()
    except Exception as exc:
        error = f'{type(exc).__name__}: {exc}'
    report = {
        'status': 'passed' if error is None else 'failed',
        'date': '2026-09-23',
        'python': platform.python_version(), 'sympy': s.__version__,
        'elapsed_seconds': round(time.perf_counter()-start,3),
        'check_groups': len(checks), 'checks': checks,
        'details': detail, 'error': error,
        'scope': 'Finite exact-arithmetic and finite combinatorial tests; not Lean verification; '
                 'not a proof of the mathematical completeness or infinite-support theorems.'
    }
    output = Path(__file__).resolve().parents[1]/'data'/'verification.json'
    output.write_text(json.dumps(report, indent=2)+'\n')
    if error:
        raise RuntimeError(error)
    print(json.dumps({key: report[key] for key in ('status','check_groups','elapsed_seconds')}, indent=2))
