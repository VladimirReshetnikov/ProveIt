#!/usr/bin/env python3
"""Optional SymPy C1/C2 algebra check; separate from the mandatory build.

Compare derivative-polynomial and harmonic-number expressions symbolically,
then compare C2 with the Fraction generator on an exact rational grid.
No file writes, removable assertions, or network access. This check verifies
algebra, not the analytic remainder theorem. Output is JSON on stdout.
"""
import argparse
from fractions import Fraction
import json
from math import factorial
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).absolute().parent))
from coefficients import coefficients


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--show-expression', action='store_true',
                        help='also print the expanded C2 numerator and denominator')
    args = parser.parse_args()
    try:
        import sympy as S
    except ImportError:
        print('Optional dependency sympy is not installed', file=sys.stderr)
        return 1
    v, s, d = S.symbols('v s d')
    D = v * v + 3 * v + 1
    alpha, a = (3 - 2 * s) / 4, S.Rational(1, 2) - s
    b1, b2 = a * a / 4 - v / 48, -a / 48
    q, polys = v * v, [v * v]
    for r in range(1, 7):
        q = S.expand(r * q + S.diff(q, v))
        polys.append(q)

    def integrate(expression):
        result = 0
        for (degree,), value in S.Poly(S.expand(expression), d).terms():
            if degree % 2 == 0:
                moment = S.factorial2(degree - 1) if degree else 1
                result += value * (-2 / D) ** (degree // 2) * moment
        return S.factor(result)

    def derive(core):
        a1 = core(3) * d ** 3 - alpha * d
        a2 = core(4) * d ** 4 + alpha * d ** 2 / 2 + b1
        a3 = core(5) * d ** 5 - alpha * d ** 3 / 3 + d * (b1 + S.Rational(1, 48))
        a4 = core(6) * d ** 6 + alpha * d ** 4 / 4 + d ** 2 / 96 + b2
        if integrate(a1) != 0 or integrate(a3 + a1 * a2 + a1 ** 3 / 6) != 0:
            raise RuntimeError('odd coefficient did not vanish')
        return (integrate(a2 + a1 ** 2 / 2),
                integrate(a4 + a1 * a3 + a2 ** 2 / 2 + a1 ** 2 * a2 / 2 + a1 ** 4 / 24))

    derivative = derive(lambda r: (-1) ** r * polys[r] / (4 * factorial(r)))
    harmonic = derive(lambda r: (-1) ** r * (v * v + 2 * S.harmonic(r) * v
                                           + S.harmonic(r) ** 2 - S.harmonic(r, 2)) / 4)
    for left, right in zip(derivative, harmonic):
        if S.cancel(left - right) != 0:
            raise RuntimeError('symbolic constructions disagree')
    E, F = 3 * v * v + 11 * v + 6, 12 * v * v + 50 * v + 35
    stated_c1 = b1 - alpha * (alpha + 1) / D + alpha * E / D ** 2 + F / (4 * D ** 2) - 5 * E ** 2 / (12 * D ** 3)
    if S.cancel(derivative[0] - stated_c1) != 0:
        raise RuntimeError('displayed C1 disagrees')
    comparisons = 0
    for vv in (S.Integer(1), S.Rational(3, 2), S.Integer(2), S.Integer(5), S.Integer(10), S.Integer(100)):
        for ss in (0, 1, 2, 5):
            expected = coefficients(Fraction(int(S.numer(vv)), int(S.denom(vv))), ss, 2)[2]
            actual = derivative[1].subs({v: vv, s: ss})
            if actual != S.Rational(expected.numerator, expected.denominator):
                raise RuntimeError('C2 rational comparison failed')
            comparisons += 1
    numerator, denominator = S.fraction(derivative[1])
    delta = S.cancel(stated_c1.subs(s, 1) - stated_c1.subs(s, 0))
    if S.cancel(delta + (v * v + 5 * v + 4) / (2 * D ** 2)) != 0:
        raise RuntimeError('C1 probability difference disagrees')
    if S.limit(derivative[1] / v ** 2, v, S.oo) != S.Rational(1, 4608):
        raise RuntimeError('C2 leading term disagrees')
    result = {'status': 'PASS', 'optional_dependency': 'sympy', 'dependency_version': S.__version__,
                      'symbolic_C1_C2_constructions_agree': True, 'displayed_C1_agrees': True,
                      'odd_coefficients_vanish': True, 'rational_C2_comparisons': comparisons,
                      'C2_numerator_degree_v': int(S.degree(numerator, v)),
                      'C2_numerator_degree_s': int(S.degree(numerator, s)),
                      'C2_denominator': str(denominator), 'C2_leading_coefficient': '1/4608',
                      'C1_probability_difference_agrees': True,
                      'certifies_analytic_remainder': False}
    if args.show_expression:
        result['C2_numerator'] = str(S.expand(numerator))
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
