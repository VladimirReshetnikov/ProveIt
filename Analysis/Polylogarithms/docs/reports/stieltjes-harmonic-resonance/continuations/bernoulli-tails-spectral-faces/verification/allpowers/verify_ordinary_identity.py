"""Replay the highlighted quintic identity from independent finite cutoffs.

No recurrence for the new generator and no numerical relation search is used.
The finite-cutoff route is verify_allpowers.M; its only reductions below are
the displayed classical weight <= 6 MZV identities.
"""
from pathlib import Path
import json
import sympy as s
from verify_allpowers import M, Z


def main():
    coefficients = {1: 195, 3: 4056, 5: 11568, 7: 5376}
    raw = s.expand(sum(c * M(5, m) for m, c in coefficients.items()))
    rules = {
        Z((2, 1)): Z((3,)),
        Z((2, 2)): s.Rational(3, 4) * Z((4,)),
        Z((2, 2, 2)): s.Rational(3, 16) * Z((6,)),
        Z((4, 2)): s.Rational(3, 4) * Z((6,)) - Z((2, 4)),
    }
    reduced = s.expand(raw.subs(rules, simultaneous=True))
    target = (-748 * Z((2,)) + 7884 * Z((3,)) - 5380 * Z((4,))
              + 171 * Z((6,)) - 748)
    assert s.expand(reduced - target) == 0
    x = s.Symbol('x')
    h50, h51 = s.S.One, -s.Rational(5, 12)
    counterterm = coefficients[7] * (h50*x**2 + h51) + coefficients[5]*h50
    assert counterterm == 5376*x**2 + 9328
    record = {
        'status': 'PASS',
        'method': 'Finite Faulhaber cutoffs, independent of the new generator',
        'raw_MZV_expression': str(raw),
        'reduction_rules': {str(k): str(v) for k, v in rules.items()},
        'reduced_expression': str(reduced),
        'counterterm': str(counterterm),
        'arithmetic_independence_used': False,
        'numerical_recognition_used': False,
    }
    Path(__file__).with_name('ordinary_identity_exact.json').write_text(
        json.dumps(record, indent=2) + '\n')
    print('PASS: exact quintic ordinary identity and subtraction polynomial')


if __name__ == '__main__':
    main()
