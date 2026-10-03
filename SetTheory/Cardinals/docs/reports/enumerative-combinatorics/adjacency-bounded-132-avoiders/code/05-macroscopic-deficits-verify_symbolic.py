"""Exact symbolic checks of identities used in the article.

These check identities, not limits, dominated-convergence hypotheses, or
proof-assistant semantics. Run without Python's -O option.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    x, z = s.symbols('x z', positive=True)
    p = s.symbols('p', real=True)
    checks: list[str] = []

    phi = 3 / s.sqrt(s.pi) * (1 - 2*x) / s.sqrt(x*(1-x))
    density = 3 / (2*s.sqrt(s.pi)) / (x*(1-x))**s.Rational(3, 2)
    assert s.simplify(s.diff(phi, x) + density) == 0
    checks.append('negative derivative of Phi equals the rare-event density')

    primitive = -2 * (1-2*x) / s.sqrt(x*(1-x))
    kernel = 1 / (x*(1-x))**s.Rational(3, 2)
    assert s.simplify(s.diff(primitive, x) - kernel) == 0
    checks.append('Catalan split integral primitive')

    q = z*z / (1+z*z)
    transformed = (x**(p-s.Rational(3,2)) * (1-x)**(-s.Rational(3,2))).subs(x,q)*s.diff(q,z)
    assert s.simplify(s.powsimp(transformed / (2*q**(p-1)), force=True) - 1) == 0
    checks.append('positive-variable substitution x=z^2/(1+z^2)')

    derivative = s.diff(z*q**(p-1), z)
    target = (2*p-1)*q**(p-1) - 2*(p-1)*q**p
    assert s.simplify(s.expand_power_base((derivative-target)/q**(p-1), force=True)) == 0
    checks.append('integration-by-parts identity for the moment recurrence')

    expected = {
        1: s.Integer(1),
        2: 1 - s.pi/4,
        3: s.Rational(5,4) - 3*s.pi/8,
        4: s.Rational(3,2) - 15*s.pi/32,
    }
    for order, value in expected.items():
        actual = s.integrate(q**(order-1), (z,0,1))
        assert s.simplify(actual-value) == 0
        checks.append(f'exact moment integral I({order})')
    assert s.simplify(s.integrate(z/s.sqrt(1+z*z),(z,0,1))-(s.sqrt(2)-1)) == 0
    checks.append('half-integral moment I(3/2)')

    catalan = (1-s.sqrt(1-4*z))/(2*z)
    assert s.simplify(1/(1-z*catalan-z)-catalan**2) == 0
    assert s.simplify(1/(1-z*catalan)-catalan) == 0
    checks.append('both outer-word generating function identities')

    length_pgf = (1/(1-z/2) + 1/(1-3*z/4))/6
    assert length_pgf.subs(z,1) == 1
    assert s.diff(length_pgf,z).subs(z,1) == s.Rational(7,3)
    checks.append('limiting outer-word length normalization and mean')

    report = {
        'status': 'PASS', 'checks': checks, 'number_of_checks': len(checks),
        'sympy_version': s.__version__, 'formal_verification': False,
        'scope': 'Exact symbolic identities only; all analytic limits require the written proofs.'
    }
    (ROOT/'data/symbolic_verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
