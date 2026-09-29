"""Optional exact symbolic identities, requiring SymPy (not for the core tests)."""
from pathlib import Path
import json
import sympy as sp


def main() -> None:
    s, q, z, r = sp.symbols('s q z r')
    radical_g = (1-s)*(4+8*s+3*s**2-s**2*sp.sqrt((1+s)/2))/(4*(1+2*s)*(1+s)**2)
    expected = [sp.Integer(1), -3,
                sp.Rational(23, 4)-sp.sqrt(2)/8,
                -sp.Rational(43, 4)+9*sp.sqrt(2)/16,
                sp.Rational(81, 4)-99*sp.sqrt(2)/64,
                -sp.Rational(155, 4)+461*sp.sqrt(2)/128]
    series = sp.series(radical_g, s, 0, 6).removeO().expand()
    assert all(sp.simplify(series.coeff(s, k)-expected[k]) == 0 for k in range(6))
    a = q*(1-r)/(2*(3-4*q))
    g = q/(3-4*q)+(q+(1-z)*a)/(4*(1-q)**2)
    cert = 8*(3-4*q)*(1-q)**2*g-q*(15-24*q+8*q*q-z-(1-z)*r)
    assert sp.factor(cert) == 0
    substituted = g.subs({q: (1-s)/2, z: 1-s*s, r: sp.sqrt((1+s)/2)})
    assert sp.simplify(substituted-radical_g) == 0
    pmf_second = sp.simplify(sp.Rational(9, 16)+3*expected[3]/4)
    tail_second = sp.simplify(-sp.Rational(3, 8)+expected[3]/2)
    assert sp.simplify(pmf_second-(-480+27*sp.sqrt(2))/64) == 0
    assert sp.simplify(tail_second-(-184+9*sp.sqrt(2))/32) == 0
    report = {'status': 'PASS', 'sympy_version': sp.__version__,
              'singular_coefficients_checked': 6,
              'radical_and_state_pgf_agree': True,
              'algebraic_certificate_checked': True,
              'second_order_transfer_constants_checked': True,
              'expansion_in_s': str(series)}
    text = json.dumps(report, indent=2)
    print(text)
    (Path(__file__).resolve().parents[1]/'data'/'symbolic_verification.json').write_text(text+'\n')


if __name__ == '__main__':
    main()
