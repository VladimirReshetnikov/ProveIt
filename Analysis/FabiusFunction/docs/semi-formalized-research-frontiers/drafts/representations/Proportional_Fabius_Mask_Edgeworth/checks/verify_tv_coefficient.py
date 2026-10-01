#!/usr/bin/env python3
"""Exact symbolic verification of the second-order TV coefficient (SymPy)."""
from pathlib import Path
import json
import sympy as sp

# ed. (2026-10-01): results are written to <output-dir>/<name>, by default
# rerun/ beside this program, with LF line endings (as delivered the program
# overwrote its recorded result beside itself, with CRLF on Windows). Pass
# --output-dir with this program's own directory, on a copy, to regenerate
# the recorded file.
def _ed_write(name, text):
    import argparse
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=Path,
                        default=Path(__file__).resolve().parent / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))


def main():
    eta, z, c, vH, vO = sp.symbols('eta z c vH vO', nonzero=True)
    alpha = 1 - eta
    A0 = z**3 / 3 - z
    B0 = z**6 / 18 - sp.Rational(7, 12) * z**4 + z**2 - sp.Rational(1, 12)
    Q2 = (B0 + vO * (z**2 - 1) / 2) / alpha
    W2 = (alpha**3 * z**6 / (18 * eta**3)
          - alpha**2 * z**4 / (4 * eta**2) - sp.Rational(1, 12)
          + vH * (alpha * z**2 / eta - 1) / 2) / eta
    P2 = sp.expand(Q2 + W2 - alpha * z**3 * A0 / (3 * eta**2)
                   + sp.Rational(1, 12) + (vH + vO) / 2)

    def gaussian_mass(polynomial, variance):
        return sp.factor(sum(sp.expand(polynomial).coeff(z, 2*j)
                             * sp.factorial2(2*j-1) * variance**j for j in range(4)))

    def boundary_integral(polynomial, variance):
        # Integral on [-c,c] divided by phi_variance(c), assuming zero total mass.
        return sp.expand(-2 * sum(sp.expand(polynomial).coeff(z, 2*j)
            * sum(sp.factorial2(2*j-1) / sp.factorial2(2*l-1)
                  * variance**(j-l+1) * c**(2*l-1)
                  for l in range(1, j+1)) for j in range(1, 4)))

    assert gaussian_mass(Q2, 1) == 0
    assert gaussian_mass(P2, eta) == 0
    boundary = alpha**2 * c**5 / (9 * eta**3)
    coefficient = boundary_integral(P2, eta) - boundary_integral(Q2, 1) + boundary
    target = c * (vO - alpha * vH / eta
                  + (2*c**4 - c**2 - 3*eta*alpha)/(18*eta**2))
    assert sp.factor(coefficient - target) == 0
    profile = c * (vO - alpha * vH / eta)
    variance_fraction = -c / eta * (alpha*vH - eta*vO)
    assert sp.factor(profile - variance_fraction) == 0
    result = {'status':'passed','arithmetic':'exact symbolic rational functions',
              'q_second_order_mass':'0','p_second_order_mass':'0',
              'full_tv_coefficient_residual':'0','variance_fraction_residual':'0',
              'moving_crossing_coefficient_divided_by_phi_c':str(boundary),
              'scope':'Coefficient algebra only; uniform analytic errors are proved in the manuscript.'}
    # ed. (2026-10-01): written by _ed_write (see above).
    _ed_write('tv_coefficient_symbolic.json', json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True))


if __name__ == '__main__':
    main()
