#!/usr/bin/env python3
"""Optional high-precision illustrations of the exact square-case formulas.

Requires mpmath (tested with 1.3.0). These are numerical checks, not interval
certificates. All theorem proofs and verify.py are independent of this script.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--digits', type=int, default=60)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parent / 'data' / 'square_constants.json')
    args = parser.parse_args()
    if args.digits < 30:
        parser.error('--digits must be at least 30')
    try:
        import mpmath as mp
    except ImportError as exc:
        raise SystemExit('This optional script requires mpmath. The main verify.py does not.') from exc
    from verify import square_determinant_stream
    mp.mp.dps = args.digits + 30
    lam = mp.findroot(lambda x: x**3 - 4*x*x + 2*x - 1, (mp.mpf('3.5'), mp.mpf('3.6')))
    beta_real = (4-lam)/2
    beta_imag = mp.sqrt(1/lam-beta_real**2)
    beta = mp.mpc(beta_real, beta_imag)
    derivative = lambda x: 3*x*x-8*x+2
    c_lam = (lam+1)/derivative(lam)
    c_beta = (beta+1)/derivative(beta)
    nu = lam*beta
    K = -c_lam*c_beta*(lam-beta)**2
    K0 = 4*abs(c_beta)**2*beta_imag**2
    theta = mp.arg(beta)
    constants = {
        'lambda': lam, 'rho': 1/lam,
        'beta_real': beta_real, 'beta_imag': beta_imag,
        'nu_real': mp.re(nu), 'nu_imag': mp.im(nu),
        'leading_amplitude_C': c_lam,
        'K_real': mp.re(K), 'K_imag': mp.im(K), 'K0': K0,
        'theta': theta, 'theta_over_pi': theta/mp.pi,
        'phi': mp.arg(K),
        'four_point_margin': -mp.cos(3*theta/2),
        'correction_amplitude': K0/(2*abs(K)),
    }
    max_error = mp.mpf(0)
    for n, exact in square_determinant_stream(100):
        if n < 2:
            continue
        approximation = 2*mp.re(K*nu**(n-1))+K0*(1/lam)**(n-1)
        relative_error = abs(approximation-exact)/max(1, abs(exact))
        max_error = max(max_error, relative_error)
    if max_error >= mp.mpf(10)**(-args.digits):
        raise AssertionError('numerical Binet comparison failed requested tolerance')
    result = {key: mp.nstr(value, args.digits) for key, value in constants.items()}
    result['mpmath_version'] = mp.__version__
    result['checked_indices'] = '2..100'
    result['max_relative_error'] = mp.nstr(max_error, 10)
    result['interpretation'] = 'Approximate numerical output; not an interval certificate.'
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
