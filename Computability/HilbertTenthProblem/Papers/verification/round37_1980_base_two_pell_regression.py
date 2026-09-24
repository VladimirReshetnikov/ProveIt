#!/usr/bin/env python3
"""Focused exact regression for the A=a+2, U=2^(2r+1) Pell change.

These are canonical Pell choices and exact ratios, not complete packed
encoding witnesses.  No relaxed/half-parameter auxiliary is materialized.
The general positive-domain proof is BASE_TWO_PELL_90_PROOF.md.
"""
from __future__ import annotations

import json
from pathlib import Path

OUT = Path(__file__).with_suffix('.json')


def pell_power(A, index):
    """Exact binary powering of A+sqrt(A^2-1), without outside helpers."""
    D = A*A-1

    def times(left, right):
        x, y = left
        z, t = right
        return x*z+D*y*t, x*t+y*z

    result, base = (1, 0), (A, 1)
    while index:
        if index & 1:
            result = times(result, base)
        index >>= 1
        if index:
            base = times(base, base)
    return result


def check_case(r):
    J = 2*r+1
    U = 1 << J
    numerator, denominator = (U+1)**(2*r), U**r
    Y, tail_numerator = divmod(numerator, denominator)
    a = Y*(U+1)
    A, D = a+2, (a+2)**2-1
    E, Q = U*Y, U*Y*Y
    P = 2*Q+1
    d, c = pell_power(A, J)
    first_chi, k = pell_power(P, r+1)
    assert d*d-D*c*c == 1
    assert first_chi*first_chi-(P*P-1)*k*k == 1
    error_numerator = c*denominator-k*numerator
    error_denominator = k*denominator
    assert error_numerator > 0
    assert error_numerator*(U+1) < 16*r*error_denominator
    assert 4*tail_numerator < denominator
    eta, zeta = c-Y*k, k-(c-Y*k)
    assert eta > 0 and zeta > 0
    assert 6*Q > a and 8*r < a
    assert (2*P-1)-4*A == 4*Y*(U*(Y-1)-1)-7 > 0
    assert Y >= U**r and a > U**(r+1)
    assert a > (1 << (3*J)) and a > U**3
    h, h_remainder = divmod(k-r-1, E)
    tau, tau_remainder = divmod(first_chi-1, 2)
    gamma, gamma_remainder = divmod(d-U-a*c, 4*a+3)
    assert h > 0 and tau > 0 and gamma > 0
    assert h_remainder == tau_remainder == gamma_remainder == 0
    assert tau*(tau+1) == (E*E+U)*(Y*k)**2

    L = 8 if r >= 64 else 4 if r >= 8 else 2
    B = 32 if L == 8 else 16 if L == 4 else 8
    q = B**L
    mu, kappa = pell_power(A, L)
    _, fixed_psi = pell_power(2, L)
    Delta, delta_remainder = divmod(kappa-fixed_psi, a)
    phi = c-kappa
    modulus = D-(A-B)**2
    rho, rho_remainder = divmod(mu-q-kappa*(A-B), modulus)
    assert mu*mu-D*kappa*kappa == 1
    assert Delta > 0 and phi > 0 and rho > 0
    assert delta_remainder == rho_remainder == 0
    assert 0 < fixed_psi < a and L < J
    if r >= 64:
        assert U > 32*r
        assert 2*error_numerator < error_denominator
        assert a > B**(3*L) and a > q**3
    return {
        'r': r, 'J': J, 'U_bits': U.bit_length(),
        'A_bits': A.bit_length(), 'c_bits': c.bit_length(), 'k_bits': k.bit_length(),
        'second_base': B, 'second_index': L,
        'ratio_strictly_above_xi': True,
        'ratio_error_below_16r_over_U_plus_1': True,
        'fractional_tail_below_one_quarter': True,
        'positive_interval_gaps': True,
        'exact_first_norm_and_positive_tau_h_gamma': True,
        'exact_second_norm_and_positive_Delta_phi_rho': True,
        'pre_exponent_main_growth': True,
        'large_r_half_error_and_second_growth': r >= 64,
    }


def verify():
    rows = []
    for r in (2, 3, 4, 8, 16, 32, 64, 66):
        rows.append(check_case(r))
    return {
        'status': 'PASS',
        'scope': 'finite exact canonical Pell-coordinate and ratio checks only; not complete packed-system witnesses or a replacement for the general proof',
        'proof': '../1980/BASE_TWO_PELL_90_PROOF.md',
        'arithmetic': 'exact integer powers and cross-multiplied rational comparisons; no floating point',
        'cases': rows,
        'case_count': len(rows),
        'large_r_cases': [row['r'] for row in rows if row['r'] >= 64],
        'auxiliary_witnesses_materialized': False,
    }


if __name__ == '__main__':
    receipt = verify()
    OUT.write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(receipt['status'], receipt['case_count'], 'exact Pell cases', flush=True)
    print('Large-r cases:', receipt['large_r_cases'], flush=True)
