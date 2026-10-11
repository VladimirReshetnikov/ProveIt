"""Reproduce the unaccelerated quartic N=1 harmonic identity check.

Article equation: dg:quarticN1jet (draft formula D35).

The left side is summed directly with a rational recurrence for w_n and
the elementary update for H_(2n). This file neither imports the Dougall
asymptotic-tail verifier nor uses its centered coefficient expansion.
The reported discrepancies are numerical diagnostics, not rigorous
remainder bounds. The exact identity is proved in the article.

Run from the package root:
    python code/verify_dougall_direct.py

The original calculation used the same recurrence and 50-digit arithmetic.
This packaged script was syntax-checked during final assembly; that
30,000-term calculation was not repeated merely to repackage it.
"""
from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp


CHECKPOINTS = (100, 1000, 10000, 30000)


def direct_harmonic_check(precision_digits: int = 50) -> dict:
    """Sum the original bracketed series without completing its tail."""
    if precision_digits < 40:
        raise ValueError('Use at least 40 decimal digits for cancellation.')

    with mp.workdps(precision_digits):
        half = mp.mpf(1)/2
        quarter = mp.mpf(1)/4
        g = mp.euler + mp.log(2)
        g3 = mp.euler + 3*mp.log(2)
        # This direct derivative at s=-1 is independent of the summation.
        zeta_prime = mp.diff(lambda order: mp.zeta(order, quarter), -1)
        expected = (
            -g3*g3/8 + 7*g3/48 + mp.zeta(2)/16 - mp.mpf(1)/16
            - 23*mp.pi/96 - mp.stieltjes(1, quarter)/4 - 2*zeta_prime
        )

        # w_0 = (1/4) [Gamma(1/2)/Gamma(1)]^4 = pi^2/4.
        weight = mp.pi**2/4
        harmonic = mp.mpf(0)  # H_(2n), initially H_0.
        total = mp.mpf(0)
        records = []
        previous_error = mp.inf

        for n in range(CHECKPOINTS[-1]):
            x = mp.mpf(n) + quarter
            log_x = mp.log(x)
            total += (
                weight*(2*n*(n+half)*(g-harmonic) + half)
                + 2*x*log_x - (log_x/4 + mp.mpf(23)/48)/x
            )

            count = n+1
            if count in CHECKPOINTS:
                signed_error = total-expected
                absolute_error = abs(signed_error)
                # Regression diagnostics only; these are not tail bounds.
                if not absolute_error < previous_error:
                    raise AssertionError('Checkpoint discrepancies did not decrease.')
                previous_error = absolute_error
                row = {
                    'summands': count,
                    'partial_sum': mp.nstr(total, 40),
                    'partial_sum_minus_rhs': mp.nstr(signed_error, 16),
                }
                records.append(row)
                print(json.dumps(row), flush=True)

            harmonic += 1/mp.mpf(2*n+1) + 1/mp.mpf(2*n+2)
            weight *= ((x+1)/x)*((mp.mpf(n)+half)/(n+1))**4

        if previous_error >= mp.mpf('3e-10'):
            raise AssertionError('Final observed discrepancy exceeds the regression tolerance.')

        return {
            'status': 'passed',
            'article_label': 'dg:quarticN1jet',
            'draft_formula': 'D35',
            'precision_digits': precision_digits,
            'method': 'Raw finite harmonic sums with the w_n recurrence; no asymptotic tail.',
            'scope': 'Numerical reproduction and convergence diagnostics, not a certified remainder bound.',
            'right_side': mp.nstr(expected, 45),
            'checkpoint_discrepancies_decrease': True,
            'final_regression_tolerance': '3e-10',
            'cases': records,
        }


def main() -> None:
    result = direct_harmonic_check()
    destination = Path(__file__).resolve().parents[1]/'results'/'dougall_direct_checks.json'
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'output': str(destination)}))


if __name__ == '__main__':
    main()
