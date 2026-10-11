#!/usr/bin/env python3
"""Check the scaled Euler--Maclaurin tail against a guarded reference.

The main check needs tiny Hurwitz tails with high relative accuracy.
This diagnostic evaluates the reference at 250 decimal digits to protect
against the absolute error floor in an unguarded fixed-precision call.
Run this file from any working directory; output is written beside it.
No interval enclosure or rigorous numerical error estimate is asserted.
"""
import json
from pathlib import Path
import mpmath as mp
import check_weighted_transform as weighted


def main():
    rows = []
    for p in (mp.mpc('3.7', '.2'), mp.mpc('50.7', '.2'), mp.mpc('52.3', '-.15')):
        value, derivative = weighted.hurwitz_tail_and_derivative(p, weighted.M_TAIL)
        ordinary = mp.zeta(p, weighted.M_TAIL)
        with mp.workdps(250):
            reference = mp.zeta(p, weighted.M_TAIL)
            reference_derivative = mp.zeta(p, weighted.M_TAIL, derivative=1)
            rows.append({
                'p': weighted.repr_complex(p),
                'em_relative_value_residual': mp.nstr(abs((value-reference)/reference), 12),
                'em_relative_derivative_residual': mp.nstr(abs((derivative-reference_derivative)/reference_derivative), 12),
                'unguarded_mpmath_relative_value_residual': mp.nstr(abs((ordinary-reference)/reference), 12),
            })
    report = {
        'description': 'Non-interval diagnostics for the scaled Euler--Maclaurin Hurwitz tail.',
        'working_dps': mp.mp.dps,
        'reference_dps': 250,
        'inner_tail_starts_at': weighted.M_TAIL,
        'euler_maclaurin_terms': weighted.K_EM,
        'checks': rows,
    }
    dest = Path(__file__).with_name('tail_backend_results.json')
    dest.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))
    assert all(mp.mpf(r['em_relative_value_residual']) < mp.mpf('1e-60')
               and mp.mpf(r['em_relative_derivative_residual']) < mp.mpf('1e-60')
               for r in rows)


if __name__ == '__main__':
    main()
