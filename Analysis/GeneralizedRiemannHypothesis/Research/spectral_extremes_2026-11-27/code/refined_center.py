#!/usr/bin/env python3
"""Heat-trace centering diagnostics, reusing existing numerical centers.

This script reads results/asymptotic_diagnostics.json. It neither reruns
the deterministic spectral sums nor generates conditional simulations.
All arithmetic here is ordinary floating point, not interval arithmetic.

For the synthetic spectrum gamma_j=2*pi*j/W(j/e), define
N0(T)=T/(2*pi)*(log(T/(2*pi))-1). Above 2*pi*e, N(T)=floor(N0(T));
below 2*pi*e, N(T)=0 and -1<=N0(T)<=0. Thus |N-N0|<=1 globally.
The proved heat-trace enclosure therefore uses epsilon=exp(-B).
"""
from __future__ import annotations

import csv
import json
import math
from pathlib import Path

from scipy.optimize import brentq

ROOT = Path(__file__).resolve().parents[1]
EULER_GAMMA = 0.577215664901532860606512090082402431
C = 1.0 / (2.0 * math.pi)
A = -math.log(2.0 * math.pi)
K = C * math.sqrt(math.pi) / 2.0
KAPPA = A - EULER_GAMMA / 2.0 - math.log(2.0)


def refined_center(u: float) -> tuple[float, float]:
    """Solve log F_u(B)=0 with scipy.optimize.brentq; return residual."""
    log_u = math.log(u)
    domain_upper = math.exp(2.0 * (log_u + KAPPA))

    def log_main_intensity(b: float) -> float:
        log_v_plus_kappa = log_u - math.log(b) / 2.0 + KAPPA
        return (-b + math.log(K) + log_u - math.log(b) / 2.0
                + math.log(log_v_plus_kappa))

    lower = min(1.0, domain_upper / 4.0) * 1e-12
    upper = min(max(2.0 * log_u + 10.0, 1.0),
                domain_upper * (1.0 - 1e-12))
    if not (log_main_intensity(lower) > 0 > log_main_intensity(upper)):
        raise ValueError(f"Failed to bracket the refined center for u={u}")
    center = brentq(log_main_intensity, lower, upper, xtol=1e-13)
    return center, log_main_intensity(center)


def main() -> None:
    results = ROOT / 'results'
    source = results / 'asymptotic_diagnostics.json'
    saved = json.loads(source.read_text())
    rows = []
    for original in saved['rows']:
        if original['theta'] != 1.0:
            continue
        if 'synthetic' not in original['spectrum']:
            raise ValueError('The global bounded-error proof is spectrum-specific.')
        u = float(original['u'])
        b = float(original['b_numerical'])
        elementary = float(original['b_explicit'])
        refined, residual = refined_center(u)
        epsilon = math.exp(-refined)
        if epsilon >= 1:
            raise ValueError('The finite bracket requires epsilon<1.')
        bracket_lower = refined + math.log1p(-epsilon)
        bracket_upper = refined + math.log1p(epsilon)
        log_u = math.log(u)
        second_order = (log_u + math.log(log_u) / 2.0 + math.log(K)
                        + (KAPPA - 0.75 * math.log(log_u)
                           - math.log(K) / 2.0) / log_u)
        omitted = original['theta1_omitted_intensity_upper_bound']
        rows.append({
            'u': u,
            'theta': 1.0,
            'b_stored_numerical': b,
            'b_elementary': elementary,
            'B_refined_numerical': refined,
            'B_second_order_expansion': second_order,
            'b_minus_elementary': b - elementary,
            'b_minus_refined': b - refined,
            'b_minus_second_order': b - second_order,
            'absolute_error_improvement_factor': abs(b - elementary) / abs(b - refined),
            'epsilon': epsilon,
            'analytic_bracket_lower_numerical': bracket_lower,
            'analytic_bracket_upper_numerical': bracket_upper,
            'stored_b_inside_numerically_evaluated_bracket': bracket_lower <= b <= bracket_upper,
            'refined_log_equation_residual': residual,
            'stored_root_intensity_residual': original['centering_residual'],
            'stored_spectral_coordinates': original['coordinates'],
            'stored_omitted_intensity_upper_bound': omitted,
            'stored_tail_bound_threshold': original['bound_threshold'],
            'implied_omitted_root_displacement_upper_bound_numerical': math.log1p(omitted),
        })
    if not rows:
        raise ValueError('No theta=1 rows were found.')
    if not all(r['stored_b_inside_numerically_evaluated_bracket'] for r in rows):
        raise AssertionError('A stored numerical center lies outside the evaluated bracket.')

    payload = {
        'purpose': 'Compare refined heat-trace centers against previously saved theta=1 centers.',
        'source_results': source.name,
        'spectrum': 'Inverse leading Riemann-von Mangoldt count, synthetic; not computed zeta zeros.',
        'simulations_rerun': False,
        'spectral_sums_rerun': False,
        'arithmetic': 'IEEE-754 binary64 with scipy.optimize.brentq; not interval arithmetic.',
        'constants': {'c': C, 'A': A, 'K': K, 'kappa': KAPPA, 'global_count_error_C0': 1.0},
        'enclosure_formula': 'B+log(1-exp(-B)) <= b <= B+log(1+exp(-B))',
        'count_error_justification': (
            'N(T)=floor(N0(T)) for T>=2*pi*e. For 0<=T<2*pi*e, '
            'N(T)=0 and -1<=N0(T)<=0. Hence |N(T)-N0(T)|<=1 globally.'),
        'limitations': [
            'The analytic enclosure is proved in the manuscript; these floating-point evaluations do not certify its endpoints.',
            'Stored b values solve truncated spectral intensity equations numerically, not with interval-certified arithmetic.',
            'The inherited omitted-intensity bounds were evaluated at lower thresholds, so also bound omission at the stored roots.',
            'The heat-trace error concerns deterministic centering, not a convergence rate for the conditional extreme-value law.',
            'The synthetic spectrum is not a numerical zero list for the zeta function.',
        ],
        'rows': rows,
    }
    (results / 'refined_center_validation.json').write_text(json.dumps(payload, indent=2) + '\n')
    with (results / 'refined_center_validation.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print(f'Compared {len(rows)} existing theta=1 centers; no simulations or spectral sums rerun.')
    for row in rows:
        print(f"u={row['u']:g}: b-B={row['b_minus_refined']:.10g}, "
              f"epsilon={row['epsilon']:.10g}, "
              f"inside={row['stored_b_inside_numerically_evaluated_bracket']}")
    print('Numerical diagnostics only; no interval certification.')


if __name__ == '__main__':
    main()
