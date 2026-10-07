#!/usr/bin/env python3
"""High-precision diagnostics only: no floating result is used as proof."""
import mpmath as mp
from magma import Q, amplitude, fixed_points, pair_orbits, require, sector, sectors_through_defect, z_type


def F(x):
    return x * (x + 1) * mp.log(x) / 2 - mp.loggamma(x + 1)


def Fprime(x):
    return (x + mp.mpf('0.5')) * mp.log(x) + (x + 1) / 2 - mp.digamma(x + 1)


def as_mpf(q):
    q = Q(q)
    return mp.mpf(q.numerator) / q.denominator


def sector_log_real(x, mu):
    """Log of the positive-base exact real sector extension, x>sum(mu)."""
    s = sum(mu)
    if not x > s:
        raise ValueError('real sector extension requires x > moved support')
    m = x - s
    value = sum(mp.log(x - j) for j in range(s)) - mp.log(z_type(mu))
    value += m * (m + 1) * mp.log(m) / 2
    for k in mu:
        value += m * mp.log(m + fixed_points(mu, k))
    for length, h in pair_orbits(mu).items():
        value += h * mp.log(m + fixed_points(mu, length))
    return value - x * (x + 1) * mp.log(x) / 2


def solve_inverse(seed, precision):
    with mp.workdps(precision):
        u = mp.mpf(seed)
        target = u * u * mp.log(u) / 2
        return mp.findroot(lambda x: F(x) - target, (u, u + 1),
                           tol=mp.mpf(10)**(-precision + 10))


def run():
    inverse_rows, ratios, amplitude_rows = [], [], []
    for seed in (10, 100, 1000, 10000):
        theta100 = solve_inverse(seed, 100)
        theta160 = solve_inverse(seed, 160)
        with mp.workdps(160):
            u = mp.mpf(seed)
            target = u * u * mp.log(u) / 2
            reconstructed_u = mp.sqrt(4 * target / mp.lambertw(4 * target))
            delta = (mp.log(u) / 2 - 1) / (mp.log(u) + mp.mpf('0.5'))
            approx = u + delta
            error = theta160 - approx
            scaled = u * error
            residual = abs(F(theta160) - target) / (1 + abs(target))
            precision_difference = abs(theta160 - theta100) / abs(theta160)
            derivative_difference = abs(Fprime(theta160) - mp.diff(F, theta160)) / abs(Fprime(theta160))
            require(u < theta160 < u + 1, 'Diagnostic inverse root outside test bracket')
            require(abs(reconstructed_u / u - 1) < mp.mpf('1e-145'), 'Diagnostic Lambert identity failed')
            require(residual < mp.mpf('1e-140'), 'Diagnostic inverse residual too large')
            require(precision_difference < mp.mpf('1e-90'), 'Diagnostic roots differ between precisions')
            require(derivative_difference < mp.mpf('1e-140'), 'Diagnostic inverse derivative mismatch')
            require(0 < scaled < 1, 'Diagnostic observed error envelope failed')
            fmt = lambda val: mp.nstr(val, 80)
            inverse_rows.append({'u': seed, 'L': fmt(target), 'theta_0': fmt(theta160),
                                 'u_plus_delta': fmt(approx), 'root_minus_approximation': fmt(error),
                                 'u_times_error': fmt(scaled), 'normalized_equation_residual': fmt(residual),
                                 'relative_root_difference_100_vs_160_dps': fmt(precision_difference),
                                 'Fprime_at_root': fmt(Fprime(theta160))})
    with mp.workdps(100):
        for n in (12, 16, 20, 25, 30, 35, 40, 50, 100):
            ratios.append({'n': n, 'T22_over_T3': mp.nstr(as_mpf(sector(n, (2, 2)) / sector(n, (3,))), 60)})
        for mu in sectors_through_defect(4):
            a = amplitude(mu, 5)
            s, d, beta = a['support'], a['defect'], a['beta']
            for n in (20, 50, 100):
                x = mp.mpf(n)
                exact_log = sector_log_real(x, mu)
                expected_log = mp.log(as_mpf(sector(n, mu)))
                require(abs(exact_log - expected_log) < mp.mpf('1e-90'), 'Real extension and exact integer sector disagree')
                log_leading = as_mpf(a['C']) - mp.log(a['z']) + (-d * x + beta) * mp.log(x) - s * x / 2
                exact_amplitude = mp.exp(exact_log - log_leading)
                truncated = sum(as_mpf(p) / x**j for j, p in enumerate(a['relative_coeff']))
                amplitude_rows.append({'mu': list(mu), 'n': n,
                                       'exact_amplitude_numeric': mp.nstr(exact_amplitude, 60),
                                       'degree_five_truncation': mp.nstr(truncated, 60),
                                       'amplitude_minus_truncation': mp.nstr(exact_amplitude - truncated, 60)})
    return {'status': 'pass', 'dependency': {'mpmath': mp.__version__},
            'working_decimal_precisions': [100, 160],
            'scope': 'Numerical diagnostics only; these values are not exact certificates or global proofs.',
            'limitations': ['The sampled inverse-error envelope is not an all-u bound.',
                           'No sampled minimum is substituted for the analytic derivative infimum m_D.',
                           'No eventual monotonicity cutoff or exact integer inverse is certified.',
                           'Finite Taylor truncations do not resolve later exponential sectors.'],
            'inverse': inverse_rows, 'sector_ordering': ratios, 'amplitude_diagnostics': amplitude_rows}
