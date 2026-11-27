#!/usr/bin/env python3
"""Numerical illustration only: mpmath evaluations are not certified intervals.

Moments are computed from logarithmic Taylor coefficients of the completed zeta
function, not by truncating a zero list. A separate call to zetazero is only a
diagnostic comparison. The general theorem and exact rational example are in
report.pdf and certify.py.
"""
import argparse
import json
from pathlib import Path
import mpmath as mp


def xi(s):
    if s == 0 or s == 1:
        return mp.mpf(1) / 2
    return s * (s - 1) * mp.gamma(s / 2) * mp.power(mp.pi, -s / 2) * mp.zeta(s) / 2


def logarithmic_moments(k, scale, samples, radius):
    """DFT Cauchy extraction for H_scale(w)=2 xi((1+sqrt(1+4 scale w))/2)."""
    values = []
    angles = []
    for j in range(samples):
        theta = 2 * mp.pi * j / samples
        w = radius * mp.exp(1j * theta)
        s = (1 + mp.sqrt(1 + 4 * scale * w)) / 2
        values.append(mp.log(2 * xi(s)))
        angles.append(theta)
    moments = {}
    imaginary_error = mp.mpf(0)
    for order in range(k, k + 3):
        coefficient = mp.fsum(values[j] * mp.exp(-1j * order * angles[j])
                              for j in range(samples)) / (samples * radius**order)
        value = (-1)**(order - 1) * order * coefficient
        imaginary_error = max(imaginary_error, abs(mp.im(value)))
        moments[order] = mp.re(value)
    return moments, imaginary_error


def evaluate(k, moments, a, radius, tau):
    residual = moments[k + 2] - 2 * a * moments[k + 1] + a*a*moments[k]
    estimate = ((k + 1) * moments[k] - k * moments[k + 1] / a) / a**k
    b = a - radius
    inside = (k*k + k) / (2 * b**(k + 2))
    outside = (1/radius**2 + k/(a*radius)) / a**k
    constant = max(inside, outside)
    count_error = constant * residual
    missing_bound = residual / (tau**k * radius**2)
    return dict(residual=residual, count_estimate=estimate,
                count_error_bound=count_error, missing_count_bound=missing_bound,
                count_rounding_margin=mp.mpf('0.5')-abs(estimate-1)-count_error,
                completeness_margin=1-missing_bound)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default=str(Path(__file__).resolve().parents[1] /
                                               'artifacts/zeta_numerical.json'))
    args = parser.parse_args()
    mp.mp.dps = 100
    scale = mp.mpf(200)
    k = 16
    a = mp.mpf('0.99979776674462794831')
    radius = mp.mpf('0.05')
    tau = mp.mpf('0.7')
    contour_radius = mp.mpf(1)/16
    p1 = scale*(1+mp.euler/2-mp.log(4*mp.pi)/2)
    runs = []
    for samples in (96, 128):
        moments, imag = logarithmic_moments(k, scale, samples, contour_radius)
        out = evaluate(k, moments, a, radius, tau)
        # Bound on DFT aliasing in exact arithmetic using p_j <= p_1^j.
        alias = {order: p1**order*(p1*contour_radius)**samples /
                 (1-(p1*contour_radius)**samples) for order in moments}
        runs.append(dict(samples=samples, moments=moments,
                         imaginary_residue=imag, alias_bounds=alias, **out))
    disagreement = max(abs(runs[0]['moments'][j]-runs[1]['moments'][j])
                       for j in runs[0]['moments'])
    gamma1 = mp.im(mp.zetazero(1))
    results = dict(
        status='NUMERICAL ILLUSTRATION ONLY; NOT A CERTIFIED ZETA-ZERO COUNT',
        precision_digits=mp.mp.dps, scale=scale, K=k, center=a,
        interval_radius=radius, inverse_threshold=tau,
        ordinate_interval=[mp.sqrt(scale/(a+radius)-mp.mpf(1)/4),
                           mp.sqrt(scale/(a-radius)-mp.mpf(1)/4)],
        height_cutoff=mp.sqrt(scale/tau-mp.mpf(1)/4),
        known_first_ordinate_diagnostic=gamma1,
        maximum_moment_disagreement=disagreement, runs=runs,
        caveat=('Cauchy alias bounds apply to exact function evaluations. '
                'mpmath special-function and arithmetic errors are not enclosed; '
                'agreement of two grids is a diagnostic, not a rigorous enclosure.'))

    def convert(x):
        if isinstance(x, dict):
            return {str(k): convert(v) for k,v in x.items()}
        if isinstance(x, (list,tuple)):
            return [convert(v) for v in x]
        if isinstance(x, mp.mpf):
            return mp.nstr(x, 60)
        return x
    results = convert(results)
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(results, indent=2)+'\n')
    print(json.dumps({'output':str(output), 'status':results['status'],
                      'last_run':results['runs'][-1],
                      'moment_disagreement':results['maximum_moment_disagreement']}, indent=2))


if __name__ == '__main__':
    main()
