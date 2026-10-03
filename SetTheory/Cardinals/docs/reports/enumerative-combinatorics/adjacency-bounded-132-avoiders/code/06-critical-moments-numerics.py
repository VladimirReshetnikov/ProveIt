"""Non-certified high-precision quadrature and exact-count-based illustrations.

Analytic identities are proved in article.tex. Decimal agreement is a regression
check, not an interval certificate or a proof of a limiting assertion.
"""
from __future__ import annotations
import csv
import json
from fractions import Fraction
from pathlib import Path
import mpmath as mp

ROOT = Path(__file__).resolve().parent.parent


def pgf(z):
    s = mp.sqrt(1-z)
    r = mp.sqrt((1+s)/2)
    return (1-s)*(4+8*s+3*s*s-s*s*r)/(4*(1+2*s)*(1+s)**2)


def ell(t):
    s = mp.sqrt(-mp.expm1(-t))
    r = mp.sqrt((1+s)/2)
    return s*(12+(25+r)*s+(11-r)*s*s)/(4*(1+2*s)*(1+s)**2)


def ell_remainder(v):
    """Stable (1-G(exp(-v^2)) - 3v) / v^2."""
    if v == 0:
        return (mp.sqrt(mp.mpf('0.5'))-23)/4
    s = mp.sqrt(-mp.expm1(-v*v))
    r = mp.sqrt((1+s)/2)
    # Rationalization and a convergent hypergeometric remainder avoid cancellation:
    # exp(-x)-1+x = x^2 * 1F1(1;3;-x) / 2.
    smv = -v**4*mp.hyp1f1(1, 3, -v*v)/(2*(s+v))
    return (3*smv+s*s*((r-23)-(49+r)*s-24*s*s)/(4*(1+2*s)*(1+s)**2))/(v*v)


def compute_constants(dps: int) -> dict[str, object]:
    with mp.workdps(dps):
        a = 3/mp.sqrt(mp.pi)
        low = mp.quad(lambda v: 2*ell_remainder(v), [0, mp.mpf('.1'), mp.mpf('.5'), 1])
        high = 2-mp.quad(lambda t: pgf(mp.exp(-t))*t**(-mp.mpf('1.5')), [1, 2, 8, 32, mp.inf])
        A = low+high
        h = A/(2*mp.sqrt(mp.pi))+a*(mp.euler+2*mp.log(2))/2
        j = a*(mp.log(2)-mp.log(1+mp.sqrt(2))+mp.sqrt(2)-2)
        # Independent quadrature for the elementary macroscopic correction.
        integrand = lambda u: (-3+4*u)/(mp.sqrt(1-u)*(1-2*u+mp.sqrt(1-u)))
        # Algebraically stable version of ((1-2u)/sqrt(1-u)-1)/u.
        j2 = a*(mp.quad(integrand, [0, mp.mpf('.25'), mp.mpf('.5')])-mp.log(2))/2
        assert abs(j-j2) < mp.power(10, -dps+8)
        return {k: mp.nstr(v, dps-8) for k, v in
                {'a': a, 'A': A, 'h': h, 'j': j, 'c_star': h+j,
                 'B0': h-a, 'B1': a+j, 'j_independent_integral': j2}.items()}


def K(p):
    a = 3/mp.sqrt(mp.pi)
    if p == mp.mpf('.5'):
        raise ValueError('K has a pole at 1/2')
    # Remove the leading singularity before integration; expm1 is stable at 0.
    rem = lambda u: u**(p-mp.mpf('1.5'))*mp.expm1(-mp.mpf('1.5')*mp.log1p(-u))
    return a*(mp.power(2, mp.mpf('.5')-p)/(p-mp.mpf('.5'))
              +mp.quad(rem, [0, mp.mpf('.25'), mp.mpf('.5')]))/2


def microscopic_H(p):
    """H(p) from regularized fractional moments (use 0<p<1)."""
    alpha = mp.mpf('.5')
    a = 3/mp.sqrt(mp.pi)
    # Change t=v^2 in the subtracted integral.
    A_p = mp.quad(lambda v: 2*ell_remainder(v)*v**(1-2*p), [0, mp.mpf('.1'), 1])
    A_p += 1/p-mp.quad(lambda t: pgf(mp.exp(-t))*t**(-p-1), [1, 2, 8, 32, mp.inf])
    c = p/mp.gamma(1-p)
    return c*A_p+(3*c-a*p)/(alpha-p)


def main() -> None:
    out = ROOT/'data'
    out.mkdir(exist_ok=True)
    c40 = compute_constants(40)
    c70 = compute_constants(70)
    with mp.workdps(70):
        for key in c40:
            assert abs(mp.mpf(c40[key])-mp.mpf(c70[key])) < mp.mpf('1e-29')
        # Independent check against the removable limit of regularized moments.
        eps = mp.mpf('1e-6')
        h = mp.mpf(c70['h'])
        Hmid = (microscopic_H(mp.mpf('.5')-eps)+microscopic_H(mp.mpf('.5')+eps))/2
        assert abs(Hmid-h) < mp.mpf('1e-9')
        a = mp.mpf(c70['a'])
        assert abs(K(mp.mpf(1))-a) < mp.mpf('1e-55')
        kvals = {p: mp.nstr(K(mp.mpf(p)), 30) for p in ['0.1','0.25','0.4','0.75','1','1.5']}
        for p in ['0.1','0.25','0.4']:
            assert mp.mpf(kvals[p]) < 0
        # Critical-pole check: finite part of K is B1, not j.
        eps = mp.mpf('1e-7')
        finitepart = (K(mp.mpf('.5')+eps)+K(mp.mpf('.5')-eps))/2
        assert abs(finitepart-mp.mpf(c70['B1'])) < mp.mpf('1e-11')
        g = [Fraction(x) for x in json.loads((out/'pgf_coefficients.json').read_text())]
        tail, truncated = mp.mpf(1), mp.mpf(0)
        for d in range(1, len(g)):
            truncated += (mp.sqrt(d)-mp.sqrt(d-1))*tail
            tail -= mp.mpf(g[d].numerator)/g[d].denominator
        N = len(g)-1
        h_lattice = truncated-a*mp.log(N)/2
        # Only a convergence illustration, no claimed rigorous error certificate.
        result = {'precision_digits': [40, 70], 'constants': c70,
                  'K_values': kvals,
                  'regularized_Mellin_symmetric_H_check': mp.nstr(Hmid, 35),
                  'symmetric_H_difference': mp.nstr(Hmid-h, 12),
                  'K_pole_finite_part_check': mp.nstr(finitepart, 35),
                  'lattice_cutoff': N, 'lattice_h_approximation': mp.nstr(h_lattice, 20),
                  'lattice_h_error_observed': mp.nstr(h_lattice-h, 12),
                  'status': 'PASS: numerical regression only, not certified intervals'}
        (out/'constants.json').write_text(json.dumps(result, indent=2)+'\n')
        hist = json.loads((out/'exact_distributions.json').read_text())
        rows = []
        for n in [8,16,32,64,128,192,256]:
            if str(n) not in hist:
                continue
            counts = hist[str(n)]
            total = sum(counts)
            p25 = mp.mpf('.25')
            probs = [mp.mpf(x)/total for x in counts]
            sqrtmean = sum(mp.sqrt(d)*probs[d] for d in range(1, n+1))
            quarter = sum(mp.power(d, p25)*probs[d] for d in range(1, n+1))
            Dquarter = microscopic_H(p25)+a*p25/(mp.mpf('.5')-p25)
            logmean = sum(mp.sqrt(d)*mp.log(d)*probs[d] for d in range(1, n+1))
            rows.append({'n': n, 'centered_sqrt': mp.nstr(sqrtmean-a*mp.log(n)/2, 16),
                         'centered_sqrt_error': mp.nstr(sqrtmean-a*mp.log(n)/2-mp.mpf(c70['c_star']),16),
                         'scaled_quarter_difference': mp.nstr(mp.power(n,mp.mpf('.25'))*(quarter-Dquarter),16),
                         'critical_biased_mean_log_scale': mp.nstr(logmean/(mp.log(n)*sqrtmean),16)})
        with (out/'finite_moments.csv').open('w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=list(rows[0]))
            writer.writeheader(); writer.writerows(rows)
        print(json.dumps(result, indent=2))
        print('Finite-size illustrations:')
        for row in rows:
            print(row)

if __name__ == '__main__':
    main()
