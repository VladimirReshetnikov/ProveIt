#!/usr/bin/env python3
"""Independent numerical diagnostics for the uniform reflected-moment theorem.

The theorem is proved analytically. These floating-point calculations are
not interval certificates. Quadrature uses t=-log(x), whereas the theorem
uses y=log(Gamma(x)); local jets are composed by finite polynomial arithmetic.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import mpmath as mp


def gamma_data(t):
    """Return f(e^-t), log Gamma(1+e^-t), B(e^-t), x F(x)."""
    x = mp.exp(-t)
    if abs(x) < mp.mpf('0.001'):
        gp = -mp.euler*x
        bm = mp.euler*x
        xf = 1+mp.euler*x
        power = x*x
        j = 2
        while True:
            z = mp.zeta(j)
            term = z*power/j
            gp += (-1)**j*term
            bm += term
            xf += (-1)**(j-1)*z*power
            if abs(z*power) < mp.eps*abs(x)/16:
                break
            power *= x
            j += 1
    else:
        gp = mp.loggamma(1+x)
        bm = mp.loggamma(1-x)
        xf = -x*mp.digamma(x)
    return t+gp, gp, bm, xf


def q_log(t):
    return mp.log(gamma_data(t)[2])


def d_of_t(t):
    _, gp, _, xf = gamma_data(t)
    return mp.exp(gp)/xf


def r_of_t(t):
    y, _, b, xf = gamma_data(t)
    x = mp.exp(-t)
    if abs(x) < mp.mpf('0.001'):
        xfr = mp.euler*x
        power = x*x
        j = 2
        while True:
            term = mp.zeta(j)*power
            xfr += term
            if abs(term) < mp.eps*abs(x)/16:
                break
            power *= x
            j += 1
    else:
        xfr = -x*mp.digamma(1-x)
    return y*xfr/(xf*b)


def saddle_t(n, m):
    def h(t):
        return gamma_data(t)[0]+m*r_of_t(t)-n
    lo = mp.mpf('0.001')
    while h(lo) >= 0:
        lo /= 2
    hi = max(mp.mpf(2), 2*n/(m+1)+2)
    while h(hi) <= 0:
        hi *= 2
    for _ in range(mp.mp.prec+8):
        mid = (lo+hi)/2
        if h(mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo+hi)/2


def multiply(a, b, degree):
    out = [mp.mpf(0)]*(degree+1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            if i+j <= degree:
                out[i+j] += ai*bj
    return out


def compose(a, b, degree):
    out = [mp.mpf(0)]*(degree+1)
    power = [mp.mpf(1)]+[mp.mpf(0)]*degree
    for ai in a[:degree+1]:
        out = [oi+ai*pi for oi, pi in zip(out, power)]
        power = multiply(power, b, degree)
    return out


def local_data(n, m):
    t = saddle_t(n, m)
    y = gamma_data(t)[0]
    cy = mp.taylor(lambda u: gamma_data(u)[0], t, 4)
    c1, c2, c3, c4 = cy[1:]
    inv = [mp.mpf(0), 1/c1, -c2/c1**3,
           (2*c2*c2-c1*c3)/c1**5,
           (-5*c2**3+5*c1*c2*c3-c1*c1*c4)/c1**7]
    lq = compose(mp.taylor(q_log, t, 4), inv, 4)
    dd = compose(mp.taylor(d_of_t, t, 2), inv, 2)
    lq = [lq[j]*mp.factorial(j) for j in range(5)]
    dd = [dd[j]*mp.factorial(j) for j in range(3)]
    phi2 = -n/y**2 + m*lq[2]
    phi3 = 2*n/y**3 + m*lq[3]
    phi4 = -6*n/y**4 + m*lq[4]
    H = -phi2
    assert H > 0
    stationary_residual = n/y + m*lq[1]-1
    assert abs(stationary_residual) < mp.mpf(10)**(-mp.mp.dps+12)
    phi0 = n*mp.log(y)+m*lq[0]-y
    leading_log = phi0+mp.log(dd[0])+mp.log(2*mp.pi/H)/2
    correction = (dd[2]/(2*dd[0]*H)
                  + dd[1]*phi3/(2*dd[0]*H**2)
                  + phi4/(8*H**2)+5*phi3**2/(24*H**3))
    return dict(t=t, s=y, H=H, d=dd[0], phi0=phi0,
                leading_log=leading_log, correction=correction,
                stationary_residual=stationary_residual)


def quadrature(n, m, data):
    t0 = data['t']
    height = data['leading_log']
    def integrand(t):
        if t == 0 or mp.isinf(t):
            return mp.mpf(0)
        f, _, b, _ = gamma_data(t)
        if not f > 0 or (m != 0 and not b > 0):
            return mp.mpf(0)
        exponent = n*mp.log(f)-t-height
        if m != 0:
            exponent += m*mp.log(b)
        return mp.exp(exponent)
    # Width obtained by converting the y Gaussian scale to the t coordinate.
    width = 1/(mp.sqrt(data['H'])*gamma_data(t0)[3])
    pts = [mp.mpf(0)]
    for z in [-20, -8, -3, 0, 3, 8, 20]:
        u = t0+z*width
        if u > 0:
            pts.append(u)
    pts += [max(t0*2, t0+30*width), mp.inf]
    pts = sorted(set(pts))
    return mp.quad(integrand, pts)


def evaluate_case(n, m, label):
    n, m = mp.mpf(n), mp.mpf(m)
    assert n >= m >= 0 and n >= 2
    data = local_data(n, m)
    ratio = quadrature(n, m, data)
    corrected_ratio = ratio/(1+data['correction'])
    row = {'family': label, 'n': mp.nstr(n, 18), 'm': mp.nstr(m, 18),
           'saddle_y': mp.nstr(data['s'], 30),
           'log10_moment': mp.nstr((data['leading_log']+mp.log(ratio))/mp.log(10), 30),
           'exact_over_leading_minus_one': mp.nstr(ratio-1, 25),
           'exact_over_corrected_minus_one': mp.nstr(corrected_ratio-1, 25),
           'n_scaled_leading_error': mp.nstr(n*(ratio-1), 20),
           'n_squared_scaled_corrected_error': mp.nstr(n*n*(corrected_ratio-1), 20),
           'first_correction': mp.nstr(data['correction'], 25),
           'stationary_residual_abs': mp.nstr(abs(data['stationary_residual']), 8)}
    if m == 0:
        factorial_ratio = mp.exp(mp.loggamma(n+1)-data['leading_log'])
        normalized = ratio/factorial_ratio
        row['moment_over_factorial_minus_one'] = mp.nstr(normalized-1, 12)
        # Independent exact inequality: convexity gives
        # -gamma*x <= log Gamma(1+x) < 0. The mean-value theorem then
        # gives 1-gamma*2^-n <= M_(n,0)/Gamma(n+1) < 1 for n>=1.
        # Test the strict sign only when its exponential scale is resolved.
        if n < 2*mp.mp.dps:
            assert 1-mp.euler*mp.power(2,-n) < normalized < 1
    assert abs(ratio-1) < mp.mpf('0.2')
    assert abs(corrected_ratio-1) < mp.mpf('0.05')
    return row


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--dps', type=int, default=60)
    ap.add_argument('--quick', action='store_true')
    ap.add_argument('--output', type=Path, default=Path('all_ratio_diagnostics.json'))
    args = ap.parse_args()
    mp.mp.dps = args.dps
    cases = []
    sizes = [20, 80] if args.quick else [20, 80, 320]
    for n in sizes:
        cases += [(n, n, 'balanced'), (n, mp.mpf(n)/4, 'ratio_four'),
                  (n, mp.sqrt(n), 'square_root'), (n, 1, 'fixed_one'),
                  (n, mp.mpf('0.5'), 'fractional'), (n, 0, 'axis')]
    if not args.quick:
        for m in [40, 160]:
            for u in [-1, 0, 2]:
                n = (m+1)*(mp.log(m)+u)-1
                cases.append((n, m, 'logarithmic_transition'))
    rows = []
    for n, m, label in cases:
        row = evaluate_case(n, m, label)
        rows.append(row)
        print(label, row['n'], row['m'], row['exact_over_corrected_minus_one'], flush=True)
    output = {'status': 'all numerical diagnostic assertions passed',
              'evidence_type': 'floating-point diagnostics; theorem proved analytically',
              'precision_decimal_digits': args.dps, 'case_count': len(rows),
              'independent_quadrature_coordinate': 't=-log(x)', 'rows': rows}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2)+'\n')


if __name__ == '__main__':
    main()
