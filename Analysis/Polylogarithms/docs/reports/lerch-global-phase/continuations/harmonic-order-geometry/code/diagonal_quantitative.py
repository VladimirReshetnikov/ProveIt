#!/usr/bin/env python3
"""A=2 diagonal-velocity certificates and conditional singularity diagnostics.

Exact integer/fraction arithmetic encloses every v_n, n=50..200.  mpmath
evaluates the conjectural singularity parameters and their asymptotic model;
those comparisons and continuation diagnostics are numerical, not rigorous
certificates of analytic continuation or singularity dominance.
"""
from fractions import Fraction
from math import factorial
from pathlib import Path
import json
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]


def ceil_div(a, b):
    return -((-a) // b)


def log2_fixed_interval(digits=400, terms=600):
    scale = 10**digits
    lo = 2 * sum((Fraction(1, (2*j+1) * 3**(2*j+1))
                  for j in range(terms)), Fraction(0))
    tail = Fraction(2, (2*terms+1) * 3**(2*terms+1)) / (1-Fraction(1,9))
    hi = lo + tail
    return (lo.numerator * scale // lo.denominator,
            ceil_div(hi.numerator * scale, hi.denominator)), scale


def stirling_table(nmax):
    c = [[0]*(nmax+1) for _ in range(nmax+1)]
    c[0][0] = 1
    for n in range(1, nmax+1):
        for j in range(1, n+1):
            c[n][j] = c[n-1][j-1] + (n-1)*c[n-1][j]
    return c


def exact_velocity_interval(n, c, log_interval, scale):
    """Horner evaluation of p_n(log 2)/2^n with outward rounding."""
    low = high = 0
    for j in range(n, -1, -1):
        products = [x*y for x in (low, high) for y in log_interval]
        low, high = min(products)//scale, ceil_div(max(products), scale)
        if j:
            num = (-1)**j * c[n][n-j+1] * scale
            den = factorial(j)
            low += num//den
            high += ceil_div(num,den)
    low, high = low//2**n, ceil_div(high,2**n)
    return low, high


def complex_record(z, digits=80):
    return {"real": mp.nstr(mp.re(z),digits), "imag": mp.nstr(mp.im(z),digits)}


def main():
    mp.mp.dps = 280
    nmin, nmax = 50, 200
    Lbox, scale = log2_fixed_interval()
    c_stirling = stirling_table(nmax)
    L = mp.log(2)
    ustar = 1+mp.lambertw(-2/mp.e)
    tstar = mp.exp(ustar)
    radius, theta = abs(tstar), mp.arg(tstar)
    root_coefficient = mp.sqrt(-2*ustar)
    linear_coefficient = ustar/3-1
    cubic_coefficient = root_coefficient*(mp.mpf(1)/2-ustar/18-1/(4*ustar))
    correction = root_coefficient*(-mp.mpf(3)/8+ustar/12+3/(8*ustar))
    assert mp.re(root_coefficient)>0 and mp.im(root_coefficient)<0
    assert abs(root_coefficient**2+2*ustar)<mp.mpf('1e-260')

    # A separate numerical coefficient recurrence; comparisons with exact
    # boxes below are diagnostics of this engine, never proof assumptions.
    vrec = [mp.mpf(0), -L/2]
    for n in range(1,nmax):
        vrec.append(((n+1-n*L)*vrec[n]
                     +mp.mpf(n)/2*mp.fsum(vrec[j]*vrec[n-j] for j in range(1,n)))
                    /(2*(n+1)))

    rows = []
    for n in range(nmin,nmax+1):
        low,high = exact_velocity_interval(n,c_stirling,Lbox,scale)
        assert low*high>0
        assert 2*(high-low)*10**330 < abs(high+low)
        # Convert exact endpoints with more precision than needed for the
        # asymptotic diagnostics. Their integer strings remain the certificate.
        vlo,vhi = mp.mpf(low)/scale,mp.mpf(high)/scale
        velocity = vrec[n]
        box_mid = mp.mpf(low+high)/(2*scale)
        box_width = mp.mpf(high-low)/scale
        # The recurrence is evaluated with 280 digits, so comparison tolerance
        # explicitly allows its numerical rounding, unlike the exact interval.
        relative_agreement = abs(velocity-box_mid)/abs(box_mid)
        assert relative_agreement < mp.mpf('1e-180')
        normalization = mp.sqrt(mp.pi)*radius**n*mp.power(n,mp.mpf('1.5'))
        normalized = velocity*normalization
        phase = mp.exp(-1j*n*theta)
        leading = mp.re(root_coefficient*phase)
        first_corrected = mp.re((root_coefficient+correction/n)*phase)
        err0,err1 = abs(normalized-leading),abs(normalized-first_corrected)
        rows.append({"n":n, "velocity_lower_integer":str(low),
                     "velocity_upper_integer":str(high),
                     "velocity_denominator_exponent":400,
                     "velocity_sign":"+" if low>0 else "-",
                     "velocity_decimal":mp.nstr(velocity,80),
                     "exact_box_relative_width":mp.nstr(box_width/abs(box_mid),12),
                     "independent_recurrence_relative_discrepancy":mp.nstr(relative_agreement,12),
                     "normalized_velocity":mp.nstr(normalized,80),
                     "leading_model":mp.nstr(leading,80),
                     "first_corrected_model":mp.nstr(first_corrected,80),
                     "leading_absolute_normalized_error":mp.nstr(err0,30),
                     "corrected_absolute_normalized_error":mp.nstr(err1,30),
                     "n_times_leading_error":mp.nstr(n*err0,30),
                     "n_squared_times_corrected_error":mp.nstr(n*n*err1,30),
                     "leading_sign_agrees":mp.sign(leading)==mp.sign(velocity)})

    # Continue the analytic germ numerically along t=s*tstar. Warm starts
    # follow the root from u(0)=log2 without using a preselected Puiseux sign.
    u = L
    continuation = []
    samples = [mp.mpf(j)/20 for j in range(1,20)]
    samples += [1-mp.mpf(1)/20/mp.power(2,j) for j in range(1,121)]
    for index,s in enumerate(samples):
        u = mp.findroot(lambda q:mp.exp(q)-2-s*tstar*q,u,
                        solver='newton',df=lambda q:mp.exp(q)-s*tstar,maxsteps=100)
        residual = abs(mp.exp(u)-2-s*tstar*u)
        assert residual<mp.mpf('1e-240')
        if index in (0,9,18,28,38,58,78,98,118,138):
            estimate = (u-ustar)/mp.sqrt(1-s)
            continuation.append({"s":mp.nstr(s,80),"u":complex_record(u),
                                 "square_root_coefficient_estimate":complex_record(estimate),
                                 "difference_from_chosen_c":mp.nstr(abs(estimate-root_coefficient),30),
                                 "equation_residual":mp.nstr(residual,12)})

    max0 = max(rows,key=lambda r:mp.mpf(r['n_times_leading_error']))
    max1 = max(rows,key=lambda r:mp.mpf(r['n_squared_times_corrected_error']))
    closest = min(rows,key=lambda r:abs(mp.mpf(r['leading_model'])))
    max_width = max(mp.mpf(r['exact_box_relative_width']) for r in rows)
    report = {"status":"conditional asymptotic with unproved dominance conjecture",
              "exact_arithmetic":"integer fixed point with outward rounding",
              "log2_series_terms":600,"exact_scale_exponent":400,
              "mpmath_decimal_precision":mp.mp.dps,
              "parameters":{"u_star":complex_record(ustar),"t_star":complex_record(tstar),
                            "radius_candidate":mp.nstr(radius,80),"theta":mp.nstr(theta,80),
                            "square_root_coefficient":complex_record(root_coefficient),
                            "linear_puiseux_coefficient":complex_record(linear_coefficient),
                            "cubic_puiseux_coefficient":complex_record(cubic_coefficient),
                            "first_coefficient_correction":complex_record(correction),
                            "cosine_amplitude":mp.nstr(abs(root_coefficient)/mp.sqrt(mp.pi),80),
                            "cosine_phase_shift":mp.nstr(-mp.arg(root_coefficient),80)},
              "summary":{"n_min":nmin,"n_max":nmax,"sample_count":len(rows),
                         "maximum_n_times_leading_error":{"n":max0['n'],"value":max0['n_times_leading_error']},
                         "maximum_n_squared_times_corrected_error":{"n":max1['n'],"value":max1['n_squared_times_corrected_error']},
                         "maximum_exact_box_relative_width":mp.nstr(max_width,12),
                         "exact_relative_width_bound":"less than 1e-330, checked by integer comparison",
                         "minimum_abs_leading_phase":{"n":closest['n'],"value":str(abs(mp.mpf(closest['leading_model'])))},
                         "leading_sign_disagreements":[r['n'] for r in rows if not r['leading_sign_agrees']]},
              "radial_continuation_diagnostics":continuation,"coefficient_data":rows,
              "limitations":["No proof of sheet accessibility or dominant singularities.",
                              "Singularity parameters and model errors use mpmath, not interval arithmetic.",
                              "Finite coefficient agreement cannot exclude an additional smaller or equal modulus singularity.",
                              "Relative error near cosine zeros is unstable; normalized absolute errors are reported instead."]}
    output_path = ROOT/'data'/'diagonal_quantitative.json'
    output_path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report['summary'],indent=2))
    for n in (50,75,100,125,150,175,200):
        r=next(x for x in rows if x['n']==n)
        print(n,r['velocity_decimal'][:25],r['leading_absolute_normalized_error'][:12],
              r['corrected_absolute_normalized_error'][:12])


if __name__=='__main__':
    main()
