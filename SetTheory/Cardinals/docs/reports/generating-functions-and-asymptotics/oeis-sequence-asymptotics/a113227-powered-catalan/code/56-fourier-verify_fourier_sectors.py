"""Reproducible high-precision diagnostics for the fixed Fourier-sector proof.

These are diagnostics, not certified finite-target bounds. Exact Bessel weights
are integrated on a central locally steepest saddle segment; the proof controls the
omitted contour and endpoint pieces asymptotically. No asymptotic weight is used
in the numerical integrand. Requires mpmath only.
"""
import argparse
import json
from pathlib import Path
import mpmath as mp


def weight_ratio(z):
    root = mp.sqrt(z)
    b = root * mp.bessely(z+1, 2*root) - mp.bessely(z, 2*root)
    exact = 1/(mp.pi**2*z*b*b)
    leading = mp.exp(-2)/(2*mp.pi)*z**-2*mp.exp(-z*mp.log(z)+2*z)
    return exact / leading


def c1(w):
    return (20*w**3+86*w**2+128*w+67)/(24*(w+1)**3)


def c2(w):
    return (1168*w**6+9968*w**5+34692*w**4+64536*w**3+69380*w**2+42208*w+11857)/(1152*(w+1)**6)


def c3(w):
    return (756544*w**9+9366816*w**8+50906544*w**7+160729864*w**6+327216240*w**5+448817556*w**4+419091724*w**3+261418266*w**2+102110592*w+20174567)/(414720*(w+1)**9)


def fmt(z):
    return mp.nstr(z, 26)


def sector_ratio(n, j, nodes, weights, T=18):
    n = mp.mpf(n)
    w = mp.lambertw(n/mp.e, -j)
    t = n/w
    A = (w+1)/t
    assert mp.re(A)>0, 'Chosen finite target has no horizontal Gaussian saddle'
    sigma = 1/mp.sqrt(A)
    result = 0
    for x, q in zip(nodes, weights):
        u = T*x*sigma
        z = t+u
        # Cancellation-friendly exact difference, avoiding n*Log(t) subtraction.
        D = n*mp.log1p(u/t) - u*(mp.log(t)-2-2j*mp.pi*j) - (t+u)*mp.log1p(u/t)
        result += q*weight_ratio(z)*(t/z)**2*mp.exp(D)
    result *= T*sigma*mp.sqrt(A/(2*mp.pi))
    # Check branch and stationarity independently.
    stationarity = n/t-mp.log(t)+1+2j*mp.pi*j
    assert abs(stationarity)<mp.mpf('1e-50')
    partial = [mp.mpf(1), 1+c1(w)/t, 1+c1(w)/t+c2(w)/t**2]
    scaled = [(result-partial[L])*t**(L+1) for L in range(3)]
    assert abs(scaled[2]-c3(w))<mp.mpf('.01')
    return {
        'n':str(n), 'j':j, 't':fmt(t), 'w':fmt(w),
        'stationarity_residual':fmt(abs(stationarity)),
        'central_exact_Bessel_integral_over_Mj':fmt(result),
        'scaled_errors_orders_1_2_3':[fmt(v) for v in scaled],
        'expected_c1_c2_c3':[fmt(c1(w)),fmt(c2(w)),fmt(c3(w))],
        'scaled_c3_discrepancy':fmt(abs(scaled[2]-c3(w))),
        'log_envelope_ratio':fmt(mp.re(n*mp.log(t)-n+t)-mp.re(n*mp.log(n/mp.lambertw(n/mp.e))-n+n/mp.lambertw(n/mp.e))
             -mp.mpf('1.5')*mp.log(abs(t)/(n/mp.lambertw(n/mp.e)))
             -mp.mpf('.5')*mp.log(abs(w+1)/(mp.lambertw(n/mp.e)+1))),
    }


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--quick',action='store_true')
    ap.add_argument('--order',type=int,default=None)
    ap.add_argument('--output',default=str(Path(__file__).with_name('fourier_sector_diagnostics.json')))
    args=ap.parse_args()
    mp.mp.dps=70
    order=args.order or (96 if args.quick else 160)
    nodes,weights=mp.gauss_quadrature(order,'legendre')
    cases=[(10000,0),(10000,1)] if args.quick else [(10000,0),(10000,1),(30000,0),(30000,1),(100000,0),(100000,1),(100000000,2)]
    output={'precision_digits':mp.mp.dps,'quadrature_order':order,
            'note':'Diagnostic central exact-Bessel contour integrals, not interval certification',
            'sector_cases':[], 'wedge_cases':[]}
    for n,j in cases:
        item=sector_ratio(n,j,nodes,weights)
        output['sector_cases'].append(item)
        print('sector',n,j,'scaled c3 discrepancy',item['scaled_c3_discrepancy'],flush=True)
    for R in [200,500,1000]:
        for theta in [mp.mpf(0),mp.mpf('.4'),mp.mpf('1.2')]:
            z=R*mp.exp(1j*theta)
            q=weight_ratio(z)
            scaled=(q-1-mp.mpf(5)/(6*z)-mp.mpf(73)/(72*z*z))*z**3
            assert abs(scaled-mp.mpf(11821)/6480)<mp.mpf('.03')
            output['wedge_cases'].append({'R':R,'theta':str(theta),'third_scaled_remainder':fmt(scaled),'expected_alpha3':str(mp.mpf(11821)/6480)})
    Path(args.output).write_text(json.dumps(output,indent=2)+'\n')
    print('Saved',Path(args.output).name,flush=True)

if __name__=='__main__':
    main()
