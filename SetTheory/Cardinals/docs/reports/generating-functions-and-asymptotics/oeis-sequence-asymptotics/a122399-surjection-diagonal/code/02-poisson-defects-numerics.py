#!/usr/bin/env python3
"""High-precision checks for expansions, Poisson bounds, local laws, and inversion.

Requires mpmath and SymPy. Exact integer Stirling rows supply the input;
noninteger exponent inversions are numerical, not interval certificates.
"""
from __future__ import annotations
import argparse
import csv
import json
import sys
from pathlib import Path
import mpmath as mp
import sympy as sp
from coefficients import generate, inverse_first_two, lam, r
from verify import ordered_stirling_row

if hasattr(sys,'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


def weights(m, n, T):
    fac=mp.factorial(m)
    return [mp.mpf(T[m-d])/fac*mp.exp(n*mp.log1p(-mp.mpf(d)/m)) for d in range(m)]


def sci(x):
    return mp.nstr(x,14)


def write_csv(path, rows):
    with path.open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]))
        w.writeheader(); w.writerows(rows)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--dps',type=int,default=80)
    ap.add_argument('--max-m',type=int,default=1000)
    args=ap.parse_args()
    if args.dps<40:
        raise ValueError('Use at least 40 decimal digits')
    mp.mp.dps=args.dps
    root=Path(__file__).resolve().parents[1]; data=root/'data'
    P,C,L=generate(4)
    cf=[sp.lambdify((lam,r),c,'mpmath') for c in C]
    beta,ell,d0,d1=inverse_first_two(L)
    df0=sp.lambdify((beta,ell),d0,'mpmath'); df1=sp.lambdify((beta,ell),d1,'mpmath')
    sizes=[m for m in [20,50,100,200,500,1000] if m<=args.max_m]
    rows={m:ordered_stirling_row(m) for m in sizes}
    critical=[]; inverse=[]; local=[]
    for m in sizes:
        T=rows[m]
        for c in [-1,0,1]:
            n=int(mp.nint(m*(mp.log(m)+c)))
            rr=mp.mpf(n)/m; ll=m*mp.exp(-rr)/2
            W=weights(m,n,T); R=sum(W); ps=[w/R for w in W]
            theta=W[1]; delta=theta**2-2*W[2]
            pois=mp.exp(-theta); s=pois; tv=abs(ps[0]-pois)
            for d in range(1,m):
                pois*=theta/d; s+=pois; tv+=abs(ps[d]-pois)
            tv=(tv+1-s)/2
            assert tv<=2*delta+mp.mpf('1e-60')
            assert theta-delta/2-mp.mpf('1e-60')<=mp.log(R)<=theta+mp.mpf('1e-60')
            row={'m':m,'n':n,'c_target':c,'lambda':sci(ll),'R':sci(R),
                 'TV_to_Poisson_theta':sci(tv),'TV_bound_2Delta':sci(2*delta)}
            approx=mp.mpf(0)
            for h in range(5):
                approx+=cf[h](ll,rr)/mp.mpf(m)**h
                err=abs(R*mp.exp(-ll)-approx)
                row[f'error_order_{h}']=sci(err)
                row[f'scaled_error_order_{h}']=sci(err*(mp.mpf(m)/(1+rr))**(h+1))
            critical.append(row)
        for q in [mp.exp(-1),mp.mpf('0.5')]:
            b=-mp.log(q); e=mp.log(m/(2*b))
            N0=m*e; N1=N0+df0(b,e); N2=N1+df1(b,e)/m
            def f(t): return mp.log(sum(weights(m,t,T)))-b
            exact=mp.findroot(f,(N2-mp.mpf('.1'),N2+mp.mpf('.1')))
            inverse.append({'m':m,'q':sci(q),'continuous_root':sci(exact),
                            'leading_error':sci(N0-exact),'first_corrected_error':sci(N1-exact),
                            'second_corrected_error':sci(N2-exact),
                            'integer_threshold':int(mp.ceil(exact)),
                            'residual':sci(abs(f(exact)))})
        W=weights(m,m,T); R=sum(W); ps=[w/R for w in W]
        mu=sum(d*p for d,p in enumerate(ps)); V=sum((d-mu)**2*p for d,p in enumerate(ps))
        k3=sum((d-mu)**3*p for d,p in enumerate(ps)); sv=mp.sqrt(V)
        err0=mp.mpf(0); err1=mp.mpf(0)
        for d,p in enumerate(ps):
            xx=(d-mu)/sv; phi=mp.exp(-xx*xx/2)/mp.sqrt(2*mp.pi)
            e0=phi/sv; e1=e0*(1+k3/(6*V**mp.mpf('1.5'))*(xx**3-3*xx))
            err0=max(err0,abs(p-e0)); err1=max(err1,abs(p-e1))
        local.append({'m=n':m,'mean_defect':sci(mu),'variance':sci(V),
                      'max_Gaussian_mass_error':sci(err0),'V_times_error':sci(V*err0),
                      'max_first_Edgeworth_error':sci(err1),'V_3over2_times_error':sci(V**mp.mpf('1.5')*err1)})
    write_csv(data/'critical_window.csv',critical); write_csv(data/'inverse.csv',inverse)
    write_csv(data/'local_limits.csv',local)
    table=['\\begin{tabular}{rrrrrr}','\\toprule',
           '$m$ & $n$ & $R_{m,n}$ & error, $J=0$ & error, $J=2$ & error, $J=4$\\\\', '\\midrule']
    for row in critical:
        if row['c_target']==0:
            def tx(s): return '$'+s.replace('e-','\\times10^{-').replace('e+','\\times10^{')+('}' if 'e' in s else '')+'$'
            table.append(f"{row['m']} & {row['n']} & {float(row['R']):.8f} & "+' & '.join(tx(mp.nstr(mp.mpf(row[f'error_order_{h}']),4)) for h in [0,2,4])+r'\\')
    table+=['\\bottomrule','\\end{tabular}']
    (data/'critical_table.tex').write_text('\n'.join(table)+'\n')
    table=['\\begin{tabular}{rrrrr}','\\toprule',
           '$m$ & $t_q$ & leading error & first correction error & second correction error\\\\','\\midrule']
    for row in inverse:
        if abs(mp.mpf(row['q'])-mp.exp(-1))<mp.mpf('1e-12'):
            table.append(f"{row['m']} & {float(row['continuous_root']):.8f} & {float(row['leading_error']):.5f} & {float(row['first_corrected_error']):.6f} & {float(row['second_corrected_error']):.7f}"+r'\\')
    table+=['\\bottomrule','\\end{tabular}']
    (data/'inverse_table.tex').write_text('\n'.join(table)+'\n')
    (data/'numerical_environment.json').write_text(json.dumps({'dps':args.dps,'mpmath':mp.__version__,
        'sympy':sp.__version__,'python':sys.version,'sizes':sizes,'status':'PASS',
        'warning':'High precision, not rigorous interval arithmetic.'},indent=2)+'\n')
    print('PASS:',len(critical),'critical-window cases,',len(inverse),'inverse cases,',len(local),'local-law cases')
    print('Critical window sample:',critical[-2]); print('Inverse sample:',inverse[-2]); print('Local sample:',local[-1])

if __name__=='__main__': main()
