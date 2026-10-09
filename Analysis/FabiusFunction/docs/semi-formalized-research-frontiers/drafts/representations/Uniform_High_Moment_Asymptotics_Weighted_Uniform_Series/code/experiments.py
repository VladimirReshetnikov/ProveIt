#!/usr/bin/env python3
"""Reproduce the article tables with independent positive moment recurrences."""
from __future__ import annotations
import argparse
import csv
import json
import time
from pathlib import Path
import mpmath as mp
from moments import (geometric_stats, geometric_moments, finite_stats,
                     solve_saddle, first_correction, log_saddle_carrier,
                     equal_weight_moment_exact, critical_approximation)

ROOT=Path(__file__).resolve().parents[1]

def text(x):
    return mp.nstr(x,35)

def csvwrite(path, rows):
    with path.open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)

def sci_tex(x, digits=3):
    x=mp.mpf(x)
    if x==0:return '0'
    exponent=int(mp.floor(mp.log10(abs(x))))
    mantissa=x/mp.power(10,exponent)
    return rf'{float(mantissa):.{digits-1}f}\times10^{{{exponent}}}'

def run(quick=True):
    mp.mp.dps=80
    started=time.time()
    rows=[]
    maxn=1024 if quick else 4096
    for qstr in ['0.5','0.8','0.95']:
        q=mp.mpf(qstr)
        moments=geometric_moments(maxn,q)
        for n in [64,256,1024]+([] if quick else [4096]):
            value=moments[n]
            t,st=solve_saddle(n,lambda x:geometric_stats(x,q,6))
            loga=log_saddle_carrier(n,t,st); delta=first_correction(n,st)
            a=mp.exp(loga)
            s0=geometric_stats(n,q,6)
            leading_error=value/mp.exp(s0.log_laplace)-1
            raw_error=value/a-1
            corrected_error=value/(a*(1+delta))-1
            rows.append({'q':qstr,'n':n,'moment':text(value),'saddle':text(t),
                'mu_saddle':text(st.cumulants[1]),'laplace_relative_error':text(leading_error),
                'saddle_relative_error':text(raw_error),'corrected_relative_error':text(corrected_error),
                'n2_saddle_error_over_log_n':text(n*n*raw_error/mp.log(n)),
                'n3_corrected_error':text(n**3*corrected_error),
                'head_terms':st.head_terms,'tail_terms':st.tail_terms})
    csvwrite(ROOT/'data'/'fixed_q.csv',rows)
    tex='\\begin{tabular}{rr rrr}\n\\toprule\n$q$ & $n$ & $M_n/L(n)-1$ & $M_n/A_n-1$ & $M_n/[A_n(1+\\Delta_n)]-1$\\\\\n\\midrule\n'
    for row in rows:
        if row['q']=='0.5' or row['n']==maxn:
            tex+=f"{row['q']} & {row['n']} & ${sci_tex(row['laplace_relative_error'])}$ & ${sci_tex(row['saddle_relative_error'])}$ & ${sci_tex(row['corrected_relative_error'])}$\\\\\n"
    tex+='\\bottomrule\n\\end{tabular}\n'
    (ROOT/'data'/'fixed_q_table.tex').write_text(tex)
    critical=[]
    for cstr in ['0.5','1','2']:
        c=mp.mpf(cstr)
        for n in ([128,512] if quick else [128,512,2048]):
            alpha=1/(2*c)
            q=mp.exp(-alpha*mp.log(n)/mp.sqrt(n))
            value=geometric_moments(n,q)[-1]
            st=geometric_stats(n,q,6)
            ratio=value/mp.exp(st.log_laplace)
            g,g1=critical_approximation(n,st)
            critical.append({'target_c':cstr,'n':n,'q':text(q),'mu_over_sqrt_n':text(st.cumulants[1]/mp.sqrt(n)),
                'exact_ratio':text(ratio),'gaussian_crossover':text(g),'corrected_crossover':text(g1),
                'leading_error':text(ratio/g-1),'corrected_error':text(ratio/g1-1),
                'self_normalized_sqrt_n_error':text(mp.sqrt(n)*(ratio/g-1)),
                'limiting_self_normalized_coefficient':text(c**3/6-c/2)})
    csvwrite(ROOT/'data'/'critical.csv',critical)
    tex='\\begin{tabular}{rr rrrr}\n\\toprule\n$c$ & $n$ & $\\mu/\\sqrt n$ & $M_n/L(n)$ & Gaussian & Corrected\\\\\n\\midrule\n'
    for row in critical:
        tex+=f"{row['target_c']} & {row['n']} & {float(row['mu_over_sqrt_n']):.4f} & {float(row['exact_ratio']):.6f} & {float(row['gaussian_crossover']):.6f} & {float(row['corrected_crossover']):.6f}\\\\\n"
    tex+='\\bottomrule\n\\end{tabular}\n'
    (ROOT/'data'/'critical_table.tex').write_text(tex)
    finite=[]
    for n,m in [(32,1),(128,1),(32,32),(128,128),(256,256),(128,512)]:
        exact=equal_weight_moment_exact(n,m)
        value=mp.mpf(exact.numerator)/exact.denominator
        weights=[mp.mpf(1)/m]*m
        # Equal factors: evaluate one factor, rather than repeat identical differentiation.
        def stfun(t):
            y=t/m
            def cg(z):
                return mp.log(-mp.expm1(-y*(1-z))/(y*(1-z))) - mp.log(-mp.expm1(-y)/y)
            from moments import TiltStats,one_cumulant
            k=[mp.mpf(0)]+[m*(one_cumulant(y,r) if y>=mp.mpf('.5') else mp.diff(cg,0,r)) for r in range(1,7)]
            return TiltStats(m*mp.log(-mp.expm1(-y)/y),k,m,0)
        t,st=solve_saddle(n,stfun)
        a=mp.exp(log_saddle_carrier(n,t,st));d=first_correction(n,st)
        finite.append({'n':n,'number_of_weights':m,'moment':text(value),'mu':text(st.cumulants[1]),
            'uncorrected_relative_error':text(value/a-1),'corrected_relative_error':text(value/(a*(1+d))-1)})
    csvwrite(ROOT/'data'/'finite_arrays.csv',finite)
    (ROOT/'data'/'experiment_summary.json').write_text(json.dumps({
        'precision_decimal_digits':mp.mp.dps,'fixed_q_rows':len(rows),'critical_rows':len(critical),
        'finite_array_rows':len(finite),'elapsed_seconds':round(time.time()-started,3),
        'reference_method':'positive exact-identity recurrences, with arbitrary-precision numerical arithmetic; finite equal arrays use exact rational Stirling numbers',
        'interval_certified':False},indent=2)+'\n')
    print((ROOT/'data'/'experiment_summary.json').read_text())

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--extended',action='store_true', help='include substantially more costly n=4096 recurrence rows')
    run(not parser.parse_args().extended)
