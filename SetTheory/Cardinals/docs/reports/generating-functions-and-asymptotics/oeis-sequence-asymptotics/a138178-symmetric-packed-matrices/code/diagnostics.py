#!/usr/bin/env python3
"""Noncertified decimal diagnostics from exact counts and exact rational moments.

These finite observations do not prove limits, uniformity, error bounds, or an
onset for the article's fixed-order asymptotic theorems.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode=True
import argparse
from math import factorial
import mpmath as mp
from common import emit, integer, new_file_path
from exact_counts import MAX_N, recurrence_counts, involutions, collision_moments


def diagnostics(n=640, digits=60):
    integer(n,32,MAX_N,'n'); integer(digits,30,100,'decimal working precision')
    points=sorted(set([m for m in (32,80,160,320,640) if m<=n]+[n]))
    with mp.workdps(digits):
        def number(value):return mp.mpf(value.numerator)/value.denominator
        def show(value):return mp.nstr(value,20)
        marked=[]
        for u,V,D in ((1,1,1),(2,2,1),(1,1,2)):
            exact=recurrence_counts(n,u,V,D); inv=involutions(n,V,D)
            L=mp.log(1+mp.mpf(1)/u);v=mp.mpf(V)/D;S=(v*v-1)*L/2+L*L/4
            C1=-v*(v*v-1)*L/2+v*(2*v*v-3)*L*L/6
            logC2=v*v*(v*v-1)*(L+L**3)/4+(-5*v**4+6*v*v-3)*L*L/8+L**4/24
            C2=logC2+C1*C1/2
            rows=[]
            for m in points:
                ratio=number(exact[m])*(1+u)*L**(m+1)*D**m/(mp.mpf(inv[m])*mp.exp(S))
                error=ratio-1
                rows.append({'n':m,'leading_ratio':show(ratio),'sqrt_n_leading_error':show(mp.sqrt(m)*error),
                             'n_error_after_C1':show(m*(error-C1/mp.sqrt(m))),
                             'n_three_halves_error_after_C2':show(m**mp.mpf('1.5')*(error-C1/mp.sqrt(m)-C2/m))})
            marked.append({'u':u,'trace_numerator':V,'trace_denominator':D,
                           'C1':show(C1),'C2':show(C2),'rows':rows})
        L=mp.log(2); rows=[]
        for m in points:
            moments={key:number(value) for key,value in collision_moments(m).items()}
            er=moments['E_R'];es=moments['E_S']
            rows.append({'n':m,'E_R':show(er),'E_S':show(es),
                         'Var_R':show(moments['E_R_falling_2']+er-er*er),
                         'Var_S':show(moments['E_S_falling_2']+es-es*es),
                         'Cov_R_S':show(moments['E_RS']-er*es),
                         'sqrt_n_E_R_error':show(mp.sqrt(m)*(er-L)),
                         'sqrt_n_E_S_error':show(mp.sqrt(m)*(es-L*L/2))})
        return {'scope':'NONCERTIFIED floating-point diagnostics from exact rational data; no numerical remainder certificate',
                'n':n,'hard_workload_cap':MAX_N,'working_decimal_digits':digits,'mpmath_version':mp.__version__,
                'marked_count_diagnostics':marked,'collision_moment_diagnostics':rows,
                'collision_mean_limits':{'R':show(L),'S':show(L*L/2)},
                'collision_first_mean_corrections':{'R':show(-L),'S':show(-L*L)}}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--n',type=int,default=640)
    p.add_argument('--digits',type=int,default=60);p.add_argument('--output');a=p.parse_args()
    if a.output is not None:new_file_path(a.output)
    emit(diagnostics(a.n,a.digits),a.output)

if __name__=='__main__':
    try:main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:raise SystemExit(str(exc))
