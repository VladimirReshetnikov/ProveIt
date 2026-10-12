#!/usr/bin/env python3
"""Independent exact and high-precision checks for three-cluster Gamma faces.

The analytic proofs are in three_cluster_notes.tex. Numerical results are
diagnostics, not certified enclosures. This script depends only on mpmath.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
import json
from math import comb, factorial, log, ceil
from pathlib import Path
import mpmath as mp


def harmonic_star_table(order, limit, exact=False):
    zero=Fraction(0) if exact else mp.mpf(0)
    one=Fraction(1) if exact else mp.mpf(1)
    row=[one]+[zero]*order
    out=[zero]*(limit+1)
    for n in range(1,limit+1):
        out[n]=row[order]
        for j in range(1,order+1):
            row[j]+=row[j-1]/n
    return out


def cumulative_mpl(indices, colors, limit):
    if len(indices)==1:
        return mp.polylog(indices[0], colors[0])
    rows=[mp.mpf(0)]*(len(indices)-1)
    total=mp.mpf(0)
    for n in range(1,limit):
        total+=rows[0]/mp.mpf(n)**indices[0]
        old=rows[:]
        for j in range(len(rows)):
            inner=old[j+1] if j+1<len(rows) else colors[-1]**n
            rows[j]=colors[j]*old[j]+colors[j]*inner/mp.mpf(n)**indices[j+1]
    return total


def mpl_limit(colors):
    radius=max(abs(complex(c)) for c in colors)
    if radius==0:
        return 2
    if radius>=1:
        raise ValueError('This numerical series evaluator requires |color|<1.')
    return max(100,ceil((mp.mp.dps+25)*log(10)/(-log(radius))))


def polylog_primitive(r,z,w):
    limit=mpl_limit((z,w))
    li=lambda ss,cc:cumulative_mpl(ss,cc,limit)
    h=lambda x:-mp.log1p(-x)
    result=(r+1)*(li((1,r+1),(z,z))+li((1,r+1),(w,w)))
    result+=h(w)*li((1,r),(z,z))+h(z)*li((1,r),(w,w))
    for x,y in ((z,w),(w,z)):
        result-=li((1,1,r),(x,y,y))
        result-=li((1,r,1),(x,x,y))
        result-=li((1,r+1),(x,y))
    return (-1)**(r+1)*mp.factorial(r)*result


def ordinary_log_integral(r,q,p):
    # t=1-exp(-v) avoids loss in log(1-t) near t=1.
    def integrand(v):
        t=-mp.expm1(-v)
        ell=-v
        aa=-mp.log1p(-q*t);bb=-mp.log1p(-p*t)
        da=q/(1-q*t);db=p/(1-p*t)
        value=ell**r*(da*(ell+bb)+db*(ell+aa))
        value+=(r+1)*ell**r*(aa+bb)/t
        value+=r*ell**(r-1)*aa*bb/t
        return mp.exp(-v)*value
    return mp.quad(integrand,[0,1,4,12,mp.inf])


def logarithmic_collision_coefficients(r,c,d,limit):
    # Coefficient of epsilon^n at base B=0, sigma=1, C=c*eps, D=d*eps.
    hr=harmonic_star_table(r,limit)
    hs=harmonic_star_table(r+1,limit)
    left=right=mp.mpf(0)
    output=[]
    for n in range(1,limit):
        convolution=(left+right)/n
        coefficient=(-1)**(r+n)*mp.factorial(r)*(
            convolution*hr[n]-(r+1)*(c**n+d**n)/n*hs[n])
        output.append((n,coefficient))
        left=c*left+c*d**n/n
        right=d*right+d*c**n/n
    return output


def collision_value(r,q,p,limit):
    return mp.fsum(v for n,v in logarithmic_collision_coefficients(r,-q,-p,limit))


def divided_difference(f,nodes):
    ordered=tuple(sorted(nodes))
    @lru_cache(None)
    def go(seq):
        if len(seq)==1:
            return f(seq[0])
        if seq[0]==seq[-1]:
            return mp.diff(f,seq[0],len(seq)-1)/mp.factorial(len(seq)-1)
        return (go(seq[1:])-go(seq[:-1]))/(seq[-1]-seq[0])
    return go(ordered)


def mixed_from_monomial_faces(r,nodes,limit):
    # Differentiated source monomial-face formula; independent of Li evaluation.
    m=len(nodes)
    hs=harmonic_star_table(r,limit+m+1)
    complete=[mp.mpf(1)]+[mp.mpf(0)]*limit
    for c in nodes:
        for j in range(1,limit+1):
            complete[j]+=c*complete[j-1]
    return mp.factorial(r)*mp.fsum(
        (-1)**(r+m+j)*hs[m+j]*complete[j] for j in range(limit))


def scaled_residual(x,y):
    return abs(x-y)/max(1,abs(x),abs(y))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--dps',type=int,default=75)
    parser.add_argument('--output',default='three_cluster_checks.json')
    args=parser.parse_args()
    mp.mp.dps=args.dps
    results={'precision_dps':args.dps,'interpretation':'Numerical diagnostics; analytic proofs are separate.'}

    exact_count=0
    for r in range(1,9):
        stars=harmonic_star_table(r,26,exact=True)
        for n in range(1,25):
            direct=sum(((-1)**(j-1)*comb(n,j)*Fraction(1,j**r)
                        for j in range(1,n+1)),Fraction(0))
            assert direct==stars[n+1]
            exact_count+=1
    results['exact_binomial_harmonic_assertions']=exact_count

    cases=[(1,'-.2','-.4'),(2,'-.2','-.4'),(3,'-.2','-.4'),
           (6,'-.2','-.4'),(2,'.2','-.3'),(3,'-.25','-.25'),(4,'0','-.3')]
    scalar=[]
    for r,q0,p0 in cases:
        q=mp.mpf(q0);p=mp.mpf(p0)
        color_z=q/(q-1);color_w=p/(p-1)
        via_mpl=polylog_primitive(r,color_z,color_w)
        via_integral=ordinary_log_integral(r,q,p)
        via_collision=collision_value(r,q,p,300)
        e1=scaled_residual(via_mpl,via_integral)
        e2=scaled_residual(via_mpl,via_collision)
        assert max(e1,e2)<mp.mpf(10)**(-args.dps+12)
        scalar.append({'r':r,'q':q0,'p':p0,'value':mp.nstr(via_mpl,args.dps-8),
                       'mpl_vs_integral_scaled_residual':mp.nstr(e1,8),
                       'mpl_vs_collision_scaled_residual':mp.nstr(e2,8)})
        print('scalar',r,q0,p0,mp.nstr(max(e1,e2),5),flush=True)
    results['scalar_checks']=scalar

    mixed=[]
    for r in (1,2,4,7):
        for m in (1,2,3,5):
            nodes=tuple(mp.mpf(j+1)/40 for j in range(m))
            f=lambda c:mp.polylog(r,c/(1+c))/(1+c)
            actual=(-1)**r*mp.factorial(r)*divided_difference(f,nodes)
            expected=mixed_from_monomial_faces(r,nodes,160)
            error=scaled_residual(actual,expected)
            assert error<mp.mpf(10)**(-args.dps+12)
            mixed.append({'r':r,'nodes':[str(c) for c in nodes],
                          'scaled_residual':mp.nstr(error,8)})
        for nodes in ((mp.mpf('.1'),)*4,(mp.mpf('.1'),mp.mpf('.1'),mp.mpf('.2'),mp.mpf('.2'))):
            f=lambda c:mp.polylog(r,c/(1+c))/(1+c)
            actual=(-1)**r*mp.factorial(r)*divided_difference(f,nodes)
            expected=mixed_from_monomial_faces(r,nodes,160)
            error=scaled_residual(actual,expected)
            assert error<mp.mpf(10)**(-args.dps+12)
            mixed.append({'r':r,'nodes':[str(c) for c in nodes],
                          'scaled_residual':mp.nstr(error,8)})
    results['mixed_derivative_checks']=mixed

    r=2;a=mp.mpf(1);c=mp.mpf('.2');d=mp.mpf('.4');head=18
    coefficients=logarithmic_collision_coefficients(r,c,d,240)
    whole=mp.fsum(v*mp.zeta(2*n,a) for n,v in coefficients if n>=2)
    independent=mp.fsum(polylog_primitive(r,c/((n+a)**2+c),d/((n+a)**2+d))
                         for n in range(head))
    independent+=mp.fsum(v*mp.zeta(2*n,a+head) for n,v in coefficients if n>=2)
    gamma_error=scaled_residual(whole,independent)
    assert gamma_error<mp.mpf(10)**(-args.dps+12)
    results['Gamma_example']={'r':r,'a':str(a),'B':'0','C':str(c),'D':str(d),
                             'value':mp.nstr(whole,args.dps-8),
                             'head_mpl_vs_hurwitz_collision_scaled_residual':mp.nstr(gamma_error,8)}
    results['assertions_total']=exact_count+2*len(scalar)+len(mixed)+1
    Path(args.output).write_text(json.dumps(results,indent=2)+'\n')
    print('PASS',results['assertions_total'],'assertions; output',args.output,flush=True)


if __name__=='__main__':
    main()
