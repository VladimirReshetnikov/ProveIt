#!/usr/bin/env python3
"""Arbitrary-precision numerical fits, NOT certified rho/C enclosures.

Runs at 100 decimal digits by default. Finite transferred sectors are fitted to
three exact sequence values. Different fits and held-out residuals are numerical
consistency checks, not rigorous error bounds or proofs of the asymptotic theorem.
All output is explicitly requested; bundled inputs are never overwritten.
"""
import argparse
import json
from math import comb
from pathlib import Path
import sys
import mpmath as mp

def need(ok,message):
    if not ok: raise ValueError(message)

def calculate(dps):
    mp.mp.dps=dps
    hi=[1,1,1]
    for n in range(498): hi.append(sum(comb(n,k)*hi[k]*hi[n-k] for k in range(n+1)))
    need(hi[:13]==[1,1,1,1,2,4,8,18,48,144,456,1560,5808],'initial recurrence terms differ')
    h={n:mp.mpf(v) for n,v in enumerate(hi)}
    alpha=(13+1j*mp.sqrt(71))/2; abar=mp.conj(alpha)
    coeff={(1,0):mp.mpf(1),(0,1):mp.mpf(1)}
    for N in range(2,5):
        for k in range(N+1):
            ell=N-k; b=k*alpha+ell*abar
            D=-(b+1)*(b-alpha)*(b-abar)
            conv=sum(coeff.get((p,q),0)*coeff.get((k-p,ell-q),0) for p in range(k+1) for q in range(ell+1))
            coeff[k,ell]=60*conv/D
    def g(n,b): return mp.gamma(n+3-b)/(mp.gamma(3-b)*mp.gamma(n+3))
    def fit(ns,J):
        terms=[(k,ell,c) for (k,ell),c in coeff.items() if k!=ell and k+ell<=J]
        gs={(n,k,ell):g(n,k*alpha+ell*abar) for n in ns for k,ell,c in terms}
        lbase={n:mp.log(h[n])-mp.log(30)-mp.loggamma(n+3) for n in ns}
        lr0=mp.log(mp.mpf('3.77462757572'))
        mat=mp.matrix([[-(n+3),4*mp.re(g(n,alpha)),-4*mp.im(g(n,alpha))] for n in ns])
        rhs=mp.matrix([mp.expm1(lbase[n]+(n+3)*lr0) for n in ns])
        dl,cr,ci=mp.lu_solve(mat,rhs)
        def fun(lr,cr,ci):
            C=mp.mpc(cr,ci)
            def bracket(n):return mp.re(1+2*sum(c*C**k*mp.conj(C)**ell*gs[n,k,ell] for k,ell,c in terms))
            return tuple(lbase[n]+(n+3)*lr-mp.log(bracket(n)) for n in ns)
        lr,cr,ci=mp.findroot(fun,(lr0+dl,cr,ci),tol=mp.mpf(10)**(-(dps-15)),maxsteps=30)
        need(max(abs(v) for v in fun(lr,cr,ci))<mp.mpf(10)**(-(dps-20)),'root solve did not meet numerical residual tolerance')
        return mp.exp(lr),mp.mpc(cr,ci)
    out={'status':'EXPLORATORY_ONLY_NOT_CERTIFIED','decimal_working_precision':dps,
         'not_certified':['rho decimals','C decimals','residual-based error bounds','number of trustworthy digits'],
         'rigorous_bounds_from_analytic_comparison':'180^(1/4) <= rho <= 60^(1/3)',
         'fits':[]}
    for ns in [(100,200,400),(200,350,500),(300,400,500),(400,450,500)]:
        for J in [1,2,3,4]:
            rho,C=fit(ns,J)
            row={'n':list(ns),'J':J,'rho':mp.nstr(rho,75),'C_real':mp.nstr(C.real,65),'C_imag':mp.nstr(C.imag,65)}
            out['fits'].append(row)
            print(f'Exploratory fit n={ns}, J={J}: rho={mp.nstr(rho,25)}',file=sys.stderr,flush=True)
    rho,C=fit((400,450,500),4)
    out['residuals_degree4']=[]
    for n in [100,150,200,250,300,350,375,425,475,500]:
        observed=h[n]/(30*mp.gamma(n+3)*rho**(-n-3))
        terms=[(k,ell,c) for (k,ell),c in coeff.items() if k!=ell and k+ell<=4]
        predicted=mp.re(1+2*sum(c*C**k*mp.conj(C)**ell*g(n,k*alpha+ell*abar) for k,ell,c in terms))
        out['residuals_degree4'].append({'n':n,'used_in_final_fit':n in [400,450,500],
                                        'relative_model_residual':mp.nstr(observed-predicted,35)})
    out['limitations']=['100-digit arithmetic is not interval arithmetic.',
        'No rigorous truncation constants or rho/C enclosures are computed.',
        'Agreement across fits is exploratory; a small fitted residual is not an independent proof.',
        'The finite transferred-sector model must not be summed to infinite sector order at fixed n.']
    return out

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--dps',type=int,default=100)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args(); need(args.dps>=90,'use at least 90 digits for the selected residual checks')
    data=json.dumps(calculate(args.dps),indent=2)+'\n'
    if args.output:args.output.write_text(data)
    else:print(data,end='')
if __name__=='__main__':main()
