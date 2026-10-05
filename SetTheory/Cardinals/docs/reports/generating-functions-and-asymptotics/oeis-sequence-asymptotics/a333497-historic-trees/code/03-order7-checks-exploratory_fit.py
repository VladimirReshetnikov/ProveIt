#!/usr/bin/env python3
"""Optional 100-decimal exploratory fits. No interval or digit certification."""
from pathlib import Path
import argparse
import json
import sys
import mpmath as mp
sys.dont_write_bytecode=True
from check import read_terms, CheckFailure, need

ROOT=Path(__file__).resolve().parent

def run():
    mp.mp.dps=100
    h=[mp.mpf(v) for v in read_terms(ROOT/'fixtures/recurrence_terms_0_500.txt')]
    r=(11+1j*mp.sqrt(159))/2; rb=mp.conj(r)
    coeff={(1,0,0):mp.mpf(1),(0,1,0):mp.mpf(1),(0,0,1):mp.mpf(1)}
    for N in range(2,5):
        for k in range(N+1):
            for l in range(N-k+1):
                m=N-k-l; b=12*k+r*l+rb*m
                D=(b+1)*(b-12)*(b-r)*(b-rb)
                conv=sum(coeff.get((p,q,u),0)*coeff.get((k-p,l-q,m-u),0)
                         for p in range(k+1) for q in range(l+1) for u in range(m+1))
                coeff[k,l,m]=840*conv/D
    def g(n,b): return mp.gamma(n+4-b)/(mp.gamma(4-b)*mp.gamma(n+4))
    def fit(ns,J):
        terms=[(k,l,m,c) for (k,l,m),c in coeff.items() if l!=m and k+l+m<=J]
        gs={(n,k,l,m):g(n,12*k+r*l+rb*m) for n in ns for k,l,m,c in terms}
        lbase={n:mp.log(h[n])-mp.log(140)-mp.loggamma(n+4) for n in ns}
        lr0=mp.log(mp.mpf('5.1791758159'))
        mat=mp.matrix([[-(n+4),12*mp.re(g(n,r)),-12*mp.im(g(n,r))] for n in ns])
        rhs=mp.matrix([mp.expm1(lbase[n]+(n+4)*lr0) for n in ns])
        dl,cr,ci=mp.lu_solve(mat,rhs)
        def fun(lr,cr,ci):
            C=mp.mpc(cr,ci); A=-mp.exp(12*lr)/18052070400
            bracket=lambda n:mp.re(1+6*sum(c*A**k*C**l*mp.conj(C)**m*gs[n,k,l,m] for k,l,m,c in terms))
            return tuple(lbase[n]+(n+4)*lr-mp.log(bracket(n)) for n in ns)
        lr,cr,ci=mp.findroot(fun,(lr0+dl,cr,ci),tol=mp.mpf('1e-85'),maxsteps=30)
        return mp.exp(lr),mp.mpc(cr,ci)
    out={'status':'EXPLORATORY_ONLY','working_decimal_digits':100,'mpmath_version':mp.__version__,
         'warning':'These are point fits, not intervals. Neither stable displayed digits nor small residuals certify rho or C. The report proves C != 0 independently.',
         'fits':[]}
    for ns in [(100,200,400),(200,350,500),(300,400,500),(400,450,500)]:
        for J in [1,2,3,4]:
            rho,C=fit(ns,J)
            out['fits'].append({'n':list(ns),'degree':J,'rho':mp.nstr(rho,75),
                               'C_real':mp.nstr(C.real,65),'C_imag':mp.nstr(C.imag,65)})
    chosen=(400,450,500)
    rho,C=fit(chosen,4); A=-rho**12/18052070400
    terms=[(k,l,m,c) for (k,l,m),c in coeff.items() if l!=m and k+l+m<=4]
    rows=[]
    for n in [100,150,200,250,300,350,375,425,475,500]:
        observed=h[n]/(140*mp.gamma(n+4)*rho**(-n-4))
        predicted=mp.re(1+6*sum(c*A**k*C**l*mp.conj(C)**m*g(n,12*k+r*l+rb*m) for k,l,m,c in terms))
        rows.append({'n':n,'used_for_fit':n in chosen,'relative_model_residual':mp.nstr(observed-predicted,35)})
    out['residual_model']={'degree':4,'fitted_indices':list(chosen),'rows':rows}
    return out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,help='optional result destination, outside this sealed checks directory')
    args=parser.parse_args()
    try:
        if args.output:
            dest=args.output.resolve()
            need(not dest.is_relative_to(ROOT), 'OUTPUT_LOCATION', 'write outside the sealed checks directory')
        out=run(); text=json.dumps(out,indent=2)+'\n'
        if args.output: args.output.write_text(text)
        else: print(text,end='')
    except CheckFailure as e:
        print(json.dumps({'status':'FAIL','diagnostic':e.name,'detail':e.detail})); return 1
    except Exception as e:
        print(json.dumps({'status':'ERROR','diagnostic':'EXPLORATORY_EXCEPTION','detail':str(e)})); return 2
    return 0
if __name__=='__main__': sys.exit(main())
