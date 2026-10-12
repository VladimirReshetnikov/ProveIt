"""High-precision numerical diagnostics, never interval certificates.

Run from any directory. Values and residuals are written to ../results.
The integral side is computed using EM plus quadrature, not the Mellin formula.
"""
from __future__ import annotations
from pathlib import Path
from math import comb
import argparse, json, time
import mpmath as mp
from balanced import (Kernel,Term,mellin_integral,kappa,master_rhs,elementary,
                      stieltjes_terms)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--dps',type=int,default=55)
    parser.add_argument('--quick',action='store_true',help='Only first point and four integral tests')
    args=parser.parse_args()
    if args.dps<45:
        parser.error('Use at least 45 decimal digits')
    mp.mp.dps=args.dps
    out=Path(__file__).resolve().parents[1]/'results'
    out.mkdir(exist_ok=True)
    cases=[]
    tol=mp.mpf('1e-42')
    def save(name,lhs,rhs,seconds=0):
        err=abs(lhs-rhs); scaled=err/max(mp.mpf(1),abs(rhs))
        case={'name':name,'lhs':mp.nstr(lhs,args.dps),'rhs':mp.nstr(rhs,args.dps),
              'absolute_residual':mp.nstr(err,12),'scaled_residual':mp.nstr(scaled,12),
              'seconds':round(seconds,3),'passed':bool(scaled<tol)}
        cases.append(case)
        print(name, 'PASS' if case['passed'] else 'FAIL', mp.nstr(err,6),flush=True)
        (out/'numeric_checks.json').write_text(json.dumps({'dps':args.dps,'partial':True,'cases':cases},indent=2)+'\n')
    for q,x,a in [(0,'5','.5'),(1,'.7','1'),(2,'2','.5'),(3,'.23','1.7')][:1 if args.quick else 4]:
        x=mp.mpf(x);a=mp.mpf(a);L=mp.log(x)
        direct=L**(q+1)/(q+1)+mp.fsum((-1)**k*comb(q,k)*mp.stieltjes(k,x+a)*L**(q-k) for k in range(q+1))
        save(f'point-definition/q={q}',Kernel(q)(x,a),direct)
    testcases=[]
    def add(name,u,terms,rhs): testcases.append((name,u,terms,rhs))
    for u,q,a in [(mp.mpf('.65'),0,mp.mpf('.7')),(mp.mpf('1.5'),2,mp.mpf('1.3')),
                  (mp.mpf('2.4'),3,mp.mpf('.4')),(mp.mpc('.8','.3'),1,mp.mpf('.5'))]:
        add(f'master/u={u}/q={q}',u,[Term(1,q,a)],master_rhs(u,q,a))
    for m,q,a in [(1,1,'1'),(1,4,'.5'),(2,2,'.7'),(3,3,'1.3'),(2,4,'1')]:
        a=mp.mpf(a)
        add(f'integer/m={m}/q={q}/a={a}',m,[Term(1,q,a)],kappa(m,q)*mp.bernpoly(m,a))
    for m,a in [(1,mp.mpf('.5')),(2,(1+1/mp.sqrt(3))/2),(3,mp.mpf('.5')),
                (3,mp.mpf(1)),(5,mp.mpf('.5'))]:
        add(f'exceptional/m={m}/a={mp.nstr(a,8)}',m,[Term(1,m-1,a)],
            (-1)**(m-1)*mp.diff(lambda s:mp.zeta(s,a),1-m))
    nodes=[mp.mpf('.5')+mp.mpf('.5')*j for j in range(4)]
    weights=[-1,3,-3,1]
    Z=lambda s:mp.fsum(c*mp.zeta(s,a) for a,c in zip(nodes,weights))
    for q in range(4):
        rhs=(-mp.factorial(q)*elementary(2)[q]*mp.diff(Z,-1)) if q<2 else mp.mpf(0)
        add(f'filter/difference-order=3/m=2/q={q}',2,[Term(c,q,a) for a,c in zip(nodes,weights)],rhs)
    # Complete raw mixed Stieltjes moments at m=1 for the second difference.
    nodes1=[mp.mpf('.5'),mp.mpf(1),mp.mpf('1.5')];weights1=[1,-2,1]
    Z1=lambda s:mp.fsum(c*mp.zeta(s,a) for a,c in zip(nodes1,weights1))
    # At m=1: M=K Z(e-h)/(e-h); log K begins with -zeta(2)*h*(e-h).
    add('raw-stieltjes/m=1/n=1/log=0',1,stieltjes_terms(1,nodes1,weights1),-mp.diff(Z1,0,2)/2)
    add('raw-stieltjes/m=1/n=1/log=1',1,stieltjes_terms(1,nodes1,weights1,1),
        mp.diff(Z1,0,3)/3+mp.zeta(2)*mp.diff(Z1,0))
    if args.quick: testcases=testcases[:4]
    for name,u,terms,rhs in testcases:
        start=time.time();lhs=mellin_integral(u,terms)
        save(name,lhs,rhs,time.time()-start)
    if not args.quick:
        # Independent recurrence, beta-sum normalization, and refinement controls.
        for q in range(5):
            x=mp.mpf('.9');a=mp.mpf('1.4');K=Kernel(q)
            save(f'shift-recurrence/q={q}',K(x,a+1)-K(x,a),
                 -mp.log(x/(x+a))**q/(x+a))
        for q in [1,2,3]:
            L=lambda t:(-mp.log(t))**q/(1-t)
            beta=mp.quad(L,[0,.5,1])
            save(f'independent-beta/q={q}',beta,mp.factorial(q)*mp.zeta(q+1))
        for m,q,a in [(2,2,mp.mpf('.7')),(3,2,mp.mpf('.5'))]:
            start=time.time()
            base=mellin_integral(m,[Term(1,q,a)])
            with mp.workdps(args.dps+10):
                refined=mellin_integral(m,[Term(1,q,a)],n=72,r=50,cutoff=80,tail_order=80)
            save(f'parameter-refinement/m={m}/q={q}',base,refined,time.time()-start)
    # Quantify an actual divergent case: the omitted leading tail is nonzero.
    nonzero=-mp.bernpoly(1,mp.mpf(1))
    report={'kind':'arbitrary-precision diagnostics, NOT certified intervals',
            'mpmath_version':mp.__version__,'dps':args.dps,
            'parameters':{'EM_head':56,'EM_terms':40,'tail_cutoff':64,'tail_terms':64},
            'tolerance':str(tol),'count':len(cases),'passed':sum(c['passed'] for c in cases),
            'max_scaled_residual':mp.nstr(max(mp.mpf(c['scaled_residual']) for c in cases),12),
            'divergence_control':{'case':'q=0, m=1, a=1','coefficient_of_x^-1':str(nonzero)},
            'cases':cases}
    (out/'numeric_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f"PASS COUNT {report['passed']} / {report['count']}",flush=True)
    if report['passed']!=report['count']: raise SystemExit(1)

if __name__=='__main__':main()
