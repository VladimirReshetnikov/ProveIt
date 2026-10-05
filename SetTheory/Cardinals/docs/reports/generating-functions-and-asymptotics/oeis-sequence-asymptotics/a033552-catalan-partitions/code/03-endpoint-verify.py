#!/usr/bin/env python3
"""Reproduce finite checks and numerical tables. Does not certify analytic remainders."""
from __future__ import annotations
import argparse,csv,json,math,platform,time
from pathlib import Path
import mpmath as mp
import sympy as sp
from catalan_statistics import *


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--max-n',type=int,default=1000000)
    parser.add_argument('--dps',type=int,default=60)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data')
    args=parser.parse_args()
    if args.dps < 60:
        parser.error('--dps must be at least 60 for the fixed-precision audit tolerances')
    args.output.mkdir(parents=True,exist_ok=True);mp.mp.dps=args.dps
    start=time.time(); checks=[]
    def passed(s): checks.append(s);print('PASS '+s,flush=True)
    ns=[n for n in [100,1000,10000,100000,1000000] if n<=args.max_n]
    if not ns: raise SystemExit('--max-n must be at least 100')
    p,u,v,prefix=exact_statistics(args.max_n,ns)
    initial=[1,1,2,2,3,4,5,6,7,8,10,11,13,14,17,19,22,24,27,30]
    assert p[:20]==initial
    passed('20 initial A033552 terms match the inspected OEIS entry')
    lim=min(300,args.max_n);b=[0]*(lim+1);alt=[0]*(lim+1);alt[0]=1
    for c in parts_to(lim):
        for j in range(c,lim+1,c): b[j]+=c
    for n in range(1,lim+1):
        total=sum(b[j]*alt[n-j] for j in range(1,n+1));assert total%n==0;alt[n]=total//n
    assert alt==p[:lim+1]
    passed(f'{lim+1} exact counts agree with an independent logarithmic-derivative recurrence')
    # Independent recursive enumeration of all partitions through n=60.
    def brute(n,cs):
        if not cs: return (int(n==0),0,0)
        c=cs[-1];ans=[0,0,0]
        for z in range(n//c+1):
            a,b1,b2=brute(n-z*c,cs[:-1])
            ans[0]+=a;ans[1]+=b1+z*a;ans[2]+=b2+2*z*b1+z*z*a
        return tuple(ans)
    for n in range(61): assert brute(n,parts_to(n))==(p[n],u[n],v[n])
    passed('61 exhaustive enumeration checks for count, length sum, and squared-length sum')
    # Formal operator benchmark: pure gamma saddle.
    x=sp.Symbol('x');m=sp.Symbol('m',positive=True)
    def op_sym(r,J):
        acc=0
        for l,ks,num,den in operator_terms(J):
            if r==0 and l>0:continue
            a=sp.Integer(1) if l==0 else (-1)**l*sp.rf(r,l)
            R=sum((i+3)*k for i,k in enumerate(ks))
            term=sp.Rational(num,den)*a/m**((l+R)//2)
            for i,k in enumerate(ks):term*=(sp.factorial(i+2)*m)**k
            acc+=term
        return sp.expand(acc)
    for J in [1,2,3]:
        for r in range(1,6):
            approx=op_sym(r,J)/op_sym(0,J)
            exact=sp.prod(1+j*x for j in range(r))**-1
            assert sp.series(approx.subs(m,1/x)-exact,x,0,J+1).removeO().expand()==0
    passed('15 exact symbolic gamma-ratio checks, orders 1--3 and moments 1--5')
    # Universal first moment of the limiting law.
    cs=catalans(2*mp.mp.dps+30)
    S=[None]+[mp.fsum(mp.mpf(c)**(-r) for c in cs) for r in range(1,7)]
    mu1=1+4*mp.pi/(9*mp.sqrt(3));assert abs(mu1-S[1])<mp.mpf('1e-50')
    mu2=S[1]**2+S[2]
    passed('reciprocal-Catalan mean agrees with 1+4*pi/(9*sqrt(3))')
    # Spectral decomposition and flatness.
    rcs,ds=residues(50)
    for s in [mp.mpf('-.5'),0,mp.mpf('.5'),1,2,10]:
        L,_=limit_laplace(s,0)
        assert abs(mp.fsum(d*c/(s+c) for c,d in zip(rcs,ds))-L)<mp.mpf('1e-45')
    assert abs(mp.fsum(ds)-1)<mp.mpf('1e-45')
    for r in range(1,7):assert abs(mp.fsum(d*mp.mpf(c)**r for c,d in zip(rcs,ds)))<mp.mpf('1e-40')
    passed('13 high-precision spectral-transform and boundary-flatness checks')
    # Exact finite version, using rational rather than floating residues.
    s=sp.Symbol('s');cs8=catalans(8)
    lhs=sp.prod(sp.Rational(c,1)/(s+c) for c in cs8)
    rhs=sum(sp.prod(sp.Rational(d,d-c) for d in cs8 if d!=c)*c/(s+c) for c in cs8)
    assert sp.cancel(lhs-rhs)==0
    passed('exact rational partial fractions for the first 8 Catalan rates')
    # Lagrange formula coefficients.
    z,a,b=sp.symbols('z a b');U=1+a*z+b*z**4
    got=[-sp.expand(sp.series(U**(-r),z,0,r+1).removeO()).coeff(z,r)/r for r in range(1,5)]
    assert got==[a,-3*a*a/2,10*a**3/3,b-35*a**4/4]
    passed('4 exact inverse-tail coefficients from Lagrange inversion')
    means=[];laps=[];exts=[];joints=[];moments=[]
    for n in ns:
        t,m,B=saddle(n,8);M=int(mp.floor(m));theta=m-M
        exact1=t*mp.mpf(u[n])/p[n]; exact2=t*t*mp.mpf(v[n])/p[n]
        estmean=mu1*(1+(B[3]-2*B[2])/(2*B[2]**2))
        means.append(dict(n=n,t=str(t),m=str(m),scaled_mean=str(exact1),limit=str(mu1),
                          mean_correction=str(estmean),limit_error=str(mu1-exact1),
                          corrected_error=str(estmean-exact1)))
        for r,exact,mu in [(1,exact1,mu1),(2,exact2,mu2)]:
            row=dict(n=n,r=r,exact=str(exact),limit=str(mu))
            for J in [1,2,3]:row[f'order{J}_error']=str(conditional_moment(B,r,mu,J)-exact)
            moments.append(row)
        s=mp.mpf(1);L,aa=limit_laplace(s,6)
        fl=weighted_count(n,float(mp.exp(-s*t)))/float(p[n])
        Lprime=-L*mp.fsum(1/(mp.mpf(c)+s) for c in cs)
        Lsecond=L*((mp.fsum(1/(mp.mpf(c)+s) for c in cs))**2+mp.fsum(1/(mp.mpf(c)+s)**2 for c in cs))
        row=dict(n=n,s=1,weighted_DP=str(fl),limit=str(L),
                 universal_first=str(L-s*s*Lsecond/(2*m)))
        for J in [1,2,3]:row[f'order{J}_error']=str(conditional_laplace(B,s,J)-fl)
        laps.append(row)
        for h in [-1,0,1]:
            K=M+h
            pp,uu,vv=prefix[n][K]
            exact=mp.mpf(pp)/p[n]
            G,S1,S2,U,C=phase_extreme(theta,h)
            tail,aext=exact_tail_amplitude(t,K,6)
            one=[mp.mpf(1)]+[mp.mpf(0)]*6
            erow=dict(n=n,h=h,theta=str(theta),exact=str(exact),limit=str(G),
                      periodic_first=str(G*(1+C/m)))
            for J in [1,2,3]:
                est=saddle_operator(B,aext,J)/saddle_operator(B,one,J)
                erow[f'exact_saddle_order{J}_error']=str(est-exact)
            exts.append(erow)
            # Event covariance (exact integer sums, normalized numerically).
            cov=t*mp.mpf(uu)/p[n]-exact1*exact
            pred=mu1*G*S1/m
            joints.append(dict(n=n,h=h,exact_covariance=str(cov),first_covariance=str(pred),
                               ratio=str(cov/pred) if pred else 'nan'))
        print('TABLES n='+str(n),flush=True)
    qs=[]
    for es in ['0.1','0.01','0.001','0.000001']:
        eps=mp.mpf(es);x0=mp.log(ds[0]/eps)
        root=mp.findroot(lambda x:survival(x,rcs,ds)-eps,(x0-.2,x0+.2))
        preds=quantile_series(eps,ds)
        qs.append(dict(epsilon=es,quantile=str(root),**{f'order{j}_error':str(q-root) for j,q in enumerate(preds)}))
        assert abs(survival(root,rcs,ds)-eps)<mp.mpf('1e-50')
    passed('4 numerical upper-quantile equations; no finite-n uniform-tail claim')
    for name,rows in [('mean',means),('moments',moments),('laplace',laps),('extremes',exts),('joint_covariance',joints),('quantiles',qs)]:
        with (args.output/(name+'.csv')).open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
    with (args.output/'a033552_0_300.txt').open('w') as f:
        for n in range(lim+1):f.write(f'{n} {p[n]}\n')
    constants=dict(mean=str(mu1),variance=str(S[2]),third_cumulant=str(2*S[3]),
                   second_moment=str(mu2),skewness=str(2*S[3]/S[2]**mp.mpf('1.5')),
                   residues=[str(d) for d in ds[:10]])
    result=dict(checks=checks,max_n=args.max_n,dps=args.dps,python=platform.python_version(),
                mpmath=mp.__version__,sympy=sp.__version__,seconds=time.time()-start,
                constants=constants,operator_term_counts={str(j):len(operator_terms(j)) for j in [0,1,2,3]},
                exact_counts={str(n):str(p[n]) for n in ns},
                scope='Exact finite algebra/count checks and non-certified floating-point diagnostics; not a formal proof of asymptotic remainders.')
    (args.output/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    (args.output/'verification.txt').write_text('\n'.join('PASS '+s for s in checks)+'\n')
    print(json.dumps(constants,indent=2),flush=True)
    print('Wrote tables; seconds',time.time()-start,flush=True)

if __name__=='__main__':main()
