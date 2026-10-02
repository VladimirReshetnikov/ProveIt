#!/usr/bin/env python3
"""Finite all-orders generator for A113226 asymptotics, symbolic Gaussian saddle.
For requested order J, computes every coefficient through n^(-J/3).
"""
import argparse,json,time
from pathlib import Path
import sympy as S
import mpmath as mp

def generate(J):
    h,u,c,rho,w=S.symbols('h u c rho w', positive=True)
    K=2*J
    Q=[S.Integer(0)]*(K+1)
    def add_power(a,base,power):
        for k in range(K-base+1):
            Q[base+k]+=a*S.binomial(power,k)*(S.I*u)**k
    # Leading essential singularity, with constant, linear and Gaussian terms removed.
    for k in range(3,K+3):
        Q[k-2]+=2*c*S.binomial(S.Rational(-1,2),k)*(S.I*u)**k
    # n[-log(1-t)-t] and extra -log(1-t); t=c h^4(1+i h u).
    for m in range(2,(K+6)//4+1):
        if 4*m-6<=K:add_power(c**m/S.Integer(m),4*m-6,m)
    for m in range(1,K//4+1):add_power(c**m/S.Integer(m),4*m,m)
    # Frobenius singular and analytic coefficients of log H around z=rho.
    maxm=(J+1)//2
    singular=S.series(S.sqrt(w/(S.exp(w)-1)),w,0,maxm+1).removeO()
    regular={0:rho/2-3}
    for m in range(1,J//2+1):
        rhs=-S.Integer(m==1)-4*(-1)**m/S.factorial(m)
        lower=4*sum((-1)**(m-k)*k*regular[k]/S.factorial(m-k+1) for k in range(1,m))
        regular[m]=S.simplify((rhs-lower)/(4*m+2))
    for m in range(1,maxm+1):
        j=2*m-1
        if j<=J:add_power(2*singular.coeff(w,m)*c**(m+1)*rho**m,2*j,S.Rational(j,2))
    for m in range(1,J//2+1):add_power(regular[m]*(c*rho)**m,4*m,m)
    Q=[S.expand(q) for q in Q]
    E=[S.Integer(1)]
    for k in range(1,K+1):
        E.append(S.expand(sum(j*Q[j]*E[k-j] for j in range(1,k+1))/k))
    ans=[S.Integer(1)]
    for j in range(1,J+1):
        p=S.Poly(E[2*j],u)
        val=0
        for (k,),v in p.terms():
            if k%2:continue
            val+=v*S.factorial2(k-1)*(S.Rational(2,3)/c)**(k//2)
        ans.append(S.factor(S.simplify(val)))
    for j in range(1,K+1,2):
        assert all(k%2 for (k,),v in S.Poly(E[j],u).terms())
    return c,rho,ans

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--order',type=int,default=4);ap.add_argument('--dps',type=int,default=70);args=ap.parse_args()
    assert args.order>=0
    start=time.monotonic();c,rho,ans=generate(args.order)
    mp.mp.dps=args.dps;r=mp.log(4);cv=(mp.pi**2/(4*r))**(mp.mpf(1)/3)
    numbers=[S.N(x.subs({c:S.Float(str(cv),args.dps),rho:S.Float(str(r),args.dps)}),args.dps) for x in ans]
    out={'rho':str(r),'c':str(cv),'C':str(3*cv),'mu':str(mp.exp(3*cv)),'amplitude':str(2*mp.exp(-3)*mp.sqrt(cv/(3*mp.pi))),'order':args.order,'coefficients':[{'j':j,'symbolic':str(a),'decimal':str(v)} for j,(a,v) in enumerate(zip(ans,numbers))]}
    Path(__file__).with_name('asymptotic_coefficients.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2));print('Elapsed',time.monotonic()-start)
if __name__=='__main__':main()
