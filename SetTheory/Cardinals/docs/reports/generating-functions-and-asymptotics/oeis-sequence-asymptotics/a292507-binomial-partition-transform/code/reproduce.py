#!/usr/bin/env python3
"""A292507 coefficient derivation and exact-integer diagnostics.
Requires Python 3, sympy and mpmath. No downloaded data or network calls.
python reproduce.py --order 6 --max-n 10000
"""
import argparse, json, math
from pathlib import Path
import sympy as s
import mpmath as mp
B,z,w=s.symbols('B z w')
R=s.Rational

def mul(a,b,N):
    return [s.expand(sum(a[k]*b[j-k] for k in range(max(0,j-len(b)+1),min(j,len(a)-1)+1))) for j in range(N+1)]

def exp_series(a,N):
    assert a[0]==0
    out=[s.Integer(1)]
    for j in range(1,N+1):
        out.append(s.expand(sum(k*a[k]*out[j-k] for k in range(1,j+1))/j))
    return out

def source(q,N):
    ex=[s.Integer(0)]*(N+1)
    for r in range(1,(N+1)//2+1):
        if 2*r-1<=N: ex[2*r-1]=B*s.binomial(R(1,2),r)*(-2*q)**r
    pref=[]
    for j in range(N+1):
        if j%2==0: pref.append((2*q)**(j//2))
        else: pref.append(-s.binomial(-R(3,2),(j-1)//2)*(-2*q)**((j-1)//2)/B)
    return mul(exp_series(ex,N),pref,N)

def coefficients(M):
    f,g=source(R(1,24),M+1),source(R(25,24),M+1)
    d=[s.expand((f[j+1]-g[j+1])/B) for j in range(M+1)]
    ex=[s.Integer(0)]+[B*s.binomial(R(1,2),j+1)*z**(j+1) for j in range(1,M+1)]
    central=[s.expand(sum(d[j]*s.binomial(-R(3+j,2),k-j)*z**(k-j) for j in range(k+1))) for k in range(M+1)]
    P=mul(exp_series(ex,M),central,M)
    logcosh=s.series(s.log(s.cosh(w)),w,0,M+4).removeO().expand()
    qe=[s.Integer(0)]*(M+1)
    for j in range(2,M+1,2): qe[j]=logcosh.coeff(w,j+2)*z**(j+2)
    Q=exp_series(qe,M)
    # e^(-z^2/2) D^r[e^(z^2/2) Q(z)] = (D+z)^r Q(z).
    coeff=[]
    for j in range(M+1):
        total=0
        for u in range(j+1):
            pol=s.Poly(P[u],z)
            derivatives=[Q[j-u]]
            for k in range(pol.degree()):
                derivatives.append(s.expand(s.diff(derivatives[-1],z)+z*derivatives[-1]))
            total+=sum(a*derivatives[p[0]].subs(z,B/2) for p,a in pol.terms())
        coeff.append(s.factor(total))
    return d,coeff

def partitions(N):
    p=[0]*(N+1);p[0]=1
    pent=[]
    for j in range(1,N+1):
        a=j*(3*j-1)//2;b=j*(3*j+1)//2
        if a>N:break
        pent.append((a,b,1 if j%2 else -1))
    for n in range(1,N+1):
        p[n]=sum(sgn*(p[n-a]+(p[n-b] if b<=n else 0)) for a,b,sgn in pent if a<=n)
    return p

def exact_a(n,p):
    choose=1;result=0
    for k in range(n+1):
        result+=choose*(p[k]-(p[k-1] if k else 0))
        choose=choose*(n-k)//(k+1)
    return result

def inverse_polynomials(M,J):
    """Formal coefficient recursion in t=X^-1/2, L=log(X)."""
    t,L,al,be,ga,lc=s.symbols('t L alpha beta gamma logC')
    cs=s.symbols('c1:'+str(M+1))
    v=1-be/al*t+(ga/al*L+be**2/(2*al**2)-lc/al)*t*t
    out=[]
    for j in range(1,J+1):
        residual=al*(v-1)/t**2+be/t*s.sqrt(v)-ga*(L+s.log(v))+lc
        residual+=s.log(1+sum(cs[k-1]*t**k*v**(-R(k,2)) for k in range(1,M+1)))
        uj=s.expand(-s.series(residual,t,0,j+1).removeO().coeff(t,j)/al)
        out.append(s.factor(uj));v+=uj*t**(j+2)
    return out

def run(M,N,out):
    mp.mp.dps=90
    d,coeff=coefficients(M)
    exact=[s.simplify(x.subs(B,s.pi/s.sqrt(3))) for x in coeff]
    numeric=[mp.mpf(str(s.N(x,100))) for x in exact]
    # Independent formulas produced in the initial derivation.
    known=[1,-17*s.pi/(12*s.sqrt(3))-3*s.sqrt(3)/s.pi-s.pi**3/(96*s.sqrt(3)),
      (497664+s.pi**2*(s.pi**6+336*s.pi**4+32416*s.pi**2+470016))/(55296*s.pi**2),
      s.sqrt(3)*(-s.pi**2*(s.pi**8+600*s.pi**6+129696*s.pi**4+11153152*s.pi**2+257679360)-1015234560)/(47775744*s.pi)]
    for j in range(min(4,M+1)): assert s.simplify(exact[j]-known[j])==0
    p=partitions(N)
    oeis=[1,1,2,5,13,33,82,201,488,1176,2817,6714,15931,37647,88628,207914]
    assert [exact_a(n,p) for n in range(min(len(oeis),N+1))]==oeis[:N+1]
    C=mp.pi/6*mp.exp(mp.pi**2/24); beta=mp.pi/mp.sqrt(3); alpha=mp.log(2)
    rows=[]
    for n in [100,500,1000,2000,5000,10000]:
        if n>N:continue
        a=exact_a(n,p)
        Y=mp.log(a); lead=mp.log(C)+n*alpha-mp.mpf('1.5')*mp.log(n)+beta*mp.sqrt(n)
        ratio=mp.exp(Y-lead)
        approximants=[sum(numeric[j]/mp.mpf(n)**(mp.mpf(j)/2) for j in range(r+1)) for r in range(M+1)]
        def F(x):return alpha*x+beta*mp.sqrt(x)-mp.mpf('1.5')*mp.log(x)+mp.log(C)+mp.log(sum(numeric[j]*x**(-mp.mpf(j)/2) for j in range(M+1)))
        xM=mp.findroot(lambda x:F(x)-Y,(mp.mpf(n)-1,mp.mpf(n)+1))
        rows.append({'n':n,'ratio_to_leading':str(ratio),'relative_errors':[str(ratio/q-1) for q in approximants],
          'scaled_M_residual':str((ratio-approximants[-1])*mp.mpf(n)**(mp.mpf(M+1)/2)),
          'model_inverse_minus_n':str(xM-n),'inverse_scaled_error':str((xM-n)*mp.mpf(n)**(mp.mpf(M+1)/2))})
    data={'order':M,'max_n':N,'note':'Numerical diagnostics support, but do not replace, the proof. Inverse error sign is not an exact-rounding theorem.',
      'coefficients':[{'j':j,'beta_form':str(coeff[j]),'pi_form':str(exact[j]),'value':str(numeric[j])} for j in range(M+1)],'diagnostics':rows}
    out.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--order',type=int,default=4);a.add_argument('--max-n',type=int,default=10000);a.add_argument('--output',type=Path,default=Path('verification.json'))
    args=a.parse_args()
    if args.order < 0 or args.max_n < 0: a.error('order and max-n must be nonnegative')
    run(args.order,args.max_n,args.output)
