#!/usr/bin/env python3
"""Exact local-germ verification and independent finite-part quadrature.

The exact side constructs log-Gamma Taylor coefficients as formal expressions.
The numerical left side integrates local Laurent/logarithmic series on [0,rho]
and uses ordinary quadrature on [rho,1]; it never evaluates the product kernel.
"""
from __future__ import annotations
import argparse
import functools
import json
import math
from pathlib import Path
import sympy as s

OUT=Path(__file__).resolve().parents[1]/'data'
OUT.mkdir(exist_ok=True)

@functools.lru_cache(None)
def zjet(w,j):
    return s.zeta(w) if j==0 else s.Symbol(f'Z{w}_{j}')

@functools.lru_cache(None)
def p(r,j):
    if j>r or j<0: return s.S.Zero
    if j==0: return s.factorial(r)
    if j==1: return s.factorial(r)*s.harmonic(r)
    if j==2: return s.factorial(r)*(s.harmonic(r)**2-s.harmonic(r,2))
    u=s.Symbol('u')
    return s.diff(s.rf(1+u,r),u,j).subs(u,0)

def add(x,y):
    out=dict(x)
    for ab,v in y.items():out[ab]=s.expand(out.get(ab,0)+v)
    return {ab:v for ab,v in out.items() if v!=0}

def mul(x,y,A,B):
    out={}
    for (a,b),v in x.items():
      for (c,d),w in y.items():
        if a+c<=A and b+d<=B:
          ab=a+c,b+d
          out[ab]=out.get(ab,0)+v*w
    return {ab:s.expand(v) for ab,v in out.items() if v!=0}

def harmonic(n,d=1):return sum((s.Rational(1,j**d) for j in range(1,n+1)),s.S.Zero)

def polygamma_at(order,N):
    if order==0:return harmonic(N-1)-s.EulerGamma
    q=order+1
    return (-1)**q*s.factorial(order)*(s.zeta(q)-harmonic(N-1,q))

@functools.lru_cache(None)
def p_series(k,l,A,B):
    """P=Gamma(k+l-1+u+v)/(Gamma(k+u)Gamma(l+v))*zeta(w+u+v)."""
    w=k+l-1
    assert w>=2
    L={}
    for a in range(A+1):
      for b in range(B+1):
        n=a+b
        if n==0:continue
        coeff=polygamma_at(n-1,w)
        if b==0:coeff-=polygamma_at(n-1,k)
        if a==0:coeff-=polygamma_at(n-1,l)
        coeff=s.expand(coeff/(s.factorial(a)*s.factorial(b)))
        if coeff:L[a,b]=coeff
    exponential={(0,0):s.S.One}
    power={(0,0):s.S.One}
    for q in range(1,A+B+1):
        power=mul(power,L,A,B)
        exponential=add(exponential,{ab:v/s.factorial(q) for ab,v in power.items()})
    C=s.binomial(k+l-2,k-1)
    Z={(a,b):C*zjet(w,a+b)/(s.factorial(a)*s.factorial(b))
       for a in range(A+1) for b in range(B+1)}
    return mul(exponential,Z,A,B)

def ecoef(j):
    if j==0:return s.S.One
    assert j%2==0
    return 2*(1-s.Rational(2)**(1-j))*s.zeta(j)

@functools.lru_cache(None)
def h_coeff(k,l,a,b):
    P=p_series(k,l,a+1,b+1)
    left=sum((ecoef(2*j)*P.get((a+1-2*j,b),0)
              for j in range((a+1)//2+1)),s.S.Zero)
    right=sum((ecoef(2*j)*P.get((a,b+1-2*j),0)
              for j in range((b+1)//2+1)),s.S.Zero)
    return s.expand((-1)**k*left+(-1)**l*right)

@functools.lru_cache(None)
def J(m,n,r,t):
    assert r+t>0
    ans=s.S.Zero
    for a in range(min(m,r)+1):
      for b in range(min(n,t)+1):
        ans+=p(r,a)/s.factorial(a)*p(t,b)/s.factorial(b)*h_coeff(r+1,t+1,m-a,n-b)
    return s.expand((-1)**(m+n+r+t)*s.factorial(m)*s.factorial(n)*ans)

@functools.lru_cache(None)
def gamma_derivative_one(m,d):
    assert d>=1
    return s.expand((-1)**(m+d)*sum(s.binomial(m,j)*p(d,j)*zjet(d+1,m-j)
                                  for j in range(min(m,d)+1)))

def exact_suite():
    checks=[]
    for m in range(3):
      for n in range(3):
       for r in range(3):
        for t in range(3):
          lhs=J(m,n,r+1,t)+J(m,n,r,t+1)
          rhs=-(-1)**(m+r)*p(r,m)/s.factorial(r+1)*gamma_derivative_one(n,r+t+1)
          rhs-=(-1)**(n+t)*p(t,n)/s.factorial(t+1)*gamma_derivative_one(m,r+t+1)
          residual=s.expand(lhs-rhs)
          assert residual==0,(m,n,r,t,residual)
          checks.append([m,n,r,t])
    printed={
      'gamma1_gamma0prime':(J(1,0,0,1),s.Rational(1,2)*zjet(2,2)-s.zeta(2)),
      'gamma0_gamma1prime':(J(0,1,0,1),-zjet(2,1)-s.Rational(1,2)*zjet(2,2)),
      'gamma1_gamma0second':(J(1,0,0,2),(4*s.zeta(2)-s.Rational(3,2))*s.zeta(3)+6*zjet(3,1)+3*zjet(3,2)),
      'gamma1_gamma1prime':(J(1,1,0,1),s.S.Zero),
    }
    for name,(actual,expected) in printed.items():
        assert s.expand(actual-expected)==0,(name,actual,expected)
    table=[]
    for m,n,r,t in [(0,0,0,1),(1,0,0,1),(0,1,0,1),(1,0,0,2),(1,1,0,1),(2,0,0,1),(1,1,0,2)]:
      table.append({'m':m,'n':n,'r':r,'t':t,'formula':str(J(m,n,r,t)),'latex':s.latex(J(m,n,r,t))})
    result={'exact_ibp_assertions':len(checks),'printed_formula_assertions':len(printed),
            'ibp_test_indices':checks,'formulas':table,'all_passed':True}
    (OUT/'edge_exact.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['ibp_test_indices','formulas']},indent=2))

def numerical_suite(dps=55,degree=65):
    import mpmath as mp
    mp.mp.dps=dps
    @functools.lru_cache(None)
    def numeric_zjet(w,j):return mp.diff(mp.zeta,w,j)
    @functools.lru_cache(None)
    def gder(m,d):
      if d==0:return mp.stieltjes(m)
      return (-1)**(m+d)*sum(math.comb(m,j)*int(p(d,j))*numeric_zjet(d+1,m-j)
                           for j in range(min(m,d)+1))
    def singular(m,r):
      return {( -r-1,m-j):mp.mpf((-1)**(r+j)*math.comb(m,j)*int(p(r,j)))
                    for j in range(min(m,r)+1)}
    def germ(m,r):
      out=singular(m,r)
      for j in range(degree+1):out[j,0]=gder(m,r+j)/mp.factorial(j)
      return out
    def integrate_monomial(a,j,rho):
      L=mp.log(rho)
      if a==-1:return L**(j+1)/(j+1)
      return rho**(a+1)*sum((-1)**h*mp.factorial(j)/mp.factorial(j-h)
                  *L**(j-h)/mp.mpf(a+1)**(h+1) for h in range(j+1))
    @functools.lru_cache(None)
    def analytic_coefficients_at_two(m,r):
      # Expand the smooth shifted part about 2.  On rho<=x<=1 the
      # Taylor ratio is at most (1-rho)/2, avoiding slow repeated
      # generalized-Stieltjes quadratures at the external quadrature nodes.
      vals=[]
      for j in range(181):
        d=r+j
        if d==0:
          val=mp.stieltjes(m)-(1 if m==0 else 0)
        else:
          val=(-1)**(m+d)*sum(math.comb(m,k)*mp.mpf(int(p(d,k)))
                  *mp.diff(lambda q:mp.zeta(q,2),d+1,m-k)
                  for k in range(min(m,d)+1))
        vals.append(val/mp.factorial(j))
      return tuple(vals)
    def direct_gamma(m,r,x):
      smooth=mp.polyval(tuple(reversed(analytic_coefficients_at_two(m,r))),x-1)
      singular_part=sum(v*x**a*mp.log(x)**j for (a,j),v in singular(m,r).items())
      return singular_part+smooth
    def fp(m,n,r,t,rho):
      f,g=germ(m,r),germ(n,t)
      local=mp.mpf(0)
      # Full product of the two truncated analytic germs is used.
      for (a,j),v in f.items():
        for (b,k),w in g.items():local+=v*w*integrate_monomial(a+b,j+k,rho)
      rest=mp.quadgl(lambda x:direct_gamma(m,r,x)*direct_gamma(n,t,x),[rho,mp.mpf('0.5'),1])
      return local+rest
    def formula_value(expr):
      replacements={}
      for sym in expr.free_symbols:
        name=str(sym)
        if name.startswith('Z'):
          w,j=map(int,name[1:].split('_'))
          replacements[sym]=s.Float(str(numeric_zjet(w,j)),dps)
      return mp.mpf(str(expr.subs(replacements).evalf(dps)))
    evaluator_checks=[]
    for m,r,x in [(0,0,mp.mpf('0.3')),(1,0,mp.mpf('0.4')),
                  (2,0,mp.mpf('0.6')),(1,1,mp.mpf('0.4'))]:
      actual=direct_gamma(m,r,x)
      if r==0: reference=mp.stieltjes(m,x)
      else: reference=(-1)**(m+r)*sum(math.comb(m,j)*int(p(r,j))*mp.diff(lambda z:mp.zeta(z,x),r+1,m-j)
                             for j in range(min(m,r)+1))
      error=abs(actual-reference)
      assert error<mp.mpf('1e-45'),(m,r,x,error)
      evaluator_checks.append({'index':m,'derivative':r,'x':str(x),'absolute_error':mp.nstr(error,10)})
    records=[]
    cases=[(1,0,0,1),(0,1,0,1),(1,0,0,2),(1,1,0,1),(2,0,0,1)]
    for case in cases:
      m,n,r,t=case
      got=fp(m,n,r,t,mp.mpf('0.125'))
      expected=formula_value(J(m,n,r,t))
      err=abs(got-expected)
      assert err<mp.mpf('1e-40'),(case,got,expected,err)
      records.append({'indices':case,'local_split':'0.125','local_degree':degree,
        'direct_fp':mp.nstr(got,dps-5),'formula':mp.nstr(expected,dps-5),'absolute_error':mp.nstr(err,10)})
      (OUT/'edge_numeric_checkpoint.json').write_text(json.dumps(records,indent=2)+'\n')
      print('verified',case,mp.nstr(err,6),flush=True)
    # One second splitting point checks the cutoff independence numerically.
    case=(1,0,0,1)
    got=fp(*case,mp.mpf('0.2'))
    expected=formula_value(J(*case))
    err=abs(got-expected)
    assert err<mp.mpf('1e-35'),(case,err)
    records.append({'indices':case,'local_split':'0.2','local_degree':degree,
        'direct_fp':mp.nstr(got,dps-5),'formula':mp.nstr(expected,dps-5),'absolute_error':mp.nstr(err,10)})
    result={'working_digits':dps,'method':'Local Laurent/logarithmic integration plus ordinary Gauss-Legendre quadrature; no product kernel used on the left.',
            'interval_certified':False,'evaluator_degree':180,'evaluator_cross_checks':evaluator_checks,'records':records,'all_passed':True}
    (OUT/'edge_numeric.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'numerical_comparisons':len(records),'all_passed':True}))

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--mode',choices=['exact','numeric','all'],default='exact')
    args=parser.parse_args()
    if args.mode in ['exact','all']:exact_suite()
    if args.mode in ['numeric','all']:numerical_suite()
