#!/usr/bin/env python3
"""Exact algebra and non-certified numerical diagnostics for the accompanying paper.
Run: python verification/verify.py.  Requires Python 3.10+, sympy, mpmath.
Numerical residuals are diagnostics, not interval certificates or proofs.
"""
from __future__ import annotations
import json, math, platform, time
from pathlib import Path
from functools import lru_cache
import sympy as sp
import mpmath as mp

ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=65
exact=[]; numerical=[]

def check_exact(name, value):
    assert sp.simplify(value)==0, (name,value)
    exact.append(name)

def check_num(name, left, right, tol='1e-42'):
    residual=abs(left-right); scale=max(mp.mpf(1),abs(left),abs(right))
    passed=residual/scale < mp.mpf(tol)
    numerical.append(dict(name=name,left=mp.nstr(left,58),right=mp.nstr(right,58),
        absolute_residual=mp.nstr(residual,8),relative_residual=mp.nstr(residual/scale,8),
        tolerance=tol,passed=passed))
    assert passed,(name,mp.nstr(residual,8))

@lru_cache(None)
def elementary(k, r):
    """e_r(1,1/2,...,1/(k-1)), exactly."""
    if r==0:return sp.S.One
    if r<0 or r>=k:return sp.S.Zero
    return elementary(k-1,r)+elementary(k-1,r-1)/sp.Integer(k-1)

def mpq(q):
    return mp.mpf(int(sp.numer(q)))/int(sp.denom(q))

def kernel(m,L):
    return sum((-1)**j*math.comb(m,2*j+1)*mp.pi**(2*j)*L**(m-2*j-1)
               for j in range((m-1)//2+1))

def qlog(r,x,u):
    # Difference formula in powers of log1p avoids cancellation for large x.
    l=mp.log(x); h=mp.log1p(u/x)
    return sum(math.comb(r+1,j)*l**(r+1-j)*h**j for j in range(1,r+2))/(r+1)

def log_coefficients(alpha, us, K):
    """Coefficient of x^{-k} log(x)^ell in product Q_alpha(x,u)."""
    co={(0,0):mp.mpf(1)}
    for r,u in zip(alpha,us):
        one={}
        for k in range(1,K+1):
            for h in range(min(r,k-1)+1):
                one[k,r-h]=((-1)**(k-1+h)*u**k/k*math.comb(r,h)
                            *math.factorial(h)*mpq(elementary(k,h)))
        out={}
        for (k1,l1),v1 in co.items():
            for (k2,l2),v2 in one.items():
                if k1+k2<=K:
                    key=(k1+k2,l1+l2)
                    out[key]=out.get(key,mp.mpf(0))+v1*v2
        co=out
    return co

@lru_cache(None)
def zd(order, k, a_string):
    a=mp.mpf(a_string)
    return mp.zeta(k,a) if order==0 else mp.diff(lambda s:mp.zeta(s,a),mp.mpf(k),order)

def F(alpha,a,us,N=50,K=38):
    """Finite direct sum plus geometrically convergent Hurwitz tail."""
    a=mp.mpf(a); us=tuple(mp.mpf(u) for u in us)
    m=len(us); total=sum(alpha); U=mp.fprod(us)
    out=U*mp.stieltjes(total,a)
    for n in range(N):
        x=a+n
        out+=x**(m-1)*mp.fprod(qlog(r,x,u) for r,u in zip(alpha,us))-U*mp.log(x)**total/x
    co=log_coefficients(alpha,us,K)
    for (k,l),c in co.items():
        if k>m: out+=c*(-1)**l*zd(l,k-m+1,mp.nstr(a+N,70))
    return out

def F0_full(a,us,K=100):
    a=mp.mpf(a);us=tuple(mp.mpf(u) for u in us);m=len(us)
    co=log_coefficients((0,)*m,us,K)
    return mp.fprod(us)*mp.stieltjes(0,a)+sum(c*mp.zeta(k-m+1,a) for (k,l),c in co.items() if k>m)

def F0_integral(a,us):
    """Independent real branch-jump formula, all u_j > 0."""
    a=mp.mpf(a);us=tuple(mp.mpf(u) for u in us);m=len(us)
    def integrand(t):
        rs=[mp.log(abs(t/(t-u)))+(mp.j*mp.pi if t<u else 0) for u in us]
        return -t**(m-1)*mp.digamma(a+t)*mp.im(mp.fprod(rs))/mp.pi
    pts=sorted(set([mp.mpf(0),*us]))
    return mp.quad(integrand,pts)

def J(m,r,a,u):
    a=mp.mpf(a);u=mp.mpf(u)
    return mp.stieltjes(r,a+u)+(-1)**r*sum(math.comb(m-1,k)*(-u)**k*
        (mp.zeta(k+1,a+u) if r==0 else mp.diff(lambda s:mp.zeta(s,a+u),mp.mpf(k+1),r))
        for k in range(1,m))

def partial_equal_spectrum_jet(m,j,r,a,u,K=105):
    """Derivative of sum x^{m-1}[x^{m-j}(x+u)^j]^{-s} at 0.
    Evaluates each spectrum separately, including its removable Hurwitz pole.
    """
    a=mp.mpf(a);u=mp.mpf(u)
    result=m**r*mp.diff(lambda s:mp.zeta(s,a),mp.mpf(1-m),r)
    for k in range(1,K+1):
        coeff=mp.mpf(0)
        for l in range(1,min(k,r+1)+1):
            p=mp.mpf(j)**l/k*mpq(elementary(k,l-1))
            if k==m:
                d=r-l
                if d>=0: coeff+=p*(-m)**d*mp.stieltjes(d,a)/math.factorial(d)
                if l==r+1:coeff+=p/m
            elif l<=r:
                d=r-l
                z=mp.zeta(k-m+1,a) if d==0 else mp.diff(lambda ss:mp.zeta(ss,a),mp.mpf(k-m+1),d)
                coeff+=p*m**d*z/math.factorial(d)
        result+=math.factorial(r)*(-u)**k*coeff
    return result

def run():
    start=time.time();s=sp.Symbol('s'); L=sp.Symbol('L',real=True)
    # Independent polynomial and harmonic descriptions of rising factorials.
    for k in range(1,17):
        poly=sp.Poly(sp.rf(s,k)/sp.factorial(k),s)
        for r in range(1,min(k,7)+1):
            check_exact(f'pochhammer_k{k}_r{r}',poly.coeff_monomial(s**r)-elementary(k,r-1)/k)
    # Inclusion-exclusion coefficient at critical degree.
    for m in range(1,8):
        # Equal-mass independent binomial finite differences.
        for d in range(m+3):
            value=sum((-1)**(m-j)*sp.binomial(m,j)*sp.rf(j*s,d)/sp.factorial(d)
                      for j in range(m+1))
            if d<m:check_exact(f'subset_zero_m{m}_degree{d}',value)
            if d==m:check_exact(f'subset_critical_m{m}',value-s**m)
    # The full distinct-mass cubic residue, independent symbolic multiplication.
    u,v,w=sp.symbols('u v w');t=sp.Symbol('t')
    terms=[sum((-1)**k*sp.rf(s,k)/sp.factorial(k)*(mass*t)**k for k in range(1,4))
           for mass in (u,v,w)]
    check_exact('distinct_cubic_residue',sp.expand(sp.prod(terms)).coeff(t,3)+u*v*w*s**3)
    # Jump polynomial and beta moments against independent Stirling coefficients.
    from sympy.functions.combinatorial.numbers import stirling
    for m in range(1,11):
        p=sum((-1)**j*sp.binomial(m,2*j+1)*sp.pi**(2*j)*L**(m-2*j-1)
              for j in range((m-1)//2+1))
        check_exact(f'jump_polynomial_m{m}',sp.expand(((L+sp.I*sp.pi)**m-(L-sp.I*sp.pi)**m)/(2*sp.pi*sp.I))-p)
        for n in range(1,m+4):
            # B(n+s,1-s) = (pi*s/sin(pi*s))*prod_{j=1}^{n-1}(j+s)/n!
            beta=sp.series(sp.pi*s/sp.sin(sp.pi*s),s,0,m).removeO()
            beta=sp.Poly(sp.expand(beta*sp.prod(j+s for j in range(1,n))/sp.factorial(n)),s)
            integ=sum(sp.expand(p).coeff(L,k)*sp.factorial(k)*beta.coeff_monomial(s**k) for k in range(m))
            target=sp.factorial(m)*stirling(n,m,kind=1)/sp.factorial(n) if n>=m else 0
            check_exact(f'beta_stirling_m{m}_n{n}',integ-target)
    # Direct/tail series versus independent one-dimensional Gamma integrals.
    for m in range(1,6):
        a=mp.mpf('1.3');us=[mp.mpf('0.2')]*m
        fs=F((0,)*m,a,us)
        check_num(f'equal_gamma_integral_m{m}',fs,F0_integral(a,us))
        check_num(f'full_mass_series_m{m}',fs,F0_full(a,us))
    for us in [('0.12','0.21'),('0.08','0.17','0.27'),('0.09','0.09','0.16','0.23')]:
        m=len(us)
        check_num('unequal_gamma_integral_'+str(m),F((0,)*m,'1.1',us),F0_integral('1.1',us))
    for a,u in [('0.7','0.18'),('1.2','0.37')]:
        check_num('gamma_depth_one_'+a,F((0,),a,[u]),mp.loggamma(mp.mpf(a))-mp.loggamma(mp.mpf(a)+mp.mpf(u)))
    # Gauss distribution, including spectral logarithmic orders.
    cases=[((0,0),['0.14','0.22']),((1,0),['0.14','0.22']),((1,1),['0.14','0.22']),((0,0,0),['0.11','0.18','0.24'])]
    import itertools
    for alpha,us0 in cases:
        a=mp.mpf('1.2');us=list(map(mp.mpf,us0));m=len(us);r=sum(alpha);q=3
        left=sum(F(alpha,(a+h)/q,[u/q for u in us]) for h in range(q))
        right=mp.mpf(0)
        for beta in itertools.product(*(range(k+1) for k in alpha)):
            right+=math.prod(math.comb(k,l) for k,l in zip(alpha,beta))*(-mp.log(q))**(r-sum(beta))*F(beta,a,us)
        right+=(-1)**r*mp.fprod(us)*mp.log(q)**(r+1)/(r+1)
        right*=mp.mpf(q)**(1-m)
        check_num('gauss_'+str(alpha),left,right,'1e-39')
        check_num('shift_'+str(alpha),F(alpha,a+1,us)-F(alpha,a,us),-a**(m-1)*mp.fprod(qlog(k,a,u) for k,u in zip(alpha,us)),'1e-39')
    # Independently regularize four cubic spectra, then form their finite difference.
    for m in [2,3,4]:
        r=m-1;a=mp.mpf('1.2');u=mp.mpf('0.12')
        vals=[partial_equal_spectrum_jet(m,j,r,a,u) for j in range(m+1)]
        left=sum((-1)**(m-j)*math.comb(m,j)*vals[j] for j in range(m+1))
        right=(-1)**m*mp.factorial(m-1)/m*u**m
        check_num(f'independent_spectral_anomaly_m{m}',left,right,'1e-42')
    # Coincident zero-order mixed derivatives: independent symbolic Leibniz formula.
    for m in range(2,6):
        a=mp.mpf('1.2');u=mp.mpf('0.17')
        rhs=-mp.diff(lambda z:z**(m-1)*mp.digamma(a+z),u,m-1)/mp.factorial(m-1)
        check_num(f'confluent_polygamma_m{m}',J(m,0,a,u),rhs)
    # Ordinary beta antiderivative, unmarked order at m=2.
    a=mp.mpf('1.2');u=mp.mpf('0.18')
    for r in [0]:
        def integrand(y):
            return sum(math.comb(r,k)*(-mp.log(y))**(r-k)*J(2,k,a,u*y) for k in range(r+1))
        left=mp.quad(integrand,[0,mp.mpf('.5'),1])
        # H_1^star({1}^j)=1.
        right=sum(math.comb(r,k)*mp.factorial(r-k)*mp.stieltjes(k,a+u) for k in range(r+1))
        check_num(f'beta_stieltjes_primitive_order{r}',left,right,'1e-39')
    # Polylog expansion checked against a geometrically convergent direct n-sum.
    for m in [2,3,4]:
        us=[mp.mpf('0.16')]*m;z=mp.mpf('0.43');a=mp.mpf(1)
        co=log_coefficients((0,)*m,us,90)
        left=sum(n**(m-1)*z**n*mp.fprod(mp.log1p(u/n) for u in us) for n in range(1,260))
        right=sum(c*mp.polylog(k-m+1,z) for (k,l),c in co.items())
        check_num(f'polylog_generation_m{m}',left,right)
    data={'status':'passed','exact_assertions':len(exact),'numerical_diagnostics':len(numerical),
          'working_decimal_digits':mp.mp.dps,'interval_certified':False,
          'proof_assistant_formalization':False,'python':platform.python_version(),
          'sympy':sp.__version__,'mpmath':mp.__version__,'elapsed_seconds':round(time.time()-start,3),
          'exact_checks':exact,'numerical_checks':numerical}
    (ROOT/'results').mkdir(exist_ok=True)
    (ROOT/'results'/'validation.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k not in ['exact_checks','numerical_checks']},indent=2))
    return data

if __name__=='__main__':run()
