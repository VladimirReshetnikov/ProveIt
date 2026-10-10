#!/usr/bin/env python3
"""Independent numerical diagnostics; not interval proofs or PSLQ certificates.

Checks defining integrals against the proved reductions, and compares the
Stieltjes closure with a separately implemented polylogarithm generating law.
"""
from __future__ import annotations
import argparse,json,platform,time
from fractions import Fraction
from pathlib import Path
from functools import lru_cache
import mpmath as mp
import sympy as sp
from identity_engine import correlation, primitive_coefficients

@lru_cache(None)
def em_constants(n: int,dps: int):
    coeff=[mp.mpf(1)]+[mp.mpf(0)]*n
    out=[]
    # Rising-factorial normalized coefficients e_j(1,...,1/r).
    for r in range(1,81):
        for j in range(min(r,n),0,-1):
            coeff[j]+=coeff[j-1]/r
        if r%2:
            k=(r+1)//2
            out.append((k,mp.bernoulli(2*k)/(2*k),tuple(coeff)))
    return out

def stieltjes_em(n: int,a):
    """EM approximation with N=96, M=40; diagnostics compare with mp.stieltjes."""
    a=mp.mpf(a)
    if a<=0 or not 0<=n<=8:
        raise ValueError('require a>0 and 0<=n<=8')
    N=96; A=a+N; L=mp.log(A)
    val=mp.fsum(mp.log(a+j)**n/(a+j) for j in range(N))
    val-=L**(n+1)/(n+1)
    val+=L**n/(2*A)
    for k,b,e in em_constants(n,mp.mp.dps):
        c=mp.fsum(e[j]*(-L)**(n-j)/mp.factorial(n-j) for j in range(min(n,2*k-1)+1))
        val+=(-1)**n*mp.factorial(n)*b*A**(-2*k)*c
    return val

def eval_expr(expr,a):
    subs={}
    for atom in expr.free_symbols:
        name=str(atom)
        if name.startswith('ga'): subs[atom]=mp.stieltjes(int(name[2:]),a)
        elif name.startswith('gb'): subs[atom]=mp.stieltjes(int(name[2:]),1-a)
        elif name.startswith('z'): subs[atom]=mp.zeta(int(name[1:]))
        else: raise ValueError(name)
    args=sorted(subs,key=str)
    return sp.lambdify(args,expr,'mpmath')(*(subs[s] for s in args))

def segmented_quad(f,top):
    cuts=[mp.mpf(0)]+[mp.mpf(t) for t in [1,3,8,16,32] if t<top]+[top]
    return mp.quad(f,cuts,method='gauss-legendre')

def j_cutoff(m,n,a,eps):
    b=1-a
    f=lambda t:(b*mp.exp(-t))*stieltjes_em(m,b*mp.exp(-t))*stieltjes_em(n,a+b*mp.exp(-t))
    g=lambda t:(a*mp.exp(-t))*stieltjes_em(m,b+a*mp.exp(-t))*stieltjes_em(n,a*mp.exp(-t))
    x=segmented_quad(f,mp.log(b/eps))+segmented_quad(g,mp.log(a/eps))
    return x+stieltjes_em(n,a)*mp.log(eps)**(m+1)/(m+1)+stieltjes_em(m,b)*mp.log(eps)**(n+1)/(n+1)

def C_poly(s,t,a):
    z=mp.exp(2j*mp.pi*a);w=2-s-t
    return mp.gamma(1-s)*mp.gamma(1-t)/(2*mp.pi)**w*(mp.exp(-.5j*mp.pi*(s-t))*mp.polylog(w,z)+mp.exp(.5j*mp.pi*(s-t))*mp.polylog(w,1/z))

def C_beta(s,t,a):
    return mp.beta(1-s,s+t-1)*mp.zeta(s+t-1,a)+mp.beta(1-t,s+t-1)*mp.zeta(s+t-1,1-a)

def C_integral(s,t,a):
    b=1-a
    return mp.quad(lambda x:mp.zeta(s,x)*mp.zeta(t,x+a),[0,b])+mp.quad(lambda x:mp.zeta(s,b+x)*mp.zeta(t,x),[0,a])

def gamma_correlation(a):
    b=1-a;L=mp.log(2*mp.pi)
    f=lambda x:mp.loggamma(x)-L/2
    return mp.quad(lambda x:f(x)*f(x+a),[0,b])+mp.quad(lambda x:f(b+x)*f(x),[0,a])

def gamma_digamma_regularized(a):
    b=1-a;L=mp.log(2*mp.pi)
    f=lambda x:mp.loggamma(x)-L/2
    fb=f(b)
    coeff=[mp.polygamma(k-1,b)/mp.factorial(k) for k in range(1,11)]
    def delta(t):
        if t<mp.mpf('1e-8'):
            return t*mp.polyval(list(reversed(coeff)),t)
        return f(b+t)-fb
    return (mp.quad(lambda x:f(x)*mp.digamma(x+a),[0,b],maxdegree=7)
            +mp.quad(lambda t:delta(t)*mp.digamma(t)+fb*mp.digamma(1+t),[0,a],maxdegree=7)
            -fb*mp.log(a))

def gamma_digamma_closed(a):
    return (mp.zeta(0,1-a,derivative=2)-mp.zeta(0,a,derivative=2))/2+mp.zeta(2)*(2*a-1)

def higher_lift_test(r,k,a):
    # Barnes G independently evaluates Q_0; the other side uses Hurwitz jets.
    L=mp.log(2*mp.pi);zp=mp.zeta(-1,derivative=1);b=1-a
    def P(x):return -mp.loggamma(x)+L/2
    def Q(x):return (x*x-x+mp.mpf(1)/6)/2-zp+mp.log(mp.barnesg(x+1))-x*mp.loggamma(x)
    f=Q;g=P if k==1 else Q
    value=mp.quad(lambda x:f(x)*g(x+a),[0,b])+mp.quad(lambda x:f(b+x)*g(x),[0,a])
    N=r+k;coeff=primitive_coefficients(1,N)
    def U(x):
        return mp.fsum(mp.mpf(int(c.p))/int(c.q)*mp.zeta(1-N,x,derivative=j) for j,c in enumerate(coeff))
    closed=(-1)**r*U(a)+(-1)**k*U(b)+(-1)**r*(-2*mp.zeta(2))*mp.bernpoly(N,a)/mp.factorial(N)
    return value,closed

def gamma_hurwitz(a):
    b=1-a
    return (1+mp.zeta(2))*(a*a-a+mp.mpf(1)/6)-sum(mp.zeta(-1,x,derivative=1) + mp.zeta(-1,x,derivative=2)/2 for x in (a,b))

def gamma_poly(a):
    # Exact rational DFT evaluates order derivatives at s=2.  Direct tiny-step
    # differentiation of mpmath.polylog near integer order can lose accuracy.
    frac=Fraction(str(a)).limit_denominator(1000)
    p,q=frac.numerator,frac.denominator
    if abs(a-mp.mpf(p)/q)>mp.mpf('1e-40'):
        raise ValueError('diagnostic requires a rational shift of denominator <=1000')
    c=mp.euler+mp.log(2*mp.pi);logq=mp.log(q)
    def derivative(k):
        return mp.fsum(mp.exp(2j*mp.pi*p*r/q)*mp.fsum(mp.binomial(k,j)*(-logq)**(k-j)*mp.zeta(2,mp.mpf(r)/q,derivative=j) for j in range(k+1)) for r in range(1,q+1))/q**2
    return mp.re(derivative(2)-2*c*derivative(1)+(c*c+mp.pi**2/4)*derivative(0))/(2*mp.pi**2)

def poly_half_jets(max_degree):
    # Independent Taylor coefficients of Li_s(-1)=(2^(1-s)-1) zeta(s).
    l=mp.taylor(lambda s:(mp.power(2,1-s)-1)*mp.zeta(s),0,max_degree)
    def e(sign):
        a=[mp.mpc(1)]
        logs=[0,mp.euler+mp.log(2*mp.pi)+sign*mp.pi*1j/2]+[mp.zeta(k)/k for k in range(2,max_degree+1)]
        for n in range(1,max_degree+1):a.append(mp.fsum(k*logs[k]*a[n-k] for k in range(1,n+1))/n)
        return a
    ep,em=e(1),e(-1)
    def evaluate(m,n):
        ans=0
        for i in range(m+2):
            for j in range(n+2):
                k=m+n+2-i-j
                ans+=(em[i]*ep[j]+ep[i]*em[j])*l[k]*(-1)**k*mp.binomial(k,m+1-i)
        return mp.re((-1)**(m+n)*mp.factorial(m)*mp.factorial(n)*ans)
    return evaluate

def polygamma_cutoff(r,k,a,eps):
    b=1-a
    first=segmented_quad(lambda t:b*mp.exp(-t)*mp.polygamma(r,b*mp.exp(-t))*mp.polygamma(k,a+b*mp.exp(-t)),mp.log(b/eps))
    second=segmented_quad(lambda t:a*mp.exp(-t)*mp.polygamma(r,b+a*mp.exp(-t))*mp.polygamma(k,a*mp.exp(-t)),mp.log(a/eps))
    if (r,k)==(0,1):
        return first+second-mp.digamma(b)/eps-(mp.polygamma(1,a)-mp.polygamma(1,b))*mp.log(eps)
    if (r,k)==(1,1):
        return first+second-(mp.polygamma(1,a)+mp.polygamma(1,b))/eps+(mp.polygamma(2,a)+mp.polygamma(2,b))*mp.log(eps)
    raise ValueError('only (0,1) and (1,1) implemented as direct diagnostics')

def polygamma_closed(r,k,a):
    N=r+k;b=1-a
    return mp.factorial(N)*((-1)**(k+1)*(mp.zeta(N+1,a,derivative=1)+(mp.harmonic(N)-mp.harmonic(r))*mp.zeta(N+1,a))+(-1)**(r+1)*(mp.zeta(N+1,b,derivative=1)+(mp.harmonic(N)-mp.harmonic(k))*mp.zeta(N+1,b)))

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--dps',type=int,default=50)
    ap.add_argument('--quick',action='store_true',help='omit the four most expensive EM finite-part quadratures')
    ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'numerical_validation.json')
    args=ap.parse_args()
    if not 35<=args.dps<=60:ap.error('--dps must be in 35..60 for the fixed EM evaluator')
    mp.mp.dps=args.dps
    results=[];start=time.time()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps({'status':'running','working_decimal_precision':args.dps,'checks':[]},indent=2)+'\n')
    def check(name,lhs,rhs,tol,kind='numerical'):
        error=abs(lhs-rhs);passed=error<mp.mpf(tol)
        row={'name':name,'kind':kind,'lhs':mp.nstr(lhs,42),'rhs':mp.nstr(rhs,42),'absolute_error':mp.nstr(error,8),'tolerance':tol,'passed':passed}
        results.append(row);print(name,mp.nstr(error,7),'PASS' if passed else 'FAIL',flush=True)
        if not passed:
            args.output.write_text(json.dumps({'status':'failed','working_decimal_precision':args.dps,'checks':results},indent=2)+'\n')
            raise AssertionError(name)
    tight='1e-'+str(args.dps-10)
    for n in range(4):
        for a in map(mp.mpf,['0.3','1.3','1.9']):check(f'EM gamma_{n}({a})',stieltjes_em(n,a),mp.stieltjes(n,a),tight)
    for s,t,a in [(mp.mpf('-.3'),mp.mpf('-.6'),mp.mpf('.37')),(mp.mpf('.2'),mp.mpf('.3'),mp.mpf('.27'))]:
        check(f'Fourier versus beta {s},{t},{a}',C_poly(s,t,a),C_beta(s,t,a),tight)
        check(f'defining Hurwitz integral {s},{t},{a}',C_integral(s,t,a),C_poly(s,t,a),'1e-28')
    p=poly_half_jets(8)
    for d in range(7):
        for m in range(d+1):
            n=d-m;check(f'independent polylog jet J_{m},{n}(1/2)',p(m,n),eval_expr(correlation(m,n),mp.mpf('.5')),'1e-'+str(args.dps-13))
    for a in map(mp.mpf,['.25','.37','.5']):
        value=gamma_correlation(a)
        check(f'logGamma Hurwitz {a}',value,gamma_hurwitz(a),tight)
        check(f'logGamma polylog {a}',value,gamma_poly(a),tight)
        check(f'logGamma-digamma {a}',gamma_digamma_regularized(a),gamma_digamma_closed(a),tight)
    for r,k in [(2,1),(2,2)]:
        lhs,rhs=higher_lift_test(r,k,mp.mpf('.3'))
        check(f'higher primitive lift {r},{k}',lhs,rhs,tight)
    g=mp.stieltjes(1);e=mp.euler;l2=mp.log(2);l3=mp.log(3)
    for a,value in [(mp.mpf('.5'),2*g-4*e*l2-2*l2*l2-2*mp.zeta(2)),(mp.mpf(1)/3,2*g-3*e*l3-mp.mpf('1.5')*l3*l3-2*mp.zeta(2)),(mp.mpf('.25'),2*g-6*e*l2-7*l2*l2-2*mp.zeta(2))]:
        check(f'rational digamma {a}',eval_expr(correlation(0,0),a),value,tight)
    eps=mp.mpf('1e-18');a=mp.mpf('.3')
    if not args.quick:
        for m,n in [(0,0),(1,0),(1,1),(2,0)]:
            check(f'cutoff finite part J_{m},{n}({a})',j_cutoff(m,n,a,eps),eval_expr(correlation(m,n),a),'1e-13','finite-cutoff diagnostic, epsilon=1e-18')
    for r,k in [(0,1),(1,1)]:check(f'polygamma contact {r},{k}',polygamma_cutoff(r,k,a,eps),polygamma_closed(r,k,a),'1e-13','finite-cutoff diagnostic, epsilon=1e-18')
    out={'working_decimal_precision':args.dps,'python':platform.python_version(),'mpmath':mp.__version__,'sympy':sp.__version__,'elapsed_seconds':round(time.time()-start,3),'status':'all passed','proof_status':'Numerical diagnostics only; analytic proofs are in the article. Cutoff checks retain truncation errors. No interval certification or proof assistant was used.','checks':results}
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(f'{len(results)} checks passed; wrote {args.output}',flush=True)
if __name__=='__main__':main()
