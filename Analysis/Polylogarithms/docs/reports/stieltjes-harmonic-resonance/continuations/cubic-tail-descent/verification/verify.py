#!/usr/bin/env python3
"""Exact coefficient checks and independent numerical diagnostics.
The analytic proofs are in article.tex. Floating-point tests are not proofs.
Run: python verification/verify.py [--exact-only] [--numeric-only] [--dps 50]
"""
from __future__ import annotations
import argparse, itertools, json, math, platform, time
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import mpmath as mp
import sympy as sp

OUT = Path(__file__).resolve().parent
S, V = sp.symbols('sigma tau')

def t(k: int):
    return sp.Symbol(f'T{k}')

def make_coefficients(A: int, D: int):
    P = {(a, 0): sp.Integer(int(a == 0)) for a in range(A + 1)}
    for d in range(1, D + 1):
        for a in range(A + 1):
            P[a,d] = sp.expand(sum(2*sp.binomial(i+b-1,i)*t(2*i+3*b)*P[a-i,d-b]
                for b in range(1,d+1,2) for i in range(a+1))/d)
    return P

def conv(a: int, d: int):
    if d == 0:
        return sp.Integer(a == 0)
    return sp.expand(sum(t(2*i+3)*conv(a-i,d-1) for i in range(a+1)))

def partitions(labels):
    """Every ordered set partition, generated independently of stuffles."""
    if not labels:
        yield ()
        return
    first, *rest = labels
    for pp in partitions(rest):
        for j in range(len(pp)):
            yield pp[:j] + ((first,) + pp[j],) + pp[j+1:]
        for j in range(len(pp)+1):
            yield pp[:j] + ((first,),) + pp[j:]

def mzv_finite(indices, N):
    total = Fraction(0)
    for inc in itertools.combinations(range(1,N+1),len(indices)):
        ns = inc[::-1]
        total += math.prod(Fraction(1,n**s) for n,s in zip(ns,indices))
    return total

def exact_suite():
    checks=[]
    def chk(name, condition):
        if not bool(condition):
            raise AssertionError(name)
        checks.append(name)
    A,D = 4,8
    P=make_coefficients(A,D)
    # Independent exponential: ordinary powers of the logarithm, convolved in a,d.
    L={(a,b): 2*sp.binomial(a+b-1,a)*t(2*a+3*b)/b
       for a in range(A+1) for b in range(1,D+1,2)}
    powers={(0,0):sp.Integer(1)}
    E=defaultdict(lambda:sp.Integer(0)); E[0,0]=1
    for k in range(1,D+1):
        nxt=defaultdict(lambda:sp.Integer(0))
        for (a,d),val in powers.items():
            for (b,e),v in L.items():
                if a+b<=A and d+e<=D:
                    nxt[a+b,d+e] += val*v
        powers={key:sp.expand(val) for key,val in nxt.items()}
        for key,val in powers.items(): E[key]+=val/sp.factorial(k)
    for a in range(A+1):
        for d in range(D+1):
            chk(f'exp_vs_recurrence_{a}_{d}',sp.expand(P[a,d]-E[a,d])==0)
            if d>=2:
                R=sp.expand(P[a,d]-sp.Rational(2**d,math.factorial(d))*conv(a,d))
                terms=sp.Poly(R,*sorted(R.free_symbols,key=str)).terms() if R!=0 else []
                chk(f'depth_drop_{a}_{d}',all(sum(mon)<=d-2 and sum(mon)%2==d%2 for mon,c in terms))
                for term in sp.Add.make_args(P[a,d]):
                    powers_dict=term.as_powers_dict()
                    wt=sum(int(str(atom)[1:])*int(exp) for atom,exp in powers_dict.items() if str(atom).startswith('T'))
                    chk(f'homogeneous_{a}_{d}_{len(checks)}',wt==2*a+3*d)
    # Newton recurrence versus closed invariant coefficients.
    N={0:sp.Integer(3),1:sp.Integer(0),2:2*S}
    for k in range(3,31): N[k]=sp.expand(S*N[k-2]-V*N[k-3])
    for k in range(2,31):
        formula=sum(sp.Rational(k,a+b)*sp.binomial(a+b,b)*(-1)**b*S**a*V**b
                    for b in range(k//3+1) for a in range(k//2+1) if 2*a+3*b==k)
        chk(f'newton_{k}',sp.expand(N[k]-formula)==0)
    # Harmonic elementary coefficients against Pochhammer derivatives.
    u=sp.Symbol('u')
    for k in range(1,21):
        elem=[sp.Integer(1)]+[sp.Integer(0)]*5
        for j in range(1,k+1):
            for r in range(5,0,-1): elem[r]+=elem[r-1]/j
        pp=sp.Poly(sp.prod(1+u/sp.Integer(j) for j in range(1,k+1)),u)
        for r in range(6): chk(f'harmonic_bell_{k}_{r}',elem[r]==pp.nth(r))
    # A finite, exact minimum-square/ordered-partition audit.
    examples=[(3,3),(3,5),(3,3,3),(3,3,5),(3,3,3,3),(3,5,7)]
    for inds in examples:
        for Nmax in (3,5):
            left=sum(Fraction(2*n+1)*math.prod(sum(Fraction(1,j**s) for j in range(n+1,Nmax+1)) for s in inds)
                     for n in range(Nmax))
            right=Fraction(0)
            for pp in partitions(list(range(len(inds)))):
                ks=[sum(inds[j] for j in block) for block in pp]; ks[-1]-=2
                right+=mzv_finite(ks,Nmax)
            chk(f'finite_minimum_square_{inds}_{Nmax}',left==right)
    # Explicit low-degree polynomials, including quartic and quintic laws.
    explicit={
      (0,2):2*t(3)**2,
      (0,3):sp.Rational(4,3)*t(3)**3+sp.Rational(2,3)*t(9),
      (0,4):sp.Rational(2,3)*t(3)**4+sp.Rational(4,3)*t(3)*t(9),
      (0,5):sp.Rational(4,15)*t(3)**5+sp.Rational(4,3)*t(3)**2*t(9)+sp.Rational(2,5)*t(15)}
    for key,val in explicit.items(): chk(f'printed_polynomial_{key}',P[key]==val)
    # Centered Bernoulli calculation used in the Dougall proof.
    p,q=sp.symbols('p q'); x=sp.Rational(1,2)
    c1=-sum(sp.bernoulli(3,z) for z in (x,x+p,x+q,x-p-q))/3
    chk('dougall_centered_C1',sp.expand(c1-p*q*(p+q))==0)
    chk('dougall_bernoulli_constant',sp.expand(sp.bernoulli(2,x-p-q)/2+sp.Rational(1,24)-(p+q)**2/2)==0)
    # Removability of all tested anchored negative-order traces.
    h,h0=sp.symbols('h h0')
    for r in range(1,9):
        # Sum of Bernoulli polynomials, using Newton's power sums (sum roots = 0).
        ztrace=-sum(sp.binomial(r,k)*sp.bernoulli(r-k,h)*N[k] for k in range(1,r+1))/r
        rem=sp.expand(ztrace-sum((h-h0)**j/sp.factorial(j)*sp.diff(ztrace,h,j).subs(h,h0) for j in range(r)))
        chk(f'primitive_removable_r{r}',rem==0)
    # Refute the tempting extrapolation using exact rational estimates, not floats.
    h4=sum(Fraction(1,j**3) for j in range(1,5))
    upper=Fraction(15,8)*(1+Fraction(1,2**10)+Fraction(1,9*2**9))
    chk('naive_all_power_extrapolation_false',h4**4>upper)
    catalog=[]
    for a in range(A+1):
        for d in range(2,D+1):
            C=sp.Rational(2*a+3*d-3,a+d-1)*sp.binomial(a+d-1,d-1)
            catalog.append({'a':a,'d':d,'weight':2*a+3*d-2,'polynomial':str(P[a,d]),
                            'zeta_coefficient':str(C),'depth_bound':max(1,d-2)})
    (OUT/'coefficient_catalog.json').write_text(json.dumps(catalog,indent=2)+'\n')
    return {'count':len(checks),'passed':checks,'catalog_size':len(catalog)}

def numeric_suite(dps):
    mp.mp.dps=dps
    rows=[]
    def check(name,left,right,tolerance='1e-27'):
        err=abs(left-right); scaled=err/max(1,abs(left),abs(right))
        ok=scaled<mp.mpf(tolerance)
        rows.append({'name':name,'left':mp.nstr(left,dps),'right':mp.nstr(right,dps),
          'absolute_residual':mp.nstr(err,12),'scaled_residual':mp.nstr(scaled,12),
          'tolerance':tolerance,'passed':bool(ok)})
        if not ok: raise AssertionError(rows[-1])
    def tail(s,n): return mp.zeta(s,n+1)
    def moment(inds): return mp.nsum(lambda n:(2*n+1)*mp.fprod(tail(s,n) for s in inds),[0,mp.inf])
    for a in range(4):
        L=mp.fsum(moment((2*j+3,2*(a-j)+3)) for j in range(a+1))
        check(f'quadratic_a{a}',L,mp.mpf(2*a+3)/2*mp.zeta(2*a+4))
    for a in range(3):
        L=mp.fsum(moment((2*i+3,2*j+3,2*(a-i-j)+3)) for i in range(a+1) for j in range(a-i+1))
        check(f'cubic_a{a}',L,mp.mpf((a+1)*(2*a+7))/4*mp.zeta(2*a+7))
    z73=mp.quad(lambda z:mp.log(z)**6*mp.polylog(3,z)/(1-z),[0,mp.mpf('.5'),1])/mp.factorial(6)
    check('quartic_depth_two',moment((3,3,3,3)),mp.zeta(10)+mp.zeta(5)**2+2*z73)
    check('quintic_depth_descent',moment((3,3,3,3,3))+5*moment((3,3,9)),mp.mpf(39)/4*mp.zeta(13))
    def A(n,x): return (2*mp.digamma(n+1)-mp.digamma(n+1-x)-mp.digamma(n+1+x))/(2*x*x)
    for x in (mp.mpf('.3'),mp.mpf('.5'),mp.mpf('1.3'),mp.mpc('.2','.15')):
        J=mp.digamma(1+x)+mp.digamma(1-x)-2*mp.digamma(1)
        Jp=mp.polygamma(1,1+x)-mp.polygamma(1,1-x)
        Jpp=mp.polygamma(2,1+x)+mp.polygamma(2,1-x)
        square=mp.pi**2/(4*x*x*mp.sin(mp.pi*x)**2)-mp.zeta(2)/(2*x*x)-1/(4*x**4)
        cube=J/(4*x**6)+Jp/(8*x**5)-Jpp/(16*x**4)+3*mp.zeta(3)/(4*x**4)
        check(f'digamma_square_{x}',mp.nsum(lambda n:(2*n+1)*A(n,x)**2,[0,mp.inf]),square)
        check(f'digamma_cube_{x}',mp.nsum(lambda n:(2*n+1)*A(n,x)**3,[0,mp.inf]),cube)
    # Direct integral representation of the harmonic-log tail, with no H_{2n} subtraction.
    def R(n): return (mp.digamma(n+1)-mp.digamma(n+mp.mpf('.5')))-1/(2*n+1)
    check('half_shift_harmonic_square',mp.nsum(lambda n:(2*n+1)*R(n)**2,[0,mp.inf]),(mp.zeta(2)-1)/4)
    check('half_shift_harmonic_cube',mp.nsum(lambda n:(2*n+1)*R(n)**3,[0,mp.inf]),5*mp.zeta(3)/8-mp.log(2))
    # The full Gamma master at small nonzero parameters, evaluated independently.
    for p,q in ((mp.mpf('.07'),mp.mpf('.03')),(mp.mpf('.12'),mp.mpf('-.04'))):
        rs=(p,q,-p-q); tau=p*q*(p+q)
        def bracket(n):
            x=n+mp.mpf('.5')
            logQ=mp.fsum(mp.loggamma(n+1+r)-mp.loggamma(n+1-r) for r in rs)
            return x*mp.expm1(logQ)-tau/x
        L=mp.nsum(bracket,[0,mp.inf])
        Rhs=tau*(mp.digamma(mp.mpf('.5'))+(mp.digamma(2)-sum(mp.digamma(1+r) for r in rs))/2)
        check(f'gamma_master_{p}_{q}',L,Rhs,'1e-25')
    # Coefficient trace versus the defining, real-argument Stieltjes constants.
    p=q=mp.mpf('.05'); rs=(p,q,-p-q); sig=p*p+p*q+q*q; tau=p*q*(p+q)
    h=mp.mpf('1.1')
    cache={}
    for k in range(2,34):
        cache[k]=[mp.diff(lambda s:mp.zeta(s,h),k+1,m) for m in range(3)]
    for m in range(3):
        acc=mp.mpf('0')
        for k in range(2,34):
            E=[mp.mpf(1)]+[mp.mpf(0)]*m
            for j in range(1,k+1):
                for r in range(m,0,-1): E[r]+=E[r-1]/j
            jet=mp.fsum(mp.binomial(m,ell)*mp.factorial(ell)*E[ell]*cache[k][m-ell] for ell in range(m+1))
            for b in range(k//3+1):
                if (k-3*b)%2: continue
                a=(k-3*b)//2
                acc+=mp.mpf(k)/(a+b)*mp.binomial(a+b,b)*sig**a*tau**b*jet
        direct=mp.fsum(mp.stieltjes(m,h+r) for r in rs)-3*mp.stieltjes(m,h)
        check(f'stieltjes_trace_m{m}_double_root',direct,(-1)**m*acc,'1e-26')
    # All-order primitive at r=1,m=0 and r=2,m=0, independently integrated.
    h0=mp.mpf('1.05'); h1=mp.mpf('1.35')
    delta0=lambda h: -sum(mp.digamma(h+r) for r in rs)+3*mp.digamma(h)
    logD=lambda h: sum(mp.loggamma(h+r) for r in rs)-3*mp.loggamma(h)
    check('anchored_first_gamma_primitive',mp.quad(delta0,[h0,h1]),logD(h0)-logD(h1))
    Z=lambda s,h:sum(mp.zeta(s,h+r) for r in rs)-3*mp.zeta(s,h)
    Zprime0=lambda h:mp.diff(lambda s:Z(s,h),0)
    # At r=2: N'_0 = Z'(-1,h1)-Z'(-1,h0) -(h1-h0)*(Z'(0,h0)-Z(0,h0)).
    # d_h Z(s,h)=-s Z(s+1,h), hence at s=-1 its s derivative is Z'(0,h)-Z(0,h).
    Nprime=mp.diff(lambda s:Z(s,h1),-1)-mp.diff(lambda s:Z(s,h0),-1)-(h1-h0)*Zprime0(h0)
    check('anchored_second_gamma_primitive',mp.quad(lambda h:(h1-h)*delta0(h),[h0,h1]),-Nprime)
    # Multiple-polylogarithm primitive by finite, fast geometric series versus quadrature.
    def li2(r,q,z):
        H=mp.mpf('0'); terms=[]
        for n in range(1,230):
            terms.append(z**n*H/n**r); H+=mp.mpf(1)/n**q
        return mp.fsum(terms)
    z=mp.mpf('.4')
    for m in range(5):
        rhs=mp.fsum(mp.factorial(m)/mp.factorial(m-j)*(-mp.log(z))**(m-j)*li2(j+1,3,z) for j in range(m+1))
        lhs=mp.quad(lambda x:(-mp.log(x))**m*mp.polylog(3,x)/(1-x),[0,z])
        check(f'polylog_primitive_m{m}',lhs,rhs)
    return {'working_decimal_digits':dps,'count':len(rows),'checks':rows}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--exact-only',action='store_true')
    parser.add_argument('--numeric-only',action='store_true')
    parser.add_argument('--dps',type=int,default=50)
    args=parser.parse_args()
    if args.exact_only and args.numeric_only: parser.error('choose at most one mode')
    if args.dps<35: parser.error('--dps must be at least 35')
    result={'python':platform.python_version(),'sympy':sp.__version__,'mpmath':mp.__version__,
            'status':'diagnostics_and_finite_exact_checks_not_analytic_proof'}
    start=time.time()
    if not args.numeric_only:
        result['exact']=exact_suite(); print('Exact checks:',result['exact']['count'],flush=True)
    if not args.exact_only:
        result['numeric']=numeric_suite(args.dps); print('Numerical checks:',result['numeric']['count'],flush=True)
    result['elapsed_seconds']=round(time.time()-start,3)
    target=OUT/('exact_results.json' if args.exact_only else 'numeric_results.json' if args.numeric_only else 'verification_results.json')
    target.write_text(json.dumps(result,indent=2)+'\n'); print(target,flush=True)
if __name__=='__main__': main()
