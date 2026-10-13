"""Finite exact diagnostics and independent Laplace checks for confluent Euler filters.

The all-order theorem is in confluent-euler.tex. Numerical integrations here
are precision-refined diagnostics, not interval certificates or proofs.
No supplied near-zero tail coefficient is silently discarded.
"""
from pathlib import Path
from math import factorial
import json
import platform
import argparse
import hashlib
import sys
import sympy as s
import mpmath as mp

HERE=Path(__file__).resolve().parent


def require(condition,message):
    if not bool(condition): raise ValueError(message)


def exact_checks():
    x,v,h=s.symbols('x v h',positive=True)
    psi=s.Function('psi'); gamma=s.Function('gamma1')
    L=s.log(x); C=L**2/2-psi(x+1)*L-gamma(x+1)
    explicit=3*L**2+5*L+1-(6*L+5)*psi(x+1)-(6*L+2)*x*s.diff(psi(x+1),x)-L*x*x*s.diff(psi(x+1),x,2)-6*gamma(x+1)-6*x*s.diff(gamma(x+1),x)-x*x*s.diff(gamma(x+1),x,2)
    rows=[]
    def check(name,cond):
        require(cond,name); rows.append({'name':name,'pass':True})
    check('Explicit gamma1 differential expression',s.simplify(x*x*s.diff(C,x,2)+6*x*s.diff(C,x)+6*C-explicit)==0)
    G=s.log(x)-psi(x+1)
    K=2*psi(x+1)+4*x*s.diff(psi(x+1),x)+x*x*s.diff(psi(x+1),x,2)-2*s.log(x)-3
    check('Explicit positive digamma expression',s.simplify(-x*x*s.diff(G,x,2)-4*x*s.diff(G,x)-2*G-K)==0)
    for q in range(5):
        for r in range(1,6):
            symbol=s.prod(v+q+j+1 for j in range(r))
            leibniz=sum(s.binomial(r,j)*s.rf(q+j+1,r-j)*s.ff(v,j) for j in range(r+1))
            check(f'Leibniz versus Euler polynomial q={q},r={r}',s.expand(symbol-leibniz)==0)
            for j in range(r):
                k=q+j; d=r-1-j
                poly=s.Poly(s.prod(ell-k-h for ell in range(q,q+r)),h)
                W=(-1)**(j+1)*factorial(j)*factorial(d)
                check(f'Integer zero and first two germ coefficients q={q},r={r},j={j}',poly.nth(0)==0 and poly.nth(1)==W and poly.nth(2)==-W*(s.harmonic(d)-s.harmonic(j)))
    for n in range(2,25):
        lhs=3**(2*n+1)-3; rhs=4*(2*n+1)*(2*n)*(2*n-1)
        check(f'Classical positivity coefficient n={n}',lhs==rhs if n==2 else lhs>rhs)
    for q,r,k,expected in [(0,2,0,-s.Rational(1,2)),(0,2,1,-s.Rational(1,12)),(1,2,1,s.Rational(1,12)),(1,2,2,0)]:
        z=s.symbols('z'); Q=s.factorial(q)*s.Poly(s.prod(1+z/s.Integer(n) for n in range(1,k+1)),z).nth(q)
        j=k-q; d=r-1-j
        value=(-1)**(q+1)*factorial(j)*factorial(d)*Q*s.bernoulli(k+1,1)/(k+1)
        check(f'Bernoulli moment q={q},r={r},k={k}',value==expected)
    return rows


def corruption_controls():
    """Each alteration is sent through the same equality gate as a valid formula."""
    x,v,h=s.symbols('x v h',positive=True)
    psi=s.Function('psi'); gamma=s.Function('gamma1'); L=s.log(x)
    C=L**2/2-psi(x+1)*L-gamma(x+1)
    correct=x*x*s.diff(C,x,2)+6*x*s.diff(C,x)+6*C
    bad_gamma=correct+gamma(x+1)  # Replace the -6 gamma1 coefficient by -5.
    tests=[('gamma1 coefficient changed from -6 to -5',s.simplify(correct-bad_gamma)==0),
           ('Euler weight shifted down by one',s.expand((v+2)*(v+3)-(v+1)*(v+2))==0)]
    # For q=1,r=3,j=0, A(2+h)=-h(1-h)(2-h): coefficient h^2 is +3.
    poly=s.Poly(-h*(1-h)*(2-h),h)
    wrong_second=-2*(s.harmonic(2)-s.harmonic(0))
    tests.append(('harmonic correction sign reversed',poly.nth(2)==wrong_second))
    # Reconstruct the actual density before its indispensable +1 subtraction.
    g=1/(s.exp(h)-1)-1/h
    raw_density=2*g-2*h*s.diff(g,h)+h*h*s.diff(g,h,2)
    tests.append(('signed-density origin subtraction omitted',s.limit(raw_density,h,0)==0))
    rows=[]
    for name,equality in tests:
        try:
            require(equality,name)
        except ValueError:
            rows.append({'name':name,'rejected':True})
        else:
            raise ValueError('Corruption was accepted: '+name)
    return rows


def run_numerics(dps):
    mp.mp.dps=dps
    rows=[]
    tolerance=mp.mpf('1e-32')
    nterms=dps//3+10
    mu_coeff=[]; nu_coeff=[]
    for n in range(2,nterms+1):
        p=2*n-1; base=mp.bernoulli(2*n)/mp.factorial(2*n)
        mu_coeff.append((p,-base*p*(p-1)))
        nu_coeff.append((p,base*(p-1)*(p-2)))

    def mu(t):
        if not t:return mp.mpf(0)
        if t<mp.mpf('0.125'):return mp.fsum(c*t**p for p,c in mu_coeff)
        e=mp.exp(-t); d=-mp.expm1(-t)
        return 2/t-t*t*e*(1+e)/d**3

    def nu(t):
        if not t:return mp.mpf(0)
        if t<mp.mpf('0.125'):return mp.fsum(c*t**p for p,c in nu_coeff)
        e=mp.exp(-t); d=-mp.expm1(-t)
        return 1+2*e/d+2*t*e/d**2+t*t*e*(1+e)/d**3-6/t

    def quad(f):return mp.quad(f,[0,mp.mpf('0.125'),1,5,mp.inf])

    def record(name,lhs,rhs):
        error=abs(lhs-rhs)
        rows.append({'name':name,'lhs':mp.nstr(lhs,dps),'rhs':mp.nstr(rhs,dps),'absolute_error':mp.nstr(error,12),'pass':bool(error<tolerance)})
        print(name,dps,mp.nstr(error,8),flush=True)

    for k,rhs in [(0,mp.mpf(1)/2),(1,mp.mpf(1)/12),(2,mp.zeta(3)/(2*mp.pi**2))]:
        record(f'K moment x^{k} from positive density',mp.factorial(k)*quad(lambda t:mu(t)/t**(k+1) if t else mp.mpf(0)),rhs)
    for k,rhs in [(0,-(1+mp.log(2*mp.pi))/2),(1,mp.diff(mp.zeta,-1)+mp.mpf(1)/12)]:
        record(f'K logarithmic moment x^{k}',mp.factorial(k)*quad(lambda t:mu(t)/t**(k+1)*(mp.digamma(k+1)-mp.log(t)) if t else mp.mpf(0)),rhs)
    for u,rhs in [(2,mp.mpf(1)/12),(3,mp.mpf(0))]:
        factor=mp.gamma(u)*(mp.digamma(u)+mp.euler)
        record(f'W moment x^{u-1} from signed density',factor*quad(lambda t:nu(t)/t**u if t else mp.mpf(0)),rhs)
    record('W logarithmic moment x^2',-3*quad(lambda t:nu(t)*mp.log(t)/t**3 if t else mp.mpf(0)),-3*mp.zeta(3)/(8*mp.pi**2))

    def Kdirect(x):
        return 2*mp.digamma(x+1)+4*x*mp.polygamma(1,x+1)+x*x*mp.polygamma(2,x+1)-2*mp.log(x)-3
    def Wdirect(x):
        v=x+1; L=mp.log(x)
        g=mp.stieltjes(1,v)
        gp=mp.diff(lambda z:mp.zeta(z,v),2)+mp.zeta(2,v)
        gpp=-2*mp.diff(lambda z:mp.zeta(z,v),3)-3*mp.zeta(3,v)
        return 3*L*L+5*L+1-(6*L+5)*mp.digamma(v)-(6*L+2)*x*mp.polygamma(1,v)-L*x*x*mp.polygamma(2,v)-6*g-6*x*gp-x*x*gpp
    for x in (mp.mpf(1)/3,mp.mpf(2)):
        record(f'K direct versus Laplace at x={x}',Kdirect(x),quad(lambda t:mp.exp(-x*t)*mu(t)))
        record(f'W generalized Stieltjes versus Laplace at x={x}',Wdirect(x),quad(lambda t:mp.exp(-x*t)*nu(t)*(mp.log(x*t)+mp.euler) if t else mp.mpf(0)))

    # This checks normalized finite dilations against their limiting Euler
    # expressions at a fixed point; errors are expected O(epsilon), not zero.
    x=mp.mpf(4)/3
    C0=lambda y:mp.log(y)-mp.digamma(y+1)
    C1=lambda y:mp.log(y)**2/2-mp.digamma(y+1)*mp.log(y)-mp.stieltjes(1,y+1)
    confluence=[]
    for q,C,target in [(0,C0,-Kdirect(x)),(1,C1,Wdirect(x))]:
        errors=[]
        for power in (8,12,16):
            eps=mp.mpf(2)**(-power); lam=mp.exp(eps)
            # Coefficients of (1-lambda^-q y)(1-lambda^-(q+1)y).
            coeff=[1,-lam**(-q)-lam**(-q-1),lam**(-2*q-1)]
            value=mp.fsum(coeff[j]*lam**(-j)*C(x/lam**j) for j in range(3))/eps**2
            err=abs(value-target); errors.append(err)
            confluence.append({'q':q,'r':2,'epsilon':str(eps),'absolute_error':mp.nstr(err,12)})
        require(errors[1]<errors[0]/8 and errors[2]<errors[1]/8,'Confluent error failed first-order refinement')
    require(all(row['pass'] for row in rows),'Numerical diagnostic tolerance failure')
    return {'precision':dps,'threshold':str(tolerance),'records':rows,'confluent_refinement':confluence,'status':'PASS'}


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exact-only',action='store_true')
    parser.add_argument('--output',type=Path,default=HERE/'confluent-euler-checks.json')
    args=parser.parse_args(argv)
    source=Path(__file__).read_bytes().replace(b'\r\n',b'\n').replace(b'\r',b'\n')
    out={'status':'RUNNING','python':platform.python_version(),'sympy':s.__version__,'mpmath':mp.__version__,
         'optimization_level':sys.flags.optimize,
         'digest_mode':'UTF-8 source bytes with CRLF and CR normalized to LF',
         'runner_sha256':hashlib.sha256(source).hexdigest(),
         'mode':'exact-only' if args.exact_only else 'exact-and-numerical',
         'evidence':'Finite exact diagnostics and noninterval precision-refined Laplace quadratures; proofs are in confluent-euler.tex.',
         'exact_checks':[],'corruption_controls':[],'numerical_runs':[]}
    path=args.output
    # Invalidate any previous PASS before running checks or quadratures.
    path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    try:
        out['exact_checks']=exact_checks()
        out['corruption_controls']=corruption_controls()
        for dps in (() if args.exact_only else (45,65)):
            out['numerical_runs'].append(run_numerics(dps))
            path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
        out['status']='PASS'
        out['exact_check_count']=len(out['exact_checks'])
        out['corruption_control_count']=len(out['corruption_controls'])
        out['numerical_check_count']=sum(len(run['records']) for run in out['numerical_runs'])
        path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
        print('PASS:',out['exact_check_count'],'finite exact checks,',out['corruption_control_count'],'corruption controls and',out['numerical_check_count'],'numerical checks',flush=True)
    except Exception as exc:
        out.update(status='FAIL',error=f'{type(exc).__name__}: {exc}')
        path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
        raise


if __name__=='__main__':
    main()
