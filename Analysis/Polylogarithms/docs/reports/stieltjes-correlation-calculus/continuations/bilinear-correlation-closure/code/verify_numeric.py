#!/usr/bin/env python3
"""Independent high-precision diagnostics, not interval certificates or proofs."""
from __future__ import annotations
import argparse, json, platform, time
from pathlib import Path
import mpmath as mp


def G(u,x):
    return -mp.digamma(x) if u==0 else mp.zeta(1+u,x)-1/u

def A(u,v):
    return mp.gamma(1+u+v)*mp.gamma(1-v)/mp.gamma(1+u)

def kernel_hurwitz(u,v,a):
    w=u+v
    if w==0: raise ValueError('This numerical evaluator avoids u+v=0; the theorem removes that singularity.')
    return -u*A(u,v)*mp.zeta(1+w,1-a)-v*A(v,u)*mp.zeta(1+w,a)

def kernel_polylog(u,v,a):
    z=mp.exp(2j*mp.pi*a)
    g=lambda x:mp.gamma(1-x)*(2*mp.pi)**x
    return g(u)*g(v)*(mp.exp(0.5j*mp.pi*(u-v))*mp.polylog(-u-v,1/z)+mp.exp(-0.5j*mp.pi*(u-v))*mp.polylog(-u-v,z))

def R_closed(u,v,a):
    if u==0 or v==0: raise ValueError('Use a limiting evaluator on the axes.')
    K=kernel_hurwitz(u,v,a)
    return (K+1+v*G(v,a)+u*G(u,1-a))/(u*v)

def R_quad(u,v,a):
    b=1-a
    first=lambda x:x**(-1-u)*(G(v,a+x)-G(v,a))+G(u,1+x)*G(v,a+x)
    second=lambda y:y**(-1-v)*(G(u,b+y)-G(u,b))+G(v,1+y)*G(u,b+y)
    term=lambda u,c: mp.log(c) if u==0 else -mp.expm1(-u*mp.log(c))/u
    return (mp.quad(first,[0,b])+mp.quad(second,[0,a])+G(v,a)*term(u,b)+G(u,b)*term(v,a))

def fp00_quad(a):
    return R_quad(mp.mpf(0),mp.mpf(0),a)

def corr_quad(s,t,a):
    b=1-a
    return mp.quad(lambda x:mp.zeta(s,x)*mp.zeta(t,a+x),[0,b])+mp.quad(lambda y:mp.zeta(s,b+y)*mp.zeta(t,y),[0,a])

def corr_beta(s,t,a):
    r=s+t-1
    return mp.gamma(r)*(mp.gamma(1-t)/mp.gamma(s)*mp.zeta(r,1-a)+mp.gamma(1-s)/mp.gamma(t)*mp.zeta(r,a))

def logcorr_quad(a):
    b=1-a
    return mp.quad(lambda x:mp.loggamma(x)*mp.loggamma(x+a),[0,b])+mp.quad(lambda y:mp.loggamma(b+y)*mp.loggamma(y),[0,a])

def logcorr_zeta(a):
    f=lambda s:mp.zeta(s,a)+mp.zeta(s,1-a)
    return mp.log(2*mp.pi)**2/4+(1+mp.zeta(2))*(a*a-a+mp.mpf(1)/6)-mp.diff(f,-1)-mp.diff(f,-1,2)/2

def logcorr_polylog(a):
    # Exact cyclotomic decompositions avoid the default polylog order-derivative
    # cancellation canary documented separately for mpmath 1.3.0.
    alpha=mp.euler+mp.log(2*mp.pi)
    if a==mp.mpf(1)/2:
        f=lambda s:(2**(1-s)-1)*mp.zeta(s)
    elif a==mp.mpf(1)/4:
        f=lambda s:2**(-s)*(2**(1-s)-1)*mp.zeta(s)
    else:
        raise ValueError('This independent root-of-unity evaluator supports 1/2 and 1/4.')
    return mp.log(2*mp.pi)**2/4+((alpha**2+mp.pi**2/4)*f(2)-2*alpha*mp.diff(f,2)+mp.diff(f,2,2))/(2*mp.pi**2)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--dps',type=int,default=45)
    p.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'results'/'numeric_verification.json')
    args=p.parse_args()
    if args.dps<30: p.error('--dps must be at least 30')
    mp.mp.dps=args.dps
    checks=[]; start=time.time()
    # Endpoint quadrature has its own loss of accuracy; tolerance is explicit.
    tolerance=mp.mpf(10)**(-min(args.dps-12,30))
    def check(name,lhs,rhs,tol=tolerance):
        e=abs(lhs-rhs); passed=e<=tol*max(1,abs(lhs),abs(rhs))
        checks.append({'name':name,'lhs':mp.nstr(lhs,args.dps),'rhs':mp.nstr(rhs,args.dps),'absolute_residual':mp.nstr(e,10),'relative_tolerance':mp.nstr(tol,8),'passed':bool(passed)})
        print(name,mp.nstr(e,6),'PASS' if passed else 'FAIL',flush=True)
        if not passed: raise AssertionError(name)
    shifts=[mp.mpf(1)/2,mp.mpf(1)/3,mp.mpf(2)/7]
    for a in shifts:
        check(f'FP digamma correlation a={mp.nstr(a,10)}',fp00_quad(a),mp.stieltjes(1,a)+mp.stieltjes(1,1-a)-2*mp.zeta(2))
    for s,t,a in [(mp.mpf('-.3'),mp.mpf('-.4'),mp.mpf('.3')),(mp.mpc('-.2','.11'),mp.mpf('-.15'),mp.mpf('.4'))]:
        check(f'ordinary Hurwitz correlation s={s},t={t}',corr_quad(s,t,a),corr_beta(s,t,a))
    for u,v,a in [(mp.mpf('-.13'),mp.mpf('-.19'),mp.mpf('0.3')),(mp.mpc('-.12','.04'),mp.mpc('-.17','-.03'),mp.mpf('.5'))]:
        check(f'polylog/Hurwitz kernel u={u},v={v}',kernel_polylog(u,v,a),kernel_hurwitz(u,v,a))
        check(f'regularized generating integral u={u},v={v}',R_quad(u,v,a),R_closed(u,v,a))
    for a in [mp.mpf(1)/2,mp.mpf(1)/4]:
        q=logcorr_quad(a)
        check(f'logGamma autocorrelation/zeta a={a}',q,logcorr_zeta(a))
        check(f'logGamma autocorrelation/polylog a={a}',q,logcorr_polylog(a))
    # Coincident singularities require an additional x^-2 subtraction.
    def reg(x):
        h=mp.digamma(1+x)
        return h*h-2*(h+mp.euler)/x
    check('coincident FP digamma square',mp.quad(reg,[0,1])-1,2*mp.stieltjes(1)-2*mp.zeta(2))
    q=5; ell=mp.log(q)
    vals=sum(mp.stieltjes(1,mp.mpf(r)/q)+mp.stieltjes(1,1-mp.mpf(r)/q)-2*mp.zeta(2) for r in range(1,q))
    check('rational-grid trace q=5',vals,2*(q-1)*(mp.stieltjes(1)-mp.zeta(2))-2*q*mp.euler*ell-q*ell**2)
    ell=mp.log(2); Z1=mp.diff(mp.zeta,-1); Z2=mp.diff(mp.zeta,-1,2); L=mp.log(2*mp.pi)
    check('half-shift closed zeta jets',logcorr_zeta(mp.mpf(1)/2),L**2/4+(1-ell)*Z1+Z2/2+(ell-1-mp.zeta(2))/12+ell**2/24)
    check('quarter-shift closed zeta jets',logcorr_zeta(mp.mpf(1)/4),L**2/4+Z1/4+Z2/8+(ell**2-1-mp.zeta(2))/48)
    a=mp.mpf('0.37')
    primitive=lambda x:(mp.diff(lambda s:mp.zeta(s,x),0,2)-mp.diff(lambda s:mp.zeta(s,1-x),0,2))/2-2*mp.zeta(2)*x
    check('antiderivative of I00',mp.diff(primitive,a),mp.stieltjes(1,a)+mp.stieltjes(1,1-a)-2*mp.zeta(2))
    # Negative control: omitting the finite-part constant is mathematically wrong.
    control=abs(fp00_quad(mp.mpf(1)/2)-2*mp.stieltjes(1,mp.mpf(1)/2))
    check('negative control discrepancy is exactly 2*zeta(2)',control,2*mp.zeta(2))
    result={'status':'PASS','dps':args.dps,'number_of_checks':len(checks),'elapsed_seconds':round(time.time()-start,3),'python':platform.python_version(),'mpmath':mp.__version__,'scope':'Non-rigorous high-precision diagnostics; not interval bounds or proof-assistant verification.','checks':checks}
    args.output.parent.mkdir(parents=True,exist_ok=True); args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='checks'},indent=2))

if __name__=='__main__': main()
