"""Independent quadrature checks. These checks are NOT proofs of identities."""
from __future__ import annotations
import json, platform
from pathlib import Path
from fractions import Fraction
import mpmath as mp
import sympy
from gap_reduce import (mixed_integral,one_variable_integral,correction,
                        double_coefficients,parity_component)
ROOT=Path(__file__).resolve().parents[1]

def fmp(x): return mp.mpf(x[0])/mp.mpf(x[1])

def run():
    mp.mp.dps=85
    results=[]
    for root,z in [('i',mp.j),('rho',mp.exp(2*mp.pi*mp.j/3))]:
        for a in range(1,6):
            b=6-a
            lhs=mp.im(one_variable_integral(a,b,z))
            rhs=parity_component(a,b,lambda n:mp.polylog(n,z),mp.zeta,mp.conj,mp.im)
            err=abs(lhs-rhs)
            assert err<mp.mpf('1e-75'),(root,a,b,err)
            results.append({'test':'weight-six-parity','root':root,'a':a,'b':b,'residual':mp.nstr(err,10)})
            print(root,a,b,'residual',mp.nstr(err,6),flush=True)
    # Odd-weight real projection and nonspecial circle arguments.
    mp.mp.dps=65
    for a,b in [(1,2),(2,1),(2,3),(4,1),(3,3),(2,4)]:
        z=mp.exp(mp.j*mp.mpf('0.7'))
        project=mp.im if (a+b)%2==0 else mp.re
        lhs=project(one_variable_integral(a,b,z))
        rhs=parity_component(a,b,lambda n:mp.polylog(n,z),mp.zeta,mp.conj,project)
        err=abs(lhs-rhs); assert err<mp.mpf('1e-55')
        results.append({'test':'generic-circle-parity','a':a,'b':b,'theta':'0.7','residual':mp.nstr(err,10)})
    # All-circle depth-one b=1 formula at a non-special point.
    z=mp.exp(mp.j*mp.mpf('1.2'))
    for m in range(5):
        a=2*m+1; w=a+1
        rhs=(m+1)*mp.im(mp.polylog(w,z))-mp.log(abs(1-z))*mp.im(mp.polylog(a,z))
        rhs-=sum(mp.zeta(2*j)*mp.im(mp.polylog(w-2*j,z)) for j in range(1,m+1))
        err=abs(mp.im(mixed_integral(a,1,z))-rhs)
        assert err<mp.mpf('1e-55')
        results.append({'test':'all-circle-odd-first-index','m':m,'theta':'1.2','residual':mp.nstr(err,10)})
    # Real-projection all-angle families at odd total weight.
    for m in range(1,5):
        a=2*m; w=a+1
        li=lambda n:mp.polylog(n,z)
        rhs_f=(a-1)*mp.re(li(w))/2+mp.zeta(w)/2-mp.im(li(a))*mp.im(li(1))
        rhs_f-=sum(mp.zeta(2*j+1)*mp.re(li(a-2*j)) for j in range(1,m))
        rhs_d=(a+1)*mp.re(li(w))/2-mp.zeta(w)/2-mp.log(abs(1-z))*mp.re(li(a))
        rhs_d-=sum(mp.zeta(2*j)*mp.re(li(w-2*j)) for j in range(1,m+1))
        for family,lhs,rhs in [('F',mp.re(one_variable_integral(a,1,z)),rhs_f),
                               ('D',mp.re(mixed_integral(a,1,z)),rhs_d)]:
            err=abs(lhs-rhs); assert err<mp.mpf('1e-55')
            results.append({'test':'all-circle-even-first-index','family':family,'m':m,'theta':'1.2','residual':mp.nstr(err,10)})
    for root,z in [('i',mp.j),('rho',mp.exp(2*mp.pi*mp.j/3))]:
        pi=mp.pi; z3=mp.zeta(3); z5=mp.zeta(5); c4=mp.im(mp.polylog(4,z))
        if root=='i':
            rf=-pi*c4/4+pi**2*z3/48+mp.mpf(467)*z5/1024
            rd=3*pi**4*mp.log(2)/512+pi**2*z3/64-mp.mpf(587)*z5/1024
        else:
            rf=-pi*c4/6-mp.mpf(13)*z5/54+pi**2*z3/18
            rd=2*pi**4*mp.log(3)/243+2*pi**2*z3/27-mp.mpf(281)*z5/162
        for family,lhs,rhs in [('F',mp.re(one_variable_integral(4,1,z)),rf),
                               ('D',mp.re(mixed_integral(4,1,z)),rd)]:
            err=abs(lhs-rhs); assert err<mp.mpf('1e-55')
            results.append({'test':'explicit-real-target','family':family,'root':root,'residual':mp.nstr(err,10)})
    mp.mp.dps=115
    certs=json.loads((ROOT/'verification'/'rational_certificates.json').read_text())['certificates']
    for c in certs:
        z=mp.j if c['root']=='i' else mp.exp(-2*mp.pi*mp.j/3)
        value=mixed_integral(c['a'],c['b'],z)
        for comp,v in [('real',mp.re(value)),('imag',mp.im(value))]:
            lo=fmp(c[comp]['lo']);hi=fmp(c[comp]['hi'])
            assert lo<=v<=hi,(c['root'],c['a'],comp)
        results.append({'test':'quadrature-inside-rational-certificate','a':c['a'],'b':c['b'],'root':c['root'],
                        'real':mp.nstr(mp.re(value),95),'imag':mp.nstr(mp.im(value),95)})
    record={'python':platform.python_version(),'mpmath':mp.__version__,'sympy':sympy.__version__,
            'status':'quadrature cross-checks, not interval proofs','checks':results}
    (ROOT/'verification'/'numerical_checks.json').write_text(json.dumps(record,indent=2)+'\n')
    print('Passed',len(results),'independent quadrature checks.')

if __name__=='__main__':run()
