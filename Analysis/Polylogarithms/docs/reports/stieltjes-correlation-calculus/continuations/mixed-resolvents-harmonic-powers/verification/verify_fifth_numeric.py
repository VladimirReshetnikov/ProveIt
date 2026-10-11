"""Two independent floating-point diagnostics of the fifth bridge.

No interval certification is claimed. The first method integrates a
local convergent digamma Taylor series and an ordinary integral. The
second evaluates the subtracted polygamma series, summing a truncated
asymptotic tail by Hurwitz-zeta derivatives. The analytic proof does
not depend on the agreement of these approximations.
"""

import argparse
import json
import platform
from pathlib import Path

import mpmath as mp
import sympy as s
mp.mp.dps=70

def q5_direct(a=mp.mpf('0.125'),order=100):
    # [x^j] x psi(x), then take its fifth power.
    base=[-mp.mpf(1),-mp.euler]+[(-1)**j*mp.zeta(j) for j in range(2,order+1)]
    coeff=[mp.mpf(1)]
    for _ in range(5):
        out=[mp.mpf(0)]*(min(order,len(coeff)+len(base)-2)+1)
        for i,u in enumerate(coeff):
            for j,v in enumerate(base[:len(out)-i]):out[i+j]+=u*v
        coeff=out
    left=mp.mpf(0)
    for j,u in enumerate(coeff):
        power=j-5
        if power==-1:left+=u*mp.log(a)
        else:left+=u*a**(power+1)/(power+1)
    return left+mp.quad(lambda x:mp.digamma(x)**5,[a,mp.mpf('0.5'),1])

def q5_series(N=40,K=18):
    z2=mp.zeta(2)
    def d(n):
        p=mp.digamma(n);p1=mp.polygamma(1,n);p2=mp.polygamma(2,n)
        L=mp.log(n)
        return ((-4*p**3+24*z2*p-12*p*p1-2*p2+4*L**3-24*z2*L)/n+(4*z2-2*p1)/n**2+4*p/n**3)*L
    total=mp.fsum(d(n) for n in range(1,N))
    X,L=s.symbols('X L')
    z2s=s.Symbol('Z2')
    psi=L-X/2-s.Add(*(s.bernoulli(2*k)*X**(2*k)/s.Integer(2*k) for k in range(1,K+1)))
    p1=X+X**2/2+s.Add(*(s.bernoulli(2*k)*X**(2*k+1) for k in range(1,K+1)))
    p2=-X**2-X**3-s.Add(*((2*k+1)*s.bernoulli(2*k)*X**(2*k+2) for k in range(1,K+1)))
    form=s.Poly(s.expand(((-4*psi**3+24*z2s*psi-12*psi*p1-2*p2+4*L**3-24*z2s*L)*X+(4*z2s-2*p1)*X**2+4*psi*X**3)*L),X,L)
    for (p,m),c in form.terms():
        if p>2*K+2:continue
        c=c.subs(z2s,str(z2))
        total+=mp.mpf(str(c.evalf(mp.mp.dps)))*(-1)**m*mp.diff(lambda w:mp.zeta(w,N),p,m)
    return 30*mp.euler**2*z2-60*mp.euler*mp.zeta(3)+mp.mpf(35)/3*mp.zeta(4)+20*mp.stieltjes(4)-120*z2*mp.stieltjes(2)-5*total

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    a=q5_direct();b=q5_series()
    result={
        'Q5_direct_local_series_and_quadrature':mp.nstr(a,68),
        'Q5_subtracted_polygamma_series':mp.nstr(b,68),
        'absolute_difference':mp.nstr(abs(a-b),12),
        'decimal_working_precision':mp.mp.dps,
        'local_taylor_cutoff':'1/8',
        'local_taylor_degree':100,
        'tail_start':40,
        'Binet_terms':18,
        'max_inverse_power_retained':38,
        'python':platform.python_version(),
        'sympy':s.__version__,
        'mpmath':mp.__version__,
        'status':'Non-interval floating-point diagnostic; no certified rounding enclosure',
    }
    output=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(output,encoding='utf-8')
    print(output)
