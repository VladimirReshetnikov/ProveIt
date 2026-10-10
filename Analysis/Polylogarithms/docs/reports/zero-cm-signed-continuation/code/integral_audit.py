#!/usr/bin/env python3
"""Independent quadrature audit of the frozen S8 integer relation.

Evaluates Mellin integrals directly with mpmath polylogarithms, rather than
Euler acceleration of the defining sums. Agreement is numerical evidence.
"""
import json
from pathlib import Path
import time
import mpmath as mp

HERE=Path(__file__).resolve().parents[1]/"results"
VECTOR=[-10974719508480,15125246115840,816174858240,-394908401664,
        -5770366156800,633846205,-44376595200,-518730670080,
        -2998569369600,-21949439016960]


def beta(s):
    return (mp.zeta(s,mp.mpf(1)/4)-mp.zeta(s,mp.mpf(3)/4))/mp.mpf(4)**s


def main():
    mp.mp.dps=220
    start=time.time()
    # x = exp(-t) makes both endpoints smooth or exponentially decaying.
    # Truncation at 256 avoids pathological huge quadrature nodes. The
    # discarded tail is bounded analytically below and is < 10^-315.
    T=256
    intervals=[0,1,4,16,64,T]
    def kernel_s(t):
        x=mp.exp(-t)
        return -t**7*mp.log1p(x*x)/(1+x*x)*x/mp.factorial(7)
    vals=[mp.quad(kernel_s,intervals)]
    print('S8 integral complete after %.2f s'%(time.time()-start),flush=True)
    for a,b in [(8,1),(6,3),(4,5),(2,7)]:
        def integrand(t):
            x=mp.exp(-t)
            if b==1:
                imaginary=-(x*mp.atan(x)+mp.log1p(x*x)/2)/(1+x*x)
            else:
                imaginary=mp.im(1j*mp.polylog(b,1j*x)/(1-1j*x))
            return t**(a-1)*imaginary*x/mp.factorial(a-1)
        vals.append(mp.quad(integrand,intervals))
        print('g%d%d integral complete after %.2f s'%(a,b,time.time()-start),flush=True)
    vals += [mp.pi**9,mp.catalan*mp.zeta(7),beta(4)*mp.zeta(5),
             beta(6)*mp.zeta(3),beta(8)*mp.log(2)]
    labels=['S8','g81','g63','g45','g27','pi^9','G*zeta(7)',
            'beta(4)*zeta(5)','beta(6)*zeta(3)','beta(8)*log(2)']
    # For t>=T, |Im[i Li_b(i e^-t)/(1-i e^-t)]| <=
    # 2 exp(-2t)/(1-exp(-2T)); the S8 kernel has the same simpler bound.
    tails={str(a):2*mp.gammainc(a,3*T,mp.inf)/(mp.factorial(a-1)*3**a*(1-mp.exp(-2*T)))
           for a in [2,4,6,8]}
    report={'status':'Numerical audit; no equality proof or quadrature interval claim',
            'working_digits':mp.mp.dps,'method':'Mellin integrals with x=exp(-t)',
            'integrated_interval':[0,T],
            'analytic_tail_bounds_by_a':{k:mp.nstr(v,30) for k,v in tails.items()},
            'vector':VECTOR,'values':{k:mp.nstr(v,215) for k,v in zip(labels,vals)},
            'integer_residual':mp.nstr(mp.fdot(VECTOR,vals),45),
            'normalized_difference':mp.nstr(mp.fdot(VECTOR,vals)/VECTOR[0],45),
            'elapsed_seconds':time.time()-start}
    (HERE/'s8_integral_audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print('integer residual',report['integer_residual'],flush=True)


if __name__=='__main__': main()
