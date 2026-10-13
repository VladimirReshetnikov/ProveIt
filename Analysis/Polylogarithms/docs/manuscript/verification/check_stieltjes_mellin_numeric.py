"""Independent numerical diagnostics for zero-Mellin Stieltjes identities.

No interval or proof certificate is claimed.  The reconstruction quadrature
uses digamma only, and the reference uses mpmath's Stieltjes implementation.
Tail expansions only stabilize point evaluation; a second precision replay
is retained.  No preserved incoming evidence is modified.
"""
from pathlib import Path
import json
import math
import mpmath as mp

OUT = Path(__file__).with_suffix('.json')


def stable_digamma_difference(a, b, dps):
    d0 = mp.digamma(b) - mp.digamma(a)
    terms = max(10, (dps + 15) // 10)
    low = [(mp.polygamma(k, b) - mp.polygamma(k, a)) / mp.factorial(k)
           for k in range(1, terms + 1)]
    high = [(-1)**(k+1) * (mp.bernpoly(k, b) - mp.bernpoly(k, a)) / k
            for k in range(1, terms + 1)]

    def centered(y):
        x = mp.exp(y)
        if y < -30:
            return mp.fsum(c*x**(k+1) for k, c in enumerate(low))
        return mp.digamma(x+b)-mp.digamma(x+a)-d0

    def raw(y):
        if y > 30:
            t = mp.exp(-y)
            return mp.fsum(c*t**(k+1) for k, c in enumerate(high))
        x = mp.exp(y)
        return mp.digamma(x+b)-mp.digamma(x+a)
    return d0, centered, raw


def string(x):
    return mp.nstr(x, 48)


def reconstruction(a, b, dps, maxn=6):
    mp.mp.dps = dps
    a, b = mp.mpf(a), mp.mpf(b)
    d0, center, raw = stable_digamma_difference(a, b, dps)
    moments = []
    for j in range(maxn):
        left = mp.quad(lambda y: y**j * center(y), [-mp.inf, -30, -8, -2, 0])
        right = mp.quad(lambda y: y**j * raw(y), [0, 2, 8, 30, mp.inf])
        moments.append(left + right)
    rows = []
    for n in range(1, maxn+1):
        actual = mp.fsum((-1)**k * mp.factorial(n) * mp.pi**(2*k)
                        / (mp.factorial(2*k+1)*mp.factorial(n-2*k-1))
                        * moments[n-2*k-1]
                        for k in range((n-1)//2+1))
        contact = ((-1)**(n//2) * mp.pi**n * d0/(n+1)) if n % 2 == 0 else mp.mpf(0)
        actual += contact
        expected = mp.stieltjes(n, a)-mp.stieltjes(n, b)
        rows.append(dict(n=n, quadrature=string(actual), reference=string(expected),
                         absolute_error=string(abs(actual-expected)),
                         omitted_even_correction_error=string(abs(actual-contact-expected))))
        print('reconstruction', dps, str(a), str(b), n, string(abs(actual-expected)), flush=True)
    return dict(dps=dps, a=str(a), b=str(b), log_moments=[string(v) for v in moments], rows=rows)


def P(n, y):
    z = y + mp.euler
    return [mp.mpf(1), z, z*z-mp.zeta(2),
            z**3-3*mp.zeta(2)*z+2*mp.zeta(3)][n]


def raising(a, b, dps=60):
    mp.mp.dps=dps
    a, b=mp.mpf(a), mp.mpf(b)
    def kernel(t):
        # Stable difference, with a < b for the recorded cases.
        return mp.exp(-a*t)*(-mp.expm1(-(b-a)*t))/(-mp.expm1(-t))
    rows=[]
    for n in range(4):
        actual=(-1)**(n+1)*mp.quad(lambda t: kernel(t)*P(n,mp.log(t))*(mp.euler+mp.log(t)),
                                  [0,mp.mpf('0.1'),1,5,mp.inf])
        D=lambda j: mp.stieltjes(j,a)-mp.stieltjes(j,b)
        expected=D(n+1)+mp.fsum(mp.factorial(n)/mp.factorial(n-k)*mp.zeta(k+1)*D(n-k)
                                for k in range(1,n+1))
        rows.append(dict(n=n, transformed_quadrature=string(actual),reference=string(expected),
                         absolute_error=string(abs(actual-expected))))
        print('raising',n,string(abs(actual-expected)),flush=True)
    return dict(dps=dps,a=str(a),b=str(b),rows=rows)


def resonances(a='0.6',h='0.4',dps=60):
    mp.mp.dps=dps
    a,h=mp.mpf(a),mp.mpf(h)
    rows=[]
    for r in [2,3,4]:
        for k in range(1,r):
            hs=[mp.mpf(0)]*4
            hs[0]=1
            for i in range(1,k):
                for j in range(1,4):
                    hs[j]+=hs[j-1]/i
            def delta_jet(order):
                return mp.fsum((-1)**j*math.comb(r,j)*mp.diff(lambda s:mp.zeta(s,a+j*h),1-k,order)
                               for j in range(r+1))
            jets=[delta_jet(j) for j in range(1,5)]
            def kernel(t):
                return mp.exp(-a*t)*(-mp.expm1(-h*t))**r/(-mp.expm1(-t))
            for n in range(3):
                actual=(-1)**n*mp.gamma(k)*mp.quad(lambda t:t**(-k)*kernel(t)*P(n,mp.log(t)),
                                                 [0,mp.mpf('0.1'),1,5,mp.inf])
                expected=(-1)**(n+k-1)*mp.factorial(n)*mp.fsum(hs[n-j]*jets[j]/mp.factorial(j+1)
                                                               for j in range(n+1))
                rows.append(dict(r=r,k=k,n=n,transformed_quadrature=string(actual),
                                 reference=string(expected),absolute_error=string(abs(actual-expected))))
                print('resonance',r,k,n,string(abs(actual-expected)),flush=True)
    return dict(dps=dps,a=str(a),h=str(h),rows=rows)


if __name__=='__main__':
    result=dict(scope='Finite numerical diagnostics, not interval certification or a general proof.',
                mpmath_version=mp.__version__,
                reconstruction=[], raising=[], resonances=None)
    for precision in [50,70]:
        result['reconstruction'].append(reconstruction('0.6','1.4',precision))
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    result['reconstruction'].append(reconstruction('0.35','0.8',60,4))
    result['reconstruction'].append(reconstruction('1','2',60,6))
    result['raising'].append(raising('0.6','1.4'))
    result['resonances']=resonances()
    result['all_absolute_errors_below_1e-40']=all(
        mp.mpf(row['absolute_error'])<mp.mpf('1e-40')
        for group in result['reconstruction']+result['raising']+[result['resonances']]
        for row in group['rows'])
    OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('ALL_ERRORS_BELOW_1E-40',result['all_absolute_errors_below_1e-40'],flush=True)

    assert result['all_absolute_errors_below_1e-40']
