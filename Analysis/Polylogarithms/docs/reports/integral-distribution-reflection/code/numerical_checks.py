#!/usr/bin/env python3
"""Independent numerical diagnostics, NOT interval or equality certificates.

Normal-form RHS uses mpmath.polylog. The LHS at nonsingular orders uses a
finite Hurwitz-zeta Fourier sum. Pole-cancelled jet identities are checked
separately using a finite Fourier transform of generalized Stieltjes constants. Exact proofs are in the
article and the integer polynomial certificates.
"""
from pathlib import Path
from math import comb
import json
import mpmath as mp
from distribution import normal_forms
ROOT=Path(__file__).resolve().parents[1]

if not __debug__:
    raise RuntimeError('Run without -O: validation uses assertions.')


def root(q,a):
    return mp.exp(2j*mp.pi*mp.mpf(a)/q)

def li(q,a,s):
    return mp.zeta(s) if a%q==0 else mp.polylog(s,root(q,a))

def fourier(q,a,s):
    return mp.fsum(root(q,a*r)*mp.zeta(s,mp.mpf(r)/q) for r in range(1,q+1))/mp.power(q,s)

def nf_value(q,a,s):
    g,nf=normal_forms(q)
    values={b:li(q,b,s) for b in g['basis']}
    return mp.fsum(c*mp.fprod(mp.power(p,(1-s)*e) for p,e in zip(g['primes'],ex))*values[b]
                   for (b,ex),c in nf[a].items())

def jet_values12(maxj):
    # The common Hurwitz pole is cancelled symbolically BEFORE evaluation.
    # Direct finite differences of polylog near integral order are avoided.
    gamma={(k,r):(-mp.digamma(mp.mpf(r)/12) if k==0 else mp.stieltjes(k,mp.mpf(r)/12))
           for k in range(maxj+1) for r in range(1,13)}
    F={}
    for a in [1,5,9]:
        G=[mp.fsum(root(12,a*r)*gamma[k,r] for r in range(1,13)) for k in range(maxj+1)]
        F[a]=[(-1)**j*mp.fsum(comb(j,k)*mp.log(12)**(j-k)*G[k] for k in range(j+1))/12
              for j in range(maxj+1)]
    out=[]
    for j in range(maxj+1):
        lhs=F[1][j]+F[5][j]+F[9][j]+mp.fsum(comb(j,h)*(-mp.log(3))**h*F[9][j-h] for h in range(j+1))
        def C(h):return (-mp.log(12))**h-(-mp.log(6))**h
        rhs=C(j+1)/(j+1)+mp.fsum(comb(j,h)*C(h)*(-1)**(j-h)*mp.stieltjes(j-h) for h in range(1,j+1))
        out.append(abs(lhs-rhs))
    return out

def main():
    results=[]
    for prec in [70,110]:
        print('Working precision',prec,flush=True)
        mp.mp.dps=prec
        orders=[mp.mpf(2),mp.mpf('2.5'),mp.mpc('0.4','0.7')]
        for q,a in [(12,1),(30,1)]:
            for s in orders:
                residual=abs(fourier(q,a,s)-nf_value(q,a,s))
                assert residual<mp.power(10,-prec+8)
                results.append(dict(kind='finite-Hurwitz-Fourier versus normal-form polylogs',
                                    q=q,a=a,s=mp.nstr(s,20),dps=prec,
                                    absolute_residual=mp.nstr(residual,14)))
        for j,residual in enumerate(jet_values12(3)):
            assert residual<mp.power(10,-prec+8)
            results.append(dict(kind='pole-cancelled level-12 order derivative',
                                derivative=j,dps=prec,absolute_residual=mp.nstr(residual,14)))
    data=dict(scope='Floating-point diagnostics only; no interval certification or proof of equality by residuals.',
              mpmath_version=mp.__version__,cases=results,case_count=len(results))
    (ROOT/'data'/'numerical_checks.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'case_count':len(results),'all_diagnostics_passed':True,
                      'scope':data['scope']},indent=2))
if __name__=='__main__':main()
