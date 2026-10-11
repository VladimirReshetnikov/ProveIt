#!/usr/bin/env python3
"""Independent numerical continuation checks for the spectral-jet module.

The numerical continuation uses a finite cutoff plus a tail expanded at n=infinity,
not the all-order jet formula in Section 7 of the article. All derivatives are extracted
by a discrete Cauchy integral. The tail and Cauchy sums are numerical truncations;
these tests corroborate the analytic proofs, not replace them.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import mpmath as mp
import sympy as sp

mp.mp.dps = 65


def jet_combination(pcoeff, shifts, spectra, *, cutoff=32, terms=50,
                    samples=64, radius=mp.mpf(1)/32):
    """Return jets 0,1,2 of a signed sum of spectra of the same total order.

    pcoeff has ascending powers of n. spectra consists of (sign, weights).
    """
    shifts = tuple(map(mp.mpf, shifts))
    spectra = [(mp.mpf(sign), tuple(map(mp.mpf, weights)))
               for sign, weights in spectra]
    total = sum(spectra[0][1])
    assert all(sum(weights) == total for _, weights in spectra)
    degree = len(pcoeff) - 1

    # logarithm expansion coefficients, fixed across contour points
    ell = []
    for _, weights in spectra:
        ell.append([mp.mpf(0)] + [
            (-1)**(j+1) * sum(w*a**j for w, a in zip(weights, shifts))/j
            for j in range(1, terms+1)])

    values = []
    for index in range(samples):
        angle = 2*mp.pi*index/samples
        phase = mp.exp(1j*angle)
        s = radius*phase
        spectral_values = []

        # All factors have the same W, so compute Hurwitz values only once.
        zetas = {j: mp.zeta(total*s+j, cutoff)
                 for j in range(-degree, terms+1)}
        for (sign, weights), logcoeff in zip(spectra, ell):
            c = [mp.mpc(1)]
            for k in range(1, terms+1):
                c.append(-s * sum(j*logcoeff[j]*c[k-j]
                                  for j in range(1, k+1))/k)
            finite = mp.mpc(0)
            for n in range(cutoff):
                polynomial = sum(mp.mpf(p)*n**k for k, p in enumerate(pcoeff))
                exponent = sum(w*mp.log(n+a) for w, a in zip(weights, shifts))
                finite += polynomial*mp.exp(-s*exponent)
            tail = sum(mp.mpf(p)*c[k]*zetas[k-d]
                       for d, p in enumerate(pcoeff)
                       for k in range(terms+1))
            spectral_values.append(sign*(finite+tail))
        values.append((phase, sum(spectral_values)))

    return [mp.factorial(r)/(samples*radius**r)
            * sum(value/phase**r for phase, value in values)
            for r in range(3)]


def single_jet(pcoeff, a, r):
    a = mp.mpf(a)
    # P(n)=sum_k p_k(a)(n+a)^k.
    shifted = [sum(mp.mpf(pcoeff[d])*math.comb(d,k)*(-a)**(d-k)
                   for d in range(k,len(pcoeff)))
               for k in range(len(pcoeff))]
    return sum(p*mp.diff(lambda s: mp.zeta(s-k,a),0,r)
               for k,p in enumerate(shifted))


def anomaly(pcoeff, shifts, weights):
    W=sum(map(mp.mpf,weights))
    value=mp.mpf(0)
    for i in range(len(shifts)):
        for j in range(i+1,len(shifts)):
            a,b=map(mp.mpf,(shifts[i],shifts[j]))
            for d in range(1,len(pcoeff)):
                pair=sum((a**r-b**r)*(a**(d+1-r)-b**(d+1-r))
                         / (r*(d+1-r)) for r in range(1,d+1))
                value += (mp.mpf(weights[i])*weights[j]*pcoeff[d]
                          * (-1)**(d+1)*pair/(2*W))
    return value


def symbolic_checks():
    z,a,b,base=sp.symbols('z a b base')
    reports=[]
    for d in range(7):
        direct=sum((-1)**(d+1)*((a**r-b**r)
                   *(a**(d+1-r)-b**(d+1-r)))
                   / sp.Integer(r*(d+1-r)) for r in range(1,d+1))
        # Independent shifted-base coefficient extraction.
        ldiff=sum((-1)**(r+1)*((a-base)**r-(b-base)**r)
                  *z**r/sp.Integer(r) for r in range(1,d+2))
        via_base=sum(sp.binomial(d,k)*(-base)**(d-k)
                     *sp.expand(ldiff**2).coeff(z,k+1)
                     for k in range(d+1))
        assert sp.expand(direct-via_base)==0
        reports.append({"degree":d,"pair_polynomial":str(sp.factor(direct))})
    return reports


def run():
    report={"dps":mp.mp.dps,"method":"finite cutoff plus Hurwitz tail; Cauchy coefficients",
            "symbolic_base_invariance":symbolic_checks(),"numerical":[]}
    cases=[([0,1],[1,2],[1,1]),
           ([0,0,1],[1,2],[1,1]),
           ([0,1],[1,2,3],[1,2,1]),
           ([0,0,1],[1,2,3],[1,2,1])]
    for pcoeff,shifts,weights in cases:
        jets=jet_combination(pcoeff,shifts,[(1,weights)])
        expected=(sum(mp.mpf(w)*single_jet(pcoeff,a,1)
                      for a,w in zip(shifts,weights))
                  -anomaly(pcoeff,shifts,weights))
        error=abs(jets[1]-expected)
        assert error<mp.mpf('1e-35'), mp.nstr(error)
        result={"polynomial":pcoeff,"shifts":shifts,"weights":weights,
                "anomaly":mp.nstr(anomaly(pcoeff,shifts,weights),45),
                "spectral_first_jet":mp.nstr(jets[1].real,45),
                "absolute_error":mp.nstr(error,8)}
        report["numerical"].append(result)
        print(json.dumps(result),flush=True)

    # T(a,b)+T(b,c)+T(c,a)-T(b,a)-T(c,b)-T(a,c).
    cyclic=[(1,[2,1,0]),(1,[0,2,1]),(1,[1,0,2]),
            (-1,[1,2,0]),(-1,[0,1,2]),(-1,[2,0,1])]
    jets=jet_combination([0,0,1],[1,2,3],cyclic)
    expected=mp.mpf(4)/3
    error=abs(jets[2]-expected)
    assert error<mp.mpf('1e-35'), mp.nstr(error)
    result={"identity":"six-term second-jet Vandermonde",
            "shifts":[1,2,3],"computed":mp.nstr(jets[2].real,45),
            "expected":"4/3","absolute_error":mp.nstr(error,8)}
    report["numerical"].append(result)
    print(json.dumps(result),flush=True)
    (Path(__file__).resolve().parent.parent/'results'/'spectral_anomaly_checks.json').write_text(
        json.dumps(report,indent=2)+'\n')


if __name__=='__main__':
    run()
