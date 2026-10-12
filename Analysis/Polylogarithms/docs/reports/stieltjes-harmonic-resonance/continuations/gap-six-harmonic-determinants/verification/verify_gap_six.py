#!/usr/bin/env python3
"""Exact finite certificate for the all-order gap-six theorem.

The analytic part of the theorem proves positivity for b >= 2048.
This script proves nonvanishing over Q for every 4 <= b < 2048 by
reducing the exact rational fixed-gap recurrence modulo a certified prime.
No floating-point operations occur in the proof certificate.
"""
from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path
from fractions import Fraction

PRIME = 2147483647
THRESHOLD = 2048
GAP_HALF = 3
OUTPUT = Path(__file__).resolve().parents[1] / "results" / "gap_six_certificate.json"

def prime_by_trial_division(p: int) -> bool:
    if p < 2 or p % 2 == 0:
        return p == 2
    return all(p % d for d in range(3, math.isqrt(p) + 1, 2))

def det3(a, p):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
            -a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            +a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])) % p

def cotangent_coefficients(nmax, p):
    """alpha_n = 2 |B_(2n)| / (2n)! by the cotangent Riccati equation."""
    alpha = [0] * (nmax + 1)
    alpha[1] = pow(6, -1, p)
    for n in range(2, nmax+1):
        val = 2 * sum(alpha[k]*alpha[n-k] for k in range(1, (n+1)//2))
        if n % 2 == 0:
            val += alpha[n//2]**2
        alpha[n] = val * pow(2*(2*n+1), -1, p) % p
    return alpha

def trig_quotient_coefficients(nmax, p):
    """Independent formal division: x cot(x/2)=2 cos(x/2)/(sin(x/2)/(x/2))."""
    # A(z)=sin(sqrt(z)/2)/(sqrt(z)/2), B(z)=cos(sqrt(z)/2).
    # f(z)=B(z)/A(z)=1 - sum alpha_n z^n / 2.
    inv_fact = [1]*(2*nmax+2)
    fac=1
    for k in range(1, len(inv_fact)):
        fac=fac*k % p
        inv_fact[k]=pow(fac,-1,p)
    a=[((-1)**n*pow(4,-n,p)*inv_fact[2*n+1]) % p for n in range(nmax+1)]
    b=[((-1)**n*pow(4,-n,p)*inv_fact[2*n]) % p for n in range(nmax+1)]
    f=[1]
    for n in range(1,nmax+1):
        f.append((b[n]-sum(a[k]*f[n-k] for k in range(1,n+1))) % p)
    return [0]+[(-2*f[n])%p for n in range(1,nmax+1)]

def fundamental_array(c, nmax, alpha, p):
    aa=[0]*(nmax+1)
    bb=[0]*(nmax+1)
    dd=[0]*(nmax+1)
    rr=[[0]*c for _ in range(nmax+1)]
    for j in range(c): rr[j+1][j]=1
    for s in range(c+1, nmax+1):
        aa[s]=math.prod(range(2*s-2*c+1,2*s+1)) % p
        bb[s]=math.prod(range(2*s-2*c,2*s)) % p
        dd[s]=2*(aa[s]+bb[s]) % p
        assert dd[s] != 0
        sums=[0]*c
        for u in range(1,s):
            weight=alpha[s-u]*(bb[s]+aa[u]) % p
            for j in range(c): sums[j]+=weight*rr[u][j]
        invd=pow(dd[s],-1,p)
        rr[s]=[val*invd % p for val in sums]
    return rr

def qmod(z,p):
    z=Fraction(z)
    assert z.denominator % p
    return z.numerator*pow(z.denominator,-1,p) % p

def direct_source_checks(rr,p):
    import sympy as sp
    records=[]
    for b in range(4,21):
        a=b-3
        def entry(i,k):
            r=i+k-a+1
            if r<0: return sp.S(0)
            d1,d2=2*i+2,2*b+2*i-2*a+2
            l1,l2=2*a-2*k,2*b-2*k
            v=sp.S(0)
            if 2<=l1<=d1:v+=sp.Rational(sp.binomial(d1,l1),d1)
            if 2<=l2<=d2:v+=sp.Rational(sp.binomial(d2,l2),d2)
            return sp.bernoulli(2*r)*v
        mat=sp.Matrix(b,b,entry)
        determinant=mat.det(method='domain-ge')
        product=math.prod(2*(math.prod(range(2*s-5,2*s+1))
                               +math.prod(range(2*s-6,2*s))) for s in range(4,b+4))
        factor=Fraction((-1)**(b*(b-1)//2)*product,4**b*math.factorial(b))
        expected=qmod(determinant,p)*pow(qmod(factor,p),-1,p)%p
        residue=det3(rr[b+1:b+4],p)
        assert expected==residue
        records.append({'b':b,'source_matrix_determinant':str(determinant),
                        'boundary_determinant_residue':residue})
    return records

def main():
    p=PRIME
    assert prime_by_trial_division(p)
    nmax=THRESHOLD+GAP_HALF-1
    assert 4*nmax+2<p
    alpha=cotangent_coefficients(nmax-1,p)
    other=trig_quotient_coefficients(nmax-1,p)
    assert alpha==other
    rr=fundamental_array(GAP_HALF,nmax,alpha,p)
    residues=[]
    for b in range(GAP_HALF+1,THRESHOLD):
        residue=det3(rr[b+1:b+GAP_HALF+1],p)
        assert residue != 0, f'Zero certificate residue at b={b}; another prime is needed.'
        residues.append({'b':b,'det_mod_prime':residue})
    direct=direct_source_checks(rr,p)
    payload={'theorem':'All even harmonic-tail gaps of six have optimal first-q formal moment prefix.',
             'half_gap':GAP_HALF,'analytic_threshold_b':THRESHOLD,
             'prime':p,'primality_proof':'Deterministic trial division through floor(sqrt(p)).',
             'modular_recurrence_denominators_nonzero':True,
             'first_certified_b':4,'last_certified_b':THRESHOLD-1,
             'nonzero_determinants':len(residues),
             'independent_cotangent_coefficients_checked':len(alpha)-1,
             'source_matrix_normalization_checks':direct,
             'residues':residues,
             'residues_sha256':hashlib.sha256(json.dumps(residues,separators=(',',':')).encode()).hexdigest()}
    OUTPUT.write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps({k:v for k,v in payload.items() if k not in ('residues','source_matrix_normalization_checks')},indent=2))
    print(f'Output: {OUTPUT}')

if __name__=='__main__':
    main()
