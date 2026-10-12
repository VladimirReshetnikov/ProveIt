#!/usr/bin/env python3
"""Independent rational and modular checks for the gap-ten certificate.

This verifier builds Bernoulli numbers with SymPy, uses the ORIGINAL
late-coordinate matrix, and uses an O(n^2) recurrence on a small prefix.
It does not call the C++ NTT or its divide-and-conquer implementation.
"""
from __future__ import annotations
import csv
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path
import sympy as sp

HERE = Path(__file__).resolve().parent
PRIME = 998244353
M = 5
THRESHOLD = 73728

def qmod(x):
    x = Fraction(x)
    assert x.denominator % PRIME
    return x.numerator * pow(x.denominator, -1, PRIME) % PRIME

def determinant_mod(a):
    a = [list(row) for row in a]
    d = 1
    for k in range(len(a)):
        p = next((p for p in range(k, len(a)) if a[p][k]), None)
        if p is None:
            return 0
        if p != k:
            a[p], a[k] = a[k], a[p]
            d = -d % PRIME
        d = d * a[k][k] % PRIME
        iv = pow(a[k][k], -1, PRIME)
        for i in range(k+1, len(a)):
            f = a[i][k] * iv % PRIME
            for j in range(k+1, len(a)):
                a[i][j] = (a[i][j] - f*a[k][j]) % PRIME
    return d

def direct_array(nmax):
    beta = [0] * (nmax+1)
    beta[1] = pow(6, -1, PRIME)
    for n in range(2, nmax+1):
        beta[n] = sum(beta[k]*beta[n-k] for k in range(1, n))
        beta[n] = beta[n]*pow(2*(2*n+1), -1, PRIME) % PRIME
    aa = [0] * (nmax+1)
    rows = [[0]*M for _ in range(nmax+1)]
    for j in range(M):
        rows[j+1][j] = 1
    for s in range(M+1, nmax+1):
        aa[s] = math.prod(range(2*s-2*M+1, 2*s+1)) % PRIME
        bb = math.prod(range(2*s-2*M, 2*s)) % PRIME
        invd = pow(2*(aa[s]+bb), -1, PRIME)
        for j in range(M):
            rows[s][j] = sum(beta[s-u]*(aa[u]+bb)*rows[u][j]
                             for u in range(1, s))*invd % PRIME
    return beta, rows

def source_matrix(b):
    p, q = 2*b-2*M, 2*b
    def entry(r, k):
        j = b+r
        d = 2*j+1
        e = d-p-q+2*k+1
        if e < 0:
            return sp.S.Zero
        coefficient = sp.S.Zero
        for upper, lower in ((d-q+1, p-2*k), (d-p+1, q-2*k)):
            if 2 <= lower <= upper:
                coefficient += sp.binomial(upper, lower)/upper
        return sp.bernoulli(e)*coefficient
    return sp.Matrix(b,b,entry)

def diagonal(s):
    aa = math.prod(range(2*s-2*M+1, 2*s+1))
    bb = math.prod(range(2*s-2*M, 2*s))
    return 2*(aa+bb)

def rational_initial_boundary():
    nmax=2*M
    beta=[sp.S.Zero]+[2*abs(sp.bernoulli(2*n))/sp.factorial(2*n)
                      for n in range(1,nmax+1)]
    rr=[[sp.S.Zero]*M for _ in range(nmax+1)]
    aa=[0]*(nmax+1)
    for j in range(M):rr[j+1][j]=sp.S.One
    for s in range(M+1,nmax+1):
        aa[s]=math.prod(range(2*s-2*M+1,2*s+1))
        bb=math.prod(range(2*s-2*M,2*s))
        for j in range(M):
            rr[s][j]=sum(beta[s-u]*(bb+aa[u])*rr[u][j]
                          for u in range(1,s))/diagonal(s)
    return sp.factor(sp.Matrix(rr[M+1:2*M+1]).det())

def main():
    certificate=HERE/'gap_ten_certificate.csv'
    with certificate.open(newline='') as f:
        records=list(csv.DictReader(f))
    residues={int(v['b']):int(v['det_mod_998244353']) for v in records}
    assert list(residues)==list(range(M+1,THRESHOLD))
    assert all(0<v<PRIME for v in residues.values())
    beta,rr=direct_array(516)
    for n in range(1,65):
        assert beta[n]==qmod(2*abs(sp.bernoulli(2*n))/sp.factorial(2*n))
    for b in range(M+1,512):
        assert determinant_mod(rr[b+1:b+M+1])==residues[b]
    source_checks=[]
    for b in range(M+1,19):
        matrix=source_matrix(b)
        d=matrix.det(method='domain-ge')
        factor=Fraction((-1)**(b*(b-1)//2),4**b*math.factorial(b))
        factor*=math.prod(diagonal(s) for s in range(M+1,b+M+1))
        expected=qmod(d)*pow(qmod(factor),-1,PRIME)%PRIME
        assert expected==residues[b]
        source_checks.append({'b':b,'source_determinant':str(d),
                              'boundary_residue':expected})
    V=sp.Matrix([[sp.Rational(1,j**(2*i)) for j in range(1,M+1)]
                 for i in range(1,M+1)])
    import itertools
    permanent=sum(sp.prod(V[i,p[i]] for i in range(M))
                  for p in itertools.permutations(range(M)))
    ratio=V.det()/permanent
    error=sp.Rational(513,512)**2*sp.Rational(1048577,1048576)**3-1
    assert error < sp.Rational(1,240) < ratio
    assert 8448*2**20 < (2*THRESHOLD-4)**2
    assert 898*512 < 5*(2*THRESHOLD-4)
    initial=rational_initial_boundary()
    assert initial != 0
    M6=source_matrix(6)
    invrow=M6.inv()[0,:]
    factor6=Fraction((-1)**15,4**6*math.factorial(6))
    factor6*=math.prod(diagonal(s) for s in range(6,12))
    f6=sp.factor(M6.det()/factor6)
    assert invrow[5]==sp.factor(24*initial/(diagonal(11)*f6))
    payload={
        'half_gap':M, 'analytic_threshold':THRESHOLD,
        'finite_range':[M+1,THRESHOLD-1], 'nonzero_residues':len(residues),
        'prime':PRIME, 'sha256':hashlib.sha256(certificate.read_bytes()).hexdigest(),
        'independent_direct_recurrence_determinants':506,
        'independent_Bernoulli_coefficients':64,
        'original_source_matrix_checks':source_checks,
        'limiting_determinant':str(V.det()), 'limiting_permanent':str(permanent),
        'determinant_to_permanent':str(ratio),
        'perturbation_multiplier':str(error),
        'auxiliary_f_5_5':str(initial),
        'initial_inverse_last_entry':str(invrow[5]),
        'all_checks_passed':True,
    }
    (HERE/'gap_ten_independent_checks.json').write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps({k:v for k,v in payload.items()
                      if k!='original_source_matrix_checks'},indent=2))

if __name__=='__main__':main()
