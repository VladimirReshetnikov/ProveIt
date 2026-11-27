#!/usr/bin/env python3
"""Illustrative finite-prime experiment (NOT a zero certificate or proof).
Requires numpy. Run: python experiment.py
"""
import csv
import math
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parent


def a(z, h):
    return -np.expm1(-z*h)/(z*h) if z != 0 else 1.0


def multiplier(z, h):
    d = a(0.5, h)
    az = a(z, h)
    return (1-az)*(d-az)**2


def antiderivative(v, j):
    """j-fold primitive of b(v)=2 sinh(v/2) for v>=0, zero otherwise."""
    u = np.maximum(v, 0.)/2
    if j == 0:
        return 2*np.sinh(u)
    pplus = sum(u**k/math.factorial(k) for k in range(j))
    pminus = sum((-u)**k/math.factorial(k) for k in range(j))
    return 2**j*(np.exp(u)-pplus)-(-2)**j*(np.exp(-u)-pminus)


def kernel(v, h):
    """Apply (I-A_h)(d I-A_h)^2 to b, using exact exponential tail."""
    v = np.asarray(v, dtype=float)
    out = np.zeros_like(v)
    near = (v >= 0) & (v < 3*h)
    u = v[near]
    d = a(0.5, h)
    coeffs = [d*d, -d*d-2*d, 1+2*d, -1]
    for j, c in enumerate(coeffs):
        out[near] += c/h**j*sum((-1)**k*math.comb(j,k)*antiderivative(u-k*h,j) for k in range(j+1))
    far = v >= 3*h
    out[far] = -multiplier(-0.5,h)*np.exp(-v[far]/2)
    return out


def prime_powers(nmax):
    sieve = bytearray(b'\x01')*(nmax+1)
    sieve[:2] = b'\x00\x00'
    for p in range(2,math.isqrt(nmax)+1):
        if sieve[p]:
            sieve[p*p:nmax+1:p] = b'\x00'*((nmax-p*p)//p+1)
    out = []
    for p in range(2,nmax+1):
        if sieve[p]:
            k=p
            while k<=nmax:
                out.append((k,math.log(p)))
                k*=p
    out.sort()
    return np.array([n for n,l in out]),np.array([l for n,l in out])


def test_kernel():
    h=1.
    # Check both zeros and the absence of cancellations at representative frequencies.
    assert abs(multiplier(0,h)) < 1e-14
    assert abs(multiplier(.5,h)) < 1e-14
    assert abs(multiplier(.5+1e-5,h)) < 1e-10
    assert min(abs(multiplier(1j*g,h)) for g in [.01,.1,1,2*np.pi,10,100]) > 0
    assert abs(kernel(np.array([3*h-1e-8]),h)[0]-kernel(np.array([3*h+1e-8]),h)[0]) < 1e-7
    # Independent Gauss-Legendre quadrature at points where the integrand is analytic.
    nodes, weights = np.polynomial.legendre.leggauss(16)
    u = h*(nodes+1)/2
    w = weights/2
    d = a(.5,h)
    def b(v): return 2*np.sinh(np.maximum(v,0.)/2)
    for v in [0., 3.1, 4., 6.]:
        r = d*d*b(v) - (d*d+2*d)*np.sum(w*b(v-u))
        r += (1+2*d)*np.sum(w[:,None]*w[None,:]*b(v-u[:,None]-u[None,:]))
        r -= np.sum(w[:,None,None]*w[None,:,None]*w[None,None,:]*b(v-u[:,None,None]-u[None,:,None]-u[None,None,:]))
        assert abs(r-kernel(np.array([v]),h)[0]) < 2e-12
    # Independent quadrature of A_h repeatedly using midpoint grids, including kink regions.
    m=120
    u=h*(np.arange(m)+.5)/m
    for v in [.4,1.3,2.2]:
        r=d*d*b(v)-(d*d+2*d)*np.mean(b(v-u))
        r+=(1+2*d)*np.mean(b(v-u[:,None]-u[None,:]))
        r-=np.mean(b(v-u[:,None,None]-u[None,:,None]-u[None,None,:]))
        assert abs(r-kernel(np.array([v]),h)[0]) < 5e-5
    print('Kernel consistency checks passed (floating point).')


def main():
    test_kernel()
    h=1.
    ts=np.linspace(5.,12.,281)
    n, logp=prime_powers(math.floor(math.exp(ts[-1])))
    logn=np.log(n)
    weights=logp/np.sqrt(n)
    print(f'Prime powers through {int(n[-1])}: {len(n)}')
    for q in [1,4,5,8]:
        residues=[a for a in range(q) if math.gcd(a,q)==1]
        masks=[n%q==a for a in residues]
        vals=np.array([[sum(v[mask]) for mask in masks] for t in ts for v in [weights*kernel(t-logn,h)]])
        with (ROOT/f'example_q{q}.csv').open('w',newline='') as f:
            writer=csv.writer(f)
            writer.writerow(['t','x']+[f'filtered_a{a}' for a in residues])
            for t, row in zip(ts, vals): writer.writerow([f'{t:.6f}',f'{math.exp(t):.8f}',*[f'{v:.12g}' for v in row]])
        cov=vals.T@vals/len(ts) # uncentered second moment, not true covariance
        eig=np.linalg.eigvalsh(cov)
        print(f'q={q}, residues={residues}: min={vals.min(axis=0)}, max={vals.max(axis=0)}')
        print('  sample second-moment eigenvalues:',eig)
        if len(residues)>1:
            contrast=vals[:,0]-vals[:,-1]
            print(f'  first-minus-last contrast: min={contrast.min():.8g}, max={contrast.max():.8g}')
    print('These finite samples are illustrative only; they certify no asymptotic claim.')

if __name__=='__main__': main()
