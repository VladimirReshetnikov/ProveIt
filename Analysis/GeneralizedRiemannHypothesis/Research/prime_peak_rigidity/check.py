#!/usr/bin/env python3
"""Reproduce numerical illustrations and exact algebraic checks.
Requires Python 3, mpmath, numpy. No zero tables and no GRH proof checking.
Prime-power samples are floating-point illustrations, not interval certificates.
"""
import csv
import math
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp
import numpy as np

HERE = Path(__file__).resolve().parent
mp.mp.dps = 45


def prime_modulus(q):
    """Compute c_chi and M_chi for a prime q (and q=1)."""
    zeta_mass = 2 + mp.euler - mp.log(4*mp.pi)
    if q == 1:
        return [0], [[mp.mpc(1)]], [-1-mp.euler], [zeta_mass]
    assert all(q % d for d in range(2, math.isqrt(q)+1))
    g = next(g for g in range(1, q) if len({pow(g,k,q) for k in range(q-1)}) == q-1)
    index = {pow(g,k,q): k for k in range(q-1)}
    residues = list(range(1,q))
    characters = [[mp.exp(2j*mp.pi*j*index[a]/(q-1)) for a in residues] for j in range(q-1)]
    c = [-1-mp.euler-mp.log(q)/(q-1)]
    M = [zeta_mass]
    gamma0 = [-mp.digamma(mp.mpf(a)/q) for a in residues]
    gamma1 = [mp.stieltjes(1,mp.mpf(a)/q) for a in residues]
    for j, chi in enumerate(characters[1:],1):
        L = sum(v*z for v,z in zip(chi,gamma0))/q
        Lp = -sum(v*z for v,z in zip(chi,gamma1))/q - mp.log(q)*L
        c.append(-Lp/L)
        parity = j % 2  # primitive root to (q-1)/2 equals -1
        M.append(mp.log(q/mp.pi)+mp.digamma(mp.mpf(1+parity)/2)+2*mp.re(Lp/L))
    assert all(m > 0 for m in M)
    return residues,characters,c,M


def real_if_close(x):
    assert abs(mp.im(x)) < mp.mpf('1e-38'), x
    return mp.re(x)


def profiles(q):
    residues, chars, c, M = prime_modulus(q)
    h = len(residues)
    C = [real_if_close(sum(mp.conj(ch[i])*v for ch,v in zip(chars,c))/h) for i in range(h)]
    V = [real_if_close(sum(mp.conj(ch[i])*v for ch,v in zip(chars,M))/h) for i in range(h)]
    return residues,C,V,M


def mangoldt(n):
    isprime = np.ones(n+1, dtype=bool)
    isprime[:2] = False
    for p in range(2,math.isqrt(n)+1):
        if isprime[p]:
            isprime[p*p::p] = False
    v = np.zeros(n+1)
    for p in np.flatnonzero(isprime):
        p = int(p)
        k = p
        while k <= n:
            v[k] = math.log(p)
            k *= p
    return v


def examples():
    scales = [100,1000,10000,100000,1000000]
    n = scales[-1]
    v = mangoldt(n)
    with (HERE/'profiles.csv').open('w', newline='') as f, (HERE/'prime_samples.csv').open('w', newline='') as f2:
        wr = csv.writer(f); ws = csv.writer(f2)
        wr.writerow(['q','a','C_a','v_a','v_identity'])
        ws.writerow(['q','x','a','E_a','v_a','E_identity','v_identity_minus_E_identity'])
        for q in [1,3,5,7,11]:
            residues,C,V,M = profiles(q)
            h = len(residues)
            i1 = residues.index(1 % q)
            for a,c,w in zip(residues,C,V):
                wr.writerow([q,a,mp.nstr(c,30),mp.nstr(w,30),mp.nstr(V[i1],30)])
            for x in scales:
                E = []
                for a,c in zip(residues,C):
                    ns = np.arange(a if a else q, x+1, q)
                    S = np.sum(v[ns]*(1.0/ns-1.0/x),dtype=np.longdouble)
                    E.append(math.sqrt(x)*(float(S)-math.log(x)/h-float(c)))
                for a,e,w in zip(residues,E,V):
                    ws.writerow([q,x,a,format(e,'.12g'),mp.nstr(w,20),format(E[i1],'.12g'),format(float(V[i1])-E[i1],'.12g')])
            print('q=',q, 'v_identity=',mp.nstr(V[i1],18), 'M=',[mp.nstr(m,12) for m in M])


def exact_checks():
    # Rational unit circle points, complex multiplication by pairs, no floats.
    def add(a,b): return (a[0]+b[0],a[1]+b[1])
    def sub(a,b): return (a[0]-b[0],a[1]-b[1])
    def mul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
    def scale(c,a): return (c*a[0],c*a[1])
    def norm2(a): return a[0]**2+a[1]**2
    def total(a):
        r=(F(0),F(0))
        for z in a: r=add(r,z)
        return r
    one=(F(1),F(0))
    phases=[one,(F(3,5),F(4,5)),(F(-5,13),F(12,13)),(F(0),F(-1))]
    w=[F(1,7),F(2,5),F(1,11),F(3,17)]
    M=sum(w)
    for k in range(4):
        z=phases[k:]+phases[:k]
        D=sum(m*(1-u[0]) for m,u in zip(w,z))
        assert sum(m*norm2(sub(u,one)) for m,u in zip(w,z)) == 2*D
        for l in range(4):
            h=phases[l:]+phases[:l]
            diff=total(scale(m,mul(v,sub(u,one))) for m,u,v in zip(w,z,h))
            assert norm2(diff)<=2*M*D
        Z=total(scale(m,u) for m,u in zip(w,z))
        assert norm2(sub((M,F(0)),Z)) <= 2*M*D
    print('Exact rational checks: phase identity and translate bound passed (16 cases).')

if __name__ == '__main__':
    exact_checks()
    examples()
