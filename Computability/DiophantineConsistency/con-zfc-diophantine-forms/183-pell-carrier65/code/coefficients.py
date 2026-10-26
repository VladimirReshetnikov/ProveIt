#!/usr/bin/env python3
"""Reconstruct the new seed, all 430 actions, 942 indexed tiles and four ports.

No external packages or network access. This is a finite coefficient check,
not a proof of the unbounded consistency equivalence.
"""
from pathlib import Path
from hashlib import sha256
from collections import defaultdict
import json
import re

HERE = Path(__file__).resolve().parents[1]
ALPHABET = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
EXPECTED = {
 'beta': '236f2a7313a08032b1d2b34726174a0dc2d4b4bf99be5ea989f815d32cb2cd70',
 'K': '930a43cdefe8e92f6f9761d84a1eb04f262ca6baf0a3d5494e7db4a7e338179e',
 'MC': '84ae3c5b5cca2284ecfb4d9504804e45a7031120da900ebc300ad77f021d5cab',
 'MF_source': '4b67d5768954dfbeb6d5cf02d26e42fad7bea6d12269802275d65dd6bf14e77b',
}

def need(ok, label):
    if not ok: raise ValueError(label)

def parse62(text):
    out = 0
    for c in text: out = out*62 + ALPHABET.index(c)
    return out

def flags(N, E, j):
    q,b = divmod(j,2)
    m = (N >> (430+q)) & 1
    tau = sum((N >> (430+k)) & 1 for k in range(q))
    F = 14 + m*((E >> (4*tau)) % 16 - 14)
    return (F >> (2*b)) & 1, (F >> (2*b+1)) & 1

def old_decode(literal):
    A = parse62(literal)
    N = A % (1 << 636)
    T = (A >> 636) % (1 << 1675)
    E = A >> 2311
    sigma = 0
    out = []
    for j in range(430):
        nu = (N >> j) & 1
        u = 1+sigma if nu else T // (216**(j-sigma)) % 216
        v,d = flags(N,E,j)
        out.append((u,v,d))
        sigma += nu
    return out

def new_decode(literal):
    A = parse62(literal)
    N = A % (1 << 636)
    Q = A >> 636
    nu = [(N >> j) & 1 for j in range(430)]
    sigma = [0]
    for n in nu: sigma.append(sigma[-1]+n)
    r = [(sigma[j]+2)**(1-nu[j]) for j in range(430)]
    P = [1]
    for b in r: P.append(P[-1]*b)
    E = Q // P[430]
    out = []
    for j in range(430):
        digit = (Q // P[j]) % r[j]
        u = (sigma[j+1] - digit) % 216
        v,d = flags(N,E,j)
        out.append((u,v,d))
    return out

def tiles(actions):
    S = [sorted({u for u,v,d in actions if d==b}) for b in (0,1)]
    def r(d,q): return 205-199*d+sum(u<q for u in S[d])
    def h(q,b): return 2*q+b+2
    t = {}
    def put(i,v):
        need(i not in t, 'unique tile index')
        t[i] = tuple(v)
    put(0,(2,435,3,1))
    for j,(u,v,d) in enumerate(actions):
        q,b = divmod(j,2)
        put(j+1,((1-d)*r(0,u),h(q,b),d*r(1,u),v))
    for a in (0,1):
        for b in (0,1):
            put(433-2*a+b,(0,432*a+b,0,432*a+b))
    for d in (0,1):
        for q in S[d]:
            for b in (0,1):
                rdq = r(d,q)
                put(423+2*rdq+b,(d*rdq,b,(1-d)*rdq,h(q,b)))
    for a in (0,1):
        for b in (0,1): put(923+2*a+b,(0,432*a+b,0,438))
    put(927,(2,434,2,0))
    put(928,(3,436,4,4))
    put(929,(4,436,4,0))
    for x in (434,435,436): put(496+x,(1,438,1,x))
    for a in range(3):
        for b in range(3): put(933+3*a+b,(a*a,437,b,437))
    need(set(t)==set(range(942)), 'all and only 942 indexed tiles')
    return [t[i] for i in range(942)]

def psi(t):
    out = defaultdict(int)
    for j in range(8):
        out[978+j] += t**j
        out[969+j] += t**(17+j)
    for j in range(9):
        out[960+j] += t**(8+j)
        out[942+j] += t**(25+j)
    out[1005] += 2-t
    return dict(out)

def constants(indexed):
    rho = 1 << 47
    power = lambda n: 1 << (47*n)
    B = power(4027)
    beta = B-1
    Lambda = power(1992)+power(2998)
    phi = defaultdict(int)
    for i,(w,n,p,s) in enumerate(indexed):
        phi[i] += 1 + 1024*(1+w+256*n+131072*p+33554432*s)
    for i,c in psi(2).items(): phi[i] += 1024*c
    MC = beta - power(977) - sum(power(i) for i in range(942))
    MC -= sum(c*power(i) for i,c in psi(1).items())
    MF = B+3+((1<<44)-2)*Lambda
    MF += sum(power(960+i) for i in range(9))
    MF += sum(power(987+i) for i in range(8))
    MF += power(1005)+(1<<27)*power(4022)-power(4004)
    K = power(18)+power(1005)+power(4036)
    for c in (1992,2998):
        K += sum(v*power(c-i) for i,v in phi.items())
    return {'beta':beta, 'K':K, 'MC':MC, 'MF_source':MF}

