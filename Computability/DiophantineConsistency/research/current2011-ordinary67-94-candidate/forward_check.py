#!/usr/bin/env python3
"""Exact sparse polynomial certificate for the strong-multiplier forward map."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import hashlib,json
from pathlib import Path
N=5;one={(0,)*N:1}
def var(i):
    a=[0]*N;a[i]=1;return {tuple(a):1}
def add(a,b):
    r=a.copy()
    for k,v in b.items():r[k]=r.get(k,0)+v
    return {k:v for k,v in r.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
    r={}
    for k,v in a.items():
        for l,w in b.items():
            m=tuple(x+y for x,y in zip(k,l));r[m]=r.get(m,0)+v*w
    return {k:v for k,v in r.items() if v}
def sq(a):return mul(a,a)
d,i,c,f,G=(var(j) for j in range(N)); ic2=mul(i,sq(c))
S=sub(sq(f),mul(d,sq(ic2))); ip=mul(d,i); I=mul(ip,sq(c)); A=mul(d,sub(sq(f),one))
oldcoef=sq(mul(d,ic2));newcoef=A
# I²-A = Delta*(1-S); newcoef-oldcoef = Delta*(S-1).
if sub(sq(I),A)!=mul(d,sub(one,S)):raise RuntimeError('strong identity')
if sub(newcoef,oldcoef)!=mul(d,sub(S,one)):raise RuntimeError('auxiliary coefficient identity')
if sub(mul(newcoef,G),mul(oldcoef,G))!=mul(mul(d,sub(S,one)),G):raise RuntimeError('auxiliary norm identity')
print(json.dumps({'status':'PASS','checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'identities':['I_new²-Aaux=Delta*(1-S_old)','Na_new-U_old=Delta*(S_old-1)*G'],
 'scope':'universal commutative-ring identities; conditional forward witness map only, no model or reverse-existence proof'},indent=2,sort_keys=True))
