#!/usr/bin/env python3
"""Sparse exact polynomial checks for the conditional integer argument in README."""
import json
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('invoke python3 -I -S -B')
D=4
Z=(0,)*D

def c(v): return {} if v == 0 else {Z:v}
def var(i):
    x=[0]*D; x[i]=1
    return {tuple(x):1}
def add(*ps):
    r={}
    for p in ps:
        for m,v in p.items(): r[m]=r.get(m,0)+v
    return {m:v for m,v in r.items() if v}
def neg(p): return {m:-v for m,v in p.items()}
def sub(p,q): return add(p,neg(q))
def mul(*ps):
    r=c(1)
    for p in ps:
        nxt={}
        for m,a in r.items():
            for n,b in p.items():
                k=tuple(i+j for i,j in zip(m,n));nxt[k]=nxt.get(k,0)+a*b
        r={m:v for m,v in nxt.items() if v}
    return r
def pw(p,n):
    r=c(1)
    for _ in range(n):r=mul(r,p)
    return r

h,x,y,L=[var(i) for i in range(D)]
k=mul(c(4),L);H=sub(mul(c(4),y,add(x,c(1))),c(1))
a=sub(mul(c(4),y),c(1))
b=sub(mul(c(4),add(k,c(1)),y),c(1))
d=sub(mul(sub(k,c(1)),y),L)
product=mul(h,x,sub(x,k),add(mul(k,x),c(1)))
left=mul(pw(mul(c(4),y),3),product)
right=mul(h,sub(H,a),sub(H,b),sub(mul(k,H),mul(c(4),d)))
assert left == right
# The second factorization proves divisibility by H after adding 4*h*a*b*d.
p=add(mul(sub(H,a),sub(H,b),sub(mul(k,H),mul(c(4),d))),mul(c(4),a,b,d))
quot=add(mul(k,pw(H,2)),neg(mul(k,H,add(a,b))),mul(k,a,b),neg(mul(c(4),d,H)),mul(c(4),d,add(a,b)))
assert p == mul(H,quot)
# Exponent-comparison difference after n=8+u is 86*u+71.
assert 30*(3*8-20)-(4*8+17)==71
assert 30*3-4==86

def pell(n,z):
    p,v=0,1
    for _ in range(n):p,v=v,z*v-p
    return p
q=2**30;Y=q**3;X=2**1000;n=8;r=9;t=2*Y
assert n>=8 and r<=n+2 and r%2==1 and Y>=q**3 and X>=32
assert t*pell(n,X*t*t+2)<pell(r,t*(X+1)+2)
assert Y**(n-2)<8*X**2
assert X>8*(q-1)*(2**r)**2*Y**2
print(json.dumps({'status':'PASS','ring_identity_terms':len(left),'exponent_difference':'86*(n-8)+71','sample_n':n,'sample_r':r,'sample_strict_gap':True,'scope':'exact identities and one sample; universal ordinary-integer proof is in README; no Lean result'},sort_keys=True,indent=2))
