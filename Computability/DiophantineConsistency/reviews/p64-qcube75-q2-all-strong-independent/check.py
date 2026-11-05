#!/usr/bin/env python3
"""Finite checks supporting an independently reviewed universal Pell argument."""
import hashlib,json,math,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent; parent=here.parents[1]/'research/p64-qcube75-q2-all-strong-obstruction'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
if sha(parent/'check.py')!='9322435c0bb31ef22854edd192acdfc3ced2dd25c434f1ef3c7b7b15271044e8' or sha(parent/'result.json')!='3fa83506bd5aba6a466a5f7079c25ff6e2124a61a55d1131bed14c00be066fd0':raise RuntimeError('author packet drift')
n=12386;D=n*n-1; factors=[3,5,2477,4129]
if math.prod(factors)!=D or len(set(factors))!=4 or any(any(p%d==0 for d in range(2,math.isqrt(p)+1)) for p in factors):raise RuntimeError('factorization or primality')
# Independently calculate the main Pell pair using the norm-one doubling law.
g,c=1,0
for bit in bin(322)[2:]:
    g,c=2*g*g-1,2*g*c
    if bit=='1':g,c=n*g+D*c,g+n*c
if g*g-D*c*c!=1 or c%2 or math.gcd(c,D)!=1 or c.bit_length()!=4686:raise RuntimeError('main Pell hypotheses')
# Exhaust finite norm-one pair groups in both quadratic-residue cases.
primes=[p for p in range(3,74,2) if all(p%d for d in range(2,math.isqrt(p)+1))]
counts={'split':0,'nonsplit':0};cheb=0
for p in primes:
    for v in range(p):
        delta=(v*v-1)%p
        if delta==0:continue
        x,y=1,0;orbit=[]
        while True:
            orbit.append((x,y))
            x,y=(v*x+delta*y)%p,(x+v*y)%p
            if (x,y)==(1,0):break
            if len(orbit)>p*p-1:raise RuntimeError('unit orbit bound')
        if len(orbit)%4==0:
            kind='split' if pow(delta,(p-1)//2,p)==1 else 'nonsplit';counts[kind]+=1
            even={b for j,(_,b) in enumerate(orbit) if j%2==0}
            odd={b for j,(_,b) in enumerate(orbit) if j%2==1}
            if even & (odd|{(-b)%p for b in odd}):raise RuntimeError('parity coefficient collision')
        # Check the odd Chebyshev identity at each admissible I, including ±I.
        for I in range(1,p):
            if (I*I+v*v-1)%p:continue
            T0,T1=1,I;U0,U1=1,(2*v)%p
            for j in range(1,40):
                if j%2 and (T1*pow(I,-1,p)-((-1)**((j-1)//2))*U0)%p:
                    raise RuntimeError('Chebyshev identity')
                T0,T1=T1,(2*I*T1-T0)%p
                U0,U1=U1,(2*v*U1-U0)%p
                cheb+=1
if not counts['split'] or not counts['nonsplit'] or not cheb:raise RuntimeError('missing test family')
result={'status':'PASS_FINITE_SUPPORT_AND_SOURCE_REVIEW','script_sha256':sha(Path(__file__)),
        'author_script_sha256':sha(parent/'check.py'),'author_result_sha256':sha(parent/'result.json'),
        'D':D,'distinct_prime_factors':factors,'c_bits':c.bit_length(),'c_even':True,'gcd_c_D':1,
        'small_field_order_multiple_four_counts':counts,'odd_chebyshev_steps_checked':cheb,
        'scope':'Finite supporting checks and mathematical source review only; no Lean theorem or assertion for other main tuples.'}
out=here/'result.json';payload=json.dumps(result,indent=2,sort_keys=True)+'\n'
if sys.argv[1:]==['--write']:
    with out.open('x') as f:f.write(payload)
elif sys.argv[1:]:raise SystemExit('usage: python3 -I -S -B check.py [--write]')
elif out.read_text()!=payload:raise SystemExit('result differs')
print(json.dumps(result,sort_keys=True))
