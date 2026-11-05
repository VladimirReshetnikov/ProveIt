#!/usr/bin/env python3
"""Finite arithmetic facts supporting the accompanying universal argument."""
import hashlib,json,math,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def require(b,s):
    if not b:raise RuntimeError(s)
def mul(x,y,d):
    a,b=x;c,e=y
    return a*c+d*b*e,a*e+b*c
def power(x,e,d):
    out=(1,0)
    while e:
        if e&1:out=mul(out,x,d)
        e//=2
        if e:x=mul(x,x,d)
    return out
n=12386; D=n*n-1; main_index=322
factors=[3,5,2477,4129]
require(math.prod(factors)==D and len(set(factors))==len(factors),'factorization')
for p in factors:
    require(p>1 and all(p%d for d in range(2,math.isqrt(p)+1)), 'nonprime factor')
g,c=power((n,1),main_index,D)
require(main_index%2==0 and c>1 and c%2==0,'main parity')
require(g*g-D*c*c==1,'Pell identity')
require(math.gcd(c,D)==1,'coprimality')
require(c.bit_length()==4686,'size')
result={'status':'PASS_FINITE_HYPOTHESES_ONLY','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'n':n,'Delta':D,'Delta_prime_factors':factors,'main_index':main_index,'c_bits':c.bit_length(),
 'c_even':True,'gcd_c_Delta':1,'norm':1,
 'c_sha256_unsigned_big_endian':hashlib.sha256(c.to_bytes((c.bit_length()+7)//8,'big')).hexdigest(),
 'scope':'Finite hypotheses for the universal handwritten argument in README; no Lean theorem or claim about other main tuples.'}
print(json.dumps(result,indent=2,sort_keys=True))
