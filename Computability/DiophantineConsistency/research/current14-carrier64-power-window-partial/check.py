#!/usr/bin/env python3
"""Finite port checks and exact identities for a symbolic partial witness."""
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
D = HERE.parents[1]
SOURCE = D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
PIN = 'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
raw=SOURCE.read_bytes()
if hashlib.sha256(raw).hexdigest()!=PIN:
    raise RuntimeError('graph pin changed')
graph=json.loads(raw); ports={}
for name,meta in graph['coefficient_binding']['ports'].items():
    packed=(SOURCE.parent/'coefficients'/meta['file']).read_bytes()
    if hashlib.sha256(packed).hexdigest()!=meta['gzip_sha256']:
        raise RuntimeError('compressed port hash mismatch')
    data=gzip.decompress(packed)
    if hashlib.sha256(data).hexdigest()!=meta['raw_sha256']:
        raise RuntimeError('raw port hash mismatch')
    ports[name]=int.from_bytes(data,'big')
beta,K,mc,mf=[ports[x] for x in ('beta','K0','MC','MF')]
B=beta.bit_length(); q=beta+1
if not (beta==(1<<B)-1 and beta>=31 and K>0 and mc%2==0):
    raise RuntimeError('required fixed-port properties failed')
gap=1; R=(q*q-1)+mc+q*mf
if not (R>=26 and R%2==1 and R>=B and R>3*B and gap<2*q-1):
    raise RuntimeError('required rank/exponent properties failed')

# Exact polynomial gap and transport identities for F=C=q-1, z=K+w.
qv={(1,0,0):1}; kv={(0,1,0):1}; wv={(0,0,1):1}; one={(0,0,0):1}
def add(a,b):
    out=Counter(a);out.update(b)
    return {k:v for k,v in out.items() if v}
def sub(a,b):return add(a,{k:-v for k,v in b.items()})
def mul(a,b):
    out=Counter()
    for x,cx in a.items():
        for y,cy in b.items():
            out[tuple(a+b for a,b in zip(x,y))]+=cx*cy
    return {k:v for k,v in out.items() if v}
b=sub(qv,one); F=C=b; z=add(kv,wv)
if sub(mul(qv,sub(qv,F)),C)!=one:
    raise RuntimeError('gap identity failed')
Nt=sub(add(mul(add(kv,wv),C),sub(qv,F)),mul(z,b))
if Nt!=one:
    raise RuntimeError('transport identity failed')

# Do not attempt to materialize w=2^(R-B), s=2^R, or the Pell power.
# With these definitions, X=2^R, Y=2^(R+3B), E=2^(2R+3B),
# m=E*Y=2^(3R+6B), and 2*((R+1)/2)=R+1.
if not ((R-B)+B==R and R+3*B>R and
        2*R+3*B==(R)+(R+3*B) and
        3*R+6*B==(2*R+3*B)+(R+3*B) and
        2*((R+1)//2)==R+1):
    raise RuntimeError('symbolic exponent arithmetic failed')
result={'source_sha256':PIN,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'beta_mersenne_exponent':B,'R_bit_length':R.bit_length(),'R_odd':True,
        'R_gt_3B':True,'gap':1,'gap_below_old_positive_minimum':True,
        'transport_and_gap':'exact sparse polynomial identities',
        'X':'2^R','Y':'2^(R+3B)','E':'2^(2R+3B)',
        'first_pell_extension':'symbolic via independently reviewed congruence lemma',
        'remaining_norms_solved':False,'full_zero_claimed':False}
print(json.dumps(result,sort_keys=True,indent=2))
