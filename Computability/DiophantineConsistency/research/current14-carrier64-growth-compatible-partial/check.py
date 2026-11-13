#!/usr/bin/env python3
"""Finite exponent/port checks for a growth-compatible symbolic partial."""
import gzip
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
D=HERE.parents[1]
SOURCE=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
PIN='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
raw=SOURCE.read_bytes()
if hashlib.sha256(raw).hexdigest()!=PIN: raise RuntimeError('source pin changed')
g=json.loads(raw); ports={}
for name,meta in g['coefficient_binding']['ports'].items():
    packed=(SOURCE.parent/'coefficients'/meta['file']).read_bytes()
    if hashlib.sha256(packed).hexdigest()!=meta['gzip_sha256']: raise RuntimeError('gzip mismatch')
    data=gzip.decompress(packed)
    if hashlib.sha256(data).hexdigest()!=meta['raw_sha256']: raise RuntimeError('raw mismatch')
    ports[name]=int.from_bytes(data,'big')
beta,K,mc,mf=[ports[x] for x in ('beta','K0','MC','MF')]
B=beta.bit_length();q=beta+1;R=q*q-1+mc+q*mf
if not (beta==(1<<B)-1 and beta>=31 and K>0 and mc%2==0 and R%2==1 and R>=27 and R>B):
    raise RuntimeError('fixed-port preconditions failed')
N=(R-1)//2
Yexp=R*R+3*B; Eexp=Yexp+R; mexp=Eexp+Yexp
if not (Yexp>R*N and Eexp==R*R+R+3*B and mexp==2*R*R+R+6*B and
        2*((R+1)//2)==R+1):
    raise RuntimeError('symbolic exponent arithmetic failed')
result={'source_sha256':PIN,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'beta_mersenne_exponent':B,'R_bit_length':R.bit_length(),'R_odd':True,
        'X':'2^R','Y':'2^(R²+3B)','E':'2^(R²+R+3B)',
        'Y_gt_X_to_N_by_exponents':True,'N':'(R-1)/2',
        'gap':1,'transport_identity':'same as independently reviewed power-window packet',
        'first_pell_extension':'symbolic via independently reviewed congruence lemma',
        'remaining_norms_solved':False,'full_zero_claimed':False}
print(json.dumps(result,sort_keys=True,indent=2))
