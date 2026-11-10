#!/usr/bin/env python3
"""Finite current-port scalar checks for a symbolic candidate-zero proof."""
import gzip
import hashlib
import json
import math
from pathlib import Path
HERE=Path(__file__).resolve().parent;D=HERE.parents[1]
pins={
 'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json':'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e',
 'research/current14-carrier64-transport-proposal/graph.json':'f3bc67492c0aa88c9881bf7e2c39e1586e38b3324305b025b010c0912625af43',
 'research/current14-carrier64-pell-floor/result.json':'8edbf8c5b59d4ba77d2bea5beb54f380bef1b7c1ddb3df8ef98e79c009b8181a',
 'research/current14-carrier64-toy-full-zero/check.py':'d1762aacab7f04df09a945f77a69cc6c9a0f0a08da15ba3efbb5289cc28ce476',
 'research/current14-carrier64-toy-full-zero/result.json':'04548f6ce0d53ce1c95f97af66e7e400d7357da447cf52751758d9b93f1d8b02'}
for name,digest in pins.items():
    if hashlib.sha256((D/name).read_bytes()).hexdigest()!=digest:raise RuntimeError(f'pin changed: {name}')
source=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
g=json.loads(source.read_bytes());ports={}
for name,meta in g['coefficient_binding']['ports'].items():
    packed=(source.parent/'coefficients'/meta['file']).read_bytes()
    if hashlib.sha256(packed).hexdigest()!=meta['gzip_sha256']:raise RuntimeError('gzip mismatch')
    raw=gzip.decompress(packed)
    if hashlib.sha256(raw).hexdigest()!=meta['raw_sha256']:raise RuntimeError('raw mismatch')
    ports[name]=int.from_bytes(raw,'big')
beta,K,lo,mf=[ports[x] for x in ('beta','K0','MC','MF')]
B=beta.bit_length();q=beta+1;hi=mf-beta
if not (beta==(1<<B)-1 and B==94517 and K>0 and 0<lo<beta< mf<2*beta and
        lo%4==2 and hi%8==4 and lo.bit_count()+hi.bit_count()==B and lo+hi>beta):
    raise RuntimeError('fixed-port prerequisites failed')
G=q*(hi-1)+lo+1;R=(G+1)*q*q-1;N=(R-1)//2
if not (G>0 and R>=2*B and R%4==3 and R.bit_count()==3*B+2 and N.bit_count()==3*B+1 and
        R==G*(q*q-1)+lo+q*mf):
    raise RuntimeError('saturated rank prerequisites failed')
u,r=divmod(G,beta);F0=q-u;alpha0=r;C0=u-r
if not (2<=u<=beta and 1<=r<u and F0==q-hi and C0==beta-lo):
    raise RuntimeError('old scalar coordinates failed')
exponent_residue=(R-B)%B;wmod=1<<exponent_residue;Mmod=(K+wmod)%beta
divisor=math.gcd(Mmod+1,beta)
if divisor!=1:raise RuntimeError('transport coefficient not invertible')
d=((F0-Mmod*C0)*pow(Mmod+1,-1,beta))%beta
F=F0-d;C=C0+q*d
if not (0<d<F0 and F>0 and C>0 and q*(q-F)-C==G and
        (Mmod*C-F)%beta==0 and (Mmod*C0-F0)%beta!=0 and q-F-C<0):
    raise RuntimeError('candidate transport or old obstruction failed')
def digest_integer(x):
    return hashlib.sha256(x.to_bytes((x.bit_length()+7)//8,'big')).hexdigest()
print(json.dumps({'pins':pins,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'beta_mersenne_exponent':B,'rank_bit_length':R.bit_length(),'rank_mod_4':R%4,
 'rank_population':R.bit_count(),'N_population':N.bit_count(),'w_exponent_residue':exponent_residue,
 'transport_coefficient_gcd':divisor,'delta_bit_length':d.bit_length(),'delta_sha256':digest_integer(d),
 'delta_positive_and_below_F0':True,'candidate_transport_congruence':True,
 'old_same_q_R_w_transport_congruence':False,'candidate_recovered_alpha_negative':True,
 'scope':'finite current-port scalar checks; complete witness remains symbolic, no Lean run'},
 sort_keys=True,indent=2))
