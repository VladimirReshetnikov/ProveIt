#!/usr/bin/env python3
"""Check finite current-port facts for the conditional Pell-theorem use."""
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
D = HERE.parents[1]
pins = {
 'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json': 'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e',
 'Lean/DiophantineConsistency/Compact44/P72Exact.lean': 'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',
 'Lean/DiophantineConsistency/Compact44/P72Power.lean': 'f46584fb3977ae5fc33b31bee18e8c27435d97bea10138f163af2de5ee66d462',
}
for path, digest in pins.items():
    if hashlib.sha256((D/path).read_bytes()).hexdigest() != digest:
        raise RuntimeError(f'pin mismatch: {path}')
source = D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
graph = json.loads(source.read_bytes())
ports = {}
for name, meta in graph['coefficient_binding']['ports'].items():
    packed = (source.parent/'coefficients'/meta['file']).read_bytes()
    if hashlib.sha256(packed).hexdigest() != meta['gzip_sha256']:
        raise RuntimeError('compressed port mismatch')
    raw = gzip.decompress(packed)
    if hashlib.sha256(raw).hexdigest() != meta['raw_sha256']:
        raise RuntimeError('raw port mismatch')
    ports[name] = int.from_bytes(raw, 'big')
beta, K, mc, mf = [ports[x] for x in ('beta','K0','MC','MF')]
q=beta+1; F=1; C=2*q-1; w=1+(q-2)*K; z=3+K*(2*q-1)
gap=q*(q-F)-C; R=gap*(q*q-1)+mc+q*mf
Y=q**3; X=w*q; E=X*Y
if not (q>=32 and K>0 and w>1 and w%2==1 and beta == (1 << beta.bit_length())-1 and
        beta%2==1 and mc%2==0 and R%2==1 and R>=26 and
        R+1<E and (K+w)*C+q-F-z*(q-1)==1 and R>=X.bit_length()):
    raise RuntimeError('fixed scalar conditions failed')

# Independent exact identity underlying the haux conversion:
# S²=d*(f²-1) and U-1=S²*(V²-y²)+y²-1.
one={(0,0,0,0):1}; d={(1,0,0,0):1}; f2={(0,1,0,0):1}
v2={(0,0,1,0):1}; y2={(0,0,0,1):1}
def add(a,b):
    out=Counter(a);out.update(b)
    return {k:v for k,v in out.items() if v}
def sub(a,b):return add(a,{k:-v for k,v in b.items()})
def mul(a,b):
    out=Counter()
    for aa,av in a.items():
        for bb,bv in b.items():
            out[tuple(x+y for x,y in zip(aa,bb))]+=av*bv
    return {k:v for k,v in out.items() if v}
coefficient=mul(d,sub(f2,one))
u_minus_one=sub(add(mul(coefficient,sub(v2,y2)),y2),one)
haux_difference=sub(add(mul(coefficient,v2),y2),add(one,mul(coefficient,y2)))
if u_minus_one != haux_difference:
    raise RuntimeError('auxiliary rearrangement failed')
result={'pins':pins,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'q_bit_length':q.bit_length(),'R_bit_length':R.bit_length(),'X_bit_length':X.bit_length(),
        'beta_mersenne_exponent':beta.bit_length(), 'R_odd':True,
        'R_plus_one_lt_E':True,'R_ge_X_bit_length':True,
        'w_odd_greater_than_one':True,'transport_is_one':True,
        'auxiliary_rearrangement':'exact sparse polynomial',
        'scope':'fixed scalar family; conditional on theorem hypothesis binding; no Lean run'}
print(json.dumps(result,sort_keys=True,indent=2))
