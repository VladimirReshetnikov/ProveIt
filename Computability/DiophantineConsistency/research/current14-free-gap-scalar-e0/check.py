#!/usr/bin/env python3
"""Reproduce an actual-port transport/rank scalar fixed point; no Lean."""
import gzip,hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];p=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';raw=p.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(raw);v={}
for name,meta in g['coefficient_binding']['ports'].items():
 z=(p.parent/'coefficients'/meta['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==meta['gzip_sha256'];b=gzip.decompress(z);assert hashlib.sha256(b).hexdigest()==meta['raw_sha256'];v[name]=int.from_bytes(b,'big')
B=v['beta'].bit_length();beta=v['beta'];q=beta+1;C=342757;F=(C*(v['K0']+1))%beta or beta;alpha=q-F-C;gap=beta*(q-F)+alpha
assert B==94517 and q==1<<B and C>0 and F>0 and alpha>0
R=gap*(q*q-1)+v['MC']+q*v['MF'];N=(R-1)//2
assert R%4==3 and R%B==0 and R>=2*B and (C*(v['K0']+1)-F)%beta==0
assert R.bit_count()==282617 and N.bit_count()-1==282615<3*B
sha=lambda n:hashlib.sha256(n.to_bytes((n.bit_length()+7)//8,'big')).hexdigest()
print(json.dumps({'source_sha256':hashlib.sha256(raw).hexdigest(),'B':B,'C':C,'F_bits':F.bit_length(),'F_sha256':sha(F),'R_bits':R.bit_length(),'R_sha256':sha(R),'R_mod4':R%4,'w_exponent_mod_B':(R-B)%B,'R_popcount':R.bit_count(),'canonical_Y_valuation':N.bit_count()-1,'required_q3_valuation':3*B,'scope':'actual-port positive scalar and transport only; no Pell completion or full zero'},sort_keys=True,indent=2))
