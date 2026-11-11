#!/usr/bin/env python3
"""Finite actual-port/scalar controls for a symbolic free-gap full zero."""
import gzip,hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];p=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';raw=p.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(raw);v={}
for name,meta in g['coefficient_binding']['ports'].items():
 z=(p.parent/'coefficients'/meta['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==meta['gzip_sha256'];b=gzip.decompress(z);assert hashlib.sha256(b).hexdigest()==meta['raw_sha256'];v[name]=int.from_bytes(b,'big')
beta=v['beta'];q=beta+1;B=beta.bit_length();assert B==94517 and q==1<<B
e=28633;C=1;F=(v['K0']+pow(2,e,beta))%beta or beta;alpha=q-F-C;gap=beta*(q-F)+alpha
assert F>0 and alpha>0 and C==q-F-alpha
R=gap*(q*q-1)+v['MC']+q*v['MF'];assert R%4==3 and (R+1)%3==0
d=(R+1)//3;assert d%4==0
r=2*d;h=3*d//2;lam=d-1
assert r%B==e and r>=2*B and lam>=3*B and 2*h==R+1
# Dominant-power equality: (2YX)^(r−1)/(2*(4XY²)^(h−1))=Y.
assert (r-1)*(r+lam+1)-1-(h-1)*(r+2*lam+2)-lam==0
# Symbolic exponent inequalities prove 4Y(r−1)<X and h−1<XY².
assert (2*d-1).bit_length()<=d-1 and h.bit_length()<=r+2*lam
assert r-1>=h-1 and d>=8 and R>=2*B
assert ((v['K0']+pow(2,e,beta))*C-F)%beta==0
old_val=((R-1)//2).bit_count()-1;assert old_val==283515 and old_val<3*B
sha=lambda n:hashlib.sha256(n.to_bytes((n.bit_length()+7)//8,'big')).hexdigest()
print(json.dumps({'source_sha256':hashlib.sha256(raw).hexdigest(),'B':B,'C':C,'e':e,'F_bits':F.bit_length(),'F_sha256':sha(F),'R_bits':R.bit_length(),'R_sha256':sha(R),'R_mod4':R%4,'R_mod_B':R%B,'d_bits':d.bit_length(),'d_mod4':d%4,'r_mod_B':r%B,'dominant_exponent_identity':True,'old_canonical_Y_valuation':old_val,'required_q3_valuation':3*B,'scope':'finite actual-port controls for symbolic noncanonical Pell/CRT construction; no Lean or unrestricted existential nonequivalence'},sort_keys=True,indent=2))
