#!/usr/bin/env python3
"""Finite source, port, and exponent checks; symbolic witnesses unexpanded."""
import gzip, hashlib, json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def pin(rel, expected):
    b=(D/rel).read_bytes(); assert hashlib.sha256(b).hexdigest()==expected; return b
raw=pin('research/ordinary13-four-square88-30/candidate.json','daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420')
g=json.loads(raw); rows=g['source']; tab={r[0]:r for r in rows}
for n,row in {'Bt':['Bt','-','g27','g28'],'M':['M','*','q3','qm'],'Z':['Z','-','g34','folded_q3Bt'],'shift':['shift','-','g56','r0'],'Dstar':['Dstar','+','g58','g59'],'Fa':['Fa','-','y2','g82'],'g72':['g72','-','g71','Q']}.items(): assert tab[n]==row
assert [row[0] for row in rows if 'r' in row[2:]]==['g31']
p=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'; data=p.read_bytes();assert hashlib.sha256(data).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
ports={}
for n,meta in json.loads(data)['coefficient_binding']['ports'].items():
    z=(p.parent/'coefficients'/meta['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==meta['gzip_sha256']
    b=gzip.decompress(z);assert hashlib.sha256(b).hexdigest()==meta['raw_sha256'];ports[n]=int.from_bytes(b,'big')
beta,K,MC,MF=(ports[n] for n in ('beta','K0','MC','MF')); B=beta.bit_length();q=beta+1
assert B==94517 and q==1<<B
e=28633; F=(K+pow(2,e,beta))%beta or beta; alpha=q-F-1
assert 0<F<beta and alpha>0
R=(beta*(q-F)+alpha)*(q*q-1)+MC+q*MF
assert R%4==3 and (R+1)%3==0
d=(R+1)//3; rX=2*d; h=3*d//2; lam=d-1
assert d%4==0 and 2*h==R+1 and rX%B==e
assert rX>K.bit_length()+B+10 and lam>=3*B+2 and rX>=2*B+1
assert rX+lam==R and rX-B> B and ((K+pow(2,e,beta))-F)%beta==0
# rX > bit_length(K)+B+10 gives X>2^(B+10)*2^bit_length(K).
# w=X/2^B <=X/2 and K<X/2, hence E=X*Y>K+w.
assert B>=3 and K>0
sha=lambda n:hashlib.sha256(n.to_bytes((n.bit_length()+7)//8,'big')).hexdigest()
print(json.dumps({'parent_sha256':hashlib.sha256(raw).hexdigest(),'B':B,'K_bits':K.bit_length(),'R_bits':R.bit_length(),'R_sha256':sha(R),'F_sha256':sha(F),'d_mod4':d%4,'rX_mod_B':rX%B,'actual_port_exponent_bounds':True,'scope':'withdrawn alternate-carrier65-port attempt; auxiliary completion unproved; no full zero or Lean'},sort_keys=True,indent=2))
