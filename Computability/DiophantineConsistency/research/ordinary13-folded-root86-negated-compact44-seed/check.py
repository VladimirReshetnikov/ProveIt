#!/usr/bin/env python3
"""Actual compact44 CRT seed for a symbolic signed-fold zero; no Lean."""
import gzip,hashlib,json,math
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h;return b
raw=pin(D/'research/ordinary13-folded-root86-negated/candidate.json','186471e8454b9443df2234b25380d6b34d494e951648291645cc492a6d646166')
rows={r[0]:r for r in json.loads(raw)['source']}
for n,row in {'qm':['qm','*','J','beta'],'q':['q','+',1,'qm'],'C':['C','-','qF','alpha'],'Bt':['Bt','-','g27','g28'],'G':['G','+','alpha','g44'],'R':['R','+','g47','g50'],'A0':['A0','-','g38','g42'],'A1':['A1','-','g61','g65'],'Fa':['Fa','-','y2','g82'],'g72':['g72','-','g71','Q']}.items():assert rows[n]==row
p=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
bind=json.loads(pin(p/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
b115=json.loads(pin(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
v={}
for name,meta in bind['ports'].items():
 assert b115['ports'][name]['sha256_raw']==meta['sha256_raw'] and b115['ports'][name]['sha256_gzip']==meta['sha256_gzip']
 z=pin(p/meta['path'],meta['sha256_gzip']);data=gzip.decompress(z)
 assert len(data)==meta['raw_bytes'] and hashlib.sha256(data).hexdigest()==meta['sha256_raw']
 v[name]=int.from_bytes(data,'little')
B=590069;beta=v['beta'];K=v['K0'];MC=v['MC'];MF=v['MF'];q=beta+1
assert beta==(1<<B)-1 and K>=0 and 0<MC<beta<MF<2*beta
assert math.gcd(K+1,beta)==1
Q=q*q-1;assert math.gcd(Q,B)==math.gcd(beta,B)==1
residue=(-pow(K+1,-1,beta))%beta
alpha_B=(-((beta%B)**2*(Q%B)+MC%B+(q%B)*(MF%B))*pow(Q%B,-1,B))%B
alpha0=residue+beta*((alpha_B-residue)*pow(beta,-1,B)%B)
alpha0+=beta*B*((MC-alpha0)*pow(beta*B,-1,4)%4)
if alpha0<=beta:alpha0+=4*beta*B
R0=(beta*beta+alpha0)*Q+MC+q*MF
assert R0%B==0 and R0%4==3 and alpha0%beta==residue and alpha0>beta
T=4*B*beta;A=T*Q;L=R0.bit_length()+1;S=A.bit_length()+1
alpha=alpha0+T*sum(1<<(L+j*S) for j in range(4))
R=(beta*beta+alpha)*Q+MC+q*MF;N=(R-1)//2
assert R%B==0 and R%4==3 and R>=27
assert alpha>beta and alpha%beta==residue
assert (residue*((K+1)%beta)+1)%beta==0
assert N.bit_count()>=3*B+1 and R%3==0
assert R.bit_length()==9441197 and N.bit_count()==5379471
def digest(n):return hashlib.sha256(n.to_bytes((n.bit_length()+7)//8,'big')).hexdigest()
print(json.dumps({'beta_bit_length':B,'R_bit_length':R.bit_length(),'R_sha256_be':digest(R),'alpha_sha256_be':digest(alpha),'N_popcount':N.bit_count(),'Y_two_adic_valuation':N.bit_count()-1,'R_mod_B':R%B,'R_mod_4':R%4,'R_mod_3':R%3,'Bt_divisible_by_beta':True,'Bt_negative':True,'scope':'actual-port scalar seed and finite controls; full symbolic zero under independent review; no Lean or unrestricted parent-equivalence conclusion'},sort_keys=True,indent=2))
