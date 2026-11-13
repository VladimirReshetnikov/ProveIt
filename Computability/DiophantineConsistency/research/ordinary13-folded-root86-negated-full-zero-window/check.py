#!/usr/bin/env python3
"""Finite controls and graph use-site checks for the symbolic toy zero; no Lean."""
import hashlib, json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def load(path, expected):
 raw=(D/path).read_bytes(); assert hashlib.sha256(raw).hexdigest()==expected
 return json.loads(raw)
signed=load('research/ordinary13-folded-root86-negated/candidate.json','186471e8454b9443df2234b25380d6b34d494e951648291645cc492a6d646166')
parent=load('research/ordinary13-four-square88-30/candidate.json','daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420')
rows={row[0]:row for row in signed['source']}
for n,row in {'C':['C','-','qF','alpha'],'G':['G','+','alpha','g44'],'Bt':['Bt','-','g27','g28'],'R':['R','+','g47','g50'],'A0':['A0','-','g38','g42'],'A1':['A1','-','g61','g65'],'Fa':['Fa','-','y2','g82'],'g72':['g72','-','g71','Q']}.items():assert rows[n]==row
assert [r[0] for r in signed['source'] if 'alpha' in r[2:]]==['C','G']
assert [r[0] for r in signed['source'] if 'MC' in r[2:]]==['g49']
assert [r[0] for r in signed['source'] if 'r' in r[2:]]==['g31']
def evaluate(graph, values):
 env=values.copy()
 def get(v):return env[v] if isinstance(v,str) else v
 for name,op,left,right in graph['source']:
  a,b=get(left),get(right)
  env[name]=a+b if op=='+' else a-b if op=='-' else a*b
 return env
beta,K,MC,MF=31,9,14,46
q=beta+1;G0=beta*(q-1)+14;R=G0*(q*q-1)+MC+q*MF
MC1=MC-beta*(q*q-1)
assert MC1==-31699 and R==998911 and (beta*(q-1)+45)*(q*q-1)+MC1+q*MF==R
assert q-1-45==-14 and q-1-14==17
# These are controls, not a search for full graph zeros: algebraically preserve
# all four residuals under the port and coordinate transformations.
for X in (1,2,31,32,101):
 for Y in (1,7,32768):
  val=dict(beta=beta,K0=K,MC=MC,MF=MF,J=1,F=1,alpha=14,f=3,i=2,T=4,X=X,Y=Y,r=7,eta=2,zeta=3,u=5,gamma=8)
  p=evaluate(parent,val); b=p['qm']; bt1=p['Bt']-b*(X+K*q)
  changed=dict(val,alpha=45,MC=MC1,r=-val['r']+p['k']*p['Bt']+(p['Bt']-bt1)//b)
  s=evaluate(signed,changed)
  assert s['Bt']==bt1 and s['R']==p['R'] and s['Z']==p['Z']
  for name in ('A0','A1','Fa','g72','out'):assert s[name]==p[name]
assert (2**20)>32 and -14*(1+9*32)-32<0
# A separate all-positive-port symbolic construction uses its own Pell seed.
R2=2**20-1; N2=(R2-1)//2
assert 995*(32**2-1)+30658+32==R2 and R2%4==3
assert N2.bit_count()-1==18 and pow(2,R2,31)==1
assert (-3*(pow(2,R2,31)+288)-32)%31==0
assert 2**(R2.bit_length()-1)>2**10
print(json.dumps({'all_positive_toy_ports':{'beta':31,'K0':9,'MC':30658,'MF':1},'all_positive_R':R2,'all_positive_Y_two_adic_valuation':18,'toy_ports':{'beta':31,'K0':9,'MC':MC1,'MF':46},'R':R,'C':-14,'F':1,'alpha':45,'finite_graph_controls':15,'scope':'symbolic full-zero transport from independently reviewed toy witness; no actual-port zero, Lean, or unrestricted existential nonequivalence'},sort_keys=True,indent=2))
