#!/usr/bin/env python3
"""Pin literal roots and check formal substitutions; no Lean execution."""
from pathlib import Path
import hashlib,itertools,json,re
D=Path(__file__).resolve().parent;ROOT=D.parents[1]
PINS={
'research/adaptive87-current-cfold-witness-algebra-draft/CfoldWitnessAlgebra.lean.src':'0eca27aec7a66f82b530ccdb43262e0ad8c2c8694787a83de6c63a0660ee723f',
'research/adaptive87-current-cfold-witness-algebra-draft/CfoldWitnessRepresentatives.lean.src':'c1e5c02db61c5db82ad406e9c0d935a1b34918c596886d1d646216405b81c7f1',
'research/adaptive87-current-cfold88-degree28/graph.json':'26b5bc4c14320b0fe2891f3aeca0e216f26e555ee1206cefd71d7fcc7b674b36',
'research/adaptive87-four-square-current88-30/graph.json':'293dac5175d4924812177a1e73a316bf5cc16bf1b5cef636388d9e110eebb7ed',
'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998',
'research/current2011-shear-positive-gap-representation-draft/PositiveGapRepresentation.lean.src':'330544ffaedd3afc061931ace2b0518f3ebd5b855e56516944cc34322033b049'}
for n,h in PINS.items():assert hashlib.sha256((ROOT/n).read_bytes()).hexdigest()==h,n
old=json.loads((ROOT/'research/adaptive87-four-square-current88-30/graph.json').read_bytes());new=json.loads((ROOT/'research/adaptive87-current-cfold88-degree28/graph.json').read_bytes())
assert old['witnesses']==new['witnesses'] and old['witnesses'][8]=='r' and old['fixed_numerals']==new['fixed_numerals']
assert new['source']==[['root_skew','*','k','C'] if row[0]=='root_skew' else row for row in old['source']]
rows={x[0]:x for x in new['source']}
for row in [['qm','*','J','beta'],['q3','*','q','q2'],['C','-','qF','alpha'],['Bt','-','g27','g28'],['k','+','eta','zeta'],['ell','*','E','kY'],['M','*','q3','qm'],['g30','+','ell','k'],['g31','+','g30','r'],['root_skew','*','k','C'],['root_inner','-','g31','root_skew'],['root_scaled','*','M','root_inner'],['g33','*','Y','qm'],['root_btq3','*','Bt','q3'],['root_sum','+','root_scaled','g33'],['Z','-','root_sum','root_btq3'],['g38','*','Z','Z'],['g39','*','M','M'],['g40','*','ell','g30'],['g41','+',1,'g40'],['g42','*','g39','g41'],['A0','-','g38','g42'],['fa_minus','-','Fa',1],['output','+','sum1','strong_sq']]:assert rows.get(row[0])==row,row
source=(D/'CfoldWitnessAlgebra.lean.src').read_text();model=(D/'CfoldWitnessRepresentatives.lean.src').read_text()
for n in ['root_transport','sphere_transport','root_transport_inverse','switch_root','bt_gap','transported_positive','switch_positive']:assert re.search(r'^theorem '+n+r'\b',source,re.M),n
for n in ['direct_coordinate','switched_coordinate']:assert re.search(r'^theorem '+n+r'\b',model,re.M),n
assert 'theorem positive_as_successor (D : DiffRing V) (hD : 0 < D)' in (ROOT/'research/current2011-shear-positive-gap-representation-draft/PositiveGapRepresentation.lean.src').read_text()
for n in ['theorem ι_nonneg (a : V)','theorem ι_lt_ι {a b : V}']:
 assert n in (ROOT/'Lean/DiophantineConsistency/ModelDifferenceRing.lean').read_text()
# Sparse free-ring identities including the alternate +tau root branch.
N=9
def var(i):return {tuple(int(i==j) for j in range(N)):1}
one={(0,)*N:1}
def add(a,b,s=1):
 z=a.copy()
 for m,v in b.items():z[m]=z.get(m,0)+s*v
 return {m:v for m,v in z.items() if v}
def mul(a,b):
 z={}
 for m,v in a.items():
  for n,w in b.items():
   k=tuple(x+y for x,y in zip(m,n));z[k]=z.get(k,0)+v*w
 return {m:v for m,v in z.items() if v}
ell,k,rho,C,Bt,Y,b,q3,M=map(var,range(N))
def proot(r):return add(add(mul(M,add(add(add(ell,k),r),mul(k,Bt),-1)),mul(Y,b)),mul(q3,Bt),-1)
def croot(r):return add(add(mul(M,add(add(add(ell,k),r),mul(k,C),-1)),mul(Y,b)),mul(q3,Bt),-1)
rparent=add(rho,mul(k,add(Bt,C,-1)));assert proot(rparent)==croot(rho)
rchild=add(rho,mul(k,add(Bt,C,-1)),-1);assert croot(rchild)==proot(rho)
# Independent switch identity: M=q3*b, Y=q3*s and Bt=b*t.
ell,k,C,b,q3,s,t,tau,unused=map(var,range(N));M=mul(q3,b);Y=mul(q3,s);Bt=mul(b,t)
rchild=add(add(add(mul(add(C,one,-1),k),add(tau,ell,-1)),s,-1),t)
assert croot(rchild)==mul(M,tau)
counts={'bt_gap':0,'transported_positive':0,'switch_positive':0}
for q,C0,X,K,F in itertools.product(range(2,8),range(1,5),range(4,53),range(0,4),range(0,6)):
 if X>=q*q and F<=q-2:
  assert C0*(X+K*q)-F*q-C0>=2*q-1;counts['bt_gap']+=1
for rho0,k0,C0,Bt0 in itertools.product(range(1,5),range(0,5),range(-3,5),range(-3,5)):
 if Bt0>=C0:assert rho0+k0*(Bt0-C0)>0;counts['transported_positive']+=1
for C0,k0,tau0,ell0,s0,t0 in itertools.product(range(1,4),range(0,4),range(0,9),range(0,5),range(0,5),range(0,4)):
 if s0<tau0-ell0:assert (C0-1)*k0+(tau0-ell0)-s0+t0>0;counts['switch_positive']+=1
print(json.dumps({'status':'PASS','pins':PINS,'exact_free_ring_forward_inverse_switch':True,'graph_one_row_cut_and_root_shapes':True,
 'bounded_order_controls':counts,'limits':['Unelaborated Lean source; no provider selection or Lean execution.',
 'Graph evaluator binding and coordinate update are not proved in Lean; generic sphere identities are conditional on those bindings.',
 'Cal, Bt>=C extraction, Pell root/scale/gap extraction, and all-model endpoint remain open obligations.']},sort_keys=True,indent=2))
