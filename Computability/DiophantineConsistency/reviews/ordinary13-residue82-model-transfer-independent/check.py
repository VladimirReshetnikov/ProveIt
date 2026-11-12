#!/usr/bin/env python3
"""Independent carrier asymmetry, scalar control and source interface audit."""
from pathlib import Path
import collections,hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
p=json.loads(pin('research/ordinary13-qcube-unscale84/candidate.json','2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77'))
c=json.loads(pin('research/ordinary13-residue-first82/candidate.json','bb90faa3815c5ff46f5fdbf41c2d001790d565baa17d97c79514c33fa928f1d2'))
pin('research/ordinary13-residue82-model-transfer-audit/result.json','299fc79374ecfd450ca78a66bb9b99f00552e2b61180dd2b1792704ebe684384')
pin('reviews/ordinary13-residue-first82-independent/result.json','75224f3e6b7811271bfa0cf343862ed09b80a9634e155521808de856a10c1a40')
indices=pin('Lean/DiophantineConsistency/Compact44/FreeJPellIndices.lean','9e098156d8aff2540e00ee31667954d7288844aad859c9df74f988c7fe0611ac')
early=pin('Lean/DiophantineConsistency/Compact44/FreeJEarlyIndex.lean','ab9b8e34903eff1e33e81b6a75438797eef1f2dab84595e23516b44de774ea3d')
finish=pin('Lean/DiophantineConsistency/Compact44/FreeJPowerFinish.lean','e4b2e84586b6232b9accc7775f094d4e1047453f1e8337f6241d39a6657d8816')
p72=pin('Lean/DiophantineConsistency/Compact44/P72Exact.lean','a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3')
assert 'magnitude (pairEval (core (fun j => (p j:ℤ))).z v)=M*first' in indices
assert '(hi : FreeJIndices p v)' in early and 'theorem early_index_of_facts' in early
assert 'theorem graph_power' in finish and '(hz : InternalZero (literal' in finish
assert 'theorem indices_ordinary' in p72 and '(haux :' in p72 and '(hi\' : 0 < i\')' in p72
assert len(p['source'])==84 and len(c['source'])==82 and p['witnesses']==c['witnesses'] and p['fixed_numerals']==c['fixed_numerals']
expect=[]
for n,op,x,y in p['source']:
 if n in ('g25','g28'):continue
 expect.append(['g26','+','X','K0'] if n=='g26' else ['Bt','-','g27','F'] if n=='Bt' else [n,op,x,y])
assert expect==c['source']
# The non-first residuals are independent of the changed root coordinate r.
for g in (p,c):
 rows={x[0]:x for x in g['source']}
 for target in ('A1','Fam','g72'):
  seen={target};todo=[target]
  while todo:
   for x in rows.get(todo.pop(),[None,None,None,None])[2:]:
    if isinstance(x,str) and x not in seen:seen.add(x);todo.append(x)
  assert 'r' not in seen,(g['scope'],target)
def atom(x):return {(x,):1}
def add(a,b,k=1):
 d=dict(a)
 for m,v in b.items():d[m]=d.get(m,0)+k*v
 return {m:v for m,v in d.items() if v}
def mul(a,b):
 d=collections.defaultdict(int)
 for ma,ca in a.items():
  for mb,cb in b.items():d[tuple(sorted(ma+mb))]+=ca*cb
 return {m:v for m,v in d.items() if v}
one={():1};B,C,X,K,F,k,ell,r,t,tau=map(atom,['b','C','X','K','F','k','ell','r','t','tau']);q=add(one,B)
D0=add(mul(C,K),F,-1);Bp=add(mul(C,add(X,K)),F,-1);old=add(mul(C,add(X,mul(K,q))),mul(F,q),-1)
assert old==add(Bp,mul(B,D0))
def carrier(P,R):return add(mul(B,add(add(add(ell,k),R),mul(k,P),-1)),P,-1)
assert carrier(old,add(r,mul(add(mul(k,B),one),D0)))==carrier(Bp,r)
P=mul(B,t);target=add(add(mul(k,add(P,one,-1)),t),add(tau,ell,-1))
assert carrier(P,target)==mul(B,tau)
N=add(one,mul(ell,add(ell,k)))
assert add(mul(add(ell,k),add(ell,k)),N,-1)==add(add(mul(ell,k),mul(k,k)),one,-1)
assert add(N,mul(ell,ell),-1)==add(one,mul(ell,k))
# Scalar control rules out a purported implication, not full graph zero.
beta,J,F0,alpha,K0,X0=46,1,1,45,0,47;q0=1+beta*J;C0=q0-F0-alpha
B0=C0*(X0+K0*q0)-F0*q0;Bp0=C0*(X0+K0)-F0
assert (q0,C0,B0,Bp0)==(47,1,0,46) and Bp0%(beta*J)==0
print(json.dumps({'scope':'source interfaces, exact carrier algebra and bounded scalar control; no Lean','parent_child_operations':[84,82],'carrier_update_identity':True,'positive_target_root_identity':True,'other_three_residuals_independent_of_r':True,'scalar_control_full_zero_claimed':False,'FreeJIndices_requires_original_core_z':True,'graph_power_requires_original_literal_zero':True,'all_model_calibration_remains_open':True},sort_keys=True,indent=2))
