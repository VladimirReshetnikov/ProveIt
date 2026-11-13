#!/usr/bin/env python3
"""Exact local first-norm identity and bounded gate/inequality controls."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
g=json.loads((root/'research/ordinary10-two-norm-divisible61/candidate.json').read_text());r={x[0]:x[1:] for x in g['source']}
for n,row in {'g30':['+','ell','k'],'g40':['*','ell','g30'], 'g41':['+',1,'g40'],
 'tausq':['*','n_tau','n_tau'],'firstres':['-','tausq','g41'],
 'firstsq':['*','firstres','firstres'],'out':['+','sum1','A1sq']}.items():assert r[n]==row,(n,r[n])
refs=[row[0] for row in g['source'] if 'n_tau' in row[2:]]
assert refs==['tausq']
# Exact free polynomial identity in (ell,k,t).
zero=(0,0,0)
def cn(x):return {} if x==0 else {zero:x}
def var(i):return {tuple(int(j==i) for j in range(3)):1}
def add(a,b,sign=1):
 out=a.copy()
 for e,v in b.items():out[e]=out.get(e,0)+sign*v
 return {e:v for e,v in out.items() if v}
def mul(a,b):
 out={}
 for e,v in a.items():
  for d,w in b.items():
   key=tuple(x+y for x,y in zip(e,d));out[key]=out.get(key,0)+v*w
 return {e:v for e,v in out.items() if v}
ell,k,t=(var(i) for i in range(3));one=cn(1);two=cn(2)
tau=add(ell,t)
old=add(mul(tau,tau),add(one,mul(ell,add(ell,k))),-1)
new=add(add(mul(t,t),one,-1),mul(ell,add(mul(two,t),k,-1)))
assert old==new
# Independent simple circuit count, allowing reuse only of existing ell and k.
old_rows=[('+','ell','k'),('*','ell','g30'),('+',1,'g40'),('*','tau','tau'),('-','tausq','g41')]
new_rows=[('*','t','t'),('-', 'tsq',1),('*',2,'t'),('-', 'twot','k'),('*','ell','gap'),('+','base','prod')]
assert len(old_rows)==5 and len(new_rows)==6
# Exact square-difference formulas, checked symbolically with same ring.
rad=add(one,mul(ell,add(ell,k)))
L=add(mul(add(ell,one),add(ell,one)),rad,-1)
assert L==mul(ell,add(two,k,-1)) # (ell+1)^2-radicand = ell*(2-k)
upper=add(add(ell,k),one,-1)
assert add(mul(upper,upper),rad,-1)==mul(add(k,two,-1),add(ell,k))
# Small direct controls; the square inequalities are proved in README.
count=0
for e in range(1,80):
 for kk in range(3,80):
  for tt in (e+1,e+kk-1):assert tt*tt!=1+e*(e+kk)
  count+=1
print(json.dumps({'literal_first_norm_five_rows_checked':True,'offset_identity_exact':True,
 'tau_used_only_in_first_norm':True,'simple_offset_local_gates':6,
 'old_local_gates':5,'endpoint_controls':count,'positive_port_endpoint_substitutions_excluded':True,
 'global_gate_lower_bound_proved':False,'smaller_graph_constructed':False,
 'lean_executed':False},indent=2,sort_keys=True))
