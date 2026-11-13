#!/usr/bin/env python3
"""Independent exact row edit and universal polynomial evaluation."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
old=json.loads((root/'research/ordinary10-two-norm-divisible61/candidate.json').read_text())
new=json.loads((root/'research/ordinary10-divisible61-s-unshift60-universal-zero/candidate.json').read_text())
assert len(old['source'])==61 and len(new['source'])==60
assert old['witnesses']==new['witnesses'] and old['fixed_numerals']==new['fixed_numerals']
expected=[];edits=[]
for row in old['source']:
 if row[0]=='s':assert row==['s','+','n_s',1];edits.append('remove_s');continue
 if row[0]=='Y':assert row==['Y','*','q3','s'];row=['Y','*','q3','n_s'];edits.append('replace_Y_s')
 expected.append(row)
assert new['source']==expected and edits==['remove_s','replace_Y_s']
# Independent live graph traversal and topological check.
env=set(new['witnesses']+new['fixed_numerals']);rows={}
for name,op,a,b in new['source']:
 assert name not in env and op in ('+','-','*')
 assert all(not isinstance(z,str) or z in env for z in (a,b))
 env.add(name);rows[name]=(a,b)
stack=[new['output']];live=set();used=set()
while stack:
 n=stack.pop()
 if not isinstance(n,str):continue
 if n not in rows:used.add(n);continue
 if n in live:continue
 live.add(n);stack.extend(rows[n])
assert len(live)==60 and set(new['witnesses'])<=used
# Exact sparse Z[beta,w,L,MC,MF] evaluation; K0=beta*L-w-1.
n=5;zero=(0,)*n
def K(x):return {} if x==0 else {zero:x}
def symbol(i):return {tuple(int(j==i) for j in range(n)):1}
def add(a,b,sign=1):
 o=a.copy()
 for k,v in b.items():o[k]=o.get(k,0)+sign*v
 return {k:v for k,v in o.items() if v}
def mul(a,b):
 o={}
 for k,v in a.items():
  for j,w in b.items():
   z=tuple(x+y for x,y in zip(k,j));o[z]=o.get(z,0)+v*w
 return {k:v for k,v in o.items() if v}
b,w,L,MC,MF=map(symbol,range(5));one=K(1);q=add(b,one)
K0=add(add(mul(b,L),w,-1),one,-1)
rank=add(mul(add(one,mul(b,b)),add(mul(q,q),one,-1)),add(MC,mul(q,MF)))
h=add(mul(add(b,one,-1),add(w,L)),one,-1)
v={'beta':b,'K0':K0,'MC':MC,'MF':MF,'n_J':one,'n_F':{},'n_alpha':{},
   'n_w':w,'n_s':{},'n_h':h,'n_tau':one,'n_eta':one,
   'n_zeta':add(rank,one,-1),'n_gamma':{}}
for name,op,a,z in new['source']:
 a=v[a] if isinstance(a,str) else K(a);z=v[z] if isinstance(z,str) else K(z)
 v[name]=mul(a,z) if op=='*' else add(a,z,1 if op=='+' else -1)
for name in ('Y','U','ell','Bres','firstres','Dstar','A1','out'):assert v[name]=={},name
assert v['R']==rank and v['kbase']==rank and v['k']==add(rank,one)
# Ceiling sanity controls, including large symbolic-size integers in memory only.
controls=0
for beta in list(range(2,40))+[(1<<67)-1]:
 for K0 in list(range(100))+[(1<<521)+17]:
  L=(K0+beta+1)//beta;w=beta*L-K0-1;h=(beta-1)*(w+L)-1
  assert L>=1 and 1<=w<=beta and h>=1
  assert (beta-1)*((beta+1)*w+K0)-1==beta*h
  controls+=1
base=root/'Lean/DiophantineConsistency/Compact44'
assert 'def betaNat : ℕ := 2^(67*8807)-1' in (base/'CompactFixedBeta.lean').read_text()
assert '![β,K,L,β+H]' in (base/'CompactSymbolicPorts.lean').read_text()
assert 'abbrev c44 : Fin 4 → ℕ := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat' in (base/'C44Short15Facts.lean').read_text()
print(json.dumps({'literal_edited_rows':edits,'live_binary_operations':len(live),
 'all_graph_residuals_zero_in_five_variable_integer_polynomial_ring':True,
 'ceiling_controls':controls,'fixed_compact_tuple_covered':True,
 'original_61_graph_nonequivalence_proved':False,'Lean_executed':False},indent=2,sort_keys=True))
