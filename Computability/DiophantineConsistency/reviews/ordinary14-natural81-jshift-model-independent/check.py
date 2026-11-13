#!/usr/bin/env python3
"""Independent finite source and formal guard-cut checks; no Lean."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2]
def pin(path,digest):
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==digest,path;return b
paths={
 'bridge':('research/ordinary14-natural81-jshift-model-draft/Natural81JShift.lean','f8e6436236c850e013ea9b9f9bbfe2ce48c45625a1d58ac1865e0413d96a5ca6'),
 'lean81':('research/ordinary14-natural-forcedj81-lean-draft/P81NaturalForcedJ.lean','73fbd4a953a32c7c56a1e1b06f93c4da9aed950c8022f8988ac82c6c06353897'),
 'lean82':('research/ordinary14-natural-forced82-lean-draft/P82NaturalForced.lean','4fd5635afea3327181cdce6d176103195a9d2698f40ab8c40e2ea5c9a9b1fb84'),
 'json81':('research/ordinary14-natural-forcedj81/candidate.json','24d0c9f0f7d0078f268b27f6d3a0698952fbc0b13c4d28b4e5f9152dc4a41999'),
 'json82':('research/ordinary14-root74-natural-forced82/candidate.json','1532ea5ec5f8dee349353044b9618a2e8a633f618e6f7ef5f1d19630b53b6c8a'),
 'difference':('Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998')}
x={n:pin(*p).decode() for n,p in paths.items()}
g81=json.loads(x['json81']);g82=json.loads(x['json82'])
def parse(source):
 block=source.split('  -- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0]
 def atom(x):return int(x) if x.isdecimal() else x
 rows=[]
 for line in block.splitlines():
  m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line);assert m,line
  n,a,op,b=m.groups();rows.append([n,op,atom(a),atom(b)])
 return rows
r81=parse(x['lean81']);r82=parse(x['lean82'])
assert r81==g81['source'] and r82==g82['source'] and len(r81)==81 and len(r82)==82
old={r[0]:r[1:] for r in r82};new={r[0]:r[1:] for r in r81}
assert set(old)-set(new)=={'J'} and set(new)<=set(old) and old['J']==['+','n_J',1]
for n,row in new.items():
 op,a,b=old[n];assert row==[op,'n_J' if a=='J' else a,'n_J' if b=='J' else b]
shape={'alpha':['+','n_alpha',1],'w':['+','n_w',1], 'qm':['*','n_J','beta'],
 'q':['+',1,'qm'],'X':['*','q','w'],'qF':['-','qm','n_F'],'C':['-','qF','alpha'],
 'g26':['+','X','K0'],'g27':['*','C','g26'],'guard_base':['-','g27','n_F'],
 'bt_quotient':['*','qm','n_h'],'guard':['-','guard_base','bt_quotient'],
 'P01':['*','F0','F1'],'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],
 'P01234':['*','P0123','guard'],'out':['-','P01234',1]}
for n,row in shape.items():assert new[n]==row,n
# The exact J=0 guard identity over Z[F,A,W,K], represented as sparse
# polynomials. The graph rows above bind these algebraic operations to names.
def c(n):return {():n} if n else {}
def v(n):return {(n,):1}
def add(a,b):
 z=dict(a)
 for m,w in b.items():z[m]=z.get(m,0)+w
 return {m:w for m,w in z.items() if w}
def neg(a):return {m:-w for m,w in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 z={}
 for i,x in a.items():
  for j,y in b.items():
   m=tuple(sorted(i+j));z[m]=z.get(m,0)+x*y
 return {m:w for m,w in z.items() if w}
f,al,w,k=map(v,('F','A','W','K'))
qf=neg(f);alpha=add(al,c(1));cc=sub(qf,alpha);X=add(w,c(1))
actual=sub(mul(cc,add(X,k)),f)
target=sub(neg(mul(add(add(f,al),c(1)),add(add(w,c(1)),k))),f)
assert actual==target
s=x['bridge'];d=x['difference']
for token in ('def down','if j = 0 then v j - 1 else v j',
 'theorem output_eval','theorem guard_zero_cut','theorem guard_at_most_negative_two',
 '(hK : (p 1 : DiffRing V) = ι κ) (hκ : 0 < κ)',
 'theorem J_pos_of_zero','have hp : P*G = 1','have hG : G ≤ -2',
 'ModelDifferenceRing.one_le_of_pos','def Related','v81 0 = v82 0 + 1',
 'theorem internalZero_iff_related','theorem exists_zero_iff'):
 assert token in s,token
assert 'theorem ι_nonneg' in d and 'theorem ι_lt_ι' in d and 'theorem one_le_of_pos' in d
print(json.dumps({'scope':'source and formal guard-cut audit; no Lean elaboration or internal proof',
 'source_graphs_matched':2,'guard_cut_exact_sparse_identity':True,'represented_positive_K0_explicit':True,
 'shifted_slot':0,'direction':'v81[0]=v82[0]+1'},sort_keys=True,indent=2))
