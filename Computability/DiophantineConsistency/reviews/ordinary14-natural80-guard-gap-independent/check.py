#!/usr/bin/env python3
"""Independent source-premise and exact guard-identity review; no Lean."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2]
files={
'research/ordinary14-natural80-guard-gap-draft/Natural80GuardGap.lean':'df59908f11990a28b4b788d0014757a897f2bdc1a4011772e0e825397cad43eb',
'research/ordinary14-natural80-partial74-bridge-draft/Natural80Partial74.lean':'942674c7951850ae30d457410cfc7a0359fc255831c31a87fc914a5ef3035c16',
'research/ordinary14-natural80-jpos-model-draft/Natural80JPos.lean':'6ac50565b28ac25581504ff28c1b4d6785c61607423d0bed7c22532d6ec8e221',
'research/ordinary14-74-ownzero-units-draft/OwnZeroUnits74.lean':'668fb089dad1ced2867530cb7f95919eb584d49f4aa953903a7e2b6d526de43c',
'research/ordinary14-74-ownzero-guard-strict-draft/OwnZeroGuardStrict74.lean':'d8d99e58177cdc6fde4fad5f79b577ce97023162656931691ce314141f98e1b8',
'research/ordinary14-unit75-guard74-lean-draft/P74PositiveGuard.lean':'5c441b8df055693e745967f01ef8128d808f5915e3cffb906473499745c4c11b',
'research/ordinary14-positive-guard74/candidate.json':'e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093',
'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998'}
s={}
for p,h in files.items():
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p.rsplit('/',1)[-1]]=b.decode()
a=s['Natural80GuardGap.lean'];part=s['Natural80Partial74.lean'];j=s['Natural80JPos.lean'];unit=s['OwnZeroUnits74.lean'];guard=s['OwnZeroGuardStrict74.lean'];lean=s['P74PositiveGuard.lean'];g=json.loads(s['candidate.json']);diff=s['ModelDifferenceRing.lean']
def hdr(src,name):
 m=re.search(r'\btheorem\s+'+name+r'\b(.*?)\s*:=\s*by',src,re.S);assert m,name
 return ' '.join(m.group(1).split())
h=hdr(a,'gap_of_80_zero')
for x in ('(hbeta : (p 0 : DiffRing V)=ι beta)','(hK : (p 1 : DiffRing V)=ι K)',
 '(hb : 0<beta) (hKpos : 0<K)','(hz : InternalZero (P80NaturalForcedGamma.graph p).output v)',
 'let u := partial74 v','u 1+u 2 < q beta u'):
 assert x in h,x
assert '(hv :' not in h and '(hgamma' not in h and '(hf :' not in h
for x in ('Natural80JPosDraft.J_pos_of_zero p K v hK hKpos hz',
 '(internalZero_iff_partial p v).mp hz',
 'guard_factor_one p beta u hbeta hb hJ hw hs hz74',
 'guard_eval p beta K u hbeta hK',
 'have hh1 : (1:DiffRing V)≤ι (u 13)',
 'have hqcast : ι (q beta u)=(1:DiffRing V)+ι (u 0*beta)',
 'exact ι_lt_ι.mp hsum',
 '#print axioms DiophantineConsistency.Natural80GuardGapDraft.gap_of_80_zero'):
 assert x in a,x
assert 'if j = 0 ∨ j = 3 ∨ j = 8 ∨ j = 11 ∨ j = 12 then v j else v j + 1' in part
assert '(hK : (p 1 : DiffRing V) = ι κ) (hκ : 0 < κ)' in hdr(j,'J_pos_of_zero')
gh=hdr(unit,'guard_factor_one')
for x in ('(hbeta : (p 0 : DiffRing V)=ι beta) (hb : 0<beta)',
 '(hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)'):
 assert x in gh,x
assert '(hv :' not in gh
ge=hdr(guard,'guard_eval')
for x in ('(hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)',
 '(ι (q beta v)-ι (v 1)-ι (v 2))*(ι (X beta v)+ι K)',
 '(ι (q beta v)-ι (v 1))-ι (v 0*beta)*ι (v 13)'):
 assert x in ge,x
assert '(hv : ∀ j, 0<v j)' in hdr(guard,'strict_of_zero')
assert 'theorem ι_nonneg' in diff and 'theorem ι_le_ι' in diff and 'theorem ι_lt_ι' in diff
block=lean.split('  -- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0]
rows=[]
for line in block.splitlines():
 m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line);assert m,line
 n,x,op,y=m.groups();atom=lambda v:int(v) if v.isdecimal() else v
 rows.append([n,op,atom(x),atom(y)])
assert rows==g['source'] and len(rows)==74
by={n:[op,x,y] for n,op,x,y in rows}
shape={'qm':['*','J','beta'],'q':['+',1,'qm'],'X':['*','q','w'],'qF':['-','q','F'],
 'C':['-','qF','alpha'],'g26':['+','X','K0'],'g27':['*','C','g26'],
 'guard_base':['+','g27','qF'],'bt_quotient':['*','qm','h'],'guard':['-','guard_base','bt_quotient']}
for n,row in shape.items():assert by[n]==row,n
assert '⟨F0, F1, Fa, Fs, guard, out,' in lean
# Exact abstract integer-ring identity used when q=1+b.
def cn(n):return {():n} if n else {}
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
C,X,K,b,F,h=map(v,('C','X','K','b','F','h'));q=add(cn(1),b)
left=sub(add(mul(C,add(X,K)),sub(q,F)),mul(b,h))
right=sub(add(mul(C,add(X,K)),sub(cn(1),F)),mul(b,sub(h,cn(1))))
assert left==right
print(json.dumps({'scope':'bounded model-source premises and exact guard identity; no Lean theorem',
 'pinned_sources':len(files),'p74_graph_rows':len(rows),'guard_rows_checked':len(shape),
 'represented_positive_beta_K_explicit':True,'gamma_positivity_not_assumed':True,
 'guard_identity_sparse_checked':True,'axiom_command_unexecuted':True},sort_keys=True,indent=2))
