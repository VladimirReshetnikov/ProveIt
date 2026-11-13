#!/usr/bin/env python3
"""Independent pinned graph, guard identity and source-premise audit; no Lean."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2]
files={
'research/ordinary14-natural80-jpos-model-draft/Natural80JPos.lean':'6ac50565b28ac25581504ff28c1b4d6785c61607423d0bed7c22532d6ec8e221',
'research/ordinary14-natural-forced-gamma80-lean-draft/P80NaturalForcedGamma.lean':'015214c4176ab1600c573297521b43987eb66fe863d918a6bcff803a76ca44d9',
'research/ordinary14-natural-forced-gamma80/candidate.json':'136560324b95b3fda68d10ebe49bdba0a02e950e0bf6b7f1b1588baea4805bf5',
'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998'}
s={}
for p,h in files.items():
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p.rsplit('/',1)[-1]]=b.decode()
a=s['Natural80JPos.lean'];lean=s['P80NaturalForcedGamma.lean'];g=json.loads(s['candidate.json']);diff=s['ModelDifferenceRing.lean']
block=lean.split('  -- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0]
rows=[]
for line in block.splitlines():
 m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line);assert m,line
 n,x,op,y=m.groups();atom=lambda v:int(v) if v.isdecimal() else v
 rows.append([n,op,atom(x),atom(y)])
assert rows==g['source'] and len(rows)==80 and g['domain']=='nonnegative integers'
by={n:[op,x,y] for n,op,x,y in rows}
shape={'alpha':['+','n_alpha',1],'w':['+','n_w',1], 'qm':['*','n_J','beta'],
 'q':['+',1,'qm'],'X':['*','q','w'],'qF':['-','qm','n_F'],'C':['-','qF','alpha'],
 'g26':['+','X','K0'],'g27':['*','C','g26'],'guard_base':['-','g27','n_F'],
 'bt_quotient':['*','qm','n_h'],'guard':['-','guard_base','bt_quotient'],
 'P01':['*','F0','F1'],'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],
 'P01234':['*','P0123','guard'],'out':['-','P01234',1]}
for n,v in shape.items():assert by[n]==v,n
assert '⟨F0, F1, Fa, Fs, guard, out, qF, C, G, R⟩' in lean
assert '(graph p).strong * (graph p).guardFactor - 1 := by rfl' in lean
# Algebraic guard identity in a free commutative ring at J=0. Port beta,
# gamma and the other graph factors are not assumed positive.
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
f,aa,w,k=map(v,('f','alpha','w','K0'))
qf=neg(f);alpha=add(aa,cn(1));cc=sub(qf,alpha);X=add(w,cn(1))
actual=sub(mul(cc,add(X,k)),f)
target=sub(neg(mul(add(add(f,aa),cn(1)),add(add(w,cn(1)),k))),f)
assert actual==target
h=re.search(r'theorem J_pos_of_zero\b(.*?)\s*:=\s*by',a,re.S);assert h
header=' '.join(h.group(1).split())
for token in ('(p : Fin 4 → ℤ) (κ : V) (v : Fin 14 → V)',
 '(hK : (p 1 : DiffRing V) = ι κ) (hκ : 0 < κ)',
 '(hz : InternalZero (P80NaturalForcedGamma.graph p).output v) : 0 < v 0'):
 assert token in header,token
assert '(hb' not in header and '(hgamma' not in header
assert '[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in a
for token in ('theorem guard_zero_cut','theorem guard_at_most_negative_two','have hp : P*G = 1',
 'have hG : G ≤ -2','ModelDifferenceRing.one_le_of_pos',
 '#print axioms DiophantineConsistency.Natural80JPosDraft.J_pos_of_zero'):
 assert token in a,token
for token in ('theorem internalZero_iff','theorem ι_nonneg','theorem ι_lt_ι','theorem one_le_of_pos'):
 assert token in diff,token
print(json.dumps({'scope':'bounded source and exact guard-cut audit; no Lean model theorem',
 'graph_rows':len(rows),'guard_and_product_rows_checked':len(shape),
 'represented_positive_K0_explicit':True,'beta_gamma_positivity_not_assumed':True,
 'guard_cut_sparse_identity':True,'axiom_report_unexecuted':True},sort_keys=True,indent=2))
