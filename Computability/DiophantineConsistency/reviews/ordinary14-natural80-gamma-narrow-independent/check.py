#!/usr/bin/env python3
"""Independent source-premise and exact algebra audit; no Lean."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2]
files={
'research/ordinary14-natural80-gamma-narrow-draft/GammaZeroNarrow.lean':'f64c3701ac0894998823fee6eaf7497549aa73b7448ae26b327983b6155642a7',
'Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean':'29c748582368b4ab2bcdb4b4cdd4f7890dda32f77718e33355b590b8f07b7fbd',
'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean':'374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5',
'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean':'63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16'}
s={}
for p,h in files.items():
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p.rsplit('/',1)[-1]]=b.decode()
a=s['GammaZeroNarrow.lean'];main=s['DirectMainNorm.lean'];first=s['ArithmeticPellFirstNorm.lean'];rec=s['ArithmeticPellRecurrence.lean']
def hdr(src,name):
 m=re.search(r'\btheorem\s+'+name+r'\b(.*?)\s*:=\s*by',src,re.S);assert m,name
 return ' '.join(m.group(1).split())
h=hdr(a,'first_ordinate_lower')
for t in ('(P n k : V)','(hP : 0 < P)','(hn : 2 ≤ n)','(hcoord : 2*ycoord n (2*(P-1)+1) = k)','8*P+4 ≤ k'):assert t in h,t
h=hdr(a,'gamma_zero_impossible')
for t in ('(U X Y k eta R : V)','(hU : 0 < U)','(hY : 8 ≤ Y)','(hk : 0 < k)',
 '(hgap : R+1 < k)','(hcX : X < eta+Y*k)','(hnorm :','let P := U*(X+a*c)+H*(U*(0:V)+R+1)',
 'magnitude (P,N)*magnitude (P,N)=U*U*(1+(H+a*a)*(c*c))',': False'):assert t in h,t
mh=hdr(main,'direct_main_orientation')
assert '(hU : 0<U) (hY : 8≤Y) (hk : 0<k)' in mh and '0<G' not in mh.replace(' ','')
assert 'direct_main_orientation U X Y k eta (0:V) R hU hY hk hnorm' in a
assert 'theorem positive_parameter_solution (Q x k : V) (hQ : 0<Q)' in first
assert 'theorem ordinate_strictMono (b : V)' in rec
assert 'theorem x_succ (time b : V)' in rec and 'theorem y_succ (time b : V)' in rec
for n in ('first_ordinate_lower','gamma_zero_impossible'):
 assert '#print axioms DiophantineConsistency.GammaZeroNarrowDraft.'+n in a
# Exact polynomial comparison in Z[a,c]. It explains why no separate c>0
# premise is needed: the positive constant 1 remains if c=0.
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
def sq(a):return mul(a,a)
a0,c0,P=map(v,('a','c','P'));H=add(cn(3),mul(cn(4),a0));N=add(cn(1),mul(add(H,sq(a0)),sq(c0)))
assert sub(N,sq(mul(add(a0,cn(1)),c0)))==add(cn(1),mul(add(mul(cn(2),a0),cn(2)),sq(c0)))
B=add(mul(cn(2),sub(P,cn(1))),cn(1))
assert mul(cn(4),add(B,cn(2)))==add(mul(cn(8),P),cn(4))
print(json.dumps({'scope':'source hypotheses and exact algebra only; no Lean or graph theorem',
 'pinned_sources':len(files),'explicit_model_premises_checked':True,'positive_gamma_not_assumed':True,
 'square_comparison_and_recurrence_algebra_checked':True,'axiom_commands_unexecuted':2},sort_keys=True,indent=2))
