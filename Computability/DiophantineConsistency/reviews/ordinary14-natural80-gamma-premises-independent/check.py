#!/usr/bin/env python3
"""Independent premise/interface and exact arithmetic audit; no Lean."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2]
files={
'research/ordinary14-natural80-gamma-premises-draft/GammaPremises.lean':'cfdbb97e748edbef9a8bf121cc3e44ac09bc91dc1e60e362b32d675df7ad7192',
'research/ordinary14-natural80-gamma-narrow-draft/GammaZeroNarrow.lean':'f64c3701ac0894998823fee6eaf7497549aa73b7448ae26b327983b6155642a7',
'Lean/DiophantineConsistency/ArithmeticPellClassification.lean':'77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78',
'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean':'374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5',
'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean':'63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16',
'Lean/DiophantineConsistency/BFS943/Direct80IndexOne.lean':'db0462fd907b629d9720106cfd9ea19fc8fa9e74e659d8286a039affbdc50761'}
s={}
for p,h in files.items():
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p.rsplit('/',1)[-1]]=b.decode()
a=s['GammaPremises.lean'];n=s['GammaZeroNarrow.lean'];cls=s['ArithmeticPellClassification.lean'];first=s['ArithmeticPellFirstNorm.lean'];rec=s['ArithmeticPellRecurrence.lean'];idx=s['Direct80IndexOne.lean']
def hdr(src,name):
 m=re.search(r'\btheorem\s+'+name+r'\b(.*?)\s*:=\s*by',src,re.S);assert m,name
 return ' '.join(m.group(1).split())
h=hdr(a,'large_ordinate_of_two_norms')
for t in ('(m tau k eta zeta X Y d : V)','(hm : 0<m)','(heta : 0<eta)','(hzeta : 0<zeta)',
 '(hY : 1≤Y)','(hk : k=eta+zeta)','(hfirst : tau*tau=1+m*(m+1)*k*k)',
 '(hmain : d*d=1+((X*Y+Y+1)*(X*Y+Y+3))* ((eta+Y*k)*(eta+Y*k)))',': 8*m+4≤k'):
 assert t in h,t
assert 'gamma' not in h.lower() and '∀j' not in h
h=hdr(a,'narrow_inequalities')
for t in ('(q X Y k eta R : V)','(hq : 2≤q)','(hX : q≤X)','(hY : q^3≤Y)',
 '(heta : 0<eta)','(hk : 8*(X*Y*Y)+4≤k)','(hR : R+q^3+q+1≤q^4)',': R+1<k ∧ X<eta+Y*k'):
 assert t in h,t
assert 'gamma' not in h.lower() and '∀j' not in h
for t in ('ArithmeticPellClassification.solution_index a d c hmain\'',
 'Direct80IndexOne.impossible Y (a+1) 0 eta zeta j hY hYle heta hzeta hsum hc',
 'positive_parameter_solution m tau k hm hfirst','first_ordinate_lower m n k hm hn2 hcoord'):
 assert t in a,t
assert 'theorem solution_index (b x y : V) (h : x*x=1+delta b*y*y)' in cls
assert 'def delta (b : V) : V := (b+1)*(b+3)' in rec
assert 'theorem positive_parameter_solution (Q x k : V) (hQ : 0<Q)' in first
assert 'theorem impossible (Y S X eta zeta m : V)' in idx
assert '(hY : 1≤Y) (hYS : Y≤S) (heta : 0<eta) (hzeta : 0<zeta)' in idx
assert '(hk : eta+zeta=2)' in idx and 'ycoord m (S*(X+1)-1)' in idx
assert 'theorem first_ordinate_lower' in n
for name in ('large_ordinate_of_two_norms','narrow_inequalities'):
 assert '#print axioms DiophantineConsistency.GammaPremisesDraft.'+name in a
# Verify identities used in the instantiation and index-two bound as sparse
# polynomials; their natural-subtraction uses require the stated positivity.
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
a0,m,q=map(v,('a','m','q'))
assert sub(mul(add(a0,cn(1)),cn(1)),cn(1))==a0
B=add(mul(cn(2),sub(m,cn(1))),cn(1))
assert mul(cn(4),add(B,cn(2)))==add(mul(cn(8),m),cn(4))
def power(base,n):
 z=cn(1)
 for _ in range(n):z=mul(z,base)
 return z
assert power(q,4)==mul(q,power(q,3))
# Sample inputs only corroborate the inequalities; the review prose gives the
# general ordered-natural reasoning, and actual model elaboration remains open.
for qq in range(2,7):
 for X in range(qq,qq+3):
  for Y in range(qq**3,qq**3+3):
   mm=X*Y*Y;k=8*mm+4;eta=1;R=qq**4-qq**3-qq-1
   assert qq**4<=X*Y<=mm<k and R+1<=qq**4 and X<eta+Y*k
print(json.dumps({'scope':'fact-level source premises and exact algebra; no Lean or graph theorem',
 'pinned_sources':len(files),'both_norms_explicit':True,'gamma_positivity_not_assumed':True,
 'index_one_S':'a+1','index_one_X':0,'narrow_inequalities_checked':True,
 'axiom_reports_unexecuted':2},sort_keys=True,indent=2))
