#!/usr/bin/env python3
"""Review bounded source signatures and exact size algebra, without Lean."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parents[2]
def pin(path,h):
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==h,path;return b.decode()
s=pin('research/ordinary14-natural79-zero-w-divisibility-client-draft/Natural79ZeroWDivisibility.lean','5166f77208e4af6ed8214663aa3b07550f86796f7183c46e0f1039b0d87c4293')
r=pin('research/ordinary14-natural79-zero-w-root-cut-draft/Natural79ZeroWRootCut.lean','c3fd2660899139ddd335214893e5698a4124399432604111a6aa1942bc8009ec')
j=pin('research/ordinary14-natural79-zero-w-jpos-draft/Natural79ZeroWJPos.lean','f1cf89c29eebe2259069dd26fd66d8cece75d48374358cc95ab9cc1ba83a2f0a')
n=pin('research/ordinary14-natural79-zero-w-main-norm-draft/Natural79ZeroWMainNorm.lean','afacf4636f4b66e2bff939300347ba5568b72d477a3028ec0a424aba42ce8009')
w=pin('research/ordinary14-natural79-wshift-model-draft/Natural79WShift.lean','7635b50c819f665a6d9410758b3db01c70d3b42c1fff2aee6f3733263f76d7a1')
d=pin('Lean/DiophantineConsistency/BFS943/Direct80NaturalProjection.lean','85e1fdcee61eeea97af1dead36de5f6593a94fb7c1f63678922ef0909b128028')
e=pin('Lean/DiophantineConsistency/ArithmeticAdaptiveExactIndices2011.lean','8d3440b042b4895f764998708fc9323918e59ed109667df15f0e558f4d859bd5')
assert 'theorem natural_dvd_of_signed (a b : V) (hd : (ι a : DiffRing V)∣ι b) : a∣b' in d
assert 'Arithmetic.le_of_dvd (by simp) hd' in e
assert 'def q (beta : V) (v : Fin 14 → V) : V := 1+v 0*beta' in n and 'q beta v*(q beta v*q beta v)*(v 7+1)' in n
assert 'theorem signed_dvd_three_square_of_zero_w_zero' in r and 'theorem J_pos_of_zero_w_zero' in j
assert 'positive_w : ∀ v, InternalZero' in w
for name in ('natural_dvd_three_square','no_divisor_in_window','zero_w_impossible','w_pos_of_zero'):assert 'theorem '+name in s
assert '(hq : 2≤Q) (hY : Q*Q*Q≤Y)' in s and '(hd : (4*Y+3) ∣ 3*Q*Q)' in s
start=s.index('theorem w_pos_of_zero');stop=s.index(' := by',start);sig=s[start:stop]
for t in ('(hbeta : (p 0 : DiffRing V)=ι beta)','(hK : (p 1 : DiffRing V)=ι K)','(hb : 0<beta)','(hz : InternalZero','0<v 6'):assert t in sig
assert not any(t in sig for t in ('(hKpos','(hgamma','(hMC','(hMF','(hw :'))
assert 'J_pos_of_zero_w_zero p K v hK hz hw' in s
assert 'signed_dvd_three_square_of_zero_w_zero p beta v hbeta hb hJ hz hw' in s
assert 'TenPositive80NaturalProjection.natural_dvd_of_signed' in s and 'Arithmetic.le_of_dvd hpos hd' in s
for t in ('natural_dvd_three_square','no_divisor_in_window','w_pos_of_zero'):assert '#print axioms DiophantineConsistency.Natural79ZeroWDivisibilityDraft.'+t in s
# 4Y+3 - 3Q² = 4(Y-Q³) + Q²(4Q-3) + 3 (integer polynomial identity).
def var(n):return {(n,):1}
def con(n):return {():n}
def plus(a,b):
 r=dict(a)
 for k,v in b.items():r[k]=r.get(k,0)+v
 return {k:v for k,v in r.items() if v}
def minus(a,b):return plus(a,{k:-v for k,v in b.items()})
def mul(a,b):
 r={}
 for x,u in a.items():
  for y,v in b.items():
   k=tuple(sorted(x+y));r[k]=r.get(k,0)+u*v
 return {k:v for k,v in r.items() if v}
Q,Y=var('Q'),var('Y');q2=mul(Q,Q);q3=mul(q2,Q);four=con(4);three=con(3)
assert minus(plus(mul(four,Y),three),mul(three,q2))==plus(plus(mul(four,minus(Y,q3)),mul(q2,minus(mul(four,Q),three))),three)
for q in range(2,101):
 for t in range(5):
  y=q**3+t; assert 0<3*q*q<4*y+3
print(json.dumps({'scope':'bounded source signatures and exact integer-polynomial size identity; no Lean/model theorem','pinned_sources':7,'size_boundary_controls':495,'represented_natural_K_not_strict':True,'axiom_reports_unexecuted':3},sort_keys=True,indent=2))
