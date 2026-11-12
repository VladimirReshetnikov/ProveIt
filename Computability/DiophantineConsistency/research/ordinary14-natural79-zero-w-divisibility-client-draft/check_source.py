#!/usr/bin/env python3
"""Bounded source-interface and exact size-identity checks; never runs Lean."""
from pathlib import Path
import hashlib,json,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];L=D/'Lean/DiophantineConsistency'
pins={
 'client':(P/'Natural79ZeroWDivisibility.lean','5166f77208e4af6ed8214663aa3b07550f86796f7183c46e0f1039b0d87c4293'),
 'root':(D/'research/ordinary14-natural79-zero-w-root-cut-draft/Natural79ZeroWRootCut.lean','c3fd2660899139ddd335214893e5698a4124399432604111a6aa1942bc8009ec'),
 'jpos':(D/'research/ordinary14-natural79-zero-w-jpos-draft/Natural79ZeroWJPos.lean','f1cf89c29eebe2259069dd26fd66d8cece75d48374358cc95ab9cc1ba83a2f0a'),
 'norm':(D/'research/ordinary14-natural79-zero-w-main-norm-draft/Natural79ZeroWMainNorm.lean','afacf4636f4b66e2bff939300347ba5568b72d477a3028ec0a424aba42ce8009'),
 'reflection':(L/'BFS943/Direct80NaturalProjection.lean','85e1fdcee61eeea97af1dead36de5f6593a94fb7c1f63678922ef0909b128028'),
 'divisor_example':(L/'ArithmeticAdaptiveExactIndices2011.lean','8d3440b042b4895f764998708fc9323918e59ed109667df15f0e558f4d859bd5'),
 'wshift':(D/'research/ordinary14-natural79-wshift-model-draft/Natural79WShift.lean','7635b50c819f665a6d9410758b3db01c70d3b42c1fff2aee6f3733263f76d7a1')}
s={}
for n,(p,h) in pins.items():
 raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==h,n;s[n]=raw.decode()
assert 'theorem natural_dvd_of_signed (a b : V) (hd : (ι a : DiffRing V)∣ι b) : a∣b' in s['reflection']
assert 'Arithmetic.le_of_dvd (by simp) hd' in s['divisor_example']
for token in ('theorem signed_dvd_three_square_of_zero_w_zero','(hbeta : (p 0 : DiffRing V)=ι beta) (hb : 0<beta) (hJ : 0<v 0)',
 '(4*ι (y beta v)+3 : DiffRing V) ∣','3*ι (q beta v)*ι (q beta v)'):
 assert token in s['root'],token
for token in ('theorem J_pos_of_zero_w_zero','(hK : (p 1 : DiffRing V)=ι K)',
 '(hz : InternalZero (P79NaturalForcedW.graph p).output v) (hw : v 6=0)'):
 assert token in s['jpos'],token
assert 'def q (beta : V) (v : Fin 14 → V) : V := 1+v 0*beta' in s['norm']
assert 'q beta v*(q beta v*q beta v)*(v 7+1)' in s['norm']
assert '(positive_w : ∀ v, InternalZero (P79NaturalForcedW.graph p).output v → 0 < v 6)' in s['wshift']
client=s['client']
for token in ('theorem natural_dvd_three_square','TenPositive80NaturalProjection.natural_dvd_of_signed',
 'theorem no_divisor_in_window','(hq : 2≤Q) (hY : Q*Q*Q≤Y)',
 '(hd : (4*Y+3) ∣ 3*Q*Q)','Arithmetic.le_of_dvd hpos hd',
 'theorem zero_w_impossible','J_pos_of_zero_w_zero p K v hK hz hw',
 'signed_dvd_three_square_of_zero_w_zero p beta v hbeta hb hJ hz hw',
 'theorem w_pos_of_zero','(hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)',
 '(hb : 0<beta) (hz : InternalZero (P79NaturalForcedW.graph p).output v)'):
 assert token in client,token
for n in ('natural_dvd_three_square','no_divisor_in_window','w_pos_of_zero'):
 assert f'#print axioms DiophantineConsistency.Natural79ZeroWDivisibilityDraft.{n}' in client
# Exact polynomial check for the size proof, with a separate explicit residual
# Y−Q³; this is an algebra certificate, not a Lean proof of model order.
def add(a,b):
 r=dict(a)
 for k,v in b.items():r[k]=r.get(k,0)+v
 return {k:v for k,v in r.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 r={}
 for ka,va in a.items():
  for kb,vb in b.items():
   k=tuple(sorted(ka+kb));r[k]=r.get(k,0)+va*vb
 return {k:v for k,v in r.items() if v}
def scale(n,a):return {k:n*v for k,v in a.items() if n*v}
Q={('Q',):1};Y={('Y',):1};one={():1};q2=mul(Q,Q);q3=mul(q2,Q)
lhs=sub(add(scale(4,Y),scale(3,one)),scale(3,q2))
rhs=add(add(scale(4,sub(Y,q3)),scale(4,mul(q2,sub(Q,one)))),add(q2,scale(3,one)))
assert lhs==rhs
# Finite arithmetic controls supplement the formal inequality argument.
checks=0
for q in range(2,80):
 for offset in (0,1,2,17):
  y=q**3+offset;h=4*y+3;n=3*q*q
  assert 0<n<h and n%h!=0;checks+=1
# If positive naturals divide in the signed integers, the signed quotient must
# be nonnegative; these are controls for, not a proof of, reflection.
for h in range(1,40):
 for z in range(-5,6):
  n=h*z
  if n>=0:assert z>=0 and n%h==0
print(json.dumps({'scope':'source signatures and exact polynomial identity; no Lean model theorem or iPRA endpoint',
 'pinned_sources':len(pins),'exact_size_identity':True,'size_controls':checks,
 'explicit_beta_and_K0_representations':True,'axiom_reports_unexecuted':3},sort_keys=True,indent=2))
