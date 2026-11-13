#!/usr/bin/env python3
"""Independent scope and arithmetic controls; never invokes Lean."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-residue-mersenne-alignment-model-draft/ResidueMersenneAlignment.lean.src':'f8554cdd4c1f1ca4e7f2b0f737c6e03e374f289ed51092232679da3058210264',
'research/ordinary13-residue-mersenne-alignment-model-draft/README.md':'3971c7b7ac928b91f82dffa86e3d264ffccd4261ffe0b44b813d33db2da84893',
'Lean/DiophantineConsistency/ArithmeticAdaptiveMersenne2011.lean':'c8a132e1b28bd1cf1ed76d80e953d5568ff0c77f566ad7b2b66715c8be9641ef',
'Lean/DiophantineConsistency/ArithmeticRadixAlignment.lean':'28275cde76bb21343e01af3bfd6f025e14e0159b66e05c7a34a9780b02c49c81',
'research/ordinary13-residue-signfree-power-model-draft/ResidueSignFreePower.lean.src':'1c6935eda3ce9ae05d257957d7e2d8f5f3786386aaf618d5a480036113c8bb92'}
def pin(p,h):
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s={p:pin(p,h) for p,h in pins.items()}
a=s['Lean/DiophantineConsistency/ArithmeticAdaptiveMersenne2011.lean']
b=s['Lean/DiophantineConsistency/ArithmeticRadixAlignment.lean']
c=s['research/ordinary13-residue-mersenne-alignment-model-draft/ResidueMersenneAlignment.lean.src']
assert '''theorem cancel_three (d R q J : V) (hd : 4≤d)
    (hq : q=(Exp.exp d-1)*J+1) (hdiv : q∣3*Exp.exp R) : q∣Exp.exp R''' in a
assert '''theorem factor_alignment (d J R w : V) (hd : 2≤d) (hJ : 0<J)
    (he : Exp.exp R=w*((Exp.exp d-1)*J+1)) :
    0<w ∧ ∃ N : V, 0<N ∧
      (Exp.exp d-1)*J+1=Exp.exp (d*N) ∧
      d*N≤R ∧ w=Exp.exp (R-d*N)''' in b
for term in ['(hd : 4≤d)','(hJ : 0<J)','(hpower : X=Exp.exp R)','(hthree : q∣3*X)', 'cancel_three d R q J hd hq hthree','factor_alignment d J R w hd2 hJ hfact','hq.trans hqn']:
 assert term in c,term
# The Mersenne port alone does not guarantee coprimality with three; X=power and divisibility matter.
d,j,q,x=5,2,63,21
assert q==(2**d-1)*j+1 and q%3==0 and (3*x)%q==0 and x%q!=0
# Weaker d=1 would invalidate cancellation even for X a power of two.
d,j,q,x=1,2,3,1
assert q==(2**d-1)*j+1 and (3*x)%q==0 and x%q!=0
# J=0 gives q=1, so no N>0 satisfies q=2^(d*N) for d≥4.
assert (2**4-1)*0+1==1 and all(2**(4*n)!=1 for n in range(1,20))
cases=0;zero_cases=0
for d in range(4,11):
 for j in range(0,51):
  q=(2**d-1)*j+1
  for r in range(0,33):
   x=1<<r
   if 3*x%q:continue
   assert x%q==0
   if j==0:zero_cases+=1;continue
   assert q&(q-1)==0
   exp=q.bit_length()-1
   assert exp%d==0 and exp//d>0 and exp<=r
   w=x//q
   assert w==1<<(r-exp) and x==q*w
   cases+=1
print(json.dumps({'pinned_sha256':pins,'positive_j_alignment_controls':cases,'zero_j_cancellation_controls':zero_cases,'controls':{'mersenne_q_divisible_by_three_without_power':True,'d1_cancellation_counterexample':True,'zero_j_positive_N_counterexample':True},'scope':'independent lexical and finite integer checks only; no Lean, provider build, graph binding, or iPRA proof','lean_executed':False},sort_keys=True,indent=2))
