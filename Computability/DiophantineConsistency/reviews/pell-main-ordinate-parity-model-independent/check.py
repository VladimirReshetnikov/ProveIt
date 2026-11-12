#!/usr/bin/env python3
"""Independent Pell model-source parity interface and finite controls; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/pell-main-ordinate-parity-model-draft/PellOrdinateParity.lean.src','bb0e98110be0d3c091c6d00c6b72a60232dfd17cd1d673fdce6cf6617ef189b1')
pin('research/pell-main-ordinate-parity-model-draft/result.json','f4bb79e11bc6e05349c3d2f47868ef37a9baf80303c0048827cf56508ed7d296')
e=pin('Lean/DiophantineConsistency/ZRows/PellEvenChebyshev.lean','290124437283244ec2733ab3e423fa64be407e3a97666052c4eeb969117e01d8')
p=pin('Lean/DiophantineConsistency/ArithmeticPellPeriodicity.lean','93e8e34ae100735ca214cc4039c978b1cdefffffccdb38f7626547a405b0e5bb')
r=pin('Lean/DiophantineConsistency/ArithmeticPellResidueClasses.lean','42dd190da5e7ab35ce7a15ea0b6c08b6fea02d990e80e4047dceeec200b02088')
c=pin('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean','63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16')
assert 'ycoord (2*t+1) b%(2*(b+3))=(2*t+1)%(2*(b+3))' in e
assert 'induction t using ISigma1.sigma1_succ_induction' in e and '· definability' in e
assert 'ycoord (2*time) b=2*xcoord time b*ycoord time b' in p
assert 'theorem mod_reduce (a m n : V) (hm : 0<m) (hdiv : m∣n)' in r and '(a%n)%m=a%m' in r
assert 'instance y_definable : 𝚺₁-Function₂[V] ycoord' in c
for x in ['theorem ordinate_mod_two (n b : V) : ycoord n b % 2 = n % 2','even_or_odd n','rw [ht, double_y]','(2 : V) ∣ 2 * (b + 3)','mod_reduce (ycoord (2 * t + 1) b) 2 (2 * (b + 3)) hp hd','(sign_index b t).2']:
 assert x in s,x
# Independent modular recurrence controls include odd-index stronger modulus.
cases=0
for b in range(24):
 mod=2*(b+3);x,y=1,0;delta=(b+1)*(b+3)
 for n in range(150):
  assert y%2==n%2
  if n%2:assert y%mod==n%mod
  x,y=((b+2)*x+delta*y)%mod,(x+(b+2)*y)%mod
  cases+=1
print(json.dumps({'scope':'source signatures and finite recurrence controls, no Lean','odd_source_modulus':'2*(b+3)','even_source_double_y':True,'upstream_induction_over_internal_model_indices':True,'finite_controls':cases,'model_induction_not_replayed':True,'graph_zero_transport_not_proved':True,'lean_elaborated':False},sort_keys=True,indent=2))
