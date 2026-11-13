from pathlib import Path
from fractions import Fraction
from itertools import product
import hashlib,json,subprocess,sys
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-positive-guard74-model-fact-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f=A/'Guard74Strict.lean'; s=f.read_text(); c=''.join(s.split())
base=D/'Lean/DiophantineConsistency/DiscreteOrderedRingFacts.lean';defs=''.join(base.read_text().split())
mathlib=Path('/home/codex/src/Proofs/.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean')
assert 'defDiscrete(R:Type*)[CommRingR][LinearOrderR]:Prop:=∀x:R,0<x→1≤x' in defs
assert 'theorempos_of_mul_pos_left[MulPosReflectLTα](h:0<a*b)(hb:0≤b):0<a' in ''.join(mathlib.read_text().split())
for token in ['[CommRingR][LinearOrderR][IsStrictOrderedRingR]','(hd:DiscreteR)','(hF:0<F)','(halpha:0<alpha)','(hX:0<X)','(hK:0≤K)','(hXq:q≤X)','(hh:1≤h)','(hguard:(q-F-alpha)*(X+K)-F=b*(h-1))','pos_of_mul_pos_lefthprod(le_of_lthXK)','havehC1:1≤q-F-alpha:=hd_hC']:
 assert token in c,token
# Independent exhaustive finite controls over signed b and q, counting only exact balances.
valid=0;b_signs=set()
for F,alpha,X,K,q,b,h in product(range(1,5),range(1,5),range(1,7),range(3),range(-1,7),range(-4,5),range(1,5)):
 if q<=X and (q-F-alpha)*(X+K)-F==b*(h-1):
  assert h>1
  valid+=1;b_signs.add((b>0)-(b<0))
assert valid>0 and b_signs=={-1,1}
q,F,alpha,X,K,h=5,3,1,1,2,1
assert X<q and (q-F-alpha)*(X+K)-F==0
# No discreteness: a positive rational factor strictly below one allows h=1.
q=X=Fraction(1,2);F=Fraction(3,20);alpha=Fraction(1,20);K=0
assert (q-F-alpha)*(X+K)-F==0 and 0<q-F-alpha<1 and q<=X
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],capture_output=True,text=True,check=True)
assert json.loads(r.stdout)==json.loads((A/'observation.json').read_text())
print(json.dumps({'author_readme_sha256':sha(A/'README.md'),'author_checker_sha256':sha(A/'check_source.py'),'author_observation_sha256':sha(A/'observation.json'),'draft_sha256':sha(f),'discrete_definition_sha256':sha(base),'ordered_mul_source_sha256':sha(mathlib),'finite_valid_balances':valid,'negative_and_positive_b_examples':sorted(b_signs),'q_le_X_necessity_witness':True,'nondiscrete_rational_witness':True,'author_receipt_replayed':True,'lean_run':False},sort_keys=True,indent=2))
