from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-pell-run-exponential-bound-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-pell-run-exponential-bound-draft/PellRunExponentialBound.lean.src').read_text()
powS=Path('Lean/DiophantineConsistency/ArithmeticPow.lean').read_text()
rec=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
bounds=Path('Lean/DiophantineConsistency/ArithmeticConstructionBoundPell.lean').read_text()
base=Path('../../lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Arithmetic/IOpen/Basic.lean').read_text()
exp=Path('../../lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Arithmetic/Exponential/Exp.lean').read_text()
assert 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in P
for s in ['noncomputable def xcoord (time b : V) : V := π₁ (run time b)',
 'noncomputable def ycoord (time b : V) : V := π₂ (run time b)']:assert s in rec
for s in ['@[simp, grind =] lemma pair_unpair (a : V) : ⟪π₁ a, π₂ a⟫ = a',
 '@[simp] lemma pair_polybound (a b : V) : ⟪a, b⟫ ≤ (a + b + 1)^2',
 'noncomputable def pair (a b : V) : V := if a < b then b * b + a else a * a + a + b']:assert s in base
assert 'simpa [xcoord,ycoord,sq] using pair_polybound (xcoord i a) (ycoord i a)' in P
for s in ['theorem power_iterate (x m n : V) : power (power x m) n=power x (m*n)',
 'theorem power_mono_base (x y n : V) (hxy : x≤y) : power x n≤power y n',
 'theorem power_mono_exponent (x m n : V) (hx : 1≤x) (hmn : m≤n)',
 'theorem power_two (n : V) : power 2 n=Exp.exp n']:assert s in powS
assert 'lemma lt_exp (a : V) : a < Exp.exp a' in exp
assert 'power_mono_base B (Exp.exp B) u (le_of_lt (lt_exp B))' in P
assert 'congrArg (fun x => power x u) (power_two B).symm' in P
assert '_ = power 2 (B*u) := power_iterate 2 B u' in P
assert 'theorem x_le (t b : V) : xcoord t b ≤ power (2 * (b + 2)) t' in bounds
assert 'theorem y_le (t b : V) : ycoord t b ≤ power (2 * (b + 2)) t' in bounds
assert 'theorem one_le_two_mul_add_two (b : V)' in bounds
for s in ['(hx : xcoord i a ≤ F) (hy : ycoord i a ≤ F)',
 'exact le_trans hp (mul_le_mul hs hs (by simp) (by simp))',
 '(hi : i ≤ u)', 'power_mono_exponent _ _ _ hb hi',
 '(le_trans (le_trans (x_le i a) hp) he)', '(le_trans (le_trans (y_le i a) hp) he)']:assert s in P
# The helper is claimed even at B=0 and u=0.
for B in range(20):
 for u in range(12):assert B**u<=2**(B*u)
# Explicitly evaluate the source's pairing, rather than just its upper bound.
count=0
for a in range(8):
 A=a+2;delta=(a+1)*(a+3);B=2*A
 for u in range(8):
  F=2**(B*u);H=(2*F+1)**2;x,y=1,0
  for i in range(u+1):
   paired=y*y+x if x<y else x*x+x+y
   assert paired<=(x+y+1)**2<=H and max(x,y)<=B**i<=B**u<=F
   x,y=A*x+delta*y,x+A*y;count+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'pair_unpair_simp_and_source_pairing_checked':True,'power_lemma_directions_checked':True,
 'model_hypotheses_match_sources':True,'explicit_pair_controls':count,
 'boundterm_and_uniform_witness_obligations_open':True,'lean_executed':False},indent=2,sort_keys=True))
