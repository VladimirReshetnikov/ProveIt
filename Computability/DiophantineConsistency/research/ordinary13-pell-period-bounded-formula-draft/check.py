from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-pell-period-bounded-formula-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
checks={
 'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean':['def xDef : 𝚺₁.Semisentence 3','def yDef : 𝚺₁.Semisentence 3','instance x_defined : 𝚺₁-Function₂[V] xcoord via xDef','instance y_defined : 𝚺₁-Function₂[V] ycoord via yDef'],
 'Lean/DiophantineConsistency/StrictSigmaOneInduction.lean':['def bnd : {n : ℕ} → ArithmeticSemiformula ξ n → ArithmeticSemiformula ξ (n + 1)','theorem hierarchy_bnd','theorem eval_bnd_imp'],
 'Lean/DiophantineConsistency/ParsonsHierarchyMap.lean':['theorem hierarchy {ξ : Type}'],
 'Lean/DiophantineConsistency/PRABoundedFormula.lean':['theorem PRA_proves_boundedBooleanCharacteristic'],
 'Lean/DiophantineConsistency/PRABoundedWitness.lean':['def characteristicMatrix','theorem characteristicMatrix_open'],
 'research/ordinary13-explicit-pell-period-model-draft/ExplicitPellPeriod.lean.src':['theorem period_at_twice_index_ordinate'],
 'research/ordinary13-pell-period-bounded-formula-draft/PellPeriodBounded.lean.src':['def periodDef : 𝚺₁.Semisentence 2','!yDef c m a','!xDef x h a','!yDef y h a','def boundedPeriod : ArithmeticSemisentence 3','def PeriodEvaluationBridge : Prop','(bridge : PeriodEvaluationBridge)','PRA_proves_boundedBooleanCharacteristic']}
for p,toks in checks.items():
 s=Path(p).read_text()
 for token in toks:assert token in s,(p,token)
# Verify growth controls for a=0: y_m >= 2^(m-1), h=2*m*c, y_h>=h.
# Compute y_h by matrix powering, without writing values, for modest m.
def mul(a,b):return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2)) for i in range(2) for j in range(2))
def power(A,n):
 r=(1,0,0,1)
 while n:
  if n&1:r=mul(r,A)
  n//=2
  if n:A=mul(A,A)
 return r
Q=(2,3,1,2);x,c=1,0
for m in range(1,5):
 x,c=2*x+3*c,x+2*c
 h=2*m*c;y=power(Q,h)[2]
 assert c>=2**(m-1) and y>=h>=m*2**m
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'checked_source_interfaces':len(checks),'period_formula_graphs_and_bound_slot_specified':True,'variable_order_semantics_is_explicit_unproved_premise':True,'bounded_characteristic_source_draft_only':True,'small_exponential_growth_controls':4,'uniform_pra_bound_proved':False,'ipra_period_derivation_proved':False,'lean_executed':False},sort_keys=True,indent=2))
