from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-pell-coordinate-wb-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
checks={
 'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean':['“out time b. ∃ state, !runDef state time b ∧ !pi₁Def out state”','“out time b. ∃ state, !runDef state time b ∧ !pi₂Def out state”','instance run_defined : 𝚺₁-Function₂[V] run via runDef'],
 'Lean/DiophantineConsistency/PRAWitnessPR.lean':['theorem wb_exs_bt\'','(A : BoundTerm n)','∃ x\' ≤ A.vval e','(hWB : WB M ψ)'],
 'Lean/DiophantineConsistency/PRAWitnessArithmetic.lean':['theorem wb_pi₁Def','theorem wb_pi₂Def'],
 'research/ordinary13-pell-run-wb-composition-draft/PellRunWBComposition.lean.src':['theorem run_wb_selected : WB M runDef.val'],
 'research/ordinary13-pell-run-majorant-client-draft/PellRunMajorantClient.lean.src':['theorem pairValueBound_vval','e 2+2','e 1'],
 'research/ordinary13-pell-run-exponential-bound-draft/PellRunExponentialBound.lean.src':['theorem run_le_exponential_horizon','(hi : i ≤ u)'],
 'research/ordinary13-pell-coordinate-wb-draft/PellCoordinateWB.lean.src':['“state out time a. !runDef state time a ∧ !pi₁Def out state”','“state out time a. !runDef state time a ∧ !pi₂Def out state”','state = run (e 1) (e 2) ∧ e 0 = π₁ state','state = run (e 1) (e 2) ∧ e 0 = π₂ state','wb_exs_bt\' xStateBody','wb_exs_bt\' yStateBody','run_le_exponential_horizon (e 1) (e 1) (e 2) le_rfl']}
for p,toks in checks.items():
 text=Path(p).read_text()
 for token in toks:assert token in text,(p,token)
# Independent standard controls verify exact state, projection, and horizon bound.
controls=0
for a in range(5):
 for time in range(7):
  x,y=1,0
  for _ in range(time):x,y=(a+2)*x+(a+1)*(a+3)*y,x+(a+2)*y
  state=y*y+x if x<y else x*x+x+y
  e=[x,time,a]; bound=(2*2**(2*(e[2]+2)*e[1])+1)**2
  assert state<=bound
  assert e[0]==x and [state]+e==[state,x,time,a]
  e=[y,time,a];assert state<=bound and e[0]==y
  controls+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'source_interfaces_checked':len(checks),'standard_coordinate_controls':controls,'state_witness_reused':True,'quoted_evaluations_and_WB_elaborated':False,'uniform_full_period_bound_proved':False,'lean_executed':False},sort_keys=True,indent=2))
