from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-pell-run-majorant-client-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
checks={
 'research/ordinary13-pell-period-history-majorant-draft/PellHistoryMajorant.lean.src':['def pairValueBound : BoundTerm 3','poly ‘2 * (#2 + 2) * #1’','def PellValueMajorant : Prop','fun j : Fin 1 => e j.succ.succ'],
 'research/ordinary13-pell-run-exponential-bound-draft/PellRunExponentialBound.lean.src':['theorem run_le_exponential_horizon (i u a : V) (hi : i ≤ u)','2*Exp.exp (2*(a+2)*u)+1'],
 'Lean/DiophantineConsistency/PRAWitnessBoundTerms.lean':['| poly P, e => P.val e Empty.elim','| exp2 A B, e => Exp.exp (A.vval e * Exp.exp (B.vval e))'],
 'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean':['noncomputable def run (time b : V) : V := construction.result ![b] time'],
 'Lean/DiophantineConsistency/PRAWitnessPR.lean':['(fun j : Fin 1 => e j.succ.succ) = ![e 2]'],
 'research/ordinary13-pell-run-majorant-client-draft/PellRunMajorantClient.lean.src':['theorem pairValueBound_vval','simp [pairValueBound, PRAWitnessBoundTerms.BoundTerm.vval','theorem pellValueMajorant : PellValueMajorant','change run i (e 2) ≤ pairValueBound.vval e','run_le_exponential_horizon i (e 1) (e 2) hi']}
for p,toks in checks.items():
 s=Path(p).read_text()
 for x in toks:assert x in s,(p,x)
# Exact controls emphasize parameter/time order and unused result slot.
controls=0
for a in range(6):
 for u in range(7):
  e=[9,u,a];other=[700,u,a]
  val=lambda z:(2*2**(2*(z[2]+2)*z[1])+1)**2
  assert val(e)==val(other)
  B=2*(a+2);F=2**(B*u);assert val(e)==(2*F+1)**2
  x,y=1,0
  for i in range(u+1):
   pair=y*y+x if x<y else x*x+x+y
   assert pair<=val(e)
   x,y=(a+2)*x+(a+1)*(a+3)*y,x+(a+2)*y
   controls+=1
assert (2*2**(2*(1+2)*3)+1)**2!=(2*2**(2*(3+2)*1)+1)**2
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'source_interfaces_checked':len(checks),'context':['result','time','parameter'],'unused_result_slot_controls':True,'paired_state_controls':controls,'valuation_and_majorant_lean_checked':False,'lean_executed':False},sort_keys=True,indent=2))
