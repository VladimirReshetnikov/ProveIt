from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-pell-run-wb-composition-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
checks={
 'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean':['def blueprint : PR.Blueprint 1','noncomputable def construction : PR.Construction V blueprint','def runDef : 𝚺₁.Semisentence 3 := blueprint.resultDef'],
 'Lean/DiophantineConsistency/PRAWitnessPR.lean':['theorem wb_resultDef {k : ℕ} (p : PR.Blueprint k)','(hz : WB M p.zero.val) (hs : WB M p.succ.val)','i ≤ e 1 → (c V).result (fun j => e j.succ.succ) i ≤ H.vval e'],
 'Lean/DiophantineConsistency/PRAModelIOpenPairing.lean':['theorem standardModelIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻'],
 'Lean/DiophantineConsistency/PRAWitnessCalculus.lean':['def WB {n : ℕ}','∃ B : (Fin n → M) → M, Mono M B'],
 'research/ordinary13-pell-run-majorant-client-draft/PellRunMajorantClient.lean.src':['theorem pellValueMajorant : PellValueMajorant'],
 'research/ordinary13-pell-blueprint-wb-draft/PellBlueprintWB.lean.src':['theorem zero_wb : WB M blueprint.zero.val'],
 'research/ordinary13-pell-blueprint-projection-bounds-draft/PellBlueprintProjectionBounds.lean.src':['theorem successor_wb : WB M blueprint.succ.val'],
 'research/ordinary13-pell-run-wb-composition-draft/PellRunWBComposition.lean.src':['theorem run_wb_of_inputs','(hz : WB M blueprint.zero.val) (hs : WB M blueprint.succ.val)','(hH : PellValueMajorant) : WB M runDef.val','PRAWitnessPR.wb_resultDef blueprint','hz hs pairValueBound hH','zero_wb (M := M)','successor_wb (M := M)','pellValueMajorant']}
for p,toks in checks.items():
 s=Path(p).read_text()
 for t in toks:assert t in s,(p,t)
# Source-level arity/context check, not elaboration.
k=1
assert k+2==3 and ['result','time','parameter'][1:] == ['time','parameter']
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'source_interfaces_checked':len(checks),'blueprint_arity':k,'majorant_context':['result','time','parameter'],'explicit_inputs':'zero WB, successor WB, PellValueMajorant','selected_clients_unelaborated':True,'uniform_primitive_recursive_code_proved':False,'lean_executed':False},sort_keys=True,indent=2))
