#!/usr/bin/env python3
"""Generate uncompiled per-gate proofs. Does not run Lean."""
import hashlib,json,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1]; slots=D/'research/nine-sharing-norm38-slot-extraction-draft/slots.json';assignment=D/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(slots)=='f3b2a0ea47962596d8753533c363a6b3e0b4121cd3150722181581d9085326a4' and sha(assignment)=='c66694acbba431aa20f4be03a85c0210d24f1b3a51378e0bbeb40452b611817a'
rows=json.loads(slots.read_text())['slots'];gates=[(int(a),int(b),int(c),op) for a,b,c,op in re.findall(r'    ⟨(\d+), (\d+), (\d+), GateOp\.(add|sub|mul)⟩',assignment.read_text())];assert len(gates)==60 and [t for t,_,_,_ in gates]==list(range(21,81))
bygate={}
for row in rows:
 if row['kind']=='norm':continue
 m=re.fullmatch(r'(positive|negative)Residual ι GateOp\.(add|sub|mul) \(v (\d+)\) \(v (\d+)\) \(v (\d+)\)',row['rhs']);assert m
 kind,op,l,r,t=m.groups();t,l,r=int(t),int(l),int(r);assert (t,l,r,op) in gates;bygate.setdefault(t,{})[kind]=row['slot']
assert len(bygate)==19 and sum(map(len,bygate.values()))==24
out=P/'src/DiophantineConsistency';out.mkdir(parents=True,exist_ok=True)
header='''set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38GateExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel Norm38SlotExtraction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

''';tail='\nend DiophantineConsistency.Norm38GateExtraction\n'
for k in range(12):
 chunk=gates[5*k:5*k+5];needed=sorted({v//3 for t,_,_,_ in chunk for v in bygate.get(t,{}).values()});imports='import DiophantineConsistency.Norm38EachSlot\n'+''.join(f'import DiophantineConsistency.Norm38Slots{x:02d}\n' for x in needed);text=imports+header
 for t,l,r,op in chunk:
  text+=f'''/-- Proposed component equations for gate {t}. -/
theorem gate{t} (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.{op} (v {l}) (v {r}) (v {t}) = 0 ∧
      negativeResidual ι GateOp.{op} (v {l}) (v {r}) (v {t}) = 0 := by
'''
  neededslots=bygate.get(t,{})
  for kind,i in neededslots.items():text+=f'  have h{i:02d} := each_slot_zero p w hz {i}\n  rw [slot{i:02d} p ports w hp] at h{i:02d}\n'
  if neededslots:
   assert 'positive' in neededslots;positive='h'+f"{neededslots['positive']:02d}"
   if 'negative' in neededslots:text+=f"  exact ⟨{positive}, h{neededslots['negative']:02d}⟩\n\n"
   else:text+=f'  refine ⟨{positive}, ?_⟩\n  simp [NormAssignment38.assignment, negativeResidual, pairCompute, map_ofNat]\n\n'
  else:text+='  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]\n\n'
 (out/f'Norm38Gates{k:02d}.lean').write_text(text+tail)
imports=''.join(f'import DiophantineConsistency.Norm38Gates{k:02d}\n' for k in range(12))
body='''/-- Proposed final 60-gate assembly; no source graph equivalence is claimed. -/
theorem seed_zero_gatesHold (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    NormAssignment38.gatesHold ι ports w := by
  unfold NormAssignment38.gatesHold
  simp only [NormAssignment38.gates, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    false_implies, forall_const, and_true]
  exact ⟨'''+',\n    '.join(f'gate{t} p ports w hp hz' for t,_,_,_ in gates)+'''⟩
'''
(out/'Norm38GatesAssembly.lean').write_text(imports+header+body+tail)
names=[f'Norm38Gates{k:02d}' for k in range(12)]+['Norm38GatesAssembly'];manifest={'rows':[]}
for name in names:
 p=out/(name+'.lean');manifest['rows'].append({'module':'DiophantineConsistency.'+name,'source':'Computability/DiophantineConsistency/'+str(p.relative_to(D)),'source_sha256':sha(p),'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',p.read_text(),re.M)})
(P/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({'status':'UNCOMPILED_SOURCE_GENERATION','gates':len(gates),'materialized':len(bygate),'slots':sum(map(len,bygate.values())),'groups':12,'stages':len(names),'manifest_sha256':sha(P/'source-manifest.json')},indent=2))
