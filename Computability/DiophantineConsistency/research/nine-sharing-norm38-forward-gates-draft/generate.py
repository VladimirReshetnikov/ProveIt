#!/usr/bin/env python3
"""Generate uncompiled forward-constructor gate checks; no Lean."""
import hashlib,json,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];assignment=D/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean';forward=D/'research/nine-sharing-forward38-draft/ForwardWitness38.lean';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(assignment)=='c66694acbba431aa20f4be03a85c0210d24f1b3a51378e0bbeb40452b611817a' and sha(forward)=='559de61d5eeeb17ef2f6c449f4d594e242ab1c784ce4b34ba58753898209ad14'
gates=[(int(a),int(b),int(c),op) for a,b,c,op in re.findall(r'    ⟨(\d+), (\d+), (\d+), GateOp\.(add|sub|mul)⟩',assignment.read_text())];assert len(gates)==60 and [t for t,_,_,_ in gates]==list(range(21,81));out=P/'src/DiophantineConsistency';out.mkdir(parents=True,exist_ok=True)
header='''set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38ForwardGates
open SharingGateModel
variable {S R : Type*} [CommSemiring S] [CommRing R]

''';tail='\nend DiophantineConsistency.Norm38ForwardGates\n'
for k in range(12):
 text='import DiophantineConsistency.NormAssignment38\nimport DiophantineConsistency.ForwardWitness38\n'+header
 for t,l,r,op in gates[5*k:5*k+5]:
  text+=f'''/-- Proposed natural-constructor component equations for gate {t}. -/
theorem forwardGate{t} (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.{op} (v {l}) (v {r}) (v {t}) = 0 ∧
      negativeResidual embed GateOp.{op} (v {l}) (v {r}) (v {t}) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

'''
 (out/f'Norm38ForwardGates{k:02d}.lean').write_text(text+tail)
imports=''.join(f'import DiophantineConsistency.Norm38ForwardGates{k:02d}\n' for k in range(12));body='''/-- Proposed finite assembly, with no source norm assumptions. -/
theorem forward_gatesHold (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    NormAssignment38.gatesHold embed ports (SharingForward38.witnessCoordinates ports u) := by
  unfold NormAssignment38.gatesHold
  simp only [NormAssignment38.gates, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    false_implies, forall_const, and_true]
  exact ⟨'''+',\n    '.join(f'forwardGate{t} embed ports u' for t,_,_,_ in gates)+''', by simp⟩
''';(out/'Norm38ForwardGatesAssembly.lean').write_text(imports+header+body+tail)
rows=[]
for name in [f'Norm38ForwardGates{k:02d}' for k in range(12)]+['Norm38ForwardGatesAssembly']:
 p=out/(name+'.lean');rows.append({'module':'DiophantineConsistency.'+name,'source':'Computability/DiophantineConsistency/'+str(p.relative_to(D)),'source_sha256':sha(p),'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',p.read_text(),re.M)})
(P/'source-manifest.json').write_text(json.dumps({'rows':rows},indent=2)+'\n');print(json.dumps({'status':'SOURCE_ONLY','gates':len(gates),'groups':12,'stages':len(rows),'manifest_sha256':sha(P/'source-manifest.json')},indent=2))
