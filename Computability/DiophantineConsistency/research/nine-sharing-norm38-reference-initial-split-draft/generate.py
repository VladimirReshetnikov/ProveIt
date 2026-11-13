#!/usr/bin/env python3
"""Source-only split diagnostic for the 21 reference initial-node equalities."""
import hashlib,json,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];ref=D/'research/nine-sharing-norm38-reference-base-retry02/src/DiophantineConsistency/Norm38ReferenceBase.lean';ass=D/'research/nine-sharing-seed38-weighted-retry/src/DiophantineConsistency/NormAssignment38.lean';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(ref)=='be7f61985d51b07cfda37da0d1ca40c7d44a01950ef6cf94866a5cb3e2bf1da2' and sha(ass)=='c66694acbba431aa20f4be03a85c0210d24f1b3a51378e0bbeb40452b611817a'
rnodes=dict((int(i),v) for i,v in re.findall(r'^  let a(\d+) : R := (.+)$',ref.read_text(),re.M));snodes=dict((int(i),v) for i,v in re.findall(r'^  let a(\d+) : SignedPair S := (.+)$',ass.read_text(),re.M))
for i in range(21):
 expectr=f'x {i}' if i<14 else (f'p {i-14}' if i<18 else str([1,3,4][i-18]));expects=f'⟨w {i} + 1, 0⟩' if i<14 else (f'⟨ports {i-14}, 0⟩' if i<18 else f'⟨{[1,3,4][i-18]}, 0⟩');assert rnodes[i]==expectr and snodes[i]==expects,(i,rnodes[i],snodes[i])
out=P/'src/DiophantineConsistency';header='''set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel SharingNormTrace SharingTopology38
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

''';end='\nend DiophantineConsistency.Norm38Reference\n';rows=[]
for g in range(7):
 name=f'Norm38ReferenceInitialGroup{g:02}';s='import DiophantineConsistency.Norm38ReferenceBase\n\n'+header
 for i in range(g*3,g*3+3):
  s+=f'''theorem initial_node{i:02} (ports : Fin 4 → V) (w : Fin 38 → V) :
    pairValue ι (NormAssignment38.assignment ports w {i}) =
      reference (fun j => ι (ports j))
        (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1)) {i} := by
  simp [reference, NormAssignment38.assignment, pairValue, map_add, map_one, map_ofNat]

'''
 s+=end;p=out/(name+'.lean');p.write_text(s);rows.append({'module':'DiophantineConsistency.'+name,'source_sha256':sha(p),'nodes':list(range(g*3,g*3+3))})
name='Norm38ReferenceInitialAll';s=''.join(f'import DiophantineConsistency.Norm38ReferenceInitialGroup{g:02}\n' for g in range(7))+'\n'+header+'''theorem initial_agreement (ports : Fin 4 → V) (w : Fin 38 → V) :
    ∀ i ∈ initialNodes,
      pairValue ι (NormAssignment38.assignment ports w i) =
        reference (fun j => ι (ports j))
          (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1)) i := by
  intro i hi
  change i ∈ (List.finRange 21).map (fun j => Fin.castLE (by decide : 21 ≤ 81) j) at hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
  fin_cases j
'''
for i in range(21):s+=f'  · exact initial_node{i:02} ports w\n'
s+=end+'#print axioms DiophantineConsistency.Norm38Reference.initial_agreement\n';p=out/(name+'.lean');p.write_text(s);rows.append({'module':'DiophantineConsistency.'+name,'source_sha256':sha(p),'nodes':[]});(P/'source-manifest.json').write_text(json.dumps({'scope':'Source-only diagnostic; no Lean proof.','rows':rows},sort_keys=True,indent=2)+'\n');print(json.dumps({'status':'PASS_SOURCE_GENERATION_ONLY','reference_sha256':sha(ref),'assignment_sha256':sha(ass),'nodes':21,'groups':7,'scope':'21 paired initial-node syntax checks; generated proofs uncompiled.'},indent=2,sort_keys=True))
