#!/usr/bin/env python3
"""Generate an uncompiled final-assignment environment for all 60 source gates."""
import json,hashlib,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];G=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';S=D/'research/nine-sharing-quartic65-norm38-candidate/seed.json';g=G.read_bytes();s=S.read_bytes();assert hashlib.sha256(g).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e' and hashlib.sha256(s).hexdigest()=='312ab65ec472f01339c41dab93859e368ec0b9a2213b906856526263dd68eb23';graph=json.loads(g);seed=json.loads(s);assert len(seed['gate_records'])==60 and len(graph['witnesses'])==14
indices={};defs=[]
for i,n in enumerate(graph['witnesses']):indices[n]=len(defs);defs.append(f'  let a{len(defs)} : SignedPair S := ⟨w {i} + 1, 0⟩')
for i,n in enumerate(graph['fixed_numerals']):indices[n]=len(defs);defs.append(f'  let a{len(defs)} : SignedPair S := ⟨ports {i}, 0⟩')
for n in (1,3,4):indices[n]=len(defs);defs.append(f'  let a{len(defs)} : SignedPair S := ⟨{n}, 0⟩')
gateRows=[];mapping={'+':'add','-':'sub','*':'mul'}
for row,rec in zip(graph['source'][:60],seed['gate_records']):
 n,op,a,b=row;assert (n,op,a,b)==(rec['name'],rec['op'],rec['left'],rec['right']) and n not in indices and a in indices and b in indices
 idx=len(defs);indices[n]=idx;gateRows.append(f'    ⟨{idx}, {indices[a]}, {indices[b]}, GateOp.{mapping[op]}⟩')
 if rec['kind']=='materialized':
  pos=rec['positive_coordinate']-1;neg=rec.get('negative_coordinate');rhs=f'⟨w {pos}, '+(f'w {neg-1}' if neg is not None else '0')+'⟩'
 else:
  assert rec['kind'] in ('inline','norm');rhs=f'pairCompute GateOp.{mapping[op]} a{indices[a]} a{indices[b]}'
 defs.append(f'  let a{idx} : SignedPair S := {rhs}')
assert len(defs)==81 and len(gateRows)==60
lst=', '.join('a'+str(i) for i in range(len(defs)));norms={n:indices[n] for n in ('N0','N1','Na','Nt','scaled_Ns','Delta')}
text='''import DiophantineConsistency.SharingNormTrace

/-! UNCOMPILED DRAFT. Concrete 60-gate final assignment environment for the
38-witness candidate. Data definitions and conditional predicates only;
none of the required model/seed/source equivalences is proved here. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.NormAssignment38
open SharingGateModel

/-- Inputs, four natural port values, constants 1/3/4, then 60 gate values. -/
def assignment {S : Type*} [CommSemiring S]
    (ports : Fin 4 → S) (w : Fin 38 → S) : Fin 81 → SignedPair S :=
'''+ '\n'.join(defs)+'\n  !['+lst+''']

/-- The checked external candidate's 60 source gates, in their original order. -/
def gates : List (Gate (Fin 81)) :=
  [
'''+',\n'.join(gateRows)+'''
  ]

/-- Proposed reverse-side gate constraints for one final assignment. -/
def gatesHold {S R : Type*} [CommSemiring S] [CommRing R]
    (embed : S →+* R) (ports : Fin 4 → S) (w : Fin 38 → S) : Prop :=
  let v := assignment ports w
  ∀ g ∈ gates,
    positiveResidual embed g.op (v g.left) (v g.right) (v g.target) = 0 ∧
    negativeResidual embed g.op (v g.left) (v g.right) (v g.target) = 0

/-- The five proposed graph norm targets, in the model difference ring. -/
def fiveNorms {S R : Type*} [CommSemiring S] [CommRing R]
    (embed : S →+* R) (ports : Fin 4 → S) (w : Fin 38 → S) : Prop :=
  let v := assignment ports w
  pairValue embed (v '''+str(norms['N0'])+''') = 1 ∧
  pairValue embed (v '''+str(norms['N1'])+''') = 1 ∧
  pairValue embed (v '''+str(norms['Na'])+''') = 1 ∧
  pairValue embed (v '''+str(norms['Nt'])+''') = 1 ∧
  pairValue embed (v '''+str(norms['scaled_Ns'])+''') = pairValue embed (v '''+str(norms['Delta'])+''')

-- Unresolved: derive gatesHold and fiveNorms from the 29 seed residuals;
-- construct the final assignment trace; identify these values with the
-- Carrier65 core under actual port casts and positive shifted inputs.
end DiophantineConsistency.NormAssignment38
'''
out=P/'NormAssignment38.lean';assert not out.exists();out.write_text(text);print('source_sha256',hashlib.sha256(text.encode()).hexdigest(),'node_count',len(defs),'gates',len(gateRows),'terminal_indices',norms)
