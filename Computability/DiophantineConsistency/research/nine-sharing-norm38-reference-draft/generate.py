#!/usr/bin/env python3
"""Generate an uncompiled concrete reference graph and source-extraction draft."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];gpath=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(gpath)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(gpath.read_text())
indices={n:i for i,n in enumerate(g['witnesses'])};indices.update({n:14+i for i,n in enumerate(g['fixed_numerals'])});indices.update({1:18,3:19,4:20});rows=[]
for off,(name,op,left,right) in enumerate(g['source'][:60]):
 idx=21+off;rows.append({'index':idx,'name':name,'op':op,'left':indices[left],'right':indices[right]});indices[name]=idx
assert len(rows)==60 and [indices[n] for n in ('N0','N1','Na','Nt','scaled_Ns','Delta')]==[61,44,78,66,80,36]
lines=['''import DiophantineConsistency.SharingTopology38
import DiophantineConsistency.Norm38SlotExtraction
import FreshModel106

/-! UNCOMPILED DRAFT. Concrete source-DAG reference and extraction direction.
Imported topology and slot modules, tactics, provider routing and all
declarations here require Lean checking. No equivalence or endpoint is claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel SharingNormTrace SharingTopology38

/-- The first 60 source rows interpreted directly in a commutative ring. -/
def reference {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) : Fin 81 → R :=
''']
for i in range(14):lines.append(f'  let a{i} : R := x {i}\n')
for i in range(4):lines.append(f'  let a{i+14} : R := p {i}\n')
for i,n in enumerate((1,3,4),18):lines.append(f'  let a{i} : R := {n}\n')
for r in rows:lines.append(f"  let a{r['index']} : R := a{r['left']} {r['op']} a{r['right']}\n")
lines.append('  !['+', '.join('a'+str(i) for i in range(81))+']\n\n')
lines.append('''/-- The exact initially defined node indices. -/
def initialNodes : List (Fin 81) :=
  (List.finRange 21).map fun i => Fin.castLE (by decide : 21 ≤ 81) i

/-- Candidate decidable check for the actual 60-row topological ordering. -/
theorem graph_topological : Topological NormAssignment38.gates initialNodes := by
  decide

/-- Candidate reference equations for every actual gate. -/
theorem reference_gate_equations {R : Type*} [CommRing R]
    (p : Fin 4 → R) (x : Fin 14 → R) :
    ∀ g ∈ NormAssignment38.gates,
      reference p x g.target = ringCompute g.op (reference p x g.left) (reference p x g.right) := by
  simp only [NormAssignment38.gates, List.mem_cons, forall_eq_or_imp]
  repeat' constructor
  all_goals simp [reference, ringCompute]

/-- The six terminal fields and Delta agree with the maintained Carrier65 core. -/
theorem reference_terminal_fields {R : Type*} [CommRing R]
    (p : Fin 4 → R) (x : Fin 14 → R) :
    let d := Carrier65.core p x
    reference p x 61 = d.P ∧ reference p x 44 = d.Q ∧
    reference p x 78 = d.U ∧ reference p x 66 = d.W ∧
    reference p x 80 = d.Z ∧ reference p x 36 = d.delta := by
  simp [reference, Carrier65.core] <;> ring

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Candidate initial agreement for natural ports and positively shifted inputs. -/
theorem initial_agreement (ports : Fin 4 → V) (w : Fin 38 → V) :
    ∀ i ∈ initialNodes,
      pairValue ι (NormAssignment38.assignment ports w i) =
        reference (fun j => ι (ports j))
          (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1)) i := by
  intro i hi
  fin_cases i <;> simp_all [initialNodes, reference, NormAssignment38.assignment,
    pairValue, map_add, map_one, map_ofNat]

/-- Static gate constraints identify the six named terminals with the actual
source reference. This uses the separately drafted generic topology theorem. -/
theorem static_terminals_agree (ports : Fin 4 → V) (w : Fin 38 → V)
    (hg : NormAssignment38.gatesHold ι ports w) :
    let v := NormAssignment38.assignment ports w
    let ref := reference (fun j => ι (ports j))
      (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1))
    pairValue ι (v 61)=ref 61 ∧ pairValue ι (v 44)=ref 44 ∧
    pairValue ι (v 78)=ref 78 ∧ pairValue ι (v 66)=ref 66 ∧
    pairValue ι (v 80)=ref 80 ∧ pairValue ι (v 36)=ref 36 := by
  let val := fun j => pairValue ι (NormAssignment38.assignment ports w j)
  let ref := reference (fun j => ι (ports j))
    (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1))
  have hfixed : val = ringRun NormAssignment38.gates val :=
    SharingTopology38.static_assignment_fixed ι ports w hg
  have hrun := SharingTopology38.ringRun_agrees_of_topological
    NormAssignment38.gates initialNodes val ref graph_topological
    (initial_agreement ports w) (reference_gate_equations _ _)
  have heq (i : Fin 81) (hi : i ∈ completed NormAssignment38.gates initialNodes) :
      val i = ref i := (congrFun hfixed i).trans (hrun i hi)
  exact ⟨heq 61 (by decide), heq 44 (by decide), heq 78 (by decide),
    heq 66 (by decide), heq 80 (by decide), heq 36 (by decide)⟩

/-- P=Q=U=W=1 and Z=Delta imply the original value zero in any model.
No Delta cancellation, first-port positivity or unit-exclusion theorem is used. -/
theorem static_implies_original_zero (ports : Fin 4 → V) (w : Fin 38 → V)
    (hg : NormAssignment38.gatesHold ι ports w)
    (hn : NormAssignment38.fiveNorms ι ports w) :
    Carrier65.value (fun j => ι (ports j))
      (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1)) = 0 := by
  let ref := reference (fun j => ι (ports j))
    (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1))
  have ht := static_terminals_agree ports w hg
  have hc := reference_terminal_fields (fun j => ι (ports j))
    (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1))
  rcases ht with ⟨ht0,ht1,hta,htt,hts,htd⟩
  rcases hc with ⟨hc0,hc1,hca,hct,hcs,hcd⟩
  unfold NormAssignment38.fiveNorms at hn
  rw [ht0,ht1,hta,htt,hts,htd,hc0,hc1,hca,hct,hcs,hcd] at hn
  rcases hn with ⟨hP,hQ,hU,hW,hZ⟩
  simp [Carrier65.value,hP,hQ,hU,hW,hZ]

/-- Candidate full seed-zero-to-source-value direction for any port tuple
with model-natural representatives. Port casting and the slot theorem are
still explicit assumptions/dependencies. -/
theorem seed_zero_implies_original_zero (p : Fin 4 → ℤ) (ports : Fin 4 → V)
    (w : Fin 38 → V) (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    Carrier65.value (fun j => ((p j : ℤ) : DiffRing V))
      (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1)) = 0 := by
  obtain ⟨hg,hn⟩ := Norm38SlotExtraction.seed_zero_static p ports w hp hz
  simpa only [hp] using static_implies_original_zero ports w hg hn

/-- Candidate transfer to the original 14-variable source syntax. -/
theorem seed_zero_implies_source_zero (p : Fin 4 → ℤ) (ports : Fin 4 → V)
    (w : Fin 38 → V) (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    InternalZero (ObjectCurrentEquation2011.expressionAt p)
      (fun j => w (Fin.castLE (by decide : 14 ≤ 38) j) + 1) := by
  rw [internalZero_iff, FreshModel106.evalRing_expressionAt65]
  exact seed_zero_implies_original_zero p ports w hp hz
end Model

-- Still required: Lean checks, fixed-port casts, reverse witness construction,
-- Jones composition and the iPRA consistency endpoint.
end DiophantineConsistency.Norm38Reference
''')
target=P/'Norm38Reference.lean';table=P/'reference-rows.json';assert not target.exists() and not table.exists();target.write_text(''.join(lines));table.write_text(json.dumps({'source_graph_sha256':sha(gpath),'rows':rows},indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'GENERATED_UNCOMPILED_DRAFT','source_sha256':sha(target),'row_table_sha256':sha(table),'rows':len(rows)},indent=2,sort_keys=True))
