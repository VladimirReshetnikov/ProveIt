import ConPAMachineCompressedNormalization
import PA194ADCompressedRows
import PA194ADCompressedChecks
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194ADCompressedPhysical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.Runtime ConPA.Machine ConPA.Machine.Compressed
open PA194ADCompressedData PA194ADCompressedChecks PA194SourceProgram

theorem rootControl : denseControl 84 = 24 := by decide +kernel
theorem haltControl : denseControl 254 = 194 := by decide +kernel
theorem rowCount : rows.length = 388 := by decide +kernel

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def root (gap : V) (box : BoxSt → V) (i : Nat) (extra : Nat := 0)
    (effect : Eff := .none) : V :=
  encode denseControl gap box (PA194RuntimeContracts.rootFrame (path i) extra effect)

theorem encodeControl (label : Nat → Nat) (gap : V) (box : BoxSt → V) (s : SConf) :
    π₁ (encode label gap box s) = (label s.1 : V) := by
  rcases s with ⟨q,onLeft,l,r⟩
  cases onLeft <;> simp [encode,scanFrame]

theorem contract_sound (gap : V) {br : Branch} {box : BoxSt → V}
    (hb : BoxAgreement table denseControl br box) (i j extra fuel : Nat) (effect : Eff)
    (cert : contract br i j extra fuel effect = true) :
    Reach1 table (root gap box i) (root gap box j extra effect) :=
  checkedMatch PA194ADCompressedRows.rowAgreement gap hb fuel _ _ cert

theorem halt_sound (gap : V) {box : BoxSt → V}
    (hb : BoxAgreement table denseControl none box) (i fuel : Nat)
    (cert : haltContract i fuel = true) :
    ∃ final, Reach1 table (root gap box i) final ∧ π₁ final = (194 : V) := by
  let start := PA194RuntimeContracts.rootFrame (path i)
  change (exec machine none (fun s => s.1 == 254) fuel start false).isSome = true at cert
  cases observed : exec machine none (fun s => s.1 == 254) fuel start false with
  | none => simp [observed] at cert
  | some last =>
    obtain ⟨finished,_,positive⟩ :=
      checkedRun PA194ADCompressedRows.rowAgreement gap hb (fun s => s.1 == 254) fuel start last false observed
    refine ⟨encode denseControl gap box last, positive rfl, ?_⟩
    rw [encodeControl, beq_iff_eq.mp finished, haltControl]
    rfl

#print axioms contract_sound
#print axioms halt_sound
end models
end PA194ADCompressedPhysical
