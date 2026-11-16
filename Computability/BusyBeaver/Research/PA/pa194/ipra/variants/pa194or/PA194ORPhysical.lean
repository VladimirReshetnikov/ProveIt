import PA194ORRows
import PA194ORChecks

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false

namespace PA194ORPhysical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.Runtime
open ConPA.Machine ConPA.Machine.Compressed
open PA194ORData PA194ORChecks

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

theorem root_control (gap : V) (box : BoxSt → V) (i extra : Nat) (effect : Eff) :
    π₁ (root gap box i extra effect) = (24 : V) := by
  rw [root,encodeControl]
  change (denseControl 84 : V) = (24 : V)
  rw [rootControl]
  rfl

theorem contract_sound (gap : V) {br : Branch} {box : BoxSt → V}
    (hb : BoxAgreement table denseControl br box) (i j extra fuel : Nat) (effect : Eff)
    (cert : contract br i j extra fuel effect = true) :
    Reach1 table (root gap box i) (root gap box j extra effect) :=
  checkedMatch PA194ORRows.rowAgreement gap hb fuel _ _ cert

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
      checkedRun PA194ORRows.rowAgreement gap hb (fun s => s.1 == 254) fuel start last false observed
    refine ⟨encode denseControl gap box last, positive rfl, ?_⟩
    rw [encodeControl, beq_iff_eq.mp finished, haltControl]
    rfl

theorem halt_absorbs (y : V) (h : π₁ y = (194 : V)) : step table y = y := by
  have he : y = PA194BModelSteps.config 194 (π₁ (π₂ y)) (π₂ (π₂ y)) := by
    unfold PA194BModelSteps.config
    change π₁ y = ((194 : Nat) : V) at h
    rw [← h,pair_unpair,pair_unpair]
  conv_lhs => rw [he]
  rw [table, PA194BModelSteps.halted rows rowCount, ← he]

theorem noInteriorHalt (initial gap : V) (box : BoxSt → V) (i extra : Nat) (effect : Eff)
    (time destination : V) (hbound : time ≤ destination)
    (reaches : runFrom table destination initial = root gap box i extra effect) :
    π₁ (runFrom table time initial) ≠ (194 : V) := by
  intro hh
  obtain ⟨duration,rfl⟩ := exists_add_of_le hbound
  rw [runFrom_add] at reaches
  letI := runFrom_definable (V := V) table
  have fixed : ∀ t : V, runFrom table t (runFrom table time initial) = runFrom table time initial := by
    intro t
    induction t using ISigma1.sigma1_succ_induction with
    | hP => definability
    | zero => simp
    | succ t ih => rw [runFrom_succ, ih, halt_absorbs _ hh]
  rw [fixed] at reaches
  have hControl := congrArg (fun x : V => π₁ x) reaches
  rw [hh,root_control] at hControl
  exact (show (194 : V) ≠ (24 : V) by norm_num) hControl

#print axioms contract_sound
#print axioms halt_sound
#print axioms noInteriorHalt
end models
end PA194ORPhysical
