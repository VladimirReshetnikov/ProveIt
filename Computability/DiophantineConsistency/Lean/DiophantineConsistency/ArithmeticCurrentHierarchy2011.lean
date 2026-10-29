import DiophantineConsistency.FoundationHACurrentNoZero2011
import DiophantineConsistency.FoundationZFCConsistencyNat

/-! Syntactic hierarchy certificates for the exact maintained source sentences.
The large polynomial terms remain opaque. These certificates neither assert
PRA provability nor apply a conservation theorem. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace DiophantineConsistency.ArithmeticCurrentHierarchy2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

private theorem allClosure_pi_one {L : Language} [L.LT] {ξ : Type*}
    {n : ℕ} (φ : Semiformula L ξ n) (hφ : Hierarchy 𝚷 1 φ) :
    Hierarchy 𝚷 1 (∀⁰* φ) := by
  induction n with
  | zero => exact hφ
  | succ n ih =>
      simpa only [allClosure_succ] using ih (∀⁰ φ) hφ.all

/-- The actual fourteen-variable no-zero source is syntactically Π₁. -/
theorem current_pi_one :
    Hierarchy 𝚷 1 FoundationHACurrentNoZero2011.classicalSentence := by
  unfold FoundationHACurrentNoZero2011.classicalSentence
    FoundationHANoZero.classicalNoZero
  exact allClosure_pi_one _ (Hierarchy.nrel _ _ _ _)

/-- Use the certificate of the actual Foundation ZFC consistency sentence. -/
theorem consistency_pi_one :
    Hierarchy 𝚷 1 FoundationZFCConsistencyNat.sourceSentence :=
  (LO.FirstOrder.SetTheory.ZermeloFraenkelChoice : LO.FirstOrder.SetTheory).consistent.pi_prop

/-- The literal biconditional, without replacing it by a prenex equivalent. -/
theorem current_iff_consistency_pi_two : Hierarchy 𝚷 2
    (FoundationHACurrentNoZero2011.classicalSentence 🡘
      FoundationZFCConsistencyNat.sourceSentence) :=
  Hierarchy.iff_iff.mpr ⟨current_pi_one.accum 𝚷, current_pi_one.accum 𝚺,
    consistency_pi_one.accum 𝚷, consistency_pi_one.accum 𝚺⟩

def endpoint : 𝚷-[2].Sentence := .mkPi
  (FoundationHACurrentNoZero2011.classicalSentence 🡘
    FoundationZFCConsistencyNat.sourceSentence) current_iff_consistency_pi_two

theorem endpoint_val : endpoint.val =
    (FoundationHACurrentNoZero2011.classicalSentence 🡘
      FoundationZFCConsistencyNat.sourceSentence) := rfl

end DiophantineConsistency.ArithmeticCurrentHierarchy2011
