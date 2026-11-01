import ZFCinPA.ModelCodedDecoderAccepted254
import ZFCinPA.ModelCodedDecoderGrowG222
import ZFCinPA.ModelCodedDecoderBundle222
import BusyBeaver.ZFC.ArithmeticHistory222

set_option autoImplicit false
noncomputable section

/-!
# Accepted C222 proofs decode to internal ZF theorems

The C222 row kernel differs from C254 only at tag 9 (the equality row
`growG`) and tag 11 (the helper-free seed bundle). Every other row is the
C254 row, whose local soundness (`ModelCodedDecoderAccepted254.rowKernel_sound`)
is reused verbatim. `growG` is provable from equality alone, and the decoded
bundle is an internal `𝗭𝗙` theorem by the compiled seed templates
(`ModelCodedDecoderBundle222`). A genuine `Σ₁` order induction over all
internal proof codes then shows that every accepted C222 conclusion decodes
to an internal `𝗭𝗙` theorem; value two decodes to falsity.
-/

namespace LeanProofs.ZFCinPA.ModelCodedDecoderAccepted222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderFalsity254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private instance value_delta : 𝚫₁-Function₁[V] ArithmeticHistory222.value :=
  ArithmeticHistory222.value_defined_delta.to_definable
private instance decode_delta : 𝚫₁-Function₁[V] ModelCodedDecoder254.decode :=
  decode_defined.graph_delta.to_definable

/-- Local soundness of one C222 row. -/
theorem rowKernel_sound (k payload u v : V)
    (hu : u ≠ 0 → Provable (𝗭𝗙 : SetTheory) (decode (u-1)))
    (hv : v ≠ 0 → Provable (𝗭𝗙 : SetTheory) (decode (v-1))) :
    ArithmeticRow222.rowKernel k payload u v = 0 ∨
      Provable (𝗭𝗙 : SetTheory) (decode (ArithmeticRow222.rowKernel k payload u v-1)) := by
  classical
  by_cases h9 : k = 9
  · subst h9
    right
    rw [ArithmeticRow222.rowKernel_growG, add_tsub_cancel_right]
    exact ModelCodedDecoderGrowG222.decoded_growG_provable 𝗭𝗙 _ _ _
  by_cases h11 : k = 11
  · subst h11
    rw [ArithmeticRow222.rowKernel_bundle]
    by_cases hg : second (second payload) ≠ first payload ∧
        second (second payload) ≠ first (second payload)
    · right
      rw [if_pos hg, add_tsub_cancel_right]
      exact ModelCodedDecoderBundle222.zf_decoded_bundle222_provable _ _ _ hg.1 hg.2
    · left
      rw [if_neg hg]
  rw [ArithmeticRow222.rowKernel_unchanged k payload u v h9 h11]
  exact ModelCodedDecoderAccepted254.rowKernel_sound k payload u v hu hv

/-- One actual `Σ₁` invariant over all internal proof codes. -/
theorem rejected_or_decoded_provable : ∀ code : V,
    ArithmeticHistory222.value code = 0 ∨
      Provable (𝗭𝗙 : SetTheory) (decode (ArithmeticHistory222.value code-1)) :=
  ModelCodedDecoderAccepted254.history_sound ArithmeticHistory222.value
    ArithmeticRow222.rowKernel ArithmeticHistory222.value_zero
    ArithmeticHistory222.value_succ rowKernel_sound

theorem accepted_conclusion_provable (code conclusion : V)
    (hv : ArithmeticHistory222.value code = conclusion+1) :
    Provable (𝗭𝗙 : SetTheory) (decode conclusion) := by
  have hne : ArithmeticHistory222.value code ≠ 0 := by rw [hv]; simp
  simpa [hv] using (rejected_or_decoded_provable code).resolve_left hne

/-- **An accepted C222 refutation is an internal ZF refutation.** -/
theorem accepted_falsity_provable_bottom (code : V) (hv : ArithmeticHistory222.value code = 2) :
    Provable (𝗭𝗙 : SetTheory) (^⊥ : V) := by
  apply decoded_one_provable_iff_bottom.mp
  exact accepted_conclusion_provable code 1 (by simpa only [one_add_one_eq_two] using hv)

end LeanProofs.ZFCinPA.ModelCodedDecoderAccepted222
