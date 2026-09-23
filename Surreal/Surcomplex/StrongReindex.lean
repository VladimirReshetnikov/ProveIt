import Surreal.Surcomplex.StrongSummation
import Surreal.Foundations.SignSequenceStrongRegroup

/-!
# Injective reindexing of actual complex strong sums

Coordinatewise real strong summation transfers injective reindexing and
removal of zero terms to actual surcomplex sums. In particular, this
justifies the odd-power inverse-sine series in `trigonometry:eq:foldroots`.
-/

universe u v w

namespace Surreal.Surcomplex

open Foundations

variable {ι : Type v} {κ : Type w} {f : ι → Surcomplex.{u}}

/-- An injectively indexed subfamily remains strongly summable. -/
theorem StronglySummable.comp_injective (hf : StronglySummable f) (k : κ → ι)
    (hk : Function.Injective k) : StronglySummable (fun n => f (k n)) := by
  rw [stronglySummable_iff_re_im]
  exact ⟨hf.re.comp_injective k hk, hf.im.comp_injective k hk⟩

/-- Removing terms that vanish outside an injective image preserves the actual sum. -/
theorem strongSum_comp_injective [Small.{u} ι] [Small.{u} κ]
    (hf : StronglySummable f) (k : κ → ι) (hk : Function.Injective k)
    (hz : ∀ i, i ∉ Set.range k → f i = 0) :
    strongSum (fun n => f (k n)) (hf.comp_injective k hk) = strongSum f hf := by
  apply ext
  · simp only [strongSum_re]
    exact SignSequence.strongSum_comp_injective hf.re k hk (by
      intro i hi
      simp only [hz i hi, QuadraticAlgebra.re_zero])
  · simp only [strongSum_im]
    exact SignSequence.strongSum_comp_injective hf.im k hk (by
      intro i hi
      simp only [hz i hi, QuadraticAlgebra.im_zero])

end Surreal.Surcomplex
