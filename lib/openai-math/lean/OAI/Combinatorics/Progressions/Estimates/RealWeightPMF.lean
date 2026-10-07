import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped ENNReal

noncomputable def realWeightPMF {X : Type*} (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : Summable w) (hZ : 0 < ∑' x, w x) : PMF X :=
  ⟨fun x => ENNReal.ofReal (w x / ∑' y, w y), ENNReal.summable.hasSum_iff.mpr (by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => div_nonneg (hw x) hZ.le) (hs.div_const _),
      tsum_div_const, div_self hZ.ne', ENNReal.ofReal_one])⟩

theorem realWeightPMF_apply {X : Type*} (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : Summable w) (hZ : 0 < ∑' x, w x) (x : X) :
    (realWeightPMF w hw hs hZ x).toReal = w x / ∑' y, w y :=
  ENNReal.toReal_ofReal (div_nonneg (hw x) hZ.le)

theorem realWeightPMF_map_fiber {X Y : Type*} (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : Summable w) (hZ : 0 < ∑' x, w x) (F : X → Y) (y : Y) :
    ((realWeightPMF w hw hs hZ).map F y).toReal =
      (∑' x : {x : X // F x = y}, w x.val) / ∑' x, w x := by
  classical
  have he : (realWeightPMF w hw hs hZ).map F y =
      ∑' x : {x : X // F x = y}, realWeightPMF w hw hs hZ x.val := by
    rw [PMF.map_apply]
    calc
      _ = ∑' x : X, ({a : X | F a = y} : Set X).indicator (realWeightPMF w hw hs hZ) x := by
        apply tsum_congr
        intro x
        by_cases hx : F x = y
        · simp [hx]
        · simp [hx, Ne.symm hx]
      _ = _ := (tsum_subtype ({a : X | F a = y}) (realWeightPMF w hw hs hZ)).symm
  rw [he]
  change (∑' x : {x : X // F x = y}, ENNReal.ofReal (w x.val / ∑' z, w z)).toReal = _
  let g : {x : X // F x = y} → ℝ := fun x => w x.val / ∑' z, w z
  have hg : Summable g := (hs.subtype (fun x => F x = y)).div_const _
  have hg0 (x) : 0 ≤ g x := div_nonneg (hw x.val) hZ.le
  have ht := ENNReal.ofReal_tsum_of_nonneg hg0 hg
  change (∑' x, ENNReal.ofReal (g x)).toReal = _
  rw [← ht, ENNReal.toReal_ofReal (tsum_nonneg hg0)]
  exact tsum_div_const

end Erdos3

end

end OAI
