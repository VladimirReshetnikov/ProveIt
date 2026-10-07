import GowersSzemeredi.Proofs08QuadraticFrequencies
import GowersSzemeredi.Proofs18IntervalCubeEnergy

/-! The terminal linear obstruction gives a large Fourier coefficient, and
for an interval model this is the correlation of the original index function. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ZMod
namespace LeanProofs.GowersSzemeredi

/-- Relate the cube-coordinate and correlation formulations in degree one. -/
theorem uniform_degree_one_iff_condition2i {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (alpha : Real) :
    UniformOfDegree f alpha 1 ↔ uniformCondition2i f alpha := by
  have hs := (pointOneEquiv N).sum_comp
    (fun x : Point N 1 ↦ ‖∑ s : ZMod N, cubeDifference f x s‖ ^ 2)
  simp only [cubeDifference_pointOne] at hs
  unfold UniformOfDegree uniformCondition2i
  rw [← hs]
  rfl

/-- Parseval and the fourth moment force a coefficient larger than
sqrt(alpha)*N when degree-one uniformity fails for a disc-valued function. -/
theorem linear_nonuniformity_large_fourier {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (alpha : Real) (hα : 0 ≤ alpha)
    (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha 1) :
    ∃ r : ZMod N, Real.sqrt alpha * N < ‖fourier f r‖ := by
  classical
  by_contra h
  push Not at h
  obtain ⟨_, hi_iii, _, hiv_iii, _, _⟩ :=
    lemma_2_2_holds N f hf alpha (Real.sqrt alpha) 0
  have hi := hi_iii.mpr (hiv_iii (Real.sq_sqrt hα).le h)
  exact hnot ((uniform_degree_one_iff_condition2i f alpha).mpr hi)

/-- The interval index set is equivalent to its supported points in a
larger cyclic group. -/
def intervalIndexEquiv {N L : Nat} [NeZero N] (hL : L ≤ N) :
    Fin L ≃ {x : ZMod N // x.val < L} where
  toFun i := ⟨(i : Nat), by simpa only [ZMod.val_natCast_of_lt (i.isLt.trans_le hL)] using i.isLt⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv i := by apply Fin.ext; exact ZMod.val_natCast_of_lt (i.isLt.trans_le hL)
  right_inv x := by apply Subtype.ext; exact ZMod.natCast_zmod_val x.val

/-- Extending by zero preserves every weighted sum of the interval values. -/
theorem intervalExtension_sum_mul {N L : Nat} [NeZero N]
    (hL : L ≤ N) (g : Fin L → Complex) (w : ZMod N → Complex) :
    (∑ x : ZMod N, intervalExtension N g x * w x) =
      ∑ i : Fin L, g i * w (i : Nat) := by
  classical
  let F := fun x : ZMod N ↦ intervalExtension N g x * w x
  calc
    _ = ∑ x : {x : ZMod N // x.val < L}, F x.val := by
      exact Finset.sum_congr_set {x : ZMod N | x.val < L} F (fun x ↦ F x.val)
        (fun _ _ ↦ rfl) (fun x hx ↦ by
          change ¬ x.val < L at hx
          simp [F, intervalExtension, hx])
    _ = ∑ i : Fin L, F ((intervalIndexEquiv hL i).val) :=
      ((intervalIndexEquiv hL).sum_comp (fun x ↦ F x.val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      change intervalExtension N g (i : Nat) * w (i : Nat) = _
      rw [intervalExtension_natCast hL]

/-- The Fourier coefficient of an interval model is its index correlation. -/
theorem fourier_intervalExtension {N L : Nat} [NeZero N]
    (hL : L ≤ N) (g : Fin L → Complex) (r : ZMod N) :
    fourier (intervalExtension N g) r =
      ∑ i : Fin L, g i * exponential (-(r * ((i : Nat) : ZMod N))) := by
  rw [fourier, ZMod.dft_apply]
  simpa only [exponential, smul_eq_mul, mul_comm] using
    intervalExtension_sum_mul hL g (fun x ↦ exponential (-(r * x)))

/-- A linear obstruction in a cyclic interval model forces bias in the
original finite function, normalized by its own length. -/
theorem interval_linear_nonuniformity_correlation {N L : Nat} [NeZero N]
    (hL : L ≤ N) (g : Fin L → Complex) (alpha : Real) (hα : 0 ≤ alpha)
    (hf : DiscValued (intervalExtension N g))
    (hnot : ¬ UniformOfDegree (intervalExtension N g) alpha 1) :
    ∃ r : ZMod N, Real.sqrt alpha * L <
      ‖∑ i : Fin L, g i * exponential (-(r * ((i : Nat) : ZMod N)))‖ := by
  obtain ⟨r, hr⟩ := linear_nonuniformity_large_fourier _ alpha hα hf hnot
  rw [fourier_intervalExtension hL] at hr
  exact ⟨r, (mul_le_mul_of_nonneg_left (by exact_mod_cast hL) (Real.sqrt_nonneg _)).trans_lt hr⟩

end LeanProofs.GowersSzemeredi
