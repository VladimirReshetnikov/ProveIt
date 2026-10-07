import OAI.Combinatorics.Progressions.Probability.FiniteDensityMassBound

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem normalized_finite_weight_approximation {X : Type*}
    (v : X → ℝ) (S : Finset X) (hv0 : ∀ x, 0 ≤ v x)
    (hv : ∀ x ∉ S, v x = 0) (hZ : 0 < ∑' x, v x)
    (w f g : X → ℂ) {η : ℝ} (hη : 0 ≤ η)
    (hw : ∀ x ∈ S, ‖w x‖ ≤ 1) (he : ∀ x ∈ S, ‖f x - g x‖ ≤ η) :
    ‖(∑' x, ((v x / (∑' y, v y) : ℝ) : ℂ) * (w x * f x)) -
      ∑' x, ((v x / (∑' y, v y) : ℝ) : ℂ) * (w x * g x)‖ ≤ η := by
  let p := finiteSupportProbability v S hv0 hv hZ
  have hm : p.mean (fun x => ‖w x.val‖) ≤ 1 :=
    (p.mean_mono (fun x => hw x.val x.property)).trans_eq (p.mean_const 1)
  have h := (p.norm_weighted_complexMean_sub_le_mean_norm (fun x => w x.val)
    (fun x => f x.val) (fun x => g x.val) (fun x _ => he x.val x.property)).trans
      ((mul_le_mul_of_nonneg_left hm hη).trans_eq (mul_one η))
  change ‖(finiteSupportProbability v S hv0 hv hZ).complexMean (fun x => w x.val * f x.val) -
    (finiteSupportProbability v S hv0 hv hZ).complexMean (fun x => w x.val * g x.val)‖ ≤ η at h
  rw [finiteSupportProbability_complexMean v S hv0 hv hZ (fun x => w x * f x),
    finiteSupportProbability_complexMean v S hv0 hv hZ (fun x => w x * g x)] at h
  exact h

end Erdos3

end

end OAI
