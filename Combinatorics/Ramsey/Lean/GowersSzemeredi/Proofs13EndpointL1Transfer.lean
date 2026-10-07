import GowersSzemeredi.Proofs13EndpointUnitPhase

/-! Uniform L1 control of derivative perturbations. Each multiplicative
difference costs a factor two, independent of the chosen direction. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def endpointL1Distance {N : Nat} [NeZero N] (f g : ZMod N → Complex) : Real :=
  𝔼 x : ZMod N, ‖f x - g x‖

theorem difference_norm_sub_le {N : Nat} (f g : ZMod N → Complex)
    (hf : DiscValued f) (hg : DiscValued g) (r x : ZMod N) :
    ‖difference f r x - difference g r x‖ ≤ ‖f x - g x‖ + ‖f (x - r) - g (x - r)‖ := by
  have he : difference f r x - difference g r x =
      (f x - g x) * star (f (x - r)) + g x * star (f (x - r) - g (x - r)) := by
    simp only [difference, star_sub]
    ring
  rw [he]
  calc
    _ ≤ ‖(f x - g x) * star (f (x - r))‖ + ‖g x * star (f (x - r) - g (x - r))‖ := norm_add_le _ _
    _ = ‖f x - g x‖ * ‖f (x - r)‖ + ‖g x‖ * ‖f (x - r) - g (x - r)‖ := by
      rw [norm_mul, norm_mul, norm_star, norm_star]
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_left (hf (x - r)) (norm_nonneg (f x - g x))
      have h₂ := mul_le_mul_of_nonneg_right (hg x) (norm_nonneg (f (x - r) - g (x - r)))
      nlinarith only [h₁, h₂]

theorem endpointL1Distance_difference {N : Nat} [NeZero N] (f g : ZMod N → Complex)
    (hf : DiscValued f) (hg : DiscValued g) (r : ZMod N) :
    endpointL1Distance (difference f r) (difference g r) ≤ 2 * endpointL1Distance f g := by
  calc
    _ ≤ 𝔼 x : ZMod N, (‖f x - g x‖ + ‖f (x - r) - g (x - r)‖) :=
      Finset.expect_le_expect (fun x _ => difference_norm_sub_le f g hf hg r x)
    _ = endpointL1Distance f g + endpointL1Distance f g := by
      rw [Finset.expect_add_distrib]
      congr 1
      exact Fintype.expect_equiv (Equiv.subRight r) _ _ (fun _ => rfl)
    _ = _ := by ring

theorem endpointL1Distance_iteratedDifference {N : Nat} [NeZero N] (f g : ZMod N → Complex)
    (hf : DiscValued f) (hg : DiscValued g) (a : List (ZMod N)) :
    endpointL1Distance (iteratedDifference f a) (iteratedDifference g a) ≤
      (2 : Real) ^ a.length * endpointL1Distance f g := by
  induction a with
  | nil => simp [iteratedDifference]
  | cons r a ih =>
    have ht := endpointL1Distance_difference (iteratedDifference f a) (iteratedDifference g a)
      (iteratedDifference_discValued hf a) (iteratedDifference_discValued hg a) r
    calc
      _ ≤ 2 * endpointL1Distance (iteratedDifference f a) (iteratedDifference g a) := ht
      _ ≤ 2 * ((2 : Real) ^ a.length * endpointL1Distance f g) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [List.length_cons, pow_succ]; ring

theorem endpointL1Distance_cubeDifference {N d : Nat} [NeZero N] (f g : ZMod N → Complex)
    (hf : DiscValued f) (hg : DiscValued g) (a : Point N d) :
    endpointL1Distance (cubeDifference f a) (cubeDifference g a) ≤
      (2 : Real) ^ d * endpointL1Distance f g := by
  simpa only [cubeDifference, List.length_ofFn] using endpointL1Distance_iteratedDifference f g hf hg (List.ofFn a)

theorem endpointL1Distance_unitPhase {N : Nat} [NeZero N] (f : ZMod N → Complex)
    (hf : DiscValued f) :
    endpointL1Distance f (fun x => endpointUnitPhase (f x)) = 1 - 𝔼 x : ZMod N, ‖f x‖ := by
  unfold endpointL1Distance
  simp_rw [endpointUnitPhase_distance _ (hf _)]
  rw [Finset.expect_sub_distrib, Fintype.expect_const]

theorem endpoint_unitPhase_mean_cube_defect {N d : Nat} [NeZero N]
    (f : ZMod N → Complex) (hf : DiscValued f) :
    1 - (𝔼 a : Point N d, 𝔼 x : ZMod N, (cubeDifference (fun y => endpointUnitPhase (f y)) a x).re) ≤
      2 * (1 - (𝔼 a : Point N d, 𝔼 x : ZMod N, (cubeDifference f a x).re)) := by
  have ht : (𝔼 a : Point N d, 𝔼 x : ZMod N,
      (1 - (cubeDifference (fun y => endpointUnitPhase (f y)) a x).re)) ≤
      𝔼 a : Point N d, 𝔼 x : ZMod N, 2 * (1 - (cubeDifference f a x).re) := by
    apply Finset.expect_le_expect
    intro a _
    apply Finset.expect_le_expect
    intro x _
    exact iteratedDifference_unitPhase_defect f hf (List.ofFn a) x
  simpa only [Finset.expect_sub_distrib, ← Finset.mul_expect, Fintype.expect_const] using ht

end LeanProofs.GowersSzemeredi
