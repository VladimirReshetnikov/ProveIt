import GowersSzemeredi.Proofs13EndpointL1Transfer

/-! Normalize a near-maximal cube average to a unit-modulus function.
This establishes the endpoint phase-rounding step with explicit L1 and
cube-average losses, and connects the average to catalogue uniformity. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def endpointCubeMean {N : Nat} [NeZero N] (f : ZMod N → Complex) (d : Nat) : Real :=
  𝔼 a : Point N d, 𝔼 x : ZMod N, (cubeDifference f a x).re

theorem iteratedDifference_norm_le_anchor {N : Nat} (f : ZMod N → Complex)
    (hf : DiscValued f) (a : List (ZMod N)) (x : ZMod N) :
    ‖iteratedDifference f a x‖ ≤ ‖f x‖ := by
  induction a generalizing x with
  | nil => exact le_refl _
  | cons r a ih =>
    simp only [iteratedDifference, difference, norm_mul, norm_star]
    calc
      _ ≤ ‖iteratedDifference f a x‖ * 1 :=
        mul_le_mul_of_nonneg_left (iteratedDifference_discValued hf a (x - r)) (norm_nonneg _)
      _ ≤ ‖f x‖ := by simpa only [mul_one] using ih x

theorem endpointCubeMean_le_mean_norm {N d : Nat} [NeZero N] (f : ZMod N → Complex)
    (hf : DiscValued f) : endpointCubeMean f d ≤ 𝔼 x : ZMod N, ‖f x‖ := by
  unfold endpointCubeMean
  apply Finset.expect_le Finset.univ_nonempty
  intro a _
  apply Finset.expect_le_expect
  intro x _
  exact (Complex.re_le_norm _).trans (iteratedDifference_norm_le_anchor f hf (List.ofFn a) x)

theorem endpointCubeMean_succ {N d : Nat} [NeZero N] (f : ZMod N → Complex) :
    endpointCubeMean f (d + 1) =
      (∑ a : Point N d, ‖∑ x : ZMod N, cubeDifference f a x‖ ^ 2) / (N : Real) ^ (d + 2) := by
  have hs : (∑ a : Point N (d + 1), ∑ x : ZMod N, (cubeDifference f a x).re) =
      ∑ a : Point N d, ‖∑ x : ZMod N, cubeDifference f a x‖ ^ 2 := by
    simpa only [Complex.re_sum, Complex.ofReal_re] using congrArg Complex.re (sum_cube_succ_eq_sum_norm_sq (n := d) f)
  unfold endpointCubeMean
  simp_rw [Fintype.expect_eq_sum_div_card]
  simp only [Point, Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]
  rw [← Finset.sum_div, hs, div_div]
  congr 1
  rw [mul_comm, ← pow_succ]

theorem uniformOfDegree_iff_endpointCubeMean {N d : Nat} [NeZero N]
    (f : ZMod N → Complex) (alpha : Real) :
    UniformOfDegree f alpha d ↔ endpointCubeMean f (d + 1) ≤ alpha := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  rw [endpointCubeMean_succ, div_le_iff₀ (by positivity : (0 : Real) < (N : Real) ^ (d + 2))]
  rfl

theorem endpoint_unitPhase_normalization {N d : Nat} [NeZero N]
    (f : ZMod N → Complex) (hf : DiscValued f) (epsilon : Real)
    (hnear : 1 - epsilon ≤ endpointCubeMean f d) :
    endpointL1Distance f (fun x => endpointUnitPhase (f x)) ≤ epsilon ∧
      1 - 2 * epsilon ≤ endpointCubeMean (fun x => endpointUnitPhase (f x)) d := by
  constructor
  · rw [endpointL1Distance_unitPhase f hf]
    have ht := endpointCubeMean_le_mean_norm (d := d) f hf
    linarith only [hnear, ht]
  · have ht := endpoint_unitPhase_mean_cube_defect (d := d) f hf
    change 1 - endpointCubeMean (fun x => endpointUnitPhase (f x)) d ≤
      2 * (1 - endpointCubeMean f d) at ht
    linarith only [hnear, ht]

theorem endpoint_unitPhase_derivative_transfer {N d s : Nat} [NeZero N]
    (f : ZMod N → Complex) (hf : DiscValued f) (epsilon : Real)
    (hnear : 1 - epsilon ≤ endpointCubeMean f d) (a : Point N s) :
    endpointL1Distance (cubeDifference f a)
      (cubeDifference (fun x => endpointUnitPhase (f x)) a) ≤ (2 : Real) ^ s * epsilon := by
  have hnorm := (endpoint_unitPhase_normalization f hf epsilon hnear).1
  exact (endpointL1Distance_cubeDifference f _ hf (endpointUnitPhase_discValued f) a).trans
    (mul_le_mul_of_nonneg_left hnorm (by positivity))

end LeanProofs.GowersSzemeredi
