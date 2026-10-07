import GowersSzemeredi.Proofs16OddDenseBox
import GowersSzemeredi.Proofs17LocalizedPhaseRemoval
import GowersSzemeredi.Proofs16CorollaryFromInduction

/-! Dense large Fourier frequencies on an arbitrary-dimensional box give
the second-moment input to polynomial localization. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- Large coefficients on a dense subset yield the full box energy lower
bound, with the exact square of the Fourier threshold. -/
theorem multilinear_box_fourier_energy {N k m : Nat} [NeZero N]
    (P : Box N k) (B : Finset (Point N k)) (f : ZMod N → Complex)
    (mu : Point N k → ZMod N) {alpha delta : Real}
    (hα : 0 ≤ alpha) (hB : B ⊆ P.carrier)
    (hmass : delta * (m : Real) ^ k ≤ B.card)
    (hfourier : ∀ x ∈ B, alpha / 2 * N ≤ ‖fourier (cubeDifference f x) (mu x)‖) :
    (delta * alpha ^ 2 / 4) * (N : Real) ^ 2 * (m : Real) ^ k ≤
      ∑ x ∈ P.carrier, ‖fourier (cubeDifference f x) (mu x)‖ ^ 2 := by
  classical
  have hpoint : ∀ x ∈ B, (alpha / 2 * N) ^ 2 ≤
      ‖fourier (cubeDifference f x) (mu x)‖ ^ 2 := by
    intro x hx
    exact pow_le_pow_left₀ (by positivity) (hfourier x hx) 2
  have hmass' := mul_le_mul_of_nonneg_right hmass (sq_nonneg (alpha / 2 * N))
  calc
    _ ≤ (B.card : Real) * (alpha / 2 * N) ^ 2 := by nlinarith only [hmass']
    _ = ∑ _x ∈ B, (alpha / 2 * N) ^ 2 := by simp
    _ ≤ ∑ x ∈ B, ‖fourier (cubeDifference f x) (mu x)‖ ^ 2 := Finset.sum_le_sum hpoint
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hB (fun _ _ _ => sq_nonneg _)

/-- Keep the stronger corollary width exponent, capped only to make the
localized prime models short enough for the next inverse step. -/
def section16ShortBoxExponent (alpha : Real) (k : Nat) : Real :=
  min (section16CorollaryWidthExponent alpha k) (1 / 2)

theorem section16ShortBoxExponent_pos {alpha : Real} (hα : 0 < alpha) (k : Nat) :
    0 < section16ShortBoxExponent alpha k :=
  lt_min (section16_corollary_width_exponent_pos hα k) (by norm_num)

/-- The density retained after making every side short, equal, and odd. -/
def section16ShortBoxDensity (alpha : Real) (k : Nat) : Real :=
  section16CorollaryExponent alpha k / (2 : Real) ^ k

theorem section16ShortBoxDensity_pos {alpha : Real} (hα : 0 < alpha) (k : Nat) :
    0 < section16ShortBoxDensity alpha k := by
  unfold section16ShortBoxDensity
  rw [section16_corollary_common_exponent_eq_width]
  have h := section16_corollary_width_exponent_pos hα k
  positivity

/-- Extract the actual large-frequency points, then use the general odd
box cover. No geometry or frequencies outside the original dense set are
assumed. The multilinear map remains globally defined. -/
theorem short_odd_multilinear_fourier_box {N k : Nat} [Fact N.Prime]
    (P : Box N k) (hP : P.IsProper) (hk : 0 < k)
    (f : ZMod N → Complex) (mu : Point N k → ZMod N) {alpha : Real}
    (hα : 0 < alpha) (hmu : IsMultilinear mu)
    (hwidth : (N : Real) ^ section16CorollaryWidthExponent alpha k ≤ P.width)
    (hmass : section16CorollaryExponent alpha k * P.carrier.card ≤
      section16LargeMultilinearFrequencyCount f P mu alpha)
    (hlarge : 4 ≤ (N : Real) ^ section16ShortBoxExponent alpha k) :
    ∃ m : Nat, ∃ Q : Box N k,
      Odd m ∧ 0 < m ∧ (N : Real) ^ section16ShortBoxExponent alpha k / 2 ≤ m ∧
      (m : Real) ≤ Real.sqrt N ∧ Q.commonDiff != 0 ∧ Q.IsProper ∧
      Q.width = m ∧ (∀ i, (Q.axis i).length = m) ∧ IsMultilinear mu ∧
      (section16ShortBoxDensity alpha k * alpha ^ 2 / 4) * (N : Real) ^ 2 * (m : Real) ^ k ≤
        ∑ x ∈ Q.carrier, ‖fourier (cubeDifference f x) (mu x)‖ ^ 2 := by
  classical
  let B := P.carrier.filter fun x => alpha / 2 * N ≤ ‖fourier (cubeDifference f x) (mu x)‖
  have hBcard : B.card = section16LargeMultilinearFrequencyCount f P mu alpha := by
    unfold section16LargeMultilinearFrequencyCount countWhere
    congr 1
    ext x
    simp [B]
  have hB : B ⊆ P.carrier := Finset.filter_subset _ _
  have hN : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  have hwidth' : (N : Real) ^ section16ShortBoxExponent alpha k ≤ P.width :=
    (Real.rpow_le_rpow_of_exponent_le hN (min_le_left _ _)).trans hwidth
  have hδ : 0 ≤ section16CorollaryExponent alpha k := by
    rw [section16_corollary_common_exponent_eq_width]
    have h := section16_corollary_width_exponent_pos hα k
    positivity
  obtain ⟨m, Q, C, hm, hmpos, hmlower, hmupper, _, hstep, hp, hw, haxes, hCB, hCQ, hCmass⟩ :=
    P.dense_odd_short_box hP hk B hδ (min_le_right _ _) hwidth' hlarge hB (by rwa [hBcard])
  refine ⟨m, Q, hm, hmpos, hmlower, hmupper, hstep, hp, hw, haxes, hmu, ?_⟩
  exact multilinear_box_fourier_energy Q C f mu hα.le hCQ hCmass
    (fun x hx => (Finset.mem_filter.mp (hCB hx)).2)

end LeanProofs.GowersSzemeredi
