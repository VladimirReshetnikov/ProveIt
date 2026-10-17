import GowersSzemeredi.Proofs16OddDenseBox
import GowersSzemeredi.Proofs17LocalizedPhaseRemoval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Dense large Fourier frequencies on an arbitrary-dimensional box give
the second-moment input to polynomial localization.

`section16ShortBoxDensity_pos`, `section16ShortBoxExponent`,
`section16ShortBoxExponent_pos` and `short_odd_multilinear_fourier_box` are in
`Proofs17MultilinearBoxEnergySide`, outside the final route. -/
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

/-- The density retained after making every side short, equal, and odd. -/
def section16ShortBoxDensity (alpha : Real) (k : Nat) : Real :=
  section16CorollaryExponent alpha k / (2 : Real) ^ k

end LeanProofs.GowersSzemeredi
