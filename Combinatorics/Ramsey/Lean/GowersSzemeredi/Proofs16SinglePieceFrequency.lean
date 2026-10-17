import GowersSzemeredi.Proofs16SinglePieceLift
import GowersSzemeredi.Proofs16FrequencySelection
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fin.Tuple.Finset

/-! The single-piece lift, step 6 (Notes L.1): a dense multilinear frequency
box from local inputs only.

**Warning.** Its inputs include the box-local `LocalRelationCoverAt` and
`LocalMultilinearPieceAt`, false for growing widths (Notes L.2), so this
statement is vacuous. The global-to-local replacement goes through
`single_piece_lift_core`.

`single_piece_frequency_box` is a conditional replacement for
`section16_joint_frequency_box`. Take `f` that is not uniform of degree
`k + 2`. Then some proper box `P ⊆ (ℤ/N)^(k+1)` and one multilinear `μ` have
`ρ·|P|` points `y` at which `μ y` is a large Fourier frequency of the
iterated difference.
- `section16_joint_frequency_box` needs the cover-form `Theorem162At l` for
  `l ≤ k`, and its density is `exp(−poly)` (Notes K.4).
- Here `ρ = singlePieceDensity c (spectrumPieceRho c_R ρ₁) 1` is polynomial
  in `α` whenever the local inputs are.

The chain:
1. `section16_large_frequency_graph`: the frequency graph `(B, φ)` with the
   product property at `α/2`.
2. Lemma 15.6 with its explicit threshold
   (`lemma_15_6_of_density_lower_all_explicit`, `β = γ = α/2`). Its
   arrangement parameter `(βγ/2)^E` is exactly
   `section16ThetaOne α (α/2) k`, and Lemma 16.4's dichotomy is not needed.
3. `single_piece_lift`, with vertex providers from the lower-dimensional
   inputs (`vertex_providers_of_low`).
4. The agreement points are large frequencies.

The output feeds `polynomial_localization_of_dense_frequency_box`
unchanged.

`single_piece_frequency_box` is in `Proofs16SinglePieceFrequencySide`, outside
the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem two_inv_pow_44_eq_rpow : (2 : Real)⁻¹ ^ 44 = (2 : Real) ^ (-(44 : Real)) := by
  rw [Real.rpow_neg (by norm_num), inv_pow]
  congr 1
  exact_mod_cast (Real.rpow_natCast (2 : Real) 44).symm

end LeanProofs.GowersSzemeredi
