import IntegerPoints.GKSec33BoundaryContradiction
import IntegerPoints.GKSec33SqrtExponentBound
import IntegerPoints.GKSec33SqrtBProcess
import IntegerPoints.GKSec33SqrtDualLower

/-!
# Graham--Kolesnik section 3.3: the square-root boundary case

This module completes the final coordinate restriction on exponent pairs.
For the phase `2 t sqrt x`, the exponent-pair hypothesis supplies an upper
bound for the original sum, Lemma 3.6 supplies its exact dual transform with
a controlled error, and a factorial choice of `t` makes every term of that
dual sum point in the same direction.  The abstract diagonal argument then
forces `k = 1 / 2` when the second coordinate is `1 / 2`.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace GKSec33

/-- The original square-root exponential sum at the perfect-square scales
used throughout the boundary argument. -/
noncomputable def sqrtBOriginal (Q R : ℕ) : ℂ :=
  ∑ n ∈ intRange (sqrtBN R) (2 * sqrtBN R),
    e (2 * sqrtBT Q R * Real.sqrt n)

/-- The smooth extension and the literal square-root phase give the same
sum at the square scales. -/
theorem sqrtPhase_sum_eq_sqrtBOriginal (Q R : ℕ) (hR : 0 < R) :
    (∑ n ∈ intRange (sqrtBN R) (2 * sqrtBN R),
      e (sqrtPhase (sqrtBT Q R) n)) = sqrtBOriginal Q R := by
  have h := sqrtPhase_sum_eq_sqrt_sum (R ^ 2) (sqrtBT Q R) (pow_pos hR 2)
  simpa only [sqrtBOriginal, sqrtBN, Nat.cast_pow] using h

end GKSec33

/-- **Graham--Kolesnik, section 3.3**: if `(k, 1 / 2)` is an exponent pair,
then its first coordinate is also `1 / 2`.  This is the square-root phase,
Lemma-3.6, and factorial-resonance argument from the book. -/
theorem gk_sec33_k_eq_half_of_l_eq_half_holds :
    gk_sec33_k_eq_half_of_l_eq_half := by
  intro k hpair
  obtain ⟨A, hA, hupperRaw⟩ := GKSec33.exists_sqrt_exponent_bound hpair
  obtain ⟨B, hB, herrorRaw⟩ := GKSec33.exists_sqrtBProcess_bound
  let S : ℕ → ℕ → ℂ := GKSec33.sqrtBOriginal
  let D : ℕ → ℕ → ℂ := GKSec33.sqrtBDualMain
  have hupper : ∀ (Q R : ℕ), 0 < Q → 0 < R →
      ‖S Q R‖ ≤
        A * ((R : ℝ) * ((Q : ℝ) ^ 2) ^ k + ((Q : ℝ) ^ 2)⁻¹) := by
    intro Q R hQ hR
    have h := hupperRaw Q R hQ hR
    simpa only [S, GKSec33.sqrtBOriginal, GKSec33.sqrtBN,
      GKSec33.sqrtBT, GKSec33.sqrtBH, Nat.cast_pow] using h
  have herror : ∀ (Q R : ℕ), 0 < Q → 0 < R →
      ‖S Q R - D Q R‖ ≤
        B * (Real.log ((Q : ℝ) ^ 2 + 2) + (R : ℝ) / (Q : ℝ)) := by
    intro Q R hQ hR
    have h := herrorRaw Q R hQ hR
    rw [GKSec33.sqrtPhase_sum_eq_sqrtBOriginal Q R hR] at h
    simpa only [S, D, GKSec33.sqrtBH] using h
  have hlower : ∀ (Q M : ℕ), 0 < Q → 0 < M →
      let H : ℕ := Q ^ 2
      let R : ℕ := M * H.factorial
      (R : ℝ) * (Q : ℝ) / 4 ≤ ‖D Q R‖ := by
    intro Q M hQ hM
    dsimp only
    simpa only [D, GKSec33.sqrtDualR, GKSec33.sqrtDualH] using
      GKSec33.sqrtBDualMain_norm_ge Q M hQ hM
  exact GKSec33.k_eq_half_of_sqrt_bounds S D hpair.2.1 hA hB
    hupper herror hlower

end LeanProofs.IntegerPoints
