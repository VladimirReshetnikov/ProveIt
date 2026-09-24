import Surreal.Surcomplex.AngleRoots
import Surreal.Foundations.SignSequencePositiveRoots

/-!
# Polar root formulas and regular polygon side lengths

This completes the radius and chord clauses of `trigonometry:cor:representatives`.
Positive radii have unique positive roots at every actual scale; the complete
root list then follows from the finite-angle root classification.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The complete root formula for a positive radius times a finite phase. -/
theorem pow_eq_polar_iff (ρ : SignSequence.{u}) (hρ : 0 < ρ)
    (θ : SignSequence.FiniteElement.{u}) (n : ℕ) (hn : 0 < n) (z : Surcomplex.{u}) :
    z ^ n = ofReal ρ * finitePhase θ ↔ ∃ k : Fin n,
      z = ofReal (SignSequence.positiveNthRoot ρ hρ n hn) *
        finitePhase (finiteRootAngle θ n k.val) := by
  let R := SignSequence.positiveNthRoot ρ hρ n hn
  have hR : R ^ n = ρ := SignSequence.positiveNthRoot_pow ρ hρ n hn
  have hR0 : ofReal R ≠ (0 : Surcomplex.{u}) :=
    (map_ne_zero ofReal).mpr (SignSequence.positiveNthRoot_pos ρ hρ n hn).ne'
  have hρ0 : ofReal ρ ≠ (0 : Surcomplex.{u}) := (map_ne_zero ofReal).mpr hρ.ne'
  constructor
  · intro hz
    have hq : (z / ofReal R) ^ n = finitePhase θ := by
      rw [div_pow, ← map_pow, hR, hz, mul_div_cancel_left₀ _ hρ0]
    obtain ⟨k, hk⟩ := (pow_eq_finitePhase_iff θ n hn (z / ofReal R)).mp hq
    refine ⟨k, ?_⟩
    simpa only [mul_comm] using (div_eq_iff hR0).mp hk
  · rintro ⟨k, rfl⟩
    rw [mul_pow, ← map_pow, SignSequence.positiveNthRoot_pow,
      finitePhase_rootAngle_pow θ n hn k.val]

/-- Every nonzero polar equation has exactly the explicitly indexed `n` roots. -/
def polarRootsEquiv (ρ : SignSequence.{u}) (hρ : 0 < ρ)
    (θ : SignSequence.FiniteElement.{u}) (n : ℕ) (hn : 0 < n) :
    Fin n ≃ {z : Surcomplex.{u} // z ^ n = ofReal ρ * finitePhase θ} :=
  Equiv.ofBijective
    (fun k => ⟨ofReal (SignSequence.positiveNthRoot ρ hρ n hn) *
      finitePhase (finiteRootAngle θ n k.val), (pow_eq_polar_iff ρ hρ θ n hn _).mpr ⟨k, rfl⟩⟩)
    ⟨by
      intro k l h
      have hR0 : ofReal (SignSequence.positiveNthRoot ρ hρ n hn) ≠ (0 : Surcomplex.{u}) :=
        (map_ne_zero ofReal).mpr (SignSequence.positiveNthRoot_pos ρ hρ n hn).ne'
      apply finitePhase_rootAngle_injective θ n hn
      exact mul_left_cancel₀ hR0 (congrArg Subtype.val h), by
      intro z
      obtain ⟨k, hk⟩ := (pow_eq_polar_iff ρ hρ θ n hn z.val).mp z.property
      exact ⟨k, Subtype.ext hk.symm⟩⟩

/-- Every nonzero actual surcomplex has exactly `n` distinct roots of positive degree. -/
theorem card_roots_of_ne_zero (w : Surcomplex.{u}) (hw : w ≠ 0) (n : ℕ) (hn : 0 < n) :
    Nat.card {z : Surcomplex.{u} // z ^ n = w} = n := by
  obtain ⟨θ, hθ⟩ := exists_polar w hw
  have h := Nat.card_congr (polarRootsEquiv (modulus w) (modulus_pos hw) θ n hn)
  rw [Nat.card_fin, ← hθ] at h
  exact h.symm

/-- The ordinary unit root has the expected sine chord length in the actual field. -/
theorem modulus_zeta_sub_one (n : ℕ) (hn : 3 ≤ n) :
    modulus (FiniteFourier.zeta.{u} n - 1) =
      2 * finiteSin (SignSequence.finiteOfReal (Real.pi / n)) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hs : 0 < Real.sin (Real.pi / n) := Real.sin_pos_of_pos_of_lt_pi
    (div_pos Real.pi_pos (by linarith)) (div_lt_self Real.pi_pos hn1)
  have he : FiniteFourier.zeta.{u} n =
      ofComplex (Complex.exp (Complex.I * ((2 * Real.pi / n : ℝ) : ℂ))) := by
    rw [FiniteFourier.zeta_eq_ofComplex]
    congr 2
    push_cast
    ring
  rw [he, ← map_one ofComplex, ← map_sub, modulus_ofComplex,
    Complex.norm_exp_I_mul_ofReal_sub_one,
    show (2 * Real.pi / n) / 2 = Real.pi / n by ring, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num) hs), map_mul, map_ofNat, finiteSin_constant]

/-- Consecutive vertices of a translated and rotated regular polygon have the stated side length. -/
theorem regularPolygon_side_length (c u : Surcomplex.{u}) (hu : modulus u = 1)
    (ρ : SignSequence.{u}) (hρ : 0 < ρ) (n : ℕ) (hn : 3 ≤ n) (k : ℕ) :
    modulus ((c + ofReal ρ * u * FiniteFourier.zeta n ^ (k + 1)) -
      (c + ofReal ρ * u * FiniteFourier.zeta n ^ k)) =
      2 * ρ * finiteSin (SignSequence.finiteOfReal (Real.pi / n)) := by
  have he : (c + ofReal ρ * u * FiniteFourier.zeta n ^ (k + 1)) -
      (c + ofReal ρ * u * FiniteFourier.zeta n ^ k) =
      (ofReal ρ * u * FiniteFourier.zeta n ^ k) * (FiniteFourier.zeta n - 1) := by
    rw [pow_succ]
    ring
  rw [he, modulus_mul, modulus_mul, modulus_mul, modulus_ofReal, abs_of_pos hρ, hu]
  have hp : modulus (FiniteFourier.zeta.{u} n ^ k) = 1 := by
    change modulusMonoidWithZeroHom (FiniteFourier.zeta n ^ k) = 1
    rw [map_pow]
    change modulus (FiniteFourier.zeta n) ^ k = 1
    rw [FiniteFourier.modulus_zeta, one_pow]
  rw [hp, modulus_zeta_sub_one n hn]
  ring

end
end Surreal.Surcomplex
