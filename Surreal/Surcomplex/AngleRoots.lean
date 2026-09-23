import Surreal.Surcomplex.FiniteFourier

/-!
# Roots of actual unit directions

The roots and torsion clauses of `trigonometry:cor:representatives` follow
from the actual finite phase and Mathlib's primitive-root theory. The
classification applies to roots anywhere in the actual surcomplex field.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Every actual root of unity is an embedded ordinary complex root, and conversely. -/
theorem pow_eq_one_iff_exists_complex (n : ℕ) (hn : 0 < n) (z : Surcomplex.{u}) :
    z ^ n = 1 ↔ ∃ c : ℂ, c ^ n = 1 ∧ ofComplex c = z := by
  constructor
  · intro hz
    letI : NeZero n := ⟨hn.ne'⟩
    obtain ⟨k, _, hk⟩ := (FiniteFourier.isPrimitiveRoot_zeta.{u} hn).eq_pow_of_pow_eq_one hz
    rw [FiniteFourier.zeta_eq_ofComplex, ← map_pow] at hk
    refine ⟨Complex.exp (2 * Real.pi * Complex.I / n) ^ k, ?_, hk⟩
    apply ofComplex_injective
    rw [map_pow, map_one, hk, hz]
  · rintro ⟨c, hc, rfl⟩
    rw [← map_pow, hc, map_one]

/-- No nontrivial root of unity is infinitesimally close to one. -/
theorem eq_one_of_pow_eq_one_of_infinitesimal (n : ℕ) (hn : 0 < n)
    (z : Surcomplex.{u}) (hz : IsInfinitesimal (z - 1)) (hp : z ^ n = 1) : z = 1 := by
  obtain ⟨c, _, rfl⟩ := (pow_eq_one_iff_exists_complex n hn z).mp hp
  have hs := (standardPart_eq_zero_iff (finite_of_infinitesimal hz)).mpr hz
  have hc : c = 1 := by
    apply sub_eq_zero.mp
    simpa only [← map_one ofComplex, ← map_sub, standardPart_ofComplex] using hs
  rw [hc, map_one]

/-- The `k`th divided angle, with its ordinary full-turn correction. -/
def finiteRootAngle (θ : SignSequence.FiniteElement.{u}) (n k : ℕ) :
    SignSequence.FiniteElement.{u} :=
  SignSequence.finiteOfReal ((n : ℝ)⁻¹) *
    (θ + SignSequence.finiteOfReal ((k : ℝ) * (2 * Real.pi)))

/-- The divided angle has exactly the source's field-valued quotient. -/
theorem val_finiteRootAngle (θ : SignSequence.FiniteElement.{u}) (n k : ℕ) :
    (finiteRootAngle θ n k).val =
      (θ.val + SignSequence.ofReal ((k : ℝ) * (2 * Real.pi))) / n := by
  change SignSequence.ofReal ((n : ℝ)⁻¹) *
    (θ.val + SignSequence.ofReal ((k : ℝ) * (2 * Real.pi))) = _
  rw [map_inv₀, map_natCast, div_eq_mul_inv, mul_comm]

private theorem finiteRootAngle_eq_add (θ : SignSequence.FiniteElement.{u}) (n k : ℕ) :
    finiteRootAngle θ n k = finiteRootAngle θ n 0 +
      k • SignSequence.finiteOfReal (2 * Real.pi / n) := by
  rw [nsmul_eq_mul, ← map_natCast SignSequence.finiteOfReal k]
  apply ArchimedeanClass.FiniteElement.ext
  simp only [finiteRootAngle, ArchimedeanClass.FiniteElement.val_add,
    ArchimedeanClass.FiniteElement.val_mul, SignSequence.finiteOfReal_val,
    map_inv₀, map_mul, map_div₀, map_natCast, Nat.cast_zero, zero_mul, map_zero, add_zero]
  ring

/-- Raising the zeroth divided phase to the prescribed positive power recovers the direction. -/
theorem finitePhase_rootAngle_zero_pow (θ : SignSequence.FiniteElement.{u})
    (n : ℕ) (hn : 0 < n) : finitePhase (finiteRootAngle θ n 0) ^ n = finitePhase θ := by
  rw [← finitePhase_nsmul]
  congr 1
  rw [nsmul_eq_mul]
  apply ArchimedeanClass.FiniteElement.ext
  change (n : SignSequence.{u}) * (finiteRootAngle θ n 0).val = θ.val
  rw [val_finiteRootAngle]
  have hn' : (n : SignSequence.{u}) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [Nat.cast_zero, zero_mul, map_zero, add_zero]
  field_simp

/-- The divided phases are one root times the ordinary roots of unity. -/
theorem finitePhase_rootAngle (θ : SignSequence.FiniteElement.{u}) (n k : ℕ) :
    finitePhase (finiteRootAngle θ n k) =
      finitePhase (finiteRootAngle θ n 0) * FiniteFourier.zeta n ^ k := by
  rw [finiteRootAngle_eq_add, finitePhase_add, finitePhase_nsmul]
  rfl

/-- Every listed divided phase is a root of the original direction. -/
theorem finitePhase_rootAngle_pow (θ : SignSequence.FiniteElement.{u}) (n : ℕ)
    (hn : 0 < n) (k : ℕ) : finitePhase (finiteRootAngle θ n k) ^ n = finitePhase θ := by
  rw [finitePhase_rootAngle, mul_pow, finitePhase_rootAngle_zero_pow θ n hn]
  have hz := (FiniteFourier.isPrimitiveRoot_zeta.{u} hn).pow_eq_one
  rw [← pow_mul, Nat.mul_comm k n, pow_mul, hz, one_pow, mul_one]

/-- The listed `n` phases are distinct. -/
theorem finitePhase_rootAngle_injective (θ : SignSequence.FiniteElement.{u})
    (n : ℕ) (hn : 0 < n) :
    Function.Injective (fun k : Fin n => finitePhase (finiteRootAngle θ n k.val)) := by
  intro k l h
  dsimp only at h
  rw [finitePhase_rootAngle θ n k.val, finitePhase_rootAngle θ n l.val] at h
  have hb : finitePhase (finiteRootAngle θ n 0) ≠ 0 := finiteExp_ne_zero _
  apply Fin.ext
  exact (FiniteFourier.isPrimitiveRoot_zeta hn).pow_inj k.isLt l.isLt (mul_left_cancel₀ hb h)

/-- All roots in the actual surcomplex field are exactly the listed divided phases. -/
theorem pow_eq_finitePhase_iff (θ : SignSequence.FiniteElement.{u}) (n : ℕ)
    (hn : 0 < n) (z : Surcomplex.{u}) :
    z ^ n = finitePhase θ ↔ ∃ k : Fin n, z = finitePhase (finiteRootAngle θ n k.val) := by
  constructor
  · intro hz
    letI : NeZero n := ⟨hn.ne'⟩
    have hb : finitePhase (finiteRootAngle θ n 0) ≠ 0 := finiteExp_ne_zero _
    have ht : finitePhase θ ≠ 0 := finiteExp_ne_zero _
    have hq : (z / finitePhase (finiteRootAngle θ n 0)) ^ n = 1 := by
      rw [div_pow, hz, finitePhase_rootAngle_zero_pow θ n hn, div_self ht]
    obtain ⟨k, hk, he⟩ := (FiniteFourier.isPrimitiveRoot_zeta hn).eq_pow_of_pow_eq_one hq
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [finitePhase_rootAngle]
    have h := (div_eq_iff hb).mp he.symm
    simpa only [mul_comm] using h
  · rintro ⟨k, rfl⟩
    exact finitePhase_rootAngle_pow θ n hn k.val

/-- The root set is in explicit bijection with `Fin n`. -/
def finitePhaseRootsEquiv (θ : SignSequence.FiniteElement.{u}) (n : ℕ) (hn : 0 < n) :
    Fin n ≃ {z : Surcomplex.{u} // z ^ n = finitePhase θ} :=
  Equiv.ofBijective
    (fun k => ⟨finitePhase (finiteRootAngle θ n k.val), finitePhase_rootAngle_pow θ n hn k.val⟩)
    ⟨fun k l h => finitePhase_rootAngle_injective θ n hn (congrArg Subtype.val h), by
      intro z
      obtain ⟨k, hk⟩ := (pow_eq_finitePhase_iff θ n hn z.val).mp z.property
      exact ⟨k, Subtype.ext hk.symm⟩⟩

/-- The unit-direction equation has exactly `n` roots. -/
theorem card_roots_finitePhase (θ : SignSequence.FiniteElement.{u}) (n : ℕ) (hn : 0 < n) :
    Nat.card {z : Surcomplex.{u} // z ^ n = finitePhase θ} = n := by
  rw [← Nat.card_congr (finitePhaseRootsEquiv θ n hn), Nat.card_fin]

end
end Surreal.Surcomplex
