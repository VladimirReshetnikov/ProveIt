import Surreal.Surcomplex.PolarNormalization
import Surreal.Surcomplex.TrigonometricOrder

/-!
# Actual interval representatives of finite surreal angles

The representative clauses of `trigonometry:cor:representatives` use actual
surreal inequalities, including infinitesimal corrections at the endpoints.
The upper semicircle is characterized by the already proved strict sine signs.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

/-- A nonnegative full-turn representative lies in the actual interval `[0, 2*pi)`. -/
def IsNonnegativeAngle (θ : SignSequence.FiniteElement.{u}) : Prop :=
  0 ≤ θ.val ∧ θ.val < SignSequence.ofReal (2 * Real.pi)

private theorem principal_pi_sub_iff (θ : SignSequence.FiniteElement.{u}) :
    IsPrincipalAngle (SignSequence.finiteOfReal Real.pi - θ) ↔ IsNonnegativeAngle θ := by
  change (-SignSequence.ofReal Real.pi < SignSequence.ofReal Real.pi - θ.val ∧
    SignSequence.ofReal Real.pi - θ.val ≤ SignSequence.ofReal Real.pi) ↔ _
  simp only [IsNonnegativeAngle, map_mul, map_ofNat]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Two full-turn representatives differing by an ordinary period coincide. -/
theorem nonnegativeAngle_eq_of_period {θ φ : SignSequence.FiniteElement.{u}}
    (hθ : IsNonnegativeAngle θ) (hφ : IsNonnegativeAngle φ)
    (hp : ∃ n : ℤ, θ.val - φ.val = SignSequence.ofReal ((n : ℝ) * (2 * Real.pi))) :
    θ = φ := by
  have he : SignSequence.finiteOfReal Real.pi - θ = SignSequence.finiteOfReal Real.pi - φ := by
    apply principalAngle_eq_of_period ((principal_pi_sub_iff θ).mpr hθ)
      ((principal_pi_sub_iff φ).mpr hφ)
    obtain ⟨n, hn⟩ := hp
    refine ⟨-n, ?_⟩
    change (SignSequence.ofReal Real.pi - θ.val) -
      (SignSequence.ofReal Real.pi - φ.val) = _
    rw [Int.cast_neg, neg_mul, map_neg, ← hn]
    abel
  exact sub_right_injective he

/-- Every finite angle has exactly one ordinary-period translate in `[0, 2*pi)`. -/
theorem existsUnique_nonnegativeAngle_period (θ : SignSequence.FiniteElement.{u}) :
    ∃! φ : SignSequence.FiniteElement.{u}, IsNonnegativeAngle φ ∧
      ∃ n : ℤ, θ.val - φ.val = SignSequence.ofReal ((n : ℝ) * (2 * Real.pi)) := by
  obtain ⟨ψ, ⟨hψ, n, hn⟩, _⟩ :=
    existsUnique_principalAngle_period (SignSequence.finiteOfReal Real.pi - θ)
  let φ := SignSequence.finiteOfReal Real.pi - ψ
  have hφ : IsNonnegativeAngle φ := by
    apply (principal_pi_sub_iff φ).mp
    simpa only [φ, sub_sub_cancel] using hψ
  have he : finitePhase θ = finitePhase φ := by
    apply (finitePhase_eq_iff θ φ).mpr
    refine ⟨-n, ?_⟩
    change θ.val - (SignSequence.ofReal Real.pi - ψ.val) = _
    rw [Int.cast_neg, neg_mul, map_neg, ← hn]
    change θ.val - (SignSequence.ofReal Real.pi - ψ.val) =
      -((SignSequence.ofReal Real.pi - θ.val) - ψ.val)
    abel
  refine ⟨φ, ⟨hφ, (finitePhase_eq_iff θ φ).mp he⟩, ?_⟩
  intro χ hχ
  apply nonnegativeAngle_eq_of_period hχ.1 hφ
  apply (finitePhase_eq_iff χ φ).mp
  exact ((finitePhase_eq_iff θ χ).mpr hχ.2).symm.trans he

/-- Every actual direction has a unique full-turn interval representative. -/
theorem existsUnique_nonnegative_phase (z : Surcomplex.{u}) (hz : modulus z = 1) :
    ∃! θ : SignSequence.FiniteElement.{u}, IsNonnegativeAngle θ ∧ finitePhase θ = z := by
  obtain ⟨φ, hφ⟩ := exists_finitePhase_eq_of_modulus_eq_one z hz
  obtain ⟨θ, ⟨hθ, hp⟩, _⟩ := existsUnique_nonnegativeAngle_period φ
  have he := ((finitePhase_eq_iff φ θ).mpr hp).symm.trans hφ
  refine ⟨θ, ⟨hθ, he⟩, ?_⟩
  intro ψ hψ
  exact nonnegativeAngle_eq_of_period hψ.1 hθ ((finitePhase_eq_iff ψ θ).mp (hψ.2.trans he.symm))

/-- Every actual direction also has a unique representative in `(-pi, pi]`. -/
theorem existsUnique_principal_phase (z : Surcomplex.{u}) (hz : modulus z = 1) :
    ∃! θ : SignSequence.FiniteElement.{u}, IsPrincipalAngle θ ∧ finitePhase θ = z := by
  have hn : z ≠ 0 := by intro h; exact zero_ne_one (by simpa only [h, modulus_zero] using hz)
  obtain ⟨θ, hθ, hu⟩ := existsUnique_principal_polar z hn
  simp only [hz, map_one, one_mul] at hθ hu
  exact ⟨θ, ⟨hθ.1, hθ.2.symm⟩, fun ψ hψ => hu ψ ⟨hψ.1, hψ.2.symm⟩⟩

/-- On the full-turn interval, positive imaginary coordinate is exactly the upper open semicircle. -/
theorem finiteSin_pos_iff_of_nonnegativeAngle (θ : SignSequence.FiniteElement.{u})
    (hθ : IsNonnegativeAngle θ) :
    0 < finiteSin θ ↔ θ.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) := by
  constructor
  · intro hs
    have hzero : θ.val ≠ 0 := by
      intro he
      have ht : θ = 0 := ArchimedeanClass.FiniteElement.ext he
      simp only [ht, finiteSin_zero, lt_self_iff_false] at hs
    refine ⟨lt_of_le_of_ne hθ.1 hzero.symm, ?_⟩
    by_contra h
    have hge := le_of_not_gt h
    rcases hge.eq_or_lt with he | he
    · have ht : θ = SignSequence.finiteOfReal Real.pi := ArchimedeanClass.FiniteElement.ext he.symm
      simp only [ht, finiteSin_constant, Real.sin_pi, map_zero, lt_self_iff_false] at hs
    · exact (finiteSin_neg_of_mem_Ioo θ ⟨he, hθ.2⟩).not_gt hs
  · exact finiteSin_pos_of_mem_Ioo θ

/-- A negative positive-infinitesimal angle is represented by the actual value `2*pi - epsilon`. -/
theorem negative_infinitesimal_full_turn (ε : SignSequence.FiniteElement.{u})
    (hε : SignSequence.IsInfinitesimal ε.val) (hpos : 0 < ε.val) :
    IsNonnegativeAngle (SignSequence.finiteOfReal (2 * Real.pi) - ε) ∧
      finitePhase (SignSequence.finiteOfReal (2 * Real.pi) - ε) = finitePhase (-ε) := by
  have hlt := (SignSequence.isInfinitesimal_iff_forall_real_abs_lt ε.val).mp hε
    (2 * Real.pi) Real.two_pi_pos
  rw [abs_of_pos hpos] at hlt
  constructor
  · change 0 ≤ SignSequence.ofReal (2 * Real.pi) - ε.val ∧
      SignSequence.ofReal (2 * Real.pi) - ε.val < SignSequence.ofReal (2 * Real.pi)
    constructor <;> linarith
  · apply (finitePhase_eq_iff _ _).mpr
    refine ⟨1, ?_⟩
    change SignSequence.ofReal (2 * Real.pi) - ε.val - -ε.val = _
    simp

end Surreal.Surcomplex
