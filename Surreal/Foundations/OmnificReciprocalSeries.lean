import Surreal.Foundations.OmnificSupportBounds
import Surreal.Foundations.SmallNormalFormUnion

/-!
# The purely infinite series with reciprocal natural exponents

Constructs the actual series sum_{n>=1} omega^(1/n) from
`odg:def:ex:certificates`. Its canonical coefficients, lower-universe
support smallness, reverse well-ordering, and zero constant term are
proved explicitly.
-/

universe u
namespace Surreal.Foundations.SignSequence

open SmallNormalForm
open scoped Classical

noncomputable section

/-- The positive exponents 1, 1/2, 1/3, ... indexed from zero. -/
def reciprocalExponent (n : ℕ) : SignSequence.{u} := ((n + 1 : ℕ) : SignSequence.{u})⁻¹

theorem reciprocalExponent_pos (n : ℕ) : 0 < reciprocalExponent.{u} n := by
  unfold reciprocalExponent
  positivity

theorem reciprocalExponent_strictAnti : StrictAnti reciprocalExponent.{u} := by
  intro m n hmn
  apply (inv_lt_inv₀ (by positivity) (by positivity)).mpr
  exact_mod_cast Nat.succ_lt_succ hmn

/-- The coefficient function for the printed reciprocal-exponent normal form. -/
def reciprocalSeriesCoeff (a : SignSequence.{u}) : ℝ :=
  if a ∈ Set.range reciprocalExponent then 1 else 0

theorem support_reciprocalSeriesCoeff :
    Function.support reciprocalSeriesCoeff.{u} = Set.range reciprocalExponent := by
  ext a
  simp [Function.mem_support, reciprocalSeriesCoeff]

theorem reciprocalSeriesCoeff_small : Small.{u} (Function.support reciprocalSeriesCoeff.{u}) := by
  rw [support_reciprocalSeriesCoeff]
  infer_instance

theorem reciprocalSeriesCoeff_wellFounded :
    (Function.support reciprocalSeriesCoeff.{u}).WellFoundedOn (· > ·) := by
  rw [support_reciprocalSeriesCoeff]
  have hp : (Set.range fun n => OrderDual.toDual (reciprocalExponent.{u} n)).IsPWO := by
    rw [← Set.image_univ]
    exact (Set.isPWO_of_wellQuasiOrderedLE _).image_of_monotone reciprocalExponent_strictAnti.antitone
  exact hp.isWF

/-- The small, reverse-well-ordered normal form of the infinite example. -/
def reciprocalOmegaNormalForm : SmallNormalForm.{u} :=
  fromCoefficients reciprocalSeriesCoeff reciprocalSeriesCoeff_small reciprocalSeriesCoeff_wellFounded

/-- The actual surreal represented by the displayed infinite normal form. -/
def reciprocalOmegaSeries : SignSequence.{u} := cutEvaluation reciprocalOmegaNormalForm

@[simp] theorem normalForm_reciprocalOmegaSeries :
    normalForm reciprocalOmegaSeries.{u} = reciprocalOmegaNormalForm := normalForm_cutEvaluation _

/-- Every coefficient is specified, including those outside the displayed exponent sequence. -/
theorem coeff_reciprocalOmegaSeries (a : SignSequence.{u}) :
    coeff (normalForm reciprocalOmegaSeries) a = if a ∈ Set.range reciprocalExponent then 1 else 0 := by
  rw [normalForm_reciprocalOmegaSeries]
  exact coeff_fromCoefficients _ _ _ a

theorem support_reciprocalOmegaSeries :
    support (normalForm reciprocalOmegaSeries.{u}) = Set.range reciprocalExponent := by
  rw [normalForm_reciprocalOmegaSeries, reciprocalOmegaNormalForm, support_fromCoefficients,
    support_reciprocalSeriesCoeff]

theorem reciprocalOmegaSeries_support_pos (a : SignSequence.{u})
    (ha : a ∈ support (normalForm reciprocalOmegaSeries)) : 0 < a := by
  rw [support_reciprocalOmegaSeries] at ha
  obtain ⟨n, rfl⟩ := ha
  exact reciprocalExponent_pos n

/-- All displayed terms have coefficient one, so the actual series is nonzero. -/
theorem reciprocalOmegaSeries_ne_zero : reciprocalOmegaSeries.{u} ≠ 0 := by
  intro hz
  have hc := coeff_reciprocalOmegaSeries (reciprocalExponent.{u} 0)
  simp [hz] at hc

/-- This is a genuinely infinite normal form, not a finite polynomial expression. -/
theorem reciprocalOmegaSeries_support_infinite :
    (support (normalForm reciprocalOmegaSeries.{u})).Infinite := by
  rw [support_reciprocalOmegaSeries]
  exact Set.infinite_range_of_injective reciprocalExponent_strictAnti.injective

/-- The infinite example belongs to the actual omnific ring. -/
def reciprocalOmegaOmnific : OmnificInteger.{u} :=
  (exists_purelyInfinite_of_support_pos reciprocalOmegaSeries reciprocalOmegaSeries_support_pos).choose

theorem reciprocalOmegaOmnific_purelyInfinite :
    reciprocalOmegaOmnific.{u} ∈ omnificPurelyInfiniteIdeal :=
  (exists_purelyInfinite_of_support_pos reciprocalOmegaSeries
    reciprocalOmegaSeries_support_pos).choose_spec.1

@[simp] theorem reciprocalOmegaOmnific_val :
    omnificToSurreal reciprocalOmegaOmnific.{u} = reciprocalOmegaSeries :=
  (exists_purelyInfinite_of_support_pos reciprocalOmegaSeries
    reciprocalOmegaSeries_support_pos).choose_spec.2

theorem reciprocalOmegaOmnific_ne_zero : reciprocalOmegaOmnific.{u} ≠ 0 := by
  intro hz
  apply reciprocalOmegaSeries_ne_zero
  rw [← reciprocalOmegaOmnific_val, hz, map_zero]

end
end Surreal.Foundations.SignSequence
