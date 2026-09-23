import Surreal.Surcomplex.OmnificDegree
import Surreal.Surcomplex.StrongSummation
import Surreal.Surcomplex.HahnLeading

/-!
# The degree is the largest actual normal-form exponent

The explicit coefficient bridge for `odg:lem:degree`: the native degree
and leading coefficient agree with the actual full complex normal form.
Each proof descends the single element to a proved small Hahn workspace;
no fixed workspace is assumed to contain all surcomplex numbers.
-/

universe u v
namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The ordinary complex coefficient at an actual Conway growth exponent. -/
def growthCoeff (z : Surcomplex.{u}) (a : SignSequence.{u}) : ℂ :=
  (rawNormalForm z).coeff (OrderDual.toDual (SignSequence.toSurreal a))


/-- On the real axis, complex normal-form coefficients are the original real coefficients. -/
@[simp] theorem growthCoeff_ofReal (x a : SignSequence.{u}) :
    growthCoeff (ofReal x) a = (SmallNormalForm.coeff (SmallNormalForm.normalForm x) a : ℂ) := by
  rw [growthCoeff, coeff_rawNormalForm]
  apply Complex.ext
  · rfl
  · change SmallNormalForm.coeff (SmallNormalForm.normalForm (0 : SignSequence.{u})) a = 0
    simp

section Workspace

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Small.{u} Γ]

/-- Native Hahn coefficients are retained at the corresponding actual growth exponents. -/
theorem growthCoeff_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F : _root_.HahnSeries Γ ℂ) (a : Γ) :
    growthCoeff (hahnEmbedding e he F) (-e a) = F.coeff a := by
  rw [growthCoeff, rawNormalForm_hahnEmbedding, SignSequence.toSurreal_neg]
  exact HahnSeries.workspaceEmbedding_coeff (SmallNormalForm.hahnGrowthMap e)
    (SmallNormalForm.hahnGrowthMap_strictMono e he) F a

/-- Every nonzero coefficient in an actual workspace image is below its leading growth exponent. -/
theorem growthCoeff_leading_bound_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F : _root_.HahnSeries Γ ℂ) (a : SignSequence.{u})
    (ha : growthCoeff (hahnEmbedding e he F) a ≠ 0) : a ≤ leadingExponent (hahnEmbedding e he F) := by
  have hr : OrderDual.toDual (SignSequence.toSurreal a) ∈ Set.range (SmallNormalForm.hahnGrowthMap e) := by
    by_contra hn
    apply ha
    rw [growthCoeff, rawNormalForm_hahnEmbedding]
    exact HahnSeries.workspaceEmbedding_coeff_of_not_mem_range (SmallNormalForm.hahnGrowthMap e)
      (SmallNormalForm.hahnGrowthMap_strictMono e he) F hn
  obtain ⟨b, hb⟩ := hr
  have hab : -e b = a := by
    apply (SignSequence.toSurreal_inj _ _).mp
    rw [SignSequence.toSurreal_neg]
    exact congrArg OrderDual.ofDual hb
  rw [← hab, growthCoeff_hahnEmbedding] at ha
  rw [← hab, leadingExponent_hahnEmbedding]
  exact neg_le_neg (he.monotone (_root_.HahnSeries.order_le_of_coeff_ne_zero ha))

end Workspace

/-- The actual leading coefficient is literally the coefficient at the actual leading exponent. -/
theorem growthCoeff_leadingExponent (z : Surcomplex.{u}) :
    growthCoeff z (leadingExponent z) = leadingCoeff z := by
  obtain ⟨F, hF⟩ := coeff_mem_range_polynomialWorkspaceEmbedding (Polynomial.C z) 0
  have he : hahnEmbedding ((polynomialWorkspaceExponents (Polynomial.C z)).subtype.toAddMonoidHom)
      (fun _ _ h => h) F = z := by simpa only [Polynomial.coeff_C_zero, polynomialWorkspaceEmbedding] using hF
  rw [← he, leadingExponent_hahnEmbedding, growthCoeff_hahnEmbedding, leadingCoeff_hahnEmbedding]
  exact _root_.HahnSeries.leadingCoeff_eq.symm

/-- No nonzero actual complex normal-form coefficient occurs above the native degree. -/
theorem growthCoeff_leading_bound (z : Surcomplex.{u}) (a : SignSequence.{u})
    (ha : growthCoeff z a ≠ 0) : a ≤ leadingExponent z := by
  obtain ⟨F, hF⟩ := coeff_mem_range_polynomialWorkspaceEmbedding (Polynomial.C z) 0
  have he : hahnEmbedding ((polynomialWorkspaceExponents (Polynomial.C z)).subtype.toAddMonoidHom)
      (fun _ _ h => h) F = z := by simpa only [Polynomial.coeff_C_zero, polynomialWorkspaceEmbedding] using hF
  rw [← he] at ha ⊢
  exact growthCoeff_leading_bound_hahnEmbedding _ _ F a ha

/-- On every nonzero actual surcomplex, the native leading exponent is the greatest support point. -/
theorem isGreatest_growthSupport {z : Surcomplex.{u}} (hz : z ≠ 0) :
    IsGreatest {a | growthCoeff z a ≠ 0} (leadingExponent z) := by
  refine ⟨?_, fun a ha => growthCoeff_leading_bound z a ha⟩
  rw [Set.mem_setOf_eq, growthCoeff_leadingExponent]
  exact leadingCoeff_ne_zero hz

/-- The actual normal-form leading coefficient multiplies with no cancellation. -/
theorem growthCoeff_leading_mul (z w : Surcomplex.{u}) :
    growthCoeff (z * w) (leadingExponent (z * w)) =
      growthCoeff z (leadingExponent z) * growthCoeff w (leadingExponent w) := by
  simp only [growthCoeff_leadingExponent, leadingCoeff_mul]

end
end Surreal.Surcomplex
