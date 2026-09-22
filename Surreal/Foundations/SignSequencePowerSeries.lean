import Surreal.Foundations.SignSequenceWorkspace
import Surreal.Foundations.SignSequenceHahnValuation
import Surreal.Foundations.SignSequenceStrongSummation
import Surreal.HahnSeries.Composition

/-!
# Formal power series at actual surreal infinitesimals

Every actual infinitesimal, including zero, belongs to a small real Hahn
workspace with strictly positive native order. Admissible Hahn evaluation
therefore defines a ring homomorphism on all real formal power series.
Its displayed terms are strongly summable in canonical actual normal forms,
and its value is their strong sum. This description makes evaluation
independent of the chosen workspace. The output is finite and has standard
part equal to the formal constant coefficient.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

private abbrev argumentFamily (x : SignSequence.{u}) : Unit → SignSequence.{u} :=
  fun _ => x

private abbrev argumentExponents (x : SignSequence.{u}) :=
  workspaceExponents
    (⋃ i, SmallNormalForm.support (SmallNormalForm.normalForm (argumentFamily x i)))

private def argumentInclusion (x : SignSequence.{u}) :
    argumentExponents x →+ SignSequence.{u} :=
  (argumentExponents x).subtype.toAddMonoidHom

private theorem argumentInclusion_strictMono (x : SignSequence.{u}) :
    StrictMono (argumentInclusion x) := fun _ _ h => h

private abbrev argumentPreimage (x : SignSequence.{u}) :
    _root_.HahnSeries (argumentExponents x) ℝ :=
  familyHahnPreimage (argumentFamily x) ()

private theorem argumentPreimage_spec (x : SignSequence.{u}) :
    hahnEmbedding (argumentInclusion x) (argumentInclusion_strictMono x)
      (argumentPreimage x) = x :=
  familyWorkspaceEmbedding_preimage (argumentFamily x) ()

private theorem argumentPreimage_pos (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    0 < (argumentPreimage x).orderTop := by
  apply (isInfinitesimal_hahnEmbedding_iff (argumentInclusion x)
    (argumentInclusion_strictMono x) (argumentPreimage x)).mp
  simpa only [argumentPreimage_spec] using hx

/-- Admissible formal-series evaluation at an actual surreal infinitesimal. -/
def powerSeriesEvaluation (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    PowerSeries ℝ →+* SignSequence.{u} :=
  (hahnEmbedding (argumentInclusion x) (argumentInclusion_strictMono x)).comp
    (Surreal.HahnSeries.evaluate (argumentPreimage x) (argumentPreimage_pos x hx)).toRingHom

section Workspace

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Small.{u} Γ]

private theorem mapped_powerSeries_terms (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (y : _root_.HahnSeries Γ ℝ) (hy : 0 < y.orderTop) (f : PowerSeries ℝ) :
    (fun n => hahnEmbedding e he (_root_.HahnSeries.SummableFamily.powerSeriesFamily y f n)) =
      (fun n => ofReal (f.coeff n) * (hahnEmbedding e he y) ^ n) := by
  funext n
  rw [_root_.HahnSeries.SummableFamily.powerSeriesFamily_of_orderTop_pos hy,
    ← _root_.HahnSeries.single_zero_mul_eq_smul, map_mul, map_pow,
    hahnEmbedding_single_zero]

/-- The literal substituted terms are strongly summable in every actual Hahn workspace. -/
theorem stronglySummable_powerSeries_hahnEmbedding
    (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (y : _root_.HahnSeries Γ ℝ) (hy : 0 < y.orderTop) (f : PowerSeries ℝ) :
    StronglySummable (fun n => ofReal (f.coeff n) * (hahnEmbedding e he y) ^ n) := by
  simpa only [mapped_powerSeries_terms e he y hy f] using
    stronglySummable_hahnEmbedding e he
      (_root_.HahnSeries.SummableFamily.powerSeriesFamily y f)

/-- Workspace evaluation equals the actual strong sum of its displayed terms. -/
theorem strongSum_powerSeries_hahnEmbedding
    (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (y : _root_.HahnSeries Γ ℝ) (hy : 0 < y.orderTop) (f : PowerSeries ℝ) :
    strongSum (fun n => ofReal (f.coeff n) * (hahnEmbedding e he y) ^ n)
      (stronglySummable_powerSeries_hahnEmbedding e he y hy f) =
      hahnEmbedding e he (Surreal.HahnSeries.evaluate y hy f) := by
  simpa only [mapped_powerSeries_terms e he y hy f, Surreal.HahnSeries.evaluate,
    PowerSeries.heval_apply] using
    strongSum_hahnEmbedding e he
      (_root_.HahnSeries.SummableFamily.powerSeriesFamily y f)

end Workspace

/-- Every real coefficient sequence is admissible at every actual infinitesimal. -/
theorem stronglySummable_powerSeries (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℝ) :
    StronglySummable (fun n => ofReal (f.coeff n) * x ^ n) := by
  simpa only [argumentPreimage_spec] using
    stronglySummable_powerSeries_hahnEmbedding (argumentInclusion x)
      (argumentInclusion_strictMono x) (argumentPreimage x) (argumentPreimage_pos x hx) f

/-- The evaluation homomorphism is precisely coefficientwise actual strong summation. -/
theorem powerSeriesEvaluation_eq_strongSum (x : SignSequence.{u})
    (hx : IsInfinitesimal x) (f : PowerSeries ℝ) :
    powerSeriesEvaluation x hx f =
      strongSum (fun n => ofReal (f.coeff n) * x ^ n)
        (stronglySummable_powerSeries x hx f) := by
  symm
  simpa only [argumentPreimage_spec, powerSeriesEvaluation, RingHom.coe_comp,
    Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using
    strongSum_powerSeries_hahnEmbedding (argumentInclusion x)
      (argumentInclusion_strictMono x) (argumentPreimage x) (argumentPreimage_pos x hx) f

/-- Arbitrary coefficient sequences, with no growth hypothesis, give strong sums. -/
theorem stronglySummable_coeff_mul_powers (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (c : ℕ → ℝ) : StronglySummable (fun n => ofReal (c n) * x ^ n) := by
  simpa only [PowerSeries.coeff_mk] using stronglySummable_powerSeries x hx (PowerSeries.mk c)

section Workspace

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Small.{u} Γ]

/-- Evaluation agrees with every small Hahn representation of its input. -/
theorem powerSeriesEvaluation_hahnEmbedding
    (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (y : _root_.HahnSeries Γ ℝ) (hy : 0 < y.orderTop) (f : PowerSeries ℝ) :
    powerSeriesEvaluation (hahnEmbedding e he y)
      ((isInfinitesimal_hahnEmbedding_iff e he y).mpr hy) f =
      hahnEmbedding e he (Surreal.HahnSeries.evaluate y hy f) := by
  rw [powerSeriesEvaluation_eq_strongSum]
  exact strongSum_powerSeries_hahnEmbedding e he y hy f

end Workspace

@[simp] theorem powerSeriesEvaluation_X (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    powerSeriesEvaluation x hx PowerSeries.X = x := by
  change hahnEmbedding _ _ (Surreal.HahnSeries.evaluate _ _ PowerSeries.X) = x
  rw [Surreal.HahnSeries.evaluate_X, argumentPreimage_spec]

@[simp] theorem powerSeriesEvaluation_C (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (r : ℝ) : powerSeriesEvaluation x hx (PowerSeries.C r) = ofReal r := by
  change hahnEmbedding _ _ (PowerSeries.heval _ (PowerSeries.C r)) = ofReal r
  rw [PowerSeries.heval_C, ← _root_.HahnSeries.single_zero_mul_eq_smul, mul_one,
    hahnEmbedding_single_zero]

/-- Every admissible formal-series value is an actual finite surreal. -/
theorem isFinite_powerSeriesEvaluation (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℝ) : IsFinite (powerSeriesEvaluation x hx f) :=
  (isFinite_hahnEmbedding_iff (argumentInclusion x) (argumentInclusion_strictMono x) _).mpr
    (Surreal.HahnSeries.orderTop_evaluate_nonneg _ (argumentPreimage_pos x hx) f)

/-- Standard part of actual evaluation is the formal constant coefficient. -/
@[simp] theorem standardPart_powerSeriesEvaluation (x : SignSequence.{u})
    (hx : IsInfinitesimal x) (f : PowerSeries ℝ) :
    standardPart (powerSeriesEvaluation x hx f) = f.constantCoeff := by
  change standardPart (hahnEmbedding _ _ (Surreal.HahnSeries.evaluate _ _ f)) = _
  rw [standardPart_hahnEmbedding _ _ _
    (Surreal.HahnSeries.orderTop_evaluate_nonneg _ (argumentPreimage_pos x hx) f),
    Surreal.HahnSeries.coeff_zero_evaluate]

/-- A vanishing formal constant term gives an actual infinitesimal output. -/
theorem isInfinitesimal_powerSeriesEvaluation_iff (x : SignSequence.{u})
    (hx : IsInfinitesimal x) (f : PowerSeries ℝ) :
    IsInfinitesimal (powerSeriesEvaluation x hx f) ↔ f.constantCoeff = 0 := by
  rw [← standardPart_eq_zero_iff (isFinite_powerSeriesEvaluation x hx f),
    standardPart_powerSeriesEvaluation]

/-- Evaluation at the zero infinitesimal is evaluation of the formal constant term. -/
@[simp] theorem powerSeriesEvaluation_zero (f : PowerSeries ℝ) :
    powerSeriesEvaluation (0 : SignSequence.{u}) infinitesimal_zero f =
      ofReal f.constantCoeff := by
  have hzero : argumentPreimage (0 : SignSequence.{u}) = 0 := by
    apply hahnEmbedding_injective (argumentInclusion (0 : SignSequence.{u}))
      (argumentInclusion_strictMono (0 : SignSequence.{u}))
    rw [argumentPreimage_spec, map_zero]
  change hahnEmbedding _ _ (_root_.HahnSeries.SummableFamily.powerSeriesFamily _ f).hsum = _
  rw [hzero, _root_.HahnSeries.SummableFamily.powerSeriesFamily_hsum_zero,
    ← _root_.HahnSeries.single_zero_mul_eq_smul, mul_one, hahnEmbedding_single_zero]

/-- Formal composition is valid whenever the inner formal constant coefficient vanishes. -/
theorem powerSeriesEvaluation_subst (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (A B : PowerSeries ℝ) (hB : B.constantCoeff = 0) :
    powerSeriesEvaluation x hx (A.subst B) =
      powerSeriesEvaluation (powerSeriesEvaluation x hx B)
        ((isInfinitesimal_powerSeriesEvaluation_iff x hx B).mpr hB) A := by
  let y := argumentPreimage x
  have hy : 0 < y.orderTop := argumentPreimage_pos x hx
  have hBy := Surreal.HahnSeries.orderTop_evaluate_pos_of_constantCoeff_zero y hy B hB
  change hahnEmbedding (argumentInclusion x) (argumentInclusion_strictMono x)
    (Surreal.HahnSeries.evaluate y hy (A.subst B)) =
      powerSeriesEvaluation
        (hahnEmbedding (argumentInclusion x) (argumentInclusion_strictMono x)
          (Surreal.HahnSeries.evaluate y hy B)) _ A
  rw [powerSeriesEvaluation_hahnEmbedding _ _ _ hBy,
    Surreal.HahnSeries.evaluate_subst y hy A B hB]

end

end Surreal.Foundations.SignSequence
