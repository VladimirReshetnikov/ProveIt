import Surreal.Foundations.SignSequencePowerSeries
import Surreal.HahnSeries.MvComposition

/-!
# Finite-variable formal series at actual surreal infinitesimals

A finite family of actual infinitesimals has a common small real Hahn
workspace. Native multivariate evaluation gives an actual ring homomorphism
on arbitrary real formal series. The displayed substituted monomials are
strongly summable, and their actual strong sum characterizes evaluation
independently of the chosen workspace. Values are finite, with standard part
equal to the formal constant coefficient. Zero-constant formal substitution
commutes with evaluation. Empty variable types and zero inputs are allowed.
-/

universe u v w t

namespace Surreal.Foundations.SignSequence

noncomputable section

variable {σ : Type v} [Fintype σ]

private abbrev mvArgumentExponents (x : σ → SignSequence.{u}) :=
  workspaceExponents (⋃ i, SmallNormalForm.support (SmallNormalForm.normalForm (x i)))

private def mvArgumentInclusion (x : σ → SignSequence.{u}) :
    mvArgumentExponents x →+ SignSequence.{u} :=
  (mvArgumentExponents x).subtype.toAddMonoidHom

omit [Fintype σ] in
private theorem mvArgumentInclusion_strictMono (x : σ → SignSequence.{u}) :
    StrictMono (mvArgumentInclusion x) := fun _ _ h => h

private abbrev mvArgumentPreimage (x : σ → SignSequence.{u}) :
    σ → _root_.HahnSeries (mvArgumentExponents x) ℝ :=
  familyHahnPreimage x

private theorem mvArgumentPreimage_spec (x : σ → SignSequence.{u}) (i : σ) :
    hahnEmbedding (mvArgumentInclusion x) (mvArgumentInclusion_strictMono x)
      (mvArgumentPreimage x i) = x i :=
  familyWorkspaceEmbedding_preimage x i

private theorem mvArgumentPreimage_pos (x : σ → SignSequence.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (i : σ) :
    0 < (mvArgumentPreimage x i).orderTop := by
  apply (isInfinitesimal_hahnEmbedding_iff (mvArgumentInclusion x)
    (mvArgumentInclusion_strictMono x) (mvArgumentPreimage x i)).mp
  simpa only [mvArgumentPreimage_spec] using hx i

/-- Evaluate arbitrary finite-variable formal series at actual infinitesimal inputs. -/
def mvPowerSeriesEvaluation (x : σ → SignSequence.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) : MvPowerSeries σ ℝ →+* SignSequence.{u} :=
  (hahnEmbedding (mvArgumentInclusion x) (mvArgumentInclusion_strictMono x)).comp
    (Surreal.HahnSeries.mvEvaluate (mvArgumentPreimage x) (mvArgumentPreimage_pos x hx)).toRingHom

section Workspace

variable {Γ : Type w} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Small.{u} Γ]

private theorem mapped_mvPowerSeries_terms (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (y : σ → _root_.HahnSeries Γ ℝ) (hy : ∀ i, 0 < (y i).orderTop)
    (F : MvPowerSeries σ ℝ) :
    (fun d => hahnEmbedding e he (Surreal.HahnSeries.mvEvaluationFamily y hy F d)) =
      (fun d => ofReal (MvPowerSeries.coeff d F) * ∏ i, (hahnEmbedding e he (y i)) ^ d i) := by
  funext d
  rw [Surreal.HahnSeries.mvEvaluationFamily_apply,
    ← _root_.HahnSeries.single_zero_mul_eq_smul]
  simp only [map_mul, map_prod, map_pow, hahnEmbedding_single_zero]

/-- Every displayed family is jointly strongly summable in an actual Hahn workspace. -/
theorem stronglySummable_mvPowerSeries_hahnEmbedding
    (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (y : σ → _root_.HahnSeries Γ ℝ) (hy : ∀ i, 0 < (y i).orderTop)
    (F : MvPowerSeries σ ℝ) :
    StronglySummable (fun d => ofReal (MvPowerSeries.coeff d F) *
      ∏ i, (hahnEmbedding e he (y i)) ^ d i) := by
  simpa only [mapped_mvPowerSeries_terms e he y hy F] using
    stronglySummable_hahnEmbedding e he (Surreal.HahnSeries.mvEvaluationFamily y hy F)

/-- Native workspace evaluation is the actual strong sum of the substituted monomials. -/
theorem strongSum_mvPowerSeries_hahnEmbedding
    (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (y : σ → _root_.HahnSeries Γ ℝ) (hy : ∀ i, 0 < (y i).orderTop)
    (F : MvPowerSeries σ ℝ) :
    strongSum (fun d => ofReal (MvPowerSeries.coeff d F) *
      ∏ i, (hahnEmbedding e he (y i)) ^ d i)
      (stronglySummable_mvPowerSeries_hahnEmbedding e he y hy F) =
      hahnEmbedding e he (Surreal.HahnSeries.mvEvaluate y hy F) := by
  simpa only [mapped_mvPowerSeries_terms e he y hy F, Surreal.HahnSeries.mvEvaluate_apply] using
    strongSum_hahnEmbedding e he (Surreal.HahnSeries.mvEvaluationFamily y hy F)

end Workspace

/-- Arbitrary real formal coefficients are admissible at finitely many actual infinitesimals. -/
theorem stronglySummable_mvPowerSeries (x : σ → SignSequence.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (F : MvPowerSeries σ ℝ) :
    StronglySummable (fun d => ofReal (MvPowerSeries.coeff d F) * ∏ i, x i ^ d i) := by
  simpa only [mvArgumentPreimage_spec] using
    stronglySummable_mvPowerSeries_hahnEmbedding (mvArgumentInclusion x)
      (mvArgumentInclusion_strictMono x) (mvArgumentPreimage x) (mvArgumentPreimage_pos x hx) F

/-- The actual multivariate evaluation is exactly the strong sum of its displayed terms. -/
theorem mvPowerSeriesEvaluation_eq_strongSum (x : σ → SignSequence.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (F : MvPowerSeries σ ℝ) :
    mvPowerSeriesEvaluation x hx F =
      strongSum (fun d => ofReal (MvPowerSeries.coeff d F) * ∏ i, x i ^ d i)
        (stronglySummable_mvPowerSeries x hx F) := by
  symm
  simpa only [mvArgumentPreimage_spec, mvPowerSeriesEvaluation, RingHom.coe_comp,
    Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using
    strongSum_mvPowerSeries_hahnEmbedding (mvArgumentInclusion x)
      (mvArgumentInclusion_strictMono x) (mvArgumentPreimage x) (mvArgumentPreimage_pos x hx) F

section Workspace

variable {Γ : Type w} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Small.{u} Γ]

/-- Every small Hahn representation gives the same actual multivariate evaluation. -/
theorem mvPowerSeriesEvaluation_hahnEmbedding
    (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (y : σ → _root_.HahnSeries Γ ℝ) (hy : ∀ i, 0 < (y i).orderTop)
    (F : MvPowerSeries σ ℝ) :
    mvPowerSeriesEvaluation (fun i => hahnEmbedding e he (y i))
      (fun i => (isInfinitesimal_hahnEmbedding_iff e he (y i)).mpr (hy i)) F =
      hahnEmbedding e he (Surreal.HahnSeries.mvEvaluate y hy F) := by
  rw [mvPowerSeriesEvaluation_eq_strongSum]
  exact strongSum_mvPowerSeries_hahnEmbedding e he y hy F

end Workspace

@[simp] theorem mvPowerSeriesEvaluation_monomial (x : σ → SignSequence.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (d : σ →₀ ℕ) (r : ℝ) :
    mvPowerSeriesEvaluation x hx (MvPowerSeries.monomial d r) =
      ofReal r * ∏ i, x i ^ d i := by
  change hahnEmbedding _ _ (Surreal.HahnSeries.mvEvaluate _ _ _) = _
  rw [Surreal.HahnSeries.mvEvaluate_monomial, ← _root_.HahnSeries.single_zero_mul_eq_smul]
  simp only [map_mul, map_prod, map_pow, hahnEmbedding_single_zero, mvArgumentPreimage_spec]

@[simp] theorem mvPowerSeriesEvaluation_X (x : σ → SignSequence.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (i : σ) :
    mvPowerSeriesEvaluation x hx (MvPowerSeries.X i) = x i := by
  change hahnEmbedding _ _ (Surreal.HahnSeries.mvEvaluate _ _ _) = _
  rw [Surreal.HahnSeries.mvEvaluate_X, mvArgumentPreimage_spec]

@[simp] theorem mvPowerSeriesEvaluation_C (x : σ → SignSequence.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (r : ℝ) :
    mvPowerSeriesEvaluation x hx (MvPowerSeries.C r) = ofReal r := by
  change hahnEmbedding _ _ (Surreal.HahnSeries.mvEvaluate _ _ _) = _
  rw [Surreal.HahnSeries.mvEvaluate_C, hahnEmbedding_single_zero]

/-- Every actual value of an admissible multivariate formal series is finite. -/
theorem isFinite_mvPowerSeriesEvaluation (x : σ → SignSequence.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (F : MvPowerSeries σ ℝ) :
    IsFinite (mvPowerSeriesEvaluation x hx F) :=
  (isFinite_hahnEmbedding_iff (mvArgumentInclusion x) (mvArgumentInclusion_strictMono x) _).mpr
    (Surreal.HahnSeries.orderTop_mvEvaluate_nonneg _ (mvArgumentPreimage_pos x hx) F)

/-- Actual standard part is the formal constant coefficient. -/
@[simp] theorem standardPart_mvPowerSeriesEvaluation (x : σ → SignSequence.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (F : MvPowerSeries σ ℝ) :
    standardPart (mvPowerSeriesEvaluation x hx F) = MvPowerSeries.constantCoeff F := by
  change standardPart (hahnEmbedding _ _ (Surreal.HahnSeries.mvEvaluate _ _ F)) = _
  rw [standardPart_hahnEmbedding _ _ _
    (Surreal.HahnSeries.orderTop_mvEvaluate_nonneg _ (mvArgumentPreimage_pos x hx) F),
    Surreal.HahnSeries.coeff_zero_mvEvaluate]

/-- Precisely the zero-constant formal series have infinitesimal actual values. -/
theorem isInfinitesimal_mvPowerSeriesEvaluation_iff (x : σ → SignSequence.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (F : MvPowerSeries σ ℝ) :
    IsInfinitesimal (mvPowerSeriesEvaluation x hx F) ↔ MvPowerSeries.constantCoeff F = 0 := by
  rw [← standardPart_eq_zero_iff (isFinite_mvPowerSeriesEvaluation x hx F),
    standardPart_mvPowerSeriesEvaluation]

/-- Zero-constant multivariate formal substitution commutes with actual evaluation. -/
theorem mvPowerSeriesEvaluation_subst {τ : Type t} [Fintype τ]
    (x : τ → SignSequence.{u}) (hx : ∀ i, IsInfinitesimal (x i))
    (A : MvPowerSeries σ ℝ) (B : σ → MvPowerSeries τ ℝ)
    (hB : ∀ i, MvPowerSeries.constantCoeff (B i) = 0) :
    mvPowerSeriesEvaluation x hx (MvPowerSeries.subst B A) =
      mvPowerSeriesEvaluation (fun i => mvPowerSeriesEvaluation x hx (B i))
        (fun i => (isInfinitesimal_mvPowerSeriesEvaluation_iff x hx (B i)).mpr (hB i)) A := by
  let y := mvArgumentPreimage x
  have hy : ∀ i, 0 < (y i).orderTop := mvArgumentPreimage_pos x hx
  have hBy : ∀ i, 0 < (Surreal.HahnSeries.mvEvaluate y hy (B i)).orderTop :=
    fun i => Surreal.HahnSeries.orderTop_mvEvaluate_pos_of_constantCoeff_zero y hy (B i) (hB i)
  change hahnEmbedding (mvArgumentInclusion x) (mvArgumentInclusion_strictMono x)
    (Surreal.HahnSeries.mvEvaluate y hy (MvPowerSeries.subst B A)) =
      mvPowerSeriesEvaluation
        (fun i => hahnEmbedding (mvArgumentInclusion x) (mvArgumentInclusion_strictMono x)
          (Surreal.HahnSeries.mvEvaluate y hy (B i))) _ A
  rw [mvPowerSeriesEvaluation_hahnEmbedding _ _ _ hBy,
    Surreal.HahnSeries.mvEvaluate_subst y hy A B hB]

end

end Surreal.Foundations.SignSequence
