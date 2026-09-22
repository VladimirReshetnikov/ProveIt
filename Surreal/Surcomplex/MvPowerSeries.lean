import Surreal.Surcomplex.PowerSeries
import Surreal.HahnSeries.MvComposition

/-!
# Finite-variable formal series at actual surcomplex infinitesimals

A finite family of actual surcomplex infinitesimals has a common small complex Hahn
workspace. Native multivariate evaluation gives an actual ring homomorphism
on arbitrary complex formal series. The displayed substituted monomials are
strongly summable, and their actual strong sum characterizes evaluation
independently of the chosen workspace. Values are finite, with standard part
equal to the formal constant coefficient. Zero-constant formal substitution
commutes with evaluation. Empty variable types and zero inputs are allowed.
This proves the finite-variable strong-summability, ring, and composition
clauses of `a:cor:complexsub`; no differentiation or holomorphic-domain theorem
is asserted.
-/

universe u v w t

namespace Surreal.Surcomplex

open Foundations

noncomputable section

variable {σ : Type v} [Fintype σ]

private abbrev mvArgumentExponents (x : σ → Surcomplex.{u}) :=
  familyWorkspaceExponents x

private def mvArgumentInclusion (x : σ → Surcomplex.{u}) :
    mvArgumentExponents x →+ SignSequence.{u} :=
  (mvArgumentExponents x).subtype.toAddMonoidHom

omit [Fintype σ] in
private theorem mvArgumentInclusion_strictMono (x : σ → Surcomplex.{u}) :
    StrictMono (mvArgumentInclusion x) := fun _ _ h => h

private abbrev mvArgumentPreimage (x : σ → Surcomplex.{u}) :
    σ → _root_.HahnSeries (mvArgumentExponents x) ℂ :=
  familyHahnPreimage x

private theorem mvArgumentPreimage_spec (x : σ → Surcomplex.{u}) (i : σ) :
    hahnEmbedding (mvArgumentInclusion x) (mvArgumentInclusion_strictMono x)
      (mvArgumentPreimage x i) = x i :=
  familyWorkspaceEmbedding_preimage x i

private theorem mvArgumentPreimage_pos (x : σ → Surcomplex.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (i : σ) :
    0 < (mvArgumentPreimage x i).orderTop := by
  apply (isInfinitesimal_hahnEmbedding_iff (mvArgumentInclusion x)
    (mvArgumentInclusion_strictMono x) (mvArgumentPreimage x i)).mp
  simpa only [mvArgumentPreimage_spec] using hx i

/-- Evaluate arbitrary finite-variable formal series at actual infinitesimal inputs. -/
def mvPowerSeriesEvaluation (x : σ → Surcomplex.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) : MvPowerSeries σ ℂ →+* Surcomplex.{u} :=
  (hahnEmbedding (mvArgumentInclusion x) (mvArgumentInclusion_strictMono x)).comp
    (Surreal.HahnSeries.mvEvaluate (mvArgumentPreimage x) (mvArgumentPreimage_pos x hx)).toRingHom

section Workspace

variable {Γ : Type w} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Small.{u} Γ]

private theorem mapped_mvPowerSeries_terms (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (y : σ → _root_.HahnSeries Γ ℂ) (hy : ∀ i, 0 < (y i).orderTop)
    (F : MvPowerSeries σ ℂ) :
    (fun d => hahnEmbedding e he (Surreal.HahnSeries.mvEvaluationFamily y hy F d)) =
      (fun d => ofComplex (MvPowerSeries.coeff d F) * ∏ i, (hahnEmbedding e he (y i)) ^ d i) := by
  funext d
  rw [Surreal.HahnSeries.mvEvaluationFamily_apply,
    ← _root_.HahnSeries.single_zero_mul_eq_smul]
  simp only [map_mul, map_prod, map_pow, hahnEmbedding_single_zero]

/-- Every displayed family is jointly strongly summable in an actual Hahn workspace. -/
theorem stronglySummable_mvPowerSeries_hahnEmbedding
    (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (y : σ → _root_.HahnSeries Γ ℂ) (hy : ∀ i, 0 < (y i).orderTop)
    (F : MvPowerSeries σ ℂ) :
    StronglySummable (fun d => ofComplex (MvPowerSeries.coeff d F) *
      ∏ i, (hahnEmbedding e he (y i)) ^ d i) := by
  simpa only [mapped_mvPowerSeries_terms e he y hy F] using
    stronglySummable_hahnEmbedding e he (Surreal.HahnSeries.mvEvaluationFamily y hy F)

/-- Native workspace evaluation is the actual strong sum of the substituted monomials. -/
theorem strongSum_mvPowerSeries_hahnEmbedding
    (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (y : σ → _root_.HahnSeries Γ ℂ) (hy : ∀ i, 0 < (y i).orderTop)
    (F : MvPowerSeries σ ℂ) :
    strongSum (fun d => ofComplex (MvPowerSeries.coeff d F) *
      ∏ i, (hahnEmbedding e he (y i)) ^ d i)
      (stronglySummable_mvPowerSeries_hahnEmbedding e he y hy F) =
      hahnEmbedding e he (Surreal.HahnSeries.mvEvaluate y hy F) := by
  simpa only [mapped_mvPowerSeries_terms e he y hy F, Surreal.HahnSeries.mvEvaluate_apply] using
    strongSum_hahnEmbedding e he (Surreal.HahnSeries.mvEvaluationFamily y hy F)

end Workspace

/-- Arbitrary complex formal coefficients are admissible at finitely many actual surcomplex infinitesimals. -/
theorem stronglySummable_mvPowerSeries (x : σ → Surcomplex.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (F : MvPowerSeries σ ℂ) :
    StronglySummable (fun d => ofComplex (MvPowerSeries.coeff d F) * ∏ i, x i ^ d i) := by
  simpa only [mvArgumentPreimage_spec] using
    stronglySummable_mvPowerSeries_hahnEmbedding (mvArgumentInclusion x)
      (mvArgumentInclusion_strictMono x) (mvArgumentPreimage x) (mvArgumentPreimage_pos x hx) F

/-- The actual multivariate evaluation is exactly the strong sum of its displayed terms. -/
theorem mvPowerSeriesEvaluation_eq_strongSum (x : σ → Surcomplex.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (F : MvPowerSeries σ ℂ) :
    mvPowerSeriesEvaluation x hx F =
      strongSum (fun d => ofComplex (MvPowerSeries.coeff d F) * ∏ i, x i ^ d i)
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
    (y : σ → _root_.HahnSeries Γ ℂ) (hy : ∀ i, 0 < (y i).orderTop)
    (F : MvPowerSeries σ ℂ) :
    mvPowerSeriesEvaluation (fun i => hahnEmbedding e he (y i))
      (fun i => (isInfinitesimal_hahnEmbedding_iff e he (y i)).mpr (hy i)) F =
      hahnEmbedding e he (Surreal.HahnSeries.mvEvaluate y hy F) := by
  rw [mvPowerSeriesEvaluation_eq_strongSum]
  exact strongSum_mvPowerSeries_hahnEmbedding e he y hy F

end Workspace

@[simp] theorem mvPowerSeriesEvaluation_monomial (x : σ → Surcomplex.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (d : σ →₀ ℕ) (r : ℂ) :
    mvPowerSeriesEvaluation x hx (MvPowerSeries.monomial d r) =
      ofComplex r * ∏ i, x i ^ d i := by
  change hahnEmbedding _ _ (Surreal.HahnSeries.mvEvaluate _ _ _) = _
  rw [Surreal.HahnSeries.mvEvaluate_monomial, ← _root_.HahnSeries.single_zero_mul_eq_smul]
  simp only [map_mul, map_prod, map_pow, hahnEmbedding_single_zero, mvArgumentPreimage_spec]

@[simp] theorem mvPowerSeriesEvaluation_X (x : σ → Surcomplex.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (i : σ) :
    mvPowerSeriesEvaluation x hx (MvPowerSeries.X i) = x i := by
  change hahnEmbedding _ _ (Surreal.HahnSeries.mvEvaluate _ _ _) = _
  rw [Surreal.HahnSeries.mvEvaluate_X, mvArgumentPreimage_spec]

@[simp] theorem mvPowerSeriesEvaluation_C (x : σ → Surcomplex.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (r : ℂ) :
    mvPowerSeriesEvaluation x hx (MvPowerSeries.C r) = ofComplex r := by
  change hahnEmbedding _ _ (Surreal.HahnSeries.mvEvaluate _ _ _) = _
  rw [Surreal.HahnSeries.mvEvaluate_C, hahnEmbedding_single_zero]

/-- Every actual value of an admissible multivariate formal series is finite. -/
theorem isFinite_mvPowerSeriesEvaluation (x : σ → Surcomplex.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (F : MvPowerSeries σ ℂ) :
    IsFinite (mvPowerSeriesEvaluation x hx F) :=
  (isFinite_hahnEmbedding_iff (mvArgumentInclusion x) (mvArgumentInclusion_strictMono x) _).mpr
    (Surreal.HahnSeries.orderTop_mvEvaluate_nonneg _ (mvArgumentPreimage_pos x hx) F)

/-- Actual standard part is the formal constant coefficient. -/
@[simp] theorem standardPart_mvPowerSeriesEvaluation (x : σ → Surcomplex.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (F : MvPowerSeries σ ℂ) :
    standardPart (mvPowerSeriesEvaluation x hx F) = MvPowerSeries.constantCoeff F := by
  change standardPart (hahnEmbedding _ _ (Surreal.HahnSeries.mvEvaluate _ _ F)) = _
  rw [standardPart_hahnEmbedding _ _ _
    (Surreal.HahnSeries.orderTop_mvEvaluate_nonneg _ (mvArgumentPreimage_pos x hx) F),
    Surreal.HahnSeries.coeff_zero_mvEvaluate]

/-- Precisely the zero-constant formal series have infinitesimal actual values. -/
theorem isInfinitesimal_mvPowerSeriesEvaluation_iff (x : σ → Surcomplex.{u})
    (hx : ∀ i, IsInfinitesimal (x i)) (F : MvPowerSeries σ ℂ) :
    IsInfinitesimal (mvPowerSeriesEvaluation x hx F) ↔ MvPowerSeries.constantCoeff F = 0 := by
  rw [← standardPart_eq_zero_iff (isFinite_mvPowerSeriesEvaluation x hx F),
    standardPart_mvPowerSeriesEvaluation]

/-- Zero-constant multivariate formal substitution commutes with actual evaluation. -/
theorem mvPowerSeriesEvaluation_subst {τ : Type t} [Fintype τ]
    (x : τ → Surcomplex.{u}) (hx : ∀ i, IsInfinitesimal (x i))
    (A : MvPowerSeries σ ℂ) (B : σ → MvPowerSeries τ ℂ)
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

end Surreal.Surcomplex
