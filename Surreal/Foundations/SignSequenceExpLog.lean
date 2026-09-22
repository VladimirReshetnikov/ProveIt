import Surreal.Foundations.SignSequencePowerSeries
import Surreal.Foundations.SignSequenceStandardPartTopology
import Surreal.HahnSeries.ExponentialAddition

/-!
# Exponential and logarithm at actual surreal infinitesimals

The ordinary formal exponential and logarithm define actual strong sums on
the explicit infinitesimal domain. Here `infLog x hx` means `log(1 + x)`.
Formal substitution proves the inverse identities, and a common small Hahn
workspace transfers the exponential addition law. These are the real
infinitesimal clauses of `e:prop-infexp`, not a global surreal exponential.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Strong exponential on actual infinitesimals, including zero. -/
def infExp (x : SignSequence.{u}) (hx : IsInfinitesimal x) : SignSequence.{u} :=
  powerSeriesEvaluation x hx (PowerSeries.exp ℝ)

/-- Strong logarithm of `1 + x`, where `x` is an actual infinitesimal. -/
def infLog (x : SignSequence.{u}) (hx : IsInfinitesimal x) : SignSequence.{u} :=
  powerSeriesEvaluation x hx (PowerSeries.log ℝ)

/-- The displayed factorial series is strongly summable in actual normal forms. -/
theorem stronglySummable_infExp (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    StronglySummable (fun n : ℕ => ofReal (algebraMap ℚ ℝ (1 / (n.factorial : ℚ))) * x ^ n) := by
  simpa only [PowerSeries.coeff_exp] using stronglySummable_powerSeries x hx (PowerSeries.exp ℝ)

/-- The displayed logarithmic series is strongly summable, with a zero term at index zero. -/
theorem stronglySummable_infLog (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    StronglySummable (fun n : ℕ =>
      ofReal (if n = 0 then 0 else algebraMap ℚ ℝ ((-1 : ℚ) ^ (n + 1) / n)) * x ^ n) := by
  simpa only [PowerSeries.coeff_log] using stronglySummable_powerSeries x hx (PowerSeries.log ℝ)

theorem infExp_eq_strongSum (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    infExp x hx = strongSum
      (fun n : ℕ => ofReal (algebraMap ℚ ℝ (1 / (n.factorial : ℚ))) * x ^ n)
      (stronglySummable_infExp x hx) := by
  simpa only [infExp, PowerSeries.coeff_exp] using
    powerSeriesEvaluation_eq_strongSum x hx (PowerSeries.exp ℝ)

theorem infLog_eq_strongSum (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    infLog x hx = strongSum
      (fun n : ℕ => ofReal
        (if n = 0 then 0 else algebraMap ℚ ℝ ((-1 : ℚ) ^ (n + 1) / n)) * x ^ n)
      (stronglySummable_infLog x hx) := by
  simpa only [infLog, PowerSeries.coeff_log] using
    powerSeriesEvaluation_eq_strongSum x hx (PowerSeries.log ℝ)

theorem isFinite_infExp (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    IsFinite (infExp x hx) := isFinite_powerSeriesEvaluation x hx _

theorem isFinite_infLog (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    IsFinite (infLog x hx) := isFinite_powerSeriesEvaluation x hx _

@[simp] theorem standardPart_infExp (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    standardPart (infExp x hx) = 1 := by simp [infExp]

@[simp] theorem standardPart_infLog (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    standardPart (infLog x hx) = 0 := by simp [infLog]

/-- Infinitesimal exponentials lie in the multiplicative neighborhood of one. -/
theorem infinitesimal_infExp_sub_one (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    IsInfinitesimal (infExp x hx - 1) := by
  simpa only [map_sub, map_one, infExp] using
    (isInfinitesimal_powerSeriesEvaluation_iff x hx (PowerSeries.exp ℝ - 1)).mpr (by simp)

/-- The logarithm of one plus an infinitesimal is infinitesimal. -/
theorem infinitesimal_infLog (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    IsInfinitesimal (infLog x hx) :=
  (isInfinitesimal_powerSeriesEvaluation_iff x hx (PowerSeries.log ℝ)).mpr (by simp)

@[simp] theorem infExp_zero : infExp (0 : SignSequence.{u}) infinitesimal_zero = 1 := by
  simp [infExp]

@[simp] theorem infLog_zero : infLog (0 : SignSequence.{u}) infinitesimal_zero = 0 := by
  simp [infLog]

theorem infExp_ne_zero (x : SignSequence.{u}) (hx : IsInfinitesimal x) : infExp x hx ≠ 0 := by
  intro h
  have hs := standardPart_infExp x hx
  simp [h] at hs

/-- The strong logarithm cancels the actual infinitesimal exponential. -/
@[simp] theorem infLog_infExp_sub_one (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    infLog (infExp x hx - 1) (infinitesimal_infExp_sub_one x hx) = x := by
  have h := powerSeriesEvaluation_subst x hx (PowerSeries.log ℝ) (PowerSeries.exp ℝ - 1) (by simp)
  rw [FormalPowerSeries.log_subst_exp_sub_one, powerSeriesEvaluation_X] at h
  simpa only [map_sub, map_one, infExp, infLog] using h.symm

/-- Exponentiating the strong logarithm recovers one plus the original infinitesimal. -/
@[simp] theorem infExp_infLog (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    infExp (infLog x hx) (infinitesimal_infLog x hx) = 1 + x := by
  have h := powerSeriesEvaluation_subst x hx (PowerSeries.exp ℝ) (PowerSeries.log ℝ) (by simp)
  rw [FormalPowerSeries.exp_subst_log, map_add, map_one, powerSeriesEvaluation_X] at h
  exact h.symm

section Workspace

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Small.{u} Γ]

/-- Actual infinitesimal exponential agrees with every small Hahn representation. -/
theorem infExp_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : _root_.HahnSeries Γ ℝ) (hx : 0 < x.orderTop) :
    infExp (hahnEmbedding e he x) ((isInfinitesimal_hahnEmbedding_iff e he x).mpr hx) =
      hahnEmbedding e he (Surreal.HahnSeries.infExp x hx) :=
  powerSeriesEvaluation_hahnEmbedding e he x hx (PowerSeries.exp ℝ)

/-- Actual infinitesimal logarithm agrees with every small Hahn representation. -/
theorem infLog_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : _root_.HahnSeries Γ ℝ) (hx : 0 < x.orderTop) :
    infLog (hahnEmbedding e he x) ((isInfinitesimal_hahnEmbedding_iff e he x).mpr hx) =
      hahnEmbedding e he (Surreal.HahnSeries.infLog x hx) :=
  powerSeriesEvaluation_hahnEmbedding e he x hx (PowerSeries.log ℝ)

end Workspace

/-- Actual infinitesimal exponential converts addition to multiplication. -/
theorem infExp_add (x y : SignSequence.{u}) (hx : IsInfinitesimal x) (hy : IsInfinitesimal y) :
    infExp (x + y) (infinitesimal_add hx hy) = infExp x hx * infExp y hy := by
  let f : Bool → SignSequence.{u} := fun b => if b then x else y
  let Γ := workspaceExponents (⋃ i, SmallNormalForm.support (SmallNormalForm.normalForm (f i)))
  let e : Γ →+ SignSequence.{u} := Γ.subtype.toAddMonoidHom
  have he : StrictMono e := fun _ _ h => h
  let X := familyHahnPreimage f true
  let Y := familyHahnPreimage f false
  have hX : hahnEmbedding e he X = x := familyWorkspaceEmbedding_preimage f true
  have hY : hahnEmbedding e he Y = y := familyWorkspaceEmbedding_preimage f false
  have hXp : 0 < X.orderTop := (isInfinitesimal_hahnEmbedding_iff e he X).mp (hX.symm ▸ hx)
  have hYp : 0 < Y.orderTop := (isInfinitesimal_hahnEmbedding_iff e he Y).mp (hY.symm ▸ hy)
  have h := congrArg (hahnEmbedding e he) (Surreal.HahnSeries.infExp_add X Y hXp hYp)
  simpa only [map_mul, ← infExp_hahnEmbedding, map_add, hX, hY] using h

/-- Negation of an infinitesimal inverts its exponential. -/
theorem infExp_neg (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    infExp (-x) (infinitesimal_neg hx) = (infExp x hx)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa using (infExp_add (-x) x (infinitesimal_neg hx) hx).symm


/-- Products of the two exponential neighborhoods remain infinitesimally close to one. -/
theorem infinitesimal_one_add_mul_sub_one (x y : SignSequence.{u})
    (hx : IsInfinitesimal x) (hy : IsInfinitesimal y) :
    IsInfinitesimal ((1 + x) * (1 + y) - 1) := by
  have h := infinitesimal_infExp_sub_one (infLog x hx + infLog y hy)
    (infinitesimal_add (infinitesimal_infLog x hx) (infinitesimal_infLog y hy))
  simpa only [infExp_add (infLog x hx) (infLog y hy)
    (infinitesimal_infLog x hx) (infinitesimal_infLog y hy), infExp_infLog] using h

/-- The logarithm converts products near one into sums of infinitesimal logarithms. -/
theorem infLog_mul (x y : SignSequence.{u}) (hx : IsInfinitesimal x) (hy : IsInfinitesimal y) :
    infLog ((1 + x) * (1 + y) - 1) (infinitesimal_one_add_mul_sub_one x y hx hy) =
      infLog x hx + infLog y hy := by
  have h := infLog_infExp_sub_one (infLog x hx + infLog y hy)
    (infinitesimal_add (infinitesimal_infLog x hx) (infinitesimal_infLog y hy))
  simpa only [infExp_add (infLog x hx) (infLog y hy)
    (infinitesimal_infLog x hx) (infinitesimal_infLog y hy), infExp_infLog] using h

/-- Infinitesimal exponential is injective on its complete stated domain. -/
theorem infExp_injective {x y : SignSequence.{u}} (hx : IsInfinitesimal x) (hy : IsInfinitesimal y)
    (h : infExp x hx = infExp y hy) : x = y := by
  have hl : infLog (infExp x hx - 1) (infinitesimal_infExp_sub_one x hx) =
      infLog (infExp y hy - 1) (infinitesimal_infExp_sub_one y hy) := by
    congr 1
    rw [h]
  simpa using hl

/-- Every actual number infinitesimally close to one has a unique infinitesimal logarithm. -/
theorem existsUnique_infExp_eq (y : SignSequence.{u}) (hy : IsInfinitesimal (y - 1)) :
    ∃! x : {x : SignSequence.{u} // IsInfinitesimal x}, infExp x.val x.property = y := by
  refine ⟨⟨infLog (y - 1) hy, infinitesimal_infLog _ _⟩, ?_, ?_⟩
  · simp only [infExp_infLog, add_sub_cancel]
  · intro x hx
    apply Subtype.ext
    apply infExp_injective x.property (infinitesimal_infLog _ _)
    simpa only [infExp_infLog, add_sub_cancel] using hx

end

end Surreal.Foundations.SignSequence
