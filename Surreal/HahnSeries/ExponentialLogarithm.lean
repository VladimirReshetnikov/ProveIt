import Surreal.Algebra.PowerSeriesExpLog
import Surreal.HahnSeries.Composition
import Surreal.HahnSeries.Characteristic

/-!
# Infinitesimal Hahn exponential and logarithm

The exponential and the logarithm of `1 + x` are defined by strongly summable
Hahn families when `x` has positive order. They are inverse through formal
substitution, with no Archimedean or topological hypothesis. This proves the
summability and inverse clauses of `e:prop-infexp` in the analysis report.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K] [CharZero K]

/-- Exponential of an infinitesimal Hahn series. -/
def infExp (x : K⟦Γ⟧) (hx : 0 < x.orderTop) : K⟦Γ⟧ :=
  evaluate x hx (PowerSeries.exp K)

/-- Logarithm of `1 + x`, with `x` infinitesimal. -/
def infLog (x : K⟦Γ⟧) (hx : 0 < x.orderTop) : K⟦Γ⟧ :=
  evaluate x hx (PowerSeries.log K)

/-- The actual strongly summable exponential family. -/
def infExpFamily (x : K⟦Γ⟧) (_hx : 0 < x.orderTop) : SummableFamily Γ K ℕ :=
  SummableFamily.powerSeriesFamily x (PowerSeries.exp K)

/-- The actual strongly summable logarithmic family, with its zero term
included to give a natural-number indexed family. -/
def infLogFamily (x : K⟦Γ⟧) (_hx : 0 < x.orderTop) : SummableFamily Γ K ℕ :=
  SummableFamily.powerSeriesFamily x (PowerSeries.log K)

theorem infExpFamily_apply (x : K⟦Γ⟧) (hx : 0 < x.orderTop) (n : ℕ) :
    infExpFamily x hx n = single 0 (algebraMap ℚ K (1 / (n.factorial : ℚ))) * x ^ n := by
  simp only [infExpFamily, SummableFamily.powerSeriesFamily_of_orderTop_pos hx,
    PowerSeries.coeff_exp, single_zero_mul_eq_smul]

theorem infLogFamily_apply (x : K⟦Γ⟧) (hx : 0 < x.orderTop) (n : ℕ) :
    infLogFamily x hx n =
      single 0 (if n = 0 then 0 else algebraMap ℚ K ((-1 : ℚ) ^ (n + 1) / n)) *
        x ^ n := by
  simp only [infLogFamily, SummableFamily.powerSeriesFamily_of_orderTop_pos hx,
    PowerSeries.coeff_log, single_zero_mul_eq_smul]

@[simp] theorem infExpFamily_hsum (x : K⟦Γ⟧) (hx : 0 < x.orderTop) :
    (infExpFamily x hx).hsum = infExp x hx := rfl

@[simp] theorem infLogFamily_hsum (x : K⟦Γ⟧) (hx : 0 < x.orderTop) :
    (infLogFamily x hx).hsum = infLog x hx := rfl

@[simp] theorem coeff_zero_infExp (x : K⟦Γ⟧) (hx : 0 < x.orderTop) :
    (infExp x hx).coeff 0 = 1 := by simp [infExp]

@[simp] theorem coeff_zero_infLog (x : K⟦Γ⟧) (hx : 0 < x.orderTop) :
    (infLog x hx).coeff 0 = 0 := by simp [infLog]

/-- The exponential has constant term one and only positive-order error. -/
theorem infExp_sub_one_pos (x : K⟦Γ⟧) (hx : 0 < x.orderTop) :
    0 < (infExp x hx - 1).orderTop := by
  simpa only [map_sub, map_one, infExp] using
    orderTop_evaluate_pos_of_constantCoeff_zero x hx (PowerSeries.exp K - 1) (by simp)

theorem infLog_orderTop_pos (x : K⟦Γ⟧) (hx : 0 < x.orderTop) :
    0 < (infLog x hx).orderTop :=
  orderTop_evaluate_pos_of_constantCoeff_zero x hx (PowerSeries.log K) (by simp)

@[simp] theorem infExp_orderTop (x : K⟦Γ⟧) (hx : 0 < x.orderTop) :
    (infExp x hx).orderTop = 0 :=
  ((orderTop_self_sub_one_pos_iff _).mp (infExp_sub_one_pos x hx)).1

@[simp] theorem infExp_leadingCoeff (x : K⟦Γ⟧) (hx : 0 < x.orderTop) :
    (infExp x hx).leadingCoeff = 1 :=
  ((orderTop_self_sub_one_pos_iff _).mp (infExp_sub_one_pos x hx)).2

theorem infExp_ne_zero (x : K⟦Γ⟧) (hx : 0 < x.orderTop) : infExp x hx ≠ 0 := by
  intro h
  have := coeff_zero_infExp x hx
  simp [h] at this

/-- The logarithm cancels the infinitesimal exponential. -/
@[simp] theorem infLog_infExp_sub_one (x : K⟦Γ⟧) (hx : 0 < x.orderTop) :
    infLog (infExp x hx - 1) (infExp_sub_one_pos x hx) = x := by
  have h := evaluate_subst x hx (PowerSeries.log K) (PowerSeries.exp K - 1) (by simp)
  rw [FormalPowerSeries.log_subst_exp_sub_one, evaluate_X] at h
  simpa only [map_sub, map_one, infExp, infLog] using h.symm

/-- Exponentiating the infinitesimal logarithm recovers `1 + x`. -/
@[simp] theorem infExp_infLog (x : K⟦Γ⟧) (hx : 0 < x.orderTop) :
    infExp (infLog x hx) (infLog_orderTop_pos x hx) = 1 + x := by
  have h := evaluate_subst x hx (PowerSeries.exp K) (PowerSeries.log K) (by simp)
  rw [FormalPowerSeries.exp_subst_log, map_add, map_one, evaluate_X] at h
  exact h.symm

/-- The exponential is injective on its whole positive-order domain. -/
theorem infExp_injective {x y : K⟦Γ⟧} (hx : 0 < x.orderTop) (hy : 0 < y.orderTop)
    (h : infExp x hx = infExp y hy) : x = y := by
  have hlog : infLog (infExp x hx - 1) (infExp_sub_one_pos x hx) =
      infLog (infExp y hy - 1) (infExp_sub_one_pos y hy) := by
    congr 1
    rw [h]
  simpa using hlog

/-- Every series differing from one by positive order is uniquely an
infinitesimal exponential. -/
theorem existsUnique_infExp_eq (y : K⟦Γ⟧) (hy : 0 < (y - 1).orderTop) :
    ∃! x : {x : K⟦Γ⟧ // 0 < x.orderTop}, infExp x.val x.property = y := by
  refine ⟨⟨infLog (y - 1) hy, infLog_orderTop_pos _ _⟩, ?_, ?_⟩
  · simp only [infExp_infLog, add_sub_cancel]
  · intro x hx
    apply Subtype.ext
    apply infExp_injective x.property (infLog_orderTop_pos _ _)
    simpa only [infExp_infLog, add_sub_cancel] using hx

end
end Surreal.HahnSeries
