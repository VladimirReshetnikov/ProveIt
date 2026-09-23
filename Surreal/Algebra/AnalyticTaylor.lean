import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Ordinary analytic germs as formal Taylor series

The coefficients are the ordinary iterated derivatives divided by factorials.
Analyticity identifies this formal series with a convergent local expansion.
Germ equality, addition, multiplication, and formal differentiation preserve it.
-/

namespace Surreal.Analytic

noncomputable section

variable {K : Type*} [NontriviallyNormedField K]

/-- The ordinary Taylor coefficients at the explicitly specified center. -/
def taylorSeries (f : K → K) (c : K) : PowerSeries K :=
  PowerSeries.mk (fun n => iteratedDeriv n f c / n.factorial)

@[simp] theorem coeff_taylorSeries (f : K → K) (c : K) (n : ℕ) :
    (taylorSeries f c).coeff n = iteratedDeriv n f c / n.factorial :=
  PowerSeries.coeff_mk _ _

@[simp] theorem constantCoeff_taylorSeries (f : K → K) (c : K) :
    (taylorSeries f c).constantCoeff = f c := by
  simp [taylorSeries]

variable [CompleteSpace K] [CharZero K]

/-- These are the coefficients of the actual ordinary analytic germ. -/
theorem hasFPowerSeriesAt_taylorSeries {f : K → K} {c : K}
    (hf : AnalyticAt K f c) :
    HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars K (fun n => (taylorSeries f c).coeff n)) c := by
  simpa only [coeff_taylorSeries] using hf.hasFPowerSeriesAt

/-- Any ordinary analytic power-series witness has these same coefficients. -/
theorem coeff_taylorSeries_eq_of_hasFPowerSeriesAt {f : K → K} {c : K}
    {p : FormalMultilinearSeries K K K} (hp : HasFPowerSeriesAt f p c) (n : ℕ) :
    (taylorSeries f c).coeff n = p.coeff n := by
  have h := (hasFPowerSeriesAt_taylorSeries hp.analyticAt).eq_formalMultilinearSeries hp
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using
    congrArg (fun q : FormalMultilinearSeries K K K => q.coeff n) h

omit [CompleteSpace K] [CharZero K] in
/-- Taylor coefficients depend only on the ordinary germ, not on values elsewhere. -/
theorem taylorSeries_congr {f g : K → K} {c : K} (h : f =ᶠ[nhds c] g) :
    taylorSeries f c = taylorSeries g c := by
  ext n
  simp only [coeff_taylorSeries, (h.iteratedDeriv n).eq_of_nhds]

omit [CharZero K] in
theorem taylorSeries_add {f g : K → K} {c : K}
    (hf : AnalyticAt K f c) (hg : AnalyticAt K g c) :
    taylorSeries (f + g) c = taylorSeries f c + taylorSeries g c := by
  ext n
  simp only [map_add, coeff_taylorSeries,
    iteratedDeriv_add hf.contDiffAt hg.contDiffAt, add_div]

theorem taylorSeries_mul {f g : K → K} {c : K}
    (hf : AnalyticAt K f c) (hg : AnalyticAt K g c) :
    taylorSeries (f * g) c = taylorSeries f c * taylorSeries g c := by
  ext n
  rw [coeff_taylorSeries, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [coeff_taylorSeries]
  have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hc : (n.choose i : K) * (i.factorial : K) * ((n - i).factorial : K) =
      (n.factorial : K) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  have hn : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hi : (i.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
  have hni : ((n - i).factorial : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (n - i).factorial_ne_zero
  field_simp
  linear_combination iteratedDeriv i f c * iteratedDeriv (n - i) g c * hc

omit [CompleteSpace K] [CharZero K] in
@[simp] theorem taylorSeries_const (r c : K) :
    taylorSeries (fun _ => r) c = PowerSeries.C r := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp [iteratedDeriv_const]

omit [CompleteSpace K] in
/-- Ordinary differentiation shifts the Taylor coefficients by the formal derivative rule. -/
theorem taylorSeries_deriv (f : K → K) (c : K) :
    taylorSeries (deriv f) c = PowerSeries.derivative K (taylorSeries f c) := by
  ext n
  simp only [coeff_taylorSeries, PowerSeries.coeff_derivative,
    iteratedDeriv_succ', Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hs : (n : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

omit [CompleteSpace K] in
/-- A nonzero ordinary derivative gives a nonzero formal Taylor series. -/
theorem taylorSeries_ne_zero_of_iteratedDeriv_ne_zero (f : K → K) (c : K) (m : ℕ)
    (hm : iteratedDeriv m f c ≠ 0) : taylorSeries f c ≠ 0 := by
  apply PowerSeries.exists_coeff_ne_zero_iff_ne_zero.mp
  refine ⟨m, ?_⟩
  rw [coeff_taylorSeries]
  exact div_ne_zero hm (Nat.cast_ne_zero.mpr m.factorial_ne_zero)

omit [CompleteSpace K] in
/-- The first nonzero ordinary derivative is exactly the formal Taylor order. -/
theorem order_taylorSeries_eq (f : K → K) (c : K) (m : ℕ)
    (hm : iteratedDeriv m f c ≠ 0)
    (hvan : ∀ n < m, iteratedDeriv n f c = 0) :
    (taylorSeries f c).order = m := by
  apply PowerSeries.order_eq_nat.mpr
  constructor
  · rw [coeff_taylorSeries]
    exact div_ne_zero hm (Nat.cast_ne_zero.mpr m.factorial_ne_zero)
  · intro n hn
    simp only [coeff_taylorSeries, hvan n hn, zero_div]

end

end Surreal.Analytic
