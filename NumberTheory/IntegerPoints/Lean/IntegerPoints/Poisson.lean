import IntegerPoints.EulerMaclaurin
import IntegerPoints.KuzminLandau

/-!
# Truncated Poisson summation: the exact identity

For `f ∈ C¹`, `a ≤ b` and every truncation level `N`,
`∑_{a < n ≤ b} e(f(n))
   = ∑_{|k| ≤ N} ∫_a^b e(f(x) + kx) dx
     + (ψ(a) + S_N(a)) e(f(a)) − (ψ(b) + S_N(b)) e(f(b))
     + ∫_a^b (ψ(x) + S_N(x)) (e∘f)'(x) dx`,
where `ψ` is the sawtooth and `S_N(x) = ∑_{h=1}^N sin(2πhx)/(πh)` its truncated Fourier
series (`Sawtooth.S`).  This follows from the first-order Euler–Maclaurin formula
(`EM.sum_eq_integral`) by integrating `S_N (e∘f)'` by parts term by term, since
`2 cos(2πhx) e(f(x)) = e(f(x) + hx) + e(f(x) − hx)`.

We also record the uniform bound `|S_N| ≤ 4`.
-/

open Real Finset intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace PS

open Sawtooth EM

/-- The derivative of `e ∘ f`. -/
theorem hasDerivAt_e_comp {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => e (f x)) (2 * π * Complex.I * f' * e (f x)) x := by
  unfold e
  have h1 : HasDerivAt (fun x : ℝ => ((f x : ℝ) : ℂ)) (f' : ℂ) x := hf.ofReal_comp
  have h2 := (h1.const_mul (2 * π * Complex.I)).cexp
  refine h2.congr_deriv ?_
  ring

theorem continuous_e_comp {f : ℝ → ℝ} (hf : Continuous f) : Continuous fun x => e (f x) := by
  unfold e
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hf))

/-- `e(t + c) + e(t − c) = 2 cos(2πc) e(t)`. -/
theorem e_add_add_e_sub (t c : ℝ) :
    e (t + c) + e (t - c) = ((2 * Real.cos (2 * π * c) : ℝ) : ℂ) * e t := by
  rw [KL.e_add, sub_eq_add_neg, KL.e_add, ← mul_add, KL.e_eq c, KL.e_eq (-c),
    show 2 * π * -c = -(2 * π * c) by ring, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- The derivative `(e∘f)' = 2πi f' e(f)` for `f ∈ C¹`. -/
noncomputable def eD (f : ℝ → ℝ) (x : ℝ) : ℂ := 2 * π * Complex.I * (deriv f x) * e (f x)

theorem hasDerivAt_e_comp' {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝ) :
    HasDerivAt (fun x => e (f x)) (eD f x) x :=
  hasDerivAt_e_comp (hf.differentiable one_ne_zero x).hasDerivAt

theorem continuous_eD {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (eD f) := by
  unfold eD
  have h1 : Continuous (deriv f) := hf.continuous_deriv le_rfl
  exact (continuous_const.mul (Complex.continuous_ofReal.comp h1)).mul
    (continuous_e_comp hf.continuous)

/-- Integration by parts for one term of the sawtooth series. -/
theorem parts_sin {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (a b : ℝ) (k : ℕ) :
    ∫ x in a..b, ((Real.sin (2 * π * (k + 1) * x) / (π * (k + 1)) : ℝ) : ℂ) * eD f x =
      ((Real.sin (2 * π * (k + 1) * b) / (π * (k + 1)) : ℝ) : ℂ) * e (f b) -
        ((Real.sin (2 * π * (k + 1) * a) / (π * (k + 1)) : ℝ) : ℂ) * e (f a) -
        ∫ x in a..b, (e (f x + (k + 1) * x) + e (f x - (k + 1) * x)) := by
  have hk : (π * (k + 1) : ℝ) ≠ 0 := by positivity
  have hu : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ => ((Real.sin (2 * π * (k + 1) * x) / (π * (k + 1)) : ℝ) : ℂ))
        (((2 * Real.cos (2 * π * (k + 1) * x) : ℝ) : ℂ)) x := by
    intro x _
    have := ((((hasDerivAt_id x).const_mul (2 * π * (k + 1))).sin).div_const (π * (k + 1))).ofReal_comp
    refine this.congr_deriv ?_
    simp only [id]
    congr 1
    first | (field_simp; done) | (field_simp; ring)
  have hv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => e (f x)) (eD f x) x :=
    fun x _ => hasDerivAt_e_comp' hf x
  have hcos : Continuous fun x : ℝ => (((2 * Real.cos (2 * π * (k + 1) * x) : ℝ) : ℂ)) := by
    fun_prop
  have h := integral_mul_deriv_eq_deriv_mul hu hv (hcos.intervalIntegrable _ _)
    ((continuous_eD hf).intervalIntegrable _ _)
  rw [h]
  congr 1
  apply integral_congr
  intro x _
  simp only
  rw [e_add_add_e_sub, show 2 * π * ((k + 1 : ℝ) * x) = 2 * π * (k + 1) * x by ring]

/-- `∫_a^b S_N (e∘f)' = S_N(b)e(f(b)) − S_N(a)e(f(a)) − ∑_{h<N} ∫_a^b (e(f+(h+1)x) + e(f−(h+1)x))`. -/
theorem integral_S_mul {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (a b : ℝ) (N : ℕ) :
    ∫ x in a..b, ((S N x : ℝ) : ℂ) * eD f x =
      ((S N b : ℝ) : ℂ) * e (f b) - ((S N a : ℝ) : ℂ) * e (f a) -
        ∑ k ∈ Finset.range N, ∫ x in a..b, (e (f x + (k + 1) * x) + e (f x - (k + 1) * x)) := by
  have hint : ∀ k ∈ Finset.range N, IntervalIntegrable
      (fun x => ((Real.sin (2 * π * (k + 1) * x) / (π * (k + 1)) : ℝ) : ℂ) * eD f x) volume a b := by
    intro k _
    apply Continuous.intervalIntegrable
    have : Continuous fun x : ℝ => ((Real.sin (2 * π * (k + 1) * x) / (π * (k + 1)) : ℝ) : ℂ) := by
      fun_prop
    exact this.mul (continuous_eD hf)
  have h1 : ∀ x, ((S N x : ℝ) : ℂ) * eD f x =
      ∑ k ∈ Finset.range N, ((Real.sin (2 * π * (k + 1) * x) / (π * (k + 1)) : ℝ) : ℂ) * eD f x := by
    intro x
    unfold S
    push_cast
    rw [Finset.sum_mul]
  simp_rw [h1]
  rw [integral_finset_sum hint]
  rw [Finset.sum_congr rfl (fun k _ => parts_sin hf a b k)]
  unfold S
  push_cast
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]

/-- **The exact truncated Poisson identity.** -/
theorem identity {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {a b : ℝ} (hab : a ≤ b) (N : ℕ) :
    ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, e (f n) =
      ((∫ x in a..b, e (f x)) +
          ∑ k ∈ Finset.range N, ∫ x in a..b, (e (f x + (k + 1) * x) + e (f x - (k + 1) * x))) +
        ((ψ a + S N a : ℝ) : ℂ) * e (f a) - ((ψ b + S N b : ℝ) : ℂ) * e (f b) +
        ∫ x in a..b, ((ψ x + S N x : ℝ) : ℂ) * eD f x := by
  have hS : Continuous (S N) := continuous_iff_continuousAt.2 fun x => (hasDerivAt_S N x).continuousAt
  have hEM := EM.sum_eq_integral (F := fun x => e (f x)) (F' := eD f)
    (fun x => hasDerivAt_e_comp' hf x) (continuous_eD hf) (continuous_e_comp hf.continuous) hab
  have hsplit : ∫ x in a..b, ((ψ x + S N x : ℝ) : ℂ) * eD f x =
      (∫ x in a..b, (ψ x : ℂ) * eD f x) + ∫ x in a..b, ((S N x : ℝ) : ℂ) * eD f x := by
    have hSi : IntervalIntegrable (fun x => ((S N x : ℝ) : ℂ) * eD f x) volume a b :=
      ((Complex.continuous_ofReal.comp hS).mul (continuous_eD hf)).intervalIntegrable _ _
    rw [← integral_add (EM.intervalIntegrable_ψ_mul (continuous_eD hf) a b) hSi]
    apply integral_congr
    intro x _
    simp only
    push_cast
    ring
  rw [hEM, hsplit, integral_S_mul hf a b N]
  push_cast
  ring

end PS

end LeanProofs.IntegerPoints
