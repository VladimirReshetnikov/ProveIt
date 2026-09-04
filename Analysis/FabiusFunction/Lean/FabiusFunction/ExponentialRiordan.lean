import FabiusFunction.BellGeneratingFunctions
import FabiusFunction.StirlingGeneratingFunctions

/-!
# Exponential Riordan arrays

An exponential Riordan array `[g, f]` (with `f` of constant term zero) is the
infinite lower-triangular matrix with entries

`R_{n,k} = (n!/k!) [t^n] g(t) f(t)^k`,

i.e. whose `k`-th column has exponential generating function `g f^k / k!`.
Its action on a sequence `a` with exponential generating function `A(t)` is

`∑_k R_{n,k} a_k  has EGF  g(t) A(f(t))`,

from which the product law `[g, f][h, l] = [g · (h ∘ f), l ∘ f]` and the
inverse law follow.  The Stirling matrices are the arrays `[1, e^t - 1]` and
`[1, log(1 + t)]`.

## Main results

* `expRiordan`, `coeff_mul_pow_eq_zero_of_lt`, `coeff_mul_subst_eq`.
* `expRiordan_action`: the action on exponential generating functions.
* `expRiordan_mul`: the product law; `expRiordan_one_X`: the identity array.
* `expRiordan_mul_inverse`: `[g, f]` times `[h, f̄]` is the identity when `f̄` is
  the compositional inverse of `f` and `g · (h ∘ f) = 1`.
* `expRiordan_one_exp_sub_one`, `expRiordan_one_log`: the Stirling matrices.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The exponential Riordan array `[g, f]`: `R_{n,k} = (n!/k!) [t^n] (g · f^k)`. -/
noncomputable def expRiordan (g f : A⟦X⟧) (n k : ℕ) : A :=
  algebraMap ℚ A (n.factorial / k.factorial) * coeff n (g * f ^ k)

omit [Algebra ℚ A] in
/-- If `f` has constant term zero then `g · f^d` has no terms below degree `d`. -/
theorem coeff_mul_pow_eq_zero_of_lt {f : A⟦X⟧} (hf : constantCoeff f = 0) (g : A⟦X⟧)
    {m d : ℕ} (h : m < d) : coeff m (g * f ^ d) = 0 := by
  obtain ⟨f', hf'⟩ := X_dvd_iff.mpr hf
  rw [hf', mul_pow, mul_left_comm, coeff_X_pow_mul', if_neg (not_le.mpr h)]

omit [Algebra ℚ A] in
/-- Coefficients of `g · φ(f)` through the truncated expansion of `φ`:
`[t^n] g · φ(f) = ∑_{d ≤ n} [t^d] φ · [t^n] g f^d`. -/
theorem coeff_mul_subst_eq {f : A⟦X⟧} (hf : constantCoeff f = 0) (g φ : A⟦X⟧) (n : ℕ) :
    coeff n (g * φ.subst f) = ∑ d ∈ Finset.range (n + 1), coeff d φ * coeff n (g * f ^ d) := by
  have hf' : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  set T : A⟦X⟧ := ∑ d ∈ Finset.range (n + 1), PowerSeries.C (coeff d φ) * f ^ d with hTdef
  have hT : ∀ m, m ≤ n → coeff m (φ.subst f) = coeff m T := by
    intro m hm
    have hsupp : Function.support (fun d : ℕ => coeff d φ • coeff m (f ^ d)) ⊆
        ↑(Finset.range (n + 1)) := by
      intro d hd
      rw [Function.mem_support] at hd
      by_contra hdn
      apply hd
      rw [Finset.mem_coe, Finset.mem_range, not_lt] at hdn
      have := coeff_mul_pow_eq_zero_of_lt A hf 1 (show m < d by omega)
      rw [one_mul] at this
      rw [this, smul_zero]
    rw [coeff_subst' hf', finsum_eq_sum_of_support_subset _ hsupp, hTdef, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [coeff_C_mul, smul_eq_mul]
  have h1 : coeff n (g * φ.subst f) = coeff n (g * T) := by
    rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp2 : p.2 ≤ n := by
      have := Finset.mem_antidiagonal.mp hp
      omega
    rw [hT p.2 hp2]
  rw [h1, hTdef, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_left_comm, coeff_C_mul]

/-- **Action of an exponential Riordan array:** if `f` has constant term zero,
`g · A(f)` is the exponential generating function of `n ↦ ∑_{k ≤ n} R_{n,k} a_k`. -/
theorem expRiordan_action {f : A⟦X⟧} (hf : constantCoeff f = 0) (g : A⟦X⟧) (a : ℕ → A) :
    g * (egfA A a).subst f =
      egfA A fun n => ∑ k ∈ Finset.range (n + 1), expRiordan A g f n k * a k := by
  ext n
  rw [coeff_mul_subst_eq A hf, coeff_egfA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_egfA, expRiordan]
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  have h : algebraMap ℚ A (1 / n.factorial) * algebraMap ℚ A (n.factorial / k.factorial)
      = algebraMap ℚ A (1 / k.factorial) := by
    rw [← map_mul]
    congr 1
    field_simp
  calc algebraMap ℚ A (1 / k.factorial) * a k * coeff n (g * f ^ k)
      = (algebraMap ℚ A (1 / n.factorial) * algebraMap ℚ A (n.factorial / k.factorial)) *
          (coeff n (g * f ^ k) * a k) := by rw [h]; ring
    _ = _ := by ring

/-- The `k`-th column of `[g, f]` has exponential generating function `g f^k / k!`. -/
theorem egfA_expRiordan_column (g f : A⟦X⟧) (k : ℕ) :
    egfA A (fun n => expRiordan A g f n k) = algebraMap ℚ A (1 / k.factorial) • (g * f ^ k) := by
  ext n
  rw [coeff_egfA, expRiordan, PowerSeries.coeff_smul, smul_eq_mul, ← mul_assoc, ← map_mul]
  congr 2
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp

/-- **Product law of exponential Riordan arrays:**
`[g, f] · [h, l] = [g · (h ∘ f), l ∘ f]` entrywise. -/
theorem expRiordan_mul {f l : A⟦X⟧} (hf : constantCoeff f = 0) (hl : constantCoeff l = 0)
    (g h : A⟦X⟧) (n k : ℕ) :
    ∑ j ∈ Finset.range (n + 1), expRiordan A g f n j * expRiordan A h l j k =
      expRiordan A (g * h.subst f) (l.subst f) n k := by
  have hf' : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  have hact := expRiordan_action A hf g (fun j => expRiordan A h l j k)
  rw [egfA_expRiordan_column, subst_smul hf', subst_mul hf', subst_pow hf'] at hact
  have hc := congrArg (coeff n) hact
  rw [coeff_egfA, mul_smul_comm, PowerSeries.coeff_smul, smul_eq_mul] at hc
  -- `hc : c_k * coeff n (g * (h∘f) * (l∘f)^k) = (1/n!) * ∑_j R^{g,f}_{n,j} R^{h,l}_{j,k}`
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  have hinv : algebraMap ℚ A (n.factorial) * algebraMap ℚ A (1 / n.factorial) = 1 := by
    rw [← map_mul, mul_one_div_cancel hn, map_one]
  have hfac : algebraMap ℚ A (n.factorial) * algebraMap ℚ A (1 / k.factorial)
      = algebraMap ℚ A (n.factorial / k.factorial) := by
    rw [← map_mul]
    congr 1
    field_simp
  calc ∑ j ∈ Finset.range (n + 1), expRiordan A g f n j * expRiordan A h l j k
      = algebraMap ℚ A (n.factorial) * (algebraMap ℚ A (1 / n.factorial) *
          ∑ j ∈ Finset.range (n + 1), expRiordan A g f n j * expRiordan A h l j k) := by
        rw [← mul_assoc, hinv, one_mul]
    _ = algebraMap ℚ A (n.factorial) * (algebraMap ℚ A (1 / k.factorial) *
          coeff n (g * (h.subst f * l.subst f ^ k))) := by rw [← hc]
    _ = _ := by
        rw [expRiordan, ← mul_assoc (algebraMap ℚ A (n.factorial : ℚ)), hfac, mul_assoc g]

/-- The array `[1, t]` is the identity matrix. -/
theorem expRiordan_one_X (n k : ℕ) : expRiordan A 1 X n k = if n = k then 1 else 0 := by
  rw [expRiordan, one_mul, coeff_X_pow]
  split_ifs with h
  · subst h
    have hn : (n.factorial : ℚ) ≠ 0 := by positivity
    rw [div_self hn, map_one, mul_one]
  · rw [mul_zero]

/-- **Inverse law:** if `f̄` is the compositional inverse of `f` and `g · (h ∘ f) = 1`,
then `[g, f] · [h, f̄]` is the identity; in particular `[g, f]⁻¹ = [1/(g ∘ f̄), f̄]`. -/
theorem expRiordan_mul_inverse {f fi : A⟦X⟧} (hf : constantCoeff f = 0)
    (hfi : constantCoeff fi = 0) (hcomp : fi.subst f = X) (g h : A⟦X⟧)
    (hgh : g * h.subst f = 1) (n k : ℕ) :
    ∑ j ∈ Finset.range (n + 1), expRiordan A g f n j * expRiordan A h fi j k =
      if n = k then 1 else 0 := by
  rw [expRiordan_mul A hf hfi, hgh, hcomp, expRiordan_one_X]

/-! ### The Stirling matrices -/

/-- The second-kind Stirling matrix is the exponential Riordan array `[1, e^t - 1]`. -/
theorem expRiordan_one_exp_sub_one (n k : ℕ) :
    expRiordan A 1 (exp A - 1) n k = Nat.stirlingSecond n k := by
  rw [expRiordan, one_mul, exp_sub_one_pow, coeff_egf, ← map_mul]
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  rw [show (n.factorial : ℚ) / k.factorial * (k.factorial * Nat.stirlingSecond n k / n.factorial)
      = (Nat.stirlingSecond n k : ℚ) by field_simp]
  simp

/-- The signed first-kind Stirling matrix is the exponential Riordan array `[1, log(1 + t)]`. -/
theorem expRiordan_one_log (n k : ℕ) :
    expRiordan A 1 (log A) n k = algebraMap ℚ A (signedStirlingFirst n k) := by
  rw [expRiordan, one_mul, log_pow, coeff_egf, ← map_mul]
  congr 1
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  field_simp

end

end Fabius
