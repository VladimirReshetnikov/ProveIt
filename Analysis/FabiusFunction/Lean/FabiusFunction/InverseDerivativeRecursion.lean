import FabiusFunction.BellComposition
import FabiusFunction.AutonomousIteratedDeriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Derivatives of an inverse function: the Bell recursion and the operator form

Two results of the combinatorial coefficient calculus manuscript, in the chapter
*Coordinate-free composition and derivatives of inverse maps*:

* `thm:merged-inverse-derivative` (**Inverse derivative recursion**): if `g = f⁻¹` then, for
  `n ≥ 2`,
  `g^{(n)} = -(1/f') ∑_{k=2}^{n} f^{(k)} B_{n,k}(g', g'', …, g^{(n-k+1)})`,
  all derivatives of `f` taken at `x = g(y)`; and the four explicit forms
  `g' = 1/f'`, `g'' = -f''/f'^3`, `g''' = (3f''^2 - f'f''')/f'^5`,
  `g'''' = (-15f''^3 + 10f'f''f''' - f'^2 f'''')/f'^7`.
* `thm:merged-inverse-derivative-operator` (**Inverse-derivative operator**): for `n ≥ 1`,
  `g^{(n)}(y) = ((1/f') d/dx)^{n-1} (1/f') |_{x = g(y)}`.

## The two settings, and why each result lives where it does

The recursion is the `n`-th coefficient of the identity `f ∘ g = id` under Faà di Bruno, and it
uses nothing about `f` and `g` except that composition acts on exponential coefficients through
partial Bell polynomials.  Its honest formal home is therefore the ring of formal power series,
where the corpus already has the exponential composition theorem
`Fabius.egfA_subst_bellWeightSeries`: with `f = ∑ f_k w^k/k!` and `g = ∑ g_n z^n/n!` (a
series with no constant term, `bellWeightSeries`), the hypothesis `f(g) = z` says exactly that
`∑_{k ≤ n} f_k B_{n,k}(g) = [n = 1]`.  The `k = 0` term vanishes for `n ≥ 1`, the `k = 1` term is
`f_1 g_n`, and what is left is the recursion (`InverseDerivative.mul_eq_neg_sum`,
`InverseDerivative.eq_neg_mul_sum`), over any commutative `ℚ`-algebra, with no inverse of `f_1`
needed for the division-free form.  The "derivatives at the point" of the manuscript are the
Taylor coefficients `f_k = f^{(k)}(g(y))`, `g_n = g^{(n)}(y)`; the analytic statement is this one
read through Taylor's formula and the analytic Faà di Bruno formula in Bell form, which the
corpus does not have and which is **not** proved here.

The operator form, on the other hand, is a statement about iterated *derivatives* of a real
function and is proved analytically.  The insight it exposes is that it is not about inverses at
all: it is the autonomous-equation lemma `AutonomousODE.iteratedDeriv_eq_comp` (module
`AutonomousIteratedDeriv`) for the equation `g' = φ ∘ g` with `φ = 1/f'`.  Once `g' = (1/f')(g)`
is known (that is the inverse function rule `HasDerivAt.of_local_left_inverse`), every higher
derivative of `g` is `G_n ∘ g` with `G_0 = id` and `G_{n+1} = G_n' · (1/f')`, which is precisely
the operator `(1/f') d/dx` iterated on the identity function — equivalently, `n-1` times on
`1/f'` (`inverseDerivOp_succ_eq_iterate`).  The smoothness needed to differentiate `G_n` is
`ContDiffOn ℝ ∞ f U` with `f' ≠ 0` on `U`.

## Main results

* `InverseDerivative.partialBell_succ_one`, `partialBell_one_right`,
  `InverseDerivative.bellWeightSeries_factorial_coeff`,
  `InverseDerivative.sum_mul_partialBell_eq`.
* `InverseDerivative.mul_eq_neg_sum`, `InverseDerivative.eq_neg_mul_sum`,
  `InverseDerivative.factorial_coeff_eq` — the recursion (`thm:merged-inverse-derivative`).
* `InverseDerivative.one_eq`, `two_eq`, `three_eq`, `four_eq` — the four explicit forms
  (`eq:merged-inverse-first-four`), with the small Bell values `partialBell_three_two`,
  `partialBell_four_two`, `partialBell_four_three`.
* `InverseDerivative.inverseDerivOp`, `inverseDerivOp_succ_eq_iterate`,
  `contDiffOn_inverseDerivOp`, `hasDerivAt_of_local_left_inverse`,
  `iteratedDeriv_eq_inverseDerivOp` — the operator form
  (`thm:merged-inverse-derivative-operator`), and its `n = 1, 2` readings
  `deriv_eq_inv_deriv`, `iteratedDeriv_two_eq`.

## Not covered

The analytic Bell recursion for `iteratedDeriv n g` (it needs the analytic Faà di Bruno formula
in partial-Bell form); the explicit forms `g'''`, `g''''` as statements about `iteratedDeriv`
(they are proved for the Taylor coefficients).
-/

set_option autoImplicit false

open Finset PowerSeries Filter Topology
open scoped ContDiff

namespace Fabius

namespace InverseDerivative

/-! ### Formal setting: the coefficient recursion -/

section Formal

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- `B_{n+1,1}(x) = x_{n+1}`: the only partition into one block is the whole set. -/
theorem partialBell_succ_one (x : ℕ → A) (n : ℕ) : partialBell x (n + 1) 1 = x (n + 1) := by
  rw [partialBell_succ_succ, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Nat.choose_self,
    Nat.sub_self, partialBell_zero_zero, Nat.cast_one, one_mul, mul_one]
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  obtain ⟨m, hm⟩ : ∃ m, n - i = m + 1 := ⟨n - i - 1, by omega⟩
  rw [hm, partialBell_succ_zero, mul_zero, mul_zero]

/-- `B_{n,1}(x) = x_n` for `n ≠ 0`, stated so that a numeral `n` rewrites to the same numeral. -/
theorem partialBell_one_right (x : ℕ → A) {n : ℕ} (hn : n ≠ 0) : partialBell x n 1 = x n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact partialBell_succ_one x m

/-- `B_{3,2}(x) = 3 x_1 x_2`. -/
theorem partialBell_three_two (x : ℕ → A) : partialBell x 3 2 = 3 * (x 1 * x 2) := by
  rw [partialBell_succ_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [partialBell_succ_one, partialBell_self, partialBell_eq_zero_of_lt]
  ring

/-- `B_{4,2}(x) = 4 x_1 x_3 + 3 x_2^2`. -/
theorem partialBell_four_two (x : ℕ → A) :
    partialBell x 4 2 = 4 * (x 1 * x 3) + 3 * x 2 ^ 2 := by
  have h32 : Nat.choose 3 2 = 3 := by decide
  rw [partialBell_succ_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [partialBell_succ_one, partialBell_self, partialBell_eq_zero_of_lt, h32]
  ring

/-- `B_{4,3}(x) = 6 x_1^2 x_2`. -/
theorem partialBell_four_three (x : ℕ → A) : partialBell x 4 3 = 6 * (x 1 ^ 2 * x 2) := by
  have h32 : Nat.choose 3 2 = 3 := by decide
  rw [partialBell_succ_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [partialBell_succ_one, partialBell_three_two, partialBell_self,
    partialBell_eq_zero_of_lt, h32]
  ring

/-- `(1/n!) · n! = 1` in a `ℚ`-algebra. -/
private theorem algebraMap_one_div_factorial_mul (n : ℕ) :
    algebraMap ℚ A (1 / n.factorial) * (n.factorial : A) = 1 := by
  rw [show (n.factorial : A) = algebraMap ℚ A (n.factorial : ℚ) by simp, ← map_mul,
    one_div_mul_cancel (by positivity), map_one]

/-- Every series without constant term is the Bell weight series of its exponential
coefficients `n! [z^n] g`; this is what lets the recursion be stated for an arbitrary
series `g` rather than for one presented by its exponential coefficients. -/
theorem bellWeightSeries_factorial_coeff (g : A⟦X⟧) (h0 : constantCoeff g = 0) :
    bellWeightSeries A (fun n => (n.factorial : A) * coeff n g) = g := by
  ext n
  rw [bellWeightSeries, coeff_egfA]
  cases n with
  | zero =>
    rw [if_pos rfl, mul_zero, coeff_zero_eq_constantCoeff_apply, h0]
  | succ n =>
    rw [if_neg (Nat.add_one_ne_zero n), ← mul_assoc, algebraMap_one_div_factorial_mul, one_mul]

variable (fc gc : ℕ → A)

/-- **Coefficient extraction from `f(g) = z`:** with `f = ∑ f_k w^k/k!` and
`g = ∑ g_n z^n/n!`, the exponential composition theorem turns `f(g) = z` into
`∑_{k ≤ n} f_k B_{n,k}(g_1, g_2, …) = [n = 1]` for every `n`. -/
theorem sum_mul_partialBell_eq (hfg : (egfA A fc).subst (bellWeightSeries A gc) = X) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), fc k * partialBell gc n k = if n = 1 then 1 else 0 := by
  have h : algebraMap ℚ A (1 / n.factorial) *
      ∑ k ∈ Finset.range (n + 1), fc k * partialBell gc n k = if n = 1 then 1 else 0 := by
    have h' := congrArg (coeff n) hfg
    rwa [egfA_subst_bellWeightSeries, coeff_egfA, PowerSeries.coeff_X] at h'
  calc ∑ k ∈ Finset.range (n + 1), fc k * partialBell gc n k
      = ((n.factorial : A) * algebraMap ℚ A (1 / n.factorial)) *
          ∑ k ∈ Finset.range (n + 1), fc k * partialBell gc n k := by
        rw [mul_comm (n.factorial : A), algebraMap_one_div_factorial_mul, one_mul]
    _ = (n.factorial : A) * (if n = 1 then 1 else 0) := by rw [mul_assoc, h]
    _ = if n = 1 then 1 else 0 := by
        split_ifs with h1
        · subst h1
          simp
        · simp

/-- The recursion in `range` form, `n = m + 2`:
`f_1 g_{m+2} = -∑_{k < m+1} f_{k+2} B_{m+2,k+2}(g)`. -/
theorem mul_eq_neg_sum_range (hfg : (egfA A fc).subst (bellWeightSeries A gc) = X) (m : ℕ) :
    fc 1 * gc (m + 2) =
      -∑ k ∈ Finset.range (m + 1), fc (k + 2) * partialBell gc (m + 2) (k + 2) := by
  have h := sum_mul_partialBell_eq fc gc hfg (m + 2)
  rw [if_neg (show m + 2 ≠ 1 by omega), Finset.sum_range_succ', Finset.sum_range_succ', zero_add,
    partialBell_succ_zero, mul_zero, add_zero,
    partialBell_one_right gc (show m + 2 ≠ 0 by omega)] at h
  have hsum : ∑ i ∈ Finset.range (m + 1), fc (i + 1 + 1) * partialBell gc (m + 2) (i + 1 + 1)
      = ∑ k ∈ Finset.range (m + 1), fc (k + 2) * partialBell gc (m + 2) (k + 2) :=
    Finset.sum_congr rfl fun k _ => rfl
  rw [hsum] at h
  linear_combination h

/-- **Inverse derivative recursion, division-free** (`thm:merged-inverse-derivative`):
if `f(g) = z` then for `n ≥ 2`
`f_1 g_n = -∑_{k=2}^{n} f_k B_{n,k}(g_1, …, g_{n-k+1})`,
where `f_k = f^{(k)}(g(y))` and `g_n = g^{(n)}(y)` are the exponential coefficients.  The
partial Bell polynomial `B_{n,k}` only involves `g_1, …, g_{n-k+1}`, so the right side involves
only `g_1, …, g_{n-1}`: this is a recursion. -/
theorem mul_eq_neg_sum (hfg : (egfA A fc).subst (bellWeightSeries A gc) = X) (n : ℕ)
    (hn : 2 ≤ n) :
    fc 1 * gc n = -∑ k ∈ Finset.Icc 2 n, fc k * partialBell gc n k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [mul_eq_neg_sum_range fc gc hfg m]
  congr 1
  have hIcc : Finset.Icc 2 (m + 2) = Finset.Ico 2 (m + 2 + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range, show m + 2 + 1 - 2 = m + 1 by omega]
  exact Finset.sum_congr rfl fun k _ => by rw [Nat.add_comm k 2]

/-- **Inverse derivative recursion** (`thm:merged-inverse-derivative`), solved for `g_n` with
an inverse `f₁inv` of `f_1 = f'(g(y))`:
`g_n = -(1/f_1) ∑_{k=2}^{n} f_k B_{n,k}(g_1, …, g_{n-k+1})` for `n ≥ 2`. -/
theorem eq_neg_mul_sum (hfg : (egfA A fc).subst (bellWeightSeries A gc) = X) {f₁inv : A}
    (hf1 : fc 1 * f₁inv = 1) (n : ℕ) (hn : 2 ≤ n) :
    gc n = -(f₁inv * ∑ k ∈ Finset.Icc 2 n, fc k * partialBell gc n k) := by
  have h := mul_eq_neg_sum fc gc hfg n hn
  linear_combination f₁inv * h - gc n * hf1

/-- The recursion for an arbitrary series `g` with `f(g) = z`, in terms of its exponential
coefficients `n! [z^n] g`. -/
theorem factorial_coeff_eq (g : A⟦X⟧) (h0 : constantCoeff g = 0)
    (hfg : (egfA A fc).subst g = X) {f₁inv : A} (hf1 : fc 1 * f₁inv = 1) (n : ℕ) (hn : 2 ≤ n) :
    (n.factorial : A) * coeff n g =
      -(f₁inv * ∑ k ∈ Finset.Icc 2 n,
        fc k * partialBell (fun j => (j.factorial : A) * coeff j g) n k) :=
  eq_neg_mul_sum fc (fun j => (j.factorial : A) * coeff j g)
    (by rw [bellWeightSeries_factorial_coeff g h0]; exact hfg) hf1 n hn

/-! #### The first four inverse derivatives (`eq:merged-inverse-first-four`) -/

/-- `g' = 1/f'`. -/
theorem one_eq (hfg : (egfA A fc).subst (bellWeightSeries A gc) = X) {f₁inv : A}
    (hf1 : fc 1 * f₁inv = 1) : gc 1 = f₁inv := by
  have h := sum_mul_partialBell_eq fc gc hfg 1
  rw [if_pos rfl, Finset.sum_range_succ, Finset.sum_range_one, partialBell_succ_zero, mul_zero,
    zero_add, partialBell_self, pow_one] at h
  linear_combination f₁inv * h - gc 1 * hf1

/-- `g'' = -f''/f'^3`. -/
theorem two_eq (hfg : (egfA A fc).subst (bellWeightSeries A gc) = X) {f₁inv : A}
    (hf1 : fc 1 * f₁inv = 1) : gc 2 = -(fc 2 * f₁inv ^ 3) := by
  have h := sum_mul_partialBell_eq fc gc hfg 2
  rw [if_neg (show (2 : ℕ) ≠ 1 by norm_num), Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, partialBell_succ_zero, mul_zero, zero_add,
    partialBell_one_right gc (show (2 : ℕ) ≠ 0 by norm_num), partialBell_self,
    one_eq fc gc hfg hf1] at h
  linear_combination f₁inv * h - gc 2 * hf1

/-- `g''' = (3 f''^2 - f' f''')/f'^5`. -/
theorem three_eq (hfg : (egfA A fc).subst (bellWeightSeries A gc) = X) {f₁inv : A}
    (hf1 : fc 1 * f₁inv = 1) : gc 3 = (3 * fc 2 ^ 2 - fc 1 * fc 3) * f₁inv ^ 5 := by
  have h := sum_mul_partialBell_eq fc gc hfg 3
  rw [if_neg (show (3 : ℕ) ≠ 1 by norm_num), Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one, partialBell_succ_zero, mul_zero, zero_add,
    partialBell_one_right gc (show (3 : ℕ) ≠ 0 by norm_num), partialBell_three_two,
    partialBell_self, one_eq fc gc hfg hf1, two_eq fc gc hfg hf1] at h
  linear_combination f₁inv * h + (fc 3 * f₁inv ^ 4 - gc 3) * hf1

/-- `g'''' = (-15 f''^3 + 10 f' f'' f''' - f'^2 f'''')/f'^7`. -/
theorem four_eq (hfg : (egfA A fc).subst (bellWeightSeries A gc) = X) {f₁inv : A}
    (hf1 : fc 1 * f₁inv = 1) :
    gc 4 = (-15 * fc 2 ^ 3 + 10 * fc 1 * fc 2 * fc 3 - fc 1 ^ 2 * fc 4) * f₁inv ^ 7 := by
  have h := sum_mul_partialBell_eq fc gc hfg 4
  rw [if_neg (show (4 : ℕ) ≠ 1 by norm_num), Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, partialBell_succ_zero,
    mul_zero, zero_add, partialBell_one_right gc (show (4 : ℕ) ≠ 0 by norm_num),
    partialBell_four_two, partialBell_four_three, partialBell_self, one_eq fc gc hfg hf1,
    two_eq fc gc hfg hf1, three_eq fc gc hfg hf1] at h
  linear_combination f₁inv * h +
    (-6 * fc 2 * fc 3 * f₁inv ^ 6 + fc 4 * f₁inv ^ 5 * (fc 1 * f₁inv + 1) - gc 4) * hf1

end Formal

/-! ### Analytic setting: the inverse-derivative operator -/

section Analytic

variable {f g : ℝ → ℝ} {U s : Set ℝ}

/-- The operator `(1/f') d/dx`: `G ↦ G' · (1/f')`. -/
noncomputable def inverseDerivStep (f : ℝ → ℝ) (G : ℝ → ℝ) : ℝ → ℝ :=
  fun x => deriv G x * (deriv f x)⁻¹

/-- **The inverse-derivative operator iterated on the identity:** `G_0 = id` and
`G_{n+1} = (1/f') d/dx G_n`.  So `G_1 = 1/f'`, `G_2 = (1/f') d/dx (1/f')`, and in general
`G_n = ((1/f') d/dx)^{n-1} (1/f')` for `n ≥ 1` (`inverseDerivOp_succ_eq_iterate`). -/
noncomputable def inverseDerivOp (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => x
  | n + 1 => fun x => deriv (inverseDerivOp f n) x * (deriv f x)⁻¹

/-- `G_0 = id`. -/
theorem inverseDerivOp_zero (f : ℝ → ℝ) : inverseDerivOp f 0 = fun x => x := rfl

/-- `G_{n+1} = G_n' · (1/f')`. -/
theorem inverseDerivOp_succ (f : ℝ → ℝ) (n : ℕ) :
    inverseDerivOp f (n + 1) = fun x => deriv (inverseDerivOp f n) x * (deriv f x)⁻¹ := rfl

/-- `G_1 = 1/f'`. -/
theorem inverseDerivOp_one (f : ℝ → ℝ) : inverseDerivOp f 1 = fun x => (deriv f x)⁻¹ := by
  funext x
  rw [inverseDerivOp_succ, inverseDerivOp_zero, deriv_id'']
  exact one_mul _

/-- **The manuscript's operator form:** `G_{n+1} = ((1/f') d/dx)^n (1/f')`. -/
theorem inverseDerivOp_succ_eq_iterate (f : ℝ → ℝ) (n : ℕ) :
    inverseDerivOp f (n + 1) = (inverseDerivStep f)^[n] (inverseDerivOp f 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rfl

/-- On an open set where `f` is `C^∞` with `f' ≠ 0`, every `G_n` is `C^∞`. -/
theorem contDiffOn_inverseDerivOp (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hf' : ∀ x ∈ U, deriv f x ≠ 0) (n : ℕ) : ContDiffOn ℝ ∞ (inverseDerivOp f n) U := by
  have hfd : ContDiffOn ℝ ∞ (deriv f) U := ((contDiffOn_infty_iff_deriv_of_isOpen hU).mp hf).2
  have hinv : ContDiffOn ℝ ∞ (fun x => (deriv f x)⁻¹) U := hfd.inv hf'
  induction n with
  | zero => exact contDiffOn_id
  | succ n ih =>
    have hd : ContDiffOn ℝ ∞ (deriv (inverseDerivOp f n)) U :=
      ((contDiffOn_infty_iff_deriv_of_isOpen hU).mp ih).2
    exact hd.mul hinv

/-- Each `G_n` is differentiable at every point of `U`. -/
theorem differentiableAt_inverseDerivOp (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hf' : ∀ x ∈ U, deriv f x ≠ 0) (n : ℕ) {x : ℝ} (hx : x ∈ U) :
    DifferentiableAt ℝ (inverseDerivOp f n) x :=
  ((contDiffOn_infty_iff_deriv_of_isOpen hU).mp
    (contDiffOn_inverseDerivOp hU hf hf' n)).1.differentiableAt (hU.mem_nhds hx)

/-- **The inverse function rule as an autonomous equation:** if `g` is a continuous local right
inverse of `f` on the open set `s` (`f (g y) = y`), taking values in the open set `U` where `f` is
differentiable with `f' ≠ 0`, then `g' = (1/f') ∘ g` on `s`. -/
theorem hasDerivAt_of_local_left_inverse (hU : IsOpen U) (hs : IsOpen s)
    (hf : DifferentiableOn ℝ f U) (hf' : ∀ x ∈ U, deriv f x ≠ 0) (hgU : ∀ y ∈ s, g y ∈ U)
    (hgc : ContinuousOn g s) (hfg : ∀ y ∈ s, f (g y) = y) {y : ℝ} (hy : y ∈ s) :
    HasDerivAt g (deriv f (g y))⁻¹ y := by
  have hfat : HasDerivAt f (deriv f (g y)) (g y) :=
    (hf.differentiableAt (hU.mem_nhds (hgU y hy))).hasDerivAt
  exact HasDerivAt.of_local_left_inverse (hgc.continuousAt (hs.mem_nhds hy)) hfat
    (hf' _ (hgU y hy)) (Filter.eventually_of_mem (hs.mem_nhds hy) hfg)

/-- **Inverse-derivative operator** (`thm:merged-inverse-derivative-operator`):
`g^{(n)}(y) = G_n(g(y))` with `G_n = ((1/f') d/dx)^n [x] = ((1/f') d/dx)^{n-1} (1/f')`,
for a continuous local right inverse `g` of a `C^∞` function `f` with `f' ≠ 0`.  This is
`AutonomousODE.iteratedDeriv_eq_comp` for the equation `g' = (1/f')(g)`. -/
theorem iteratedDeriv_eq_inverseDerivOp (hU : IsOpen U) (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f U) (hf' : ∀ x ∈ U, deriv f x ≠ 0) (hgU : ∀ y ∈ s, g y ∈ U)
    (hgc : ContinuousOn g s) (hfg : ∀ y ∈ s, f (g y) = y) :
    ∀ n, ∀ y ∈ s, iteratedDeriv n g y = inverseDerivOp f n (g y) := by
  have hfd : DifferentiableOn ℝ f U := ((contDiffOn_infty_iff_deriv_of_isOpen hU).mp hf).1
  exact AutonomousODE.iteratedDeriv_eq_comp (φ := fun x => (deriv f x)⁻¹) hs
    (fun y hy => hasDerivAt_of_local_left_inverse hU hs hfd hf' hgU hgc hfg hy)
    (inverseDerivOp f) (fun n => deriv (inverseDerivOp f n)) (fun _ _ => rfl)
    (fun n y hy => (differentiableAt_inverseDerivOp hU hf hf' n (hgU y hy)).hasDerivAt)
    (fun _ _ _ => rfl)

/-- `n = 1`: `g' = 1/f'(g)` (`eq:merged-inverse-first-four`, first line). -/
theorem deriv_eq_inv_deriv (hU : IsOpen U) (hs : IsOpen s) (hf : DifferentiableOn ℝ f U)
    (hf' : ∀ x ∈ U, deriv f x ≠ 0) (hgU : ∀ y ∈ s, g y ∈ U) (hgc : ContinuousOn g s)
    (hfg : ∀ y ∈ s, f (g y) = y) {y : ℝ} (hy : y ∈ s) : deriv g y = (deriv f (g y))⁻¹ :=
  (hasDerivAt_of_local_left_inverse hU hs hf hf' hgU hgc hfg hy).deriv

/-- `G_2 = -f''/f'^3` on `U`: one application of `(1/f') d/dx` to `1/f'`. -/
theorem inverseDerivOp_two (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hf' : ∀ x ∈ U, deriv f x ≠ 0) {x : ℝ} (hx : x ∈ U) :
    inverseDerivOp f 2 x = -(iteratedDeriv 2 f x) * (deriv f x)⁻¹ ^ 3 := by
  have hfd : ContDiffOn ℝ ∞ (deriv f) U := ((contDiffOn_infty_iff_deriv_of_isOpen hU).mp hf).2
  have hd : DifferentiableAt ℝ (deriv f) x :=
    ((contDiffOn_infty_iff_deriv_of_isOpen hU).mp hfd).1.differentiableAt (hU.mem_nhds hx)
  have hdi : deriv (fun x => (deriv f x)⁻¹) x = -(deriv (deriv f) x) / deriv f x ^ 2 :=
    (hd.hasDerivAt.inv (hf' x hx)).deriv
  have h2 : inverseDerivOp f 2 x = deriv (fun x => (deriv f x)⁻¹) x * (deriv f x)⁻¹ := by
    rw [inverseDerivOp_succ, inverseDerivOp_one]
  rw [h2, hdi, iteratedDeriv_succ, iteratedDeriv_one, div_eq_mul_inv, ← inv_pow]
  ring

/-- `n = 2`: `g'' = -f''(g)/f'(g)^3` (`eq:merged-inverse-first-four`, second line). -/
theorem iteratedDeriv_two_eq (hU : IsOpen U) (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f U)
    (hf' : ∀ x ∈ U, deriv f x ≠ 0) (hgU : ∀ y ∈ s, g y ∈ U) (hgc : ContinuousOn g s)
    (hfg : ∀ y ∈ s, f (g y) = y) {y : ℝ} (hy : y ∈ s) :
    iteratedDeriv 2 g y = -(iteratedDeriv 2 f (g y)) * (deriv f (g y))⁻¹ ^ 3 := by
  rw [iteratedDeriv_eq_inverseDerivOp hU hs hf hf' hgU hgc hfg 2 y hy,
    inverseDerivOp_two hU hf hf' (hgU y hy)]

end Analytic

end InverseDerivative

end Fabius
