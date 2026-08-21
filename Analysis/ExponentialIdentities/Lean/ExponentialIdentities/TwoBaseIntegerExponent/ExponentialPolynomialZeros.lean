import ExponentialIdentities.TwoBaseIntegerExponent
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Zeros of real exponential polynomials

This module formalizes the classical zero-count theorem for real exponential polynomials,
the analytic engine behind the positivity of generalized Vandermonde determinants used in
the two-base survey (appendix "Detailed proof of the generalized Vandermonde sign").

For real exponents `λ₀ < λ₁ < ⋯ < λ_n` and real coefficients `c₀, …, c_n`, the *exponential
polynomial*
`F t = ∑ j, c j * exp (λ j * t)`
has at most `n` real zeros unless all coefficients vanish.  Equivalently — and this is the
form actually consumed downstream — if `F` vanishes at `n + 1` distinct real points, then
every coefficient is zero.

## Proof

The argument is a descending induction on the number of exponents, exactly as in the report.

* For a single exponent, `c₀ * exp (λ₀ * t) = 0` forces `c₀ = 0` because `exp` is positive.
* For `n + 2` exponents, multiply by the nowhere-vanishing factor `exp (-(λ₀ * t))`.  This
  replaces `λ j` by `λ j - λ₀` and does not change the zero set
  (`expPoly_sub_const`).  The normalized function `G` is differentiable everywhere, and its
  derivative is again an exponential polynomial with the same exponents and coefficients
  `c j * (λ j - λ₀)` (`hasDerivAt_expPoly`).  Since the coefficient of the constant term
  `j = 0` is `c₀ * (λ₀ - λ₀) = 0`, the derivative is genuinely an exponential polynomial
  with only `n + 1` terms (`expPoly_deriv_shift`).  Applying Rolle's theorem on each of the
  `n + 1` gaps between consecutive zeros of `G` produces `n + 1` strictly increasing zeros of
  `G'` (`exists_strictMono_deriv_eq_zero`), and the induction hypothesis kills all of them:
  `c j * (λ j - λ₀) = 0`, hence `c j = 0` for `j > 0` because `λ j > λ₀`.  Finally `G` reduces
  to the constant `c₀`, which therefore vanishes as well.

The bookkeeping is carried out with `Fin`-indexed strictly monotone node families rather
than `Finset`s: Rolle's theorem hands back exactly one point per gap, so `Fin n → ℝ` is the
natural output type and the reindexing `Fin (n + 2) → Fin (n + 1)` is `Fin.succ`.  A
`Finset` wrapper is provided on top, obtained by sorting the zero set with
`Finset.orderEmbOfFin`.

## Consequences

Substituting `t = log x` transports the theorem to the functions `x ↦ x ^ λ` on `(0, ∞)`
(`rpow_coeff_eq_zero_of_zeros`), which immediately gives nonvanishing of the generalized
Vandermonde determinant `det (xᵢ ^ λⱼ)` for strictly increasing positive nodes and strictly
increasing real exponents (`det_rpowVandermonde_ne_zero`).

Only *nonvanishing* is established here.  The sharper statement that the determinant is
strictly *positive* additionally requires a connectedness/continuity argument together with
the coalescing-node Wronskian limit, which is deliberately left out of this module.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- The real exponential polynomial with exponents `lam` and coefficients `c`, evaluated at
`t`.  This is `∑ j, c j * exp (lam j * t)`. -/
def expPoly {m : ℕ} (lam c : Fin m → ℝ) (t : ℝ) : ℝ :=
  ∑ j, c j * Real.exp (lam j * t)

/-- Unfolding lemma for `expPoly`. -/
theorem expPoly_apply {m : ℕ} (lam c : Fin m → ℝ) (t : ℝ) :
    expPoly lam c t = ∑ j, c j * Real.exp (lam j * t) := rfl

/-- The derivative of an exponential polynomial is the exponential polynomial with the same
exponents and coefficients multiplied by their exponents. -/
theorem hasDerivAt_expPoly {m : ℕ} (lam c : Fin m → ℝ) (t : ℝ) :
    HasDerivAt (expPoly lam c) (expPoly lam (fun j ↦ c j * lam j) t) t := by
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      HasDerivAt (fun s : ℝ ↦ c j * Real.exp (lam j * s))
        (c j * lam j * Real.exp (lam j * t)) t := by
    intro j _
    have h1 : HasDerivAt (fun s : ℝ ↦ lam j * s) (lam j) t := by
      simpa using (hasDerivAt_id t).const_mul (lam j)
    have h2 := h1.exp.const_mul (c j)
    have heq : c j * lam j * Real.exp (lam j * t)
        = c j * (Real.exp (lam j * t) * lam j) := by ring
    rw [heq]
    exact h2
  have hsum := HasDerivAt.fun_sum hterm
  simp only [expPoly_apply]
  exact hsum

/-- Multiplying an exponential polynomial by the nowhere-vanishing factor `exp (-(a * t))`
shifts every exponent down by `a`. -/
theorem expPoly_sub_const {m : ℕ} (lam c : Fin m → ℝ) (a t : ℝ) :
    expPoly (fun j ↦ lam j - a) c t = Real.exp (-(a * t)) * expPoly lam c t := by
  simp only [expPoly_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show (lam j - a) * t = lam j * t + -(a * t) by ring, Real.exp_add]
  ring

/-- Differentiating a normalized exponential polynomial — one whose lowest exponent has been
subtracted from all exponents — deletes its constant term, leaving an exponential polynomial
with one term fewer. -/
theorem expPoly_deriv_shift {m : ℕ} (lam c : Fin (m + 1) → ℝ) (t : ℝ) :
    expPoly (fun j ↦ lam j - lam 0) (fun j ↦ c j * (lam j - lam 0)) t =
      expPoly (fun j : Fin m ↦ lam j.succ - lam 0)
        (fun j : Fin m ↦ c j.succ * (lam j.succ - lam 0)) t := by
  simp only [expPoly_apply]
  rw [Fin.sum_univ_succ (f := fun j : Fin (m + 1) ↦
    c j * (lam j - lam 0) * Real.exp ((lam j - lam 0) * t))]
  simp

/-- **Rolle chaining.**  If `g` has derivative `g'` at every real point and vanishes at
`m + 1` strictly increasing points, then `g'` vanishes at `m` strictly increasing points. -/
theorem exists_strictMono_deriv_eq_zero {m : ℕ} (g g' : ℝ → ℝ)
    (hg : ∀ t : ℝ, HasDerivAt g (g' t) t)
    (x : Fin (m + 1) → ℝ) (hx : StrictMono x) (hgx : ∀ i, g (x i) = 0) :
    ∃ y : Fin m → ℝ, StrictMono y ∧ ∀ i, g' (y i) = 0 := by
  have key : ∀ i : Fin m, ∃ z : ℝ, x i.castSucc < z ∧ z < x i.succ ∧ g' z = 0 := by
    intro i
    obtain ⟨z, hz, hz0⟩ :=
      exists_hasDerivAt_eq_zero (f := g) (f' := g')
        (a := x i.castSucc) (b := x i.succ)
        (hx (Fin.castSucc_lt_succ (i := i)))
        (fun t _ ↦ (hg t).continuousAt.continuousWithinAt)
        (by rw [hgx i.castSucc, hgx i.succ])
        (fun t _ ↦ hg t)
    exact ⟨z, hz.1, hz.2, hz0⟩
  choose y hlo hhi hy0 using key
  refine ⟨y, ?_, hy0⟩
  intro i j hij
  have hval : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp hij
  have hle : (i.succ : Fin (m + 1)) ≤ j.castSucc := by
    rw [Fin.le_def]
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  exact ((hhi i).trans_le (hx.monotone hle)).trans (hlo j)

/-- Induction carrier for the zero-count theorem: the order `n` is quantified first so that
`induction` can generalize over the exponents, the coefficients and the nodes. -/
private theorem expPoly_coeff_eq_zero_aux :
    ∀ (n : ℕ) (lam c : Fin (n + 1) → ℝ), StrictMono lam →
      ∀ x : Fin (n + 1) → ℝ, StrictMono x →
        (∀ i, expPoly lam c (x i) = 0) → ∀ j, c j = 0 := by
  intro n
  induction n with
  | zero =>
      intro lam c _hlam x _hx hzero j
      have h0 : ∑ k : Fin (0 + 1), c k * Real.exp (lam k * x 0) = 0 := hzero 0
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h0
      have hc0 : c 0 = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact h
        · exact absurd h (Real.exp_pos _).ne'
      rcases Fin.eq_zero_or_eq_succ j with hj | ⟨i, _⟩
      · rw [hj]; exact hc0
      · exact i.elim0
  | succ n ih =>
      intro lam c hlam x hx hzero
      -- Normalize: subtract the lowest exponent.  This preserves the zero set.
      have hGzero : ∀ i, expPoly (fun j ↦ lam j - lam 0) c (x i) = 0 := by
        intro i
        rw [expPoly_sub_const lam c (lam 0) (x i), hzero i, mul_zero]
      -- Rolle's theorem on each of the `n + 1` gaps.
      obtain ⟨y, hymono, hy0⟩ :=
        exists_strictMono_deriv_eq_zero
          (expPoly (fun j ↦ lam j - lam 0) c)
          (expPoly (fun j ↦ lam j - lam 0) (fun j ↦ c j * (lam j - lam 0)))
          (fun t ↦ hasDerivAt_expPoly (fun j ↦ lam j - lam 0) c t)
          x hx hGzero
      -- The derivative has one term fewer, so the induction hypothesis applies.
      have hd : ∀ j : Fin (n + 1), c j.succ * (lam j.succ - lam 0) = 0 := by
        refine ih (fun j : Fin (n + 1) ↦ lam j.succ - lam 0)
          (fun j : Fin (n + 1) ↦ c j.succ * (lam j.succ - lam 0)) ?_ y hymono ?_
        · intro a b hab
          have hlt : lam a.succ < lam b.succ := hlam (Fin.succ_lt_succ_iff.mpr hab)
          show lam a.succ - lam 0 < lam b.succ - lam 0
          exact sub_lt_sub_right hlt (lam 0)
        · intro i
          have h : expPoly (fun j ↦ lam j - lam 0)
              (fun j ↦ c j * (lam j - lam 0)) (y i) = 0 := hy0 i
          rw [expPoly_deriv_shift lam c (y i)] at h
          exact h
      have hpos : ∀ j : Fin (n + 1), 0 < lam j.succ - lam 0 := fun j ↦
        sub_pos.mpr (hlam (Fin.succ_pos j))
      have hcsucc : ∀ j : Fin (n + 1), c j.succ = 0 := by
        intro j
        rcases mul_eq_zero.mp (hd j) with h | h
        · exact h
        · exact absurd h (hpos j).ne'
      -- With all higher coefficients gone, the normalized function is the constant `c 0`.
      have hc0 : c 0 = 0 := by
        have h0 : ∑ k : Fin (n + 1 + 1), c k * Real.exp ((lam k - lam 0) * x 0) = 0 :=
          hGzero 0
        simp only [Fin.sum_univ_succ, hcsucc, zero_mul, Finset.sum_const_zero, add_zero,
          sub_self, Real.exp_zero, mul_one] at h0
        exact h0
      intro j
      rcases Fin.eq_zero_or_eq_succ j with hj | ⟨i, hi⟩
      · rw [hj]; exact hc0
      · rw [hi]; exact hcsucc i

/-- **Zero-count theorem for exponential polynomials, node form.**  If the exponents are
strictly increasing and the exponential polynomial vanishes at `n + 1` strictly increasing
real points, then all of its coefficients vanish. -/
theorem expPoly_coeff_eq_zero_of_zeros {n : ℕ} (lam c : Fin (n + 1) → ℝ)
    (hlam : StrictMono lam) (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hzero : ∀ i, expPoly lam c (x i) = 0) : ∀ j, c j = 0 :=
  expPoly_coeff_eq_zero_aux n lam c hlam x hx hzero

/-- **Zero-count theorem for exponential polynomials, `Finset` form.**  This is the shape
consumed downstream: a finite set of at least `n + 1` real zeros forces every coefficient of
an `(n + 1)`-term exponential polynomial with strictly increasing exponents to vanish. -/
theorem expPoly_coeff_eq_zero_of_card_zeros {n : ℕ} (lam c : Fin (n + 1) → ℝ)
    (hlam : StrictMono lam) (S : Finset ℝ) (hS : n + 1 ≤ S.card)
    (hzero : ∀ t ∈ S, ∑ j, c j * Real.exp (lam j * t) = 0) : ∀ j, c j = 0 := by
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hS
  refine expPoly_coeff_eq_zero_of_zeros lam c hlam ⇑(T.orderEmbOfFin hT)
    (T.orderEmbOfFin hT).strictMono ?_
  intro i
  rw [expPoly_apply]
  exact hzero _ (hTS (T.orderEmbOfFin_mem hT i))

/-- **At most `n` real zeros.**  A nonzero exponential polynomial with `n + 1` strictly
increasing exponents vanishes on no finite set of more than `n` points. -/
theorem card_le_of_expPoly_eq_zero {n : ℕ} (lam c : Fin (n + 1) → ℝ)
    (hlam : StrictMono lam) (hc : ∃ j, c j ≠ 0) (S : Finset ℝ)
    (hzero : ∀ t ∈ S, expPoly lam c t = 0) : S.card ≤ n := by
  by_contra hcon
  have hS : n + 1 ≤ S.card := by omega
  obtain ⟨j, hj⟩ := hc
  exact hj (expPoly_coeff_eq_zero_of_card_zeros lam c hlam S hS
    (fun t ht ↦ (expPoly_apply lam c t).symm.trans (hzero t ht)) j)

/-- **Linear independence of real power functions on the positive half-line.**  If the real
exponents `lam` are strictly increasing and `∑ j, c j * x i ^ lam j` vanishes at `n + 1`
strictly increasing positive nodes, then all coefficients vanish.  This is the substitution
`x = exp t` applied to `expPoly_coeff_eq_zero_of_zeros`. -/
theorem rpow_coeff_eq_zero_of_zeros {n : ℕ} (lam c : Fin (n + 1) → ℝ)
    (hlam : StrictMono lam) (x : Fin (n + 1) → ℝ) (hx : StrictMono x) (hx0 : 0 < x 0)
    (hzero : ∀ i, ∑ j, c j * x i ^ lam j = 0) : ∀ j, c j = 0 := by
  have hxpos : ∀ i, 0 < x i := fun i ↦ hx0.trans_le (hx.monotone (Fin.zero_le i))
  refine expPoly_coeff_eq_zero_of_zeros lam c hlam (fun i ↦ Real.log (x i)) ?_ ?_
  · intro a b hab
    exact Real.log_lt_log (hxpos a) (hx hab)
  · intro i
    have hterm : ∀ j : Fin (n + 1),
        c j * Real.exp (lam j * Real.log (x i)) = c j * x i ^ lam j := by
      intro j
      rw [Real.rpow_def_of_pos (hxpos i) (lam j), mul_comm (Real.log (x i)) (lam j)]
    show expPoly lam c (Real.log (x i)) = 0
    calc expPoly lam c (Real.log (x i))
        = ∑ j, c j * x i ^ lam j := by
          rw [expPoly_apply]
          exact Finset.sum_congr rfl fun j _ ↦ hterm j
      _ = 0 := hzero i

/-- The generalized Vandermonde matrix with arbitrary real exponents:
`rpowVandermonde x lam i j = x i ^ lam j`, the power being `Real.rpow`. -/
def rpowVandermonde {m : ℕ} (x lam : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j ↦ x i ^ lam j

@[simp] theorem rpowVandermonde_apply {m : ℕ} (x lam : Fin m → ℝ) (i j : Fin m) :
    rpowVandermonde x lam i j = x i ^ lam j := rfl

/-- **Nonvanishing of the generalized Vandermonde determinant.**  For strictly increasing
positive nodes and strictly increasing real exponents, `det (xᵢ ^ λⱼ) ≠ 0`.

This is the determinantal form of the zero-count theorem: a vanishing determinant would
produce a nontrivial kernel vector, i.e. a nonzero real linear combination of the functions
`x ↦ x ^ λⱼ` with `n + 1` distinct positive zeros.  The strict positivity of the determinant
needs a further continuity argument and is not proved here. -/
theorem det_rpowVandermonde_ne_zero {n : ℕ} (x lam : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (hx0 : 0 < x 0) (hlam : StrictMono lam) :
    (rpowVandermonde x lam).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv
  funext k
  show v k = 0
  refine rpow_coeff_eq_zero_of_zeros lam v hlam x hx hx0 ?_ k
  intro i
  have h0 := congrFun hmul i
  rw [Matrix.mulVec_apply_eq_sum] at h0
  simp only [Pi.zero_apply, rpowVandermonde_apply] at h0
  calc ∑ j, v j * x i ^ lam j
      = ∑ j, x i ^ lam j * v j := Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    _ = 0 := h0

end

end LeanProofs.TwoBaseIntegerExponent
