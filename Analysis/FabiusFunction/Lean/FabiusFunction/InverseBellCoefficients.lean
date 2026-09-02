import FabiusFunction.LagrangeInversion
import FabiusFunction.BellComposition
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The inverse coefficients of an exponential series, in Bell-polynomial form

Let `f(w) = ∑_{j ≥ 1} f_j w^j/j!` with `f_1` invertible, and let `g` be its compositional
inverse, `g(z) = ∑_{n ≥ 1} g_n z^n/n!`.  Writing

`f̂_j = f_{j+1}/((j+1) f_1)`   (`normRev`)

for the normalized reversion coefficients, the inverse coefficients are

`g_n = f_1^{-n} ∑_{k < n} (-1)^k (n)^{(k)} B_{n-1,k}(f̂_1, …)`

(`factorial_mul_coeff_reversion`), where `(n)^{(k)}` is the rising factorial and `B_{n,k}` the
exponential partial Bell polynomial.  The `k = 0` term contributes only at `n = 1`, where it
gives `g_1 = f_1^{-1}` (`coeff_reversion_one`); for `n ≥ 2` the sum may be restricted to
`1 ≤ k ≤ n-1` (`factorial_mul_coeff_reversion_of_two_le`), which is the form the literature
states.

Nothing here is conditional on an inverse existing: `g` is built by `Fabius.Lagrange.solution`
from the weight `w/f(w)`, and `subst_egfA_reversion` proves that it does invert `f`.

The route is the one in the source: `f(w)/(f_1 w) = 1 + U(w)` with `U` the Bell weight series
of `f̂`, so `(w/f(w))^n = f_1^{-n}(1 + U)^{-n}`, and the negative binomial series expands
`(1+U)^{-n}` through the exponential composition theorem.  Two ingredients are separated out
because they are of independent use:

* `negBinomSeries`, the expansion of `(1+w)^{-(d+1)}` with its inverse property
  (`negBinomSeries_mul`) and its exponential form with rising-factorial coefficients
  (`negBinomSeries_eq_egfA`), over an arbitrary commutative ring;
* `egfA_eq_X_mul_normRev`, the factorization `f = w f_1 (1 + U(w))`, which is what makes `f̂`
  the right normalization.

## Main results

* `negBinomSeries`, `negBinomSeries_mul`, `negBinomSeries_zero_pow`, `negBinomSeries_eq_egfA`.
* `normRev`, `egfA_eq_X_mul_normRev`.
* `reversion`, `subst_egfA_reversion`.
* `factorial_mul_coeff_reversion`, `coeff_reversion_one`,
  `factorial_mul_coeff_reversion_of_two_le`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-! ### The negative binomial series -/

section NegBinom

variable (S : Type*) [CommRing S]

/-- The negative binomial series `(1+w)^{-(d+1)} = ∑_k (-1)^k C(d+k, k) w^k`. -/
noncomputable def negBinomSeries (d : ℕ) : S⟦X⟧ :=
  PowerSeries.mk fun k => (-1 : S) ^ k * ((d + k).choose d : S)

/-- The coefficients of the negative binomial series. -/
@[simp] theorem coeff_negBinomSeries (d k : ℕ) :
    coeff k (negBinomSeries S d) = (-1 : S) ^ k * ((d + k).choose d : S) :=
  coeff_mk _ _

/-- **The defining property:** `(1+w)^{-(d+1)} (1+w)^{d+1} = 1`. -/
theorem negBinomSeries_mul (d : ℕ) : negBinomSeries S d * (1 + X) ^ (d + 1) = 1 := by
  have h : (mk 1 : S⟦X⟧) ^ (d + 1) * (1 - X) ^ (d + 1) = 1 := by
    rw [← mul_pow, mk_one_mul_one_sub_eq_one S, one_pow]
  rw [mk_one_pow_eq_mk_choose_add] at h
  have h2 := congrArg (rescale (-1 : S)) h
  rw [map_mul, map_one, rescale_mk, map_pow, map_sub, map_one, rescale_X] at h2
  have e : (1 : S⟦X⟧) - C (-1 : S) * X = 1 + X := by
    rw [map_neg, map_one, neg_one_mul, sub_neg_eq_add]
  rw [e] at h2
  exact h2

/-- `(1+w)^{-1} (1+w) = 1`. -/
theorem negBinomSeries_zero_mul : negBinomSeries S 0 * (1 + X) = 1 := by
  have h := negBinomSeries_mul S 0
  rwa [zero_add, pow_one] at h

/-- The negative binomial series is a power of the simplest one:
`(1+w)^{-(d+1)} = ((1+w)^{-1})^{d+1}`. -/
theorem negBinomSeries_zero_pow (d : ℕ) :
    negBinomSeries S 0 ^ (d + 1) = negBinomSeries S d := by
  have hp : negBinomSeries S 0 ^ (d + 1) * (1 + X) ^ (d + 1) = 1 := by
    rw [← mul_pow, negBinomSeries_zero_mul, one_pow]
  calc negBinomSeries S 0 ^ (d + 1)
      = negBinomSeries S 0 ^ (d + 1) * ((1 + X) ^ (d + 1) * negBinomSeries S d) := by
        rw [mul_comm ((1 + X : S⟦X⟧) ^ (d + 1)), negBinomSeries_mul, mul_one]
    _ = negBinomSeries S 0 ^ (d + 1) * (1 + X) ^ (d + 1) * negBinomSeries S d := by ring
    _ = negBinomSeries S d := by rw [hp, one_mul]

end NegBinom

/-! ### The exponential form -/

section Exponential

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- `(1/n!) · n! = 1` in a `ℚ`-algebra. -/
theorem algebraMap_inv_factorial_mul (n : ℕ) :
    algebraMap ℚ A (1 / n.factorial) * (n.factorial : A) = 1 := by
  have hn : ((n.factorial : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  rw [← map_natCast (algebraMap ℚ A) n.factorial, ← map_mul, one_div,
    inv_mul_cancel₀ hn, map_one]

/-- **The exponential form of the negative binomial series:** its exponential coefficients are
the signed rising factorials, `(1+w)^{-(d+1)} = ∑_k (-1)^k (d+1)^{(k)} w^k/k!`. -/
theorem negBinomSeries_eq_egfA (d : ℕ) :
    negBinomSeries A d =
      egfA A fun k => (-1 : A) ^ k * (((ascPochhammer ℕ k).eval (d + 1) : ℕ) : A) := by
  refine PowerSeries.ext fun k => ?_
  rw [coeff_negBinomSeries, coeff_egfA, ascPochhammer_nat_eq_ascFactorial,
    Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul, Nat.choose_symm_add]
  calc (-1 : A) ^ k * (((d + k).choose k : ℕ) : A)
      = algebraMap ℚ A (1 / k.factorial) * ((k.factorial : ℕ) : A) *
          ((-1 : A) ^ k * (((d + k).choose k : ℕ) : A)) := by
        rw [algebraMap_inv_factorial_mul, one_mul]
    _ = algebraMap ℚ A (1 / k.factorial) *
          ((-1 : A) ^ k * (((k.factorial : ℕ) : A) * (((d + k).choose k : ℕ) : A))) := by ring

end Exponential

/-! ### The reversion -/

section Reversion

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The normalized reversion coefficients `f̂_j = f_{j+1}/((j+1) f_1)`, written with an
explicit inverse `f₁inv` of `f_1` so that no field structure is needed. -/
noncomputable def normRev (f₁inv : A) (fc : ℕ → A) (j : ℕ) : A :=
  algebraMap ℚ A (1 / (j + 1)) * fc (j + 1) * f₁inv

variable (fc : ℕ → A) (f₁inv : A)

/-- The Bell weight series `U(w) = ∑_{j ≥ 1} f̂_j w^j/j!` of the normalized coefficients. -/
noncomputable abbrev revWeightSeries : A⟦X⟧ := bellWeightSeries A (normRev A f₁inv fc)

/-- `U` has no constant term, so it may be substituted into any series. -/
theorem hasSubst_revWeightSeries : HasSubst (revWeightSeries A fc f₁inv) :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_bellWeightSeries A _)

/-- **The normalization is the right one:** `f(w) = w f_1 (1 + U(w))`. -/
theorem egfA_eq_X_mul_normRev (h0 : fc 0 = 0) (hf : fc 1 * f₁inv = 1) :
    egfA A fc = X * (C (fc 1) * (1 + revWeightSeries A fc f₁inv)) := by
  refine PowerSeries.ext fun n => ?_
  cases n with
  | zero =>
    rw [coeff_egfA, h0, mul_zero, coeff_zero_X_mul]
  | succ m =>
    rw [coeff_succ_X_mul, coeff_C_mul, map_add]
    cases m with
    | zero =>
      rw [coeff_egfA, coeff_one, if_pos rfl, revWeightSeries, bellWeightSeries, coeff_egfA,
        if_pos rfl, mul_zero, add_zero, mul_one, Nat.factorial_one, Nat.cast_one, div_one,
        map_one, one_mul]
    | succ j =>
      rw [coeff_egfA, coeff_one, if_neg (Nat.succ_ne_zero j), zero_add, revWeightSeries,
        bellWeightSeries, coeff_egfA, if_neg (Nat.succ_ne_zero j), normRev]
      have hfac : ((j + 1 + 1).factorial : ℚ) =
          ((j + 1).factorial : ℚ) * (((j + 1 : ℕ) : ℚ) + 1) := by
        rw [Nat.factorial_succ (j + 1)]
        push_cast
        ring
      have hq : (1 : ℚ) / (j + 1 + 1).factorial =
          1 / (j + 1).factorial * (1 / (((j + 1 : ℕ) : ℚ) + 1)) := by
        rw [hfac]
        field_simp
      calc algebraMap ℚ A (1 / (j + 1 + 1).factorial) * fc (j + 1 + 1)
          = algebraMap ℚ A (1 / (j + 1).factorial) *
              (algebraMap ℚ A (1 / (((j + 1 : ℕ) : ℚ) + 1)) * fc (j + 1 + 1)) * 1 := by
            rw [mul_one, ← mul_assoc, ← map_mul, ← hq]
        _ = algebraMap ℚ A (1 / (j + 1).factorial) *
              (algebraMap ℚ A (1 / (((j + 1 : ℕ) : ℚ) + 1)) * fc (j + 1 + 1)) *
              (fc 1 * f₁inv) := by rw [hf]
        _ = fc 1 * (algebraMap ℚ A (1 / (j + 1).factorial) *
              (algebraMap ℚ A (1 / (((j + 1 : ℕ) : ℚ) + 1)) * fc (j + 1 + 1) * f₁inv)) := by
            ring

/-- The Lagrange weight `w/f(w) = f_1^{-1}(1 + U(w))^{-1}`. -/
noncomputable def revWeight : A⟦X⟧ :=
  C f₁inv * (negBinomSeries A 0).subst (revWeightSeries A fc f₁inv)

/-- The co-weight `f(w)/w = f_1(1 + U(w))`. -/
noncomputable def revCoWeight : A⟦X⟧ :=
  C (fc 1) * (1 + revWeightSeries A fc f₁inv)

/-- Substituting `U` into `(1+w)^{-1}(1+w) = 1`. -/
theorem subst_negBinomSeries_zero_mul :
    (negBinomSeries A 0).subst (revWeightSeries A fc f₁inv) *
      (1 + revWeightSeries A fc f₁inv) = 1 := by
  have hs : HasSubst (revWeightSeries A fc f₁inv) := hasSubst_revWeightSeries A fc f₁inv
  have h := congrArg (substAlgHom (R := A) hs) (negBinomSeries_zero_mul A)
  rw [map_mul, map_one, map_add, map_one, coe_substAlgHom, subst_X hs] at h
  exact h

/-- The weight and the co-weight are inverse to each other. -/
theorem revWeight_mul_revCoWeight (hf : fc 1 * f₁inv = 1) :
    revWeight A fc f₁inv * revCoWeight A fc f₁inv = 1 := by
  have h := subst_negBinomSeries_zero_mul A fc f₁inv
  calc revWeight A fc f₁inv * revCoWeight A fc f₁inv
      = C (f₁inv * fc 1) * ((negBinomSeries A 0).subst (revWeightSeries A fc f₁inv) *
          (1 + revWeightSeries A fc f₁inv)) := by
        rw [revWeight, revCoWeight, map_mul]
        ring
    _ = 1 := by rw [h, mul_one, mul_comm f₁inv, hf, map_one]

/-- **The reversion of `f`,** built rather than assumed. -/
noncomputable def reversion (hf : fc 1 * f₁inv = 1) : A⟦X⟧ :=
  Lagrange.solution (revWeight A fc f₁inv) (revCoWeight A fc f₁inv)
    (revWeight_mul_revCoWeight A fc f₁inv hf)

/-- The unfolding lemma for `reversion`, needed because a definition taking arguments does
not fold under `rw [← reversion]`. -/
theorem reversion_def (hf : fc 1 * f₁inv = 1) :
    reversion A fc f₁inv hf =
      Lagrange.solution (revWeight A fc f₁inv) (revCoWeight A fc f₁inv)
        (revWeight_mul_revCoWeight A fc f₁inv hf) := rfl

/-- **It really is the inverse:** `f(g(z)) = z`. -/
theorem subst_egfA_reversion (h0 : fc 0 = 0) (hf : fc 1 * f₁inv = 1) :
    (egfA A fc).subst (reversion A fc f₁inv hf) = X := by
  set g := reversion A fc f₁inv hf with hg
  have hs : HasSubst g := by
    rw [hg, reversion_def]
    exact Lagrange.hasSubst_solution _ _ _
  have heq : g = X * (revWeight A fc f₁inv).subst g := by
    rw [hg, reversion_def]
    exact Lagrange.solution_eq _ _ _
  have hone : (revWeight A fc f₁inv).subst g * (revCoWeight A fc f₁inv).subst g = 1 := by
    rw [hg, reversion_def]
    exact Lagrange.subst_solution_mul _ _ _
  rw [egfA_eq_X_mul_normRev A fc f₁inv h0 hf, subst_mul hs, subst_X hs]
  calc g * (revCoWeight A fc f₁inv).subst g
      = X * (revWeight A fc f₁inv).subst g * (revCoWeight A fc f₁inv).subst g := by
        rw [← heq]
    _ = X * ((revWeight A fc f₁inv).subst g * (revCoWeight A fc f₁inv).subst g) := by ring
    _ = X := by rw [hone, mul_one]

/-- The `n`-th power of the weight is the negative binomial series of order `n`, rescaled. -/
theorem revWeight_pow (d : ℕ) :
    revWeight A fc f₁inv ^ (d + 1) =
      C (f₁inv ^ (d + 1)) * (negBinomSeries A d).subst (revWeightSeries A fc f₁inv) := by
  have hs : HasSubst (revWeightSeries A fc f₁inv) := hasSubst_revWeightSeries A fc f₁inv
  rw [revWeight, mul_pow, ← map_pow, ← subst_pow hs, negBinomSeries_zero_pow]

/-- **The inverse coefficients in Bell-polynomial form:**
`g_n = f_1^{-n} ∑_{k < n} (-1)^k (n)^{(k)} B_{n-1,k}(f̂)`, with `n = d+1`. -/
theorem factorial_mul_coeff_reversion (hf : fc 1 * f₁inv = 1) (d : ℕ) :
    (((d + 1).factorial : ℕ) : A) * coeff (d + 1) (reversion A fc f₁inv hf) =
      f₁inv ^ (d + 1) *
        ∑ k ∈ range (d + 1), (-1 : A) ^ k * (((ascPochhammer ℕ k).eval (d + 1) : ℕ) : A) *
          partialBell (normRev A f₁inv fc) d k := by
  have hcoeff := Lagrange.coeff_solution (revWeight A fc f₁inv) (revCoWeight A fc f₁inv)
    (revWeight_mul_revCoWeight A fc f₁inv hf) (d + 1) (by omega)
  rw [← reversion_def A fc f₁inv hf, Nat.add_sub_cancel, revWeight_pow, coeff_C_mul,
    negBinomSeries_eq_egfA, egfA_subst_bellWeightSeries, coeff_egfA] at hcoeff
  have hfac : (((d + 1).factorial : ℕ) : A) = ((d.factorial : ℕ) : A) * ((d + 1 : ℕ) : A) := by
    rw [Nat.factorial_succ, Nat.cast_mul, mul_comm]
  rw [hfac, mul_assoc, hcoeff]
  set T := ∑ k ∈ range (d + 1), (-1 : A) ^ k * (((ascPochhammer ℕ k).eval (d + 1) : ℕ) : A) *
      partialBell (normRev A f₁inv fc) d k with hT
  calc ((d.factorial : ℕ) : A) * (f₁inv ^ (d + 1) * (algebraMap ℚ A (1 / d.factorial) * T))
      = algebraMap ℚ A (1 / d.factorial) * ((d.factorial : ℕ) : A) * (f₁inv ^ (d + 1) * T) := by
        ring
    _ = f₁inv ^ (d + 1) * T := by rw [algebraMap_inv_factorial_mul, one_mul]

/-- `g_1 = f_1^{-1}`. -/
theorem coeff_reversion_one (hf : fc 1 * f₁inv = 1) :
    coeff 1 (reversion A fc f₁inv hf) = f₁inv := by
  have h := factorial_mul_coeff_reversion A fc f₁inv hf 0
  rw [Finset.sum_range_one, partialBell_zero_zero, ascPochhammer_zero, Polynomial.eval_one] at h
  simpa using h

/-- For `n ≥ 2` the `k = 0` term drops out, which is the form
`g_n = f_1^{-n} ∑_{k=1}^{n-1} (-1)^k (n)^{(k)} B_{n-1,k}(f̂)`. -/
theorem factorial_mul_coeff_reversion_of_two_le (hf : fc 1 * f₁inv = 1) (d : ℕ) :
    (((d + 2).factorial : ℕ) : A) * coeff (d + 2) (reversion A fc f₁inv hf) =
      f₁inv ^ (d + 2) *
        ∑ k ∈ Ico 1 (d + 2), (-1 : A) ^ k * (((ascPochhammer ℕ k).eval (d + 2) : ℕ) : A) *
          partialBell (normRev A f₁inv fc) (d + 1) k := by
  have h := factorial_mul_coeff_reversion A fc f₁inv hf (d + 1)
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ d + 2),
    Nat.Ico_zero_eq_range, Finset.sum_range_one, partialBell_succ_zero,
    mul_zero, zero_add] at h
  exact h

end Reversion

end Fabius
