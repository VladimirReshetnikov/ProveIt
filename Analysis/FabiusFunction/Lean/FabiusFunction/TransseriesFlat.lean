import FabiusFunction.TransseriesScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Flat remainders for Poincaré expansions

This module formalizes `q0:def:flat` and the valid core of
`q0:prop:invisible`.  A vector-valued function is flat relative to a scale
when it is bounded by every member of that scale.  Flat functions form a
vector subspace: they are closed under zero, addition, negation, subtraction,
and constant scalar multiplication.  Adding a flat remainder to a function
does not alter any coefficient of a Poincaré expansion, and two functions
have the same coefficient sequence exactly when their difference is flat.

Multiplication by a variable scalar function needs an additional hypothesis.
The generic theorem below requires that multiplication absorb some later
scale member into each requested scale order.  For the power scale `u^n`, an
eventually nonzero `u` and a bound by an inverse power of `u` supply precisely
that hypothesis.  No unrestricted multiplier claim is made for an arbitrary
asymptotic scale.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Fabius

variable {α 𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E]
  {l : Filter α} {φ : ℕ → α → 𝕜} {f g r s : α → E} {a : ℕ → E}

/-- **`q0:def:flat`.**  A function is flat relative to `φ` along `l` when it
is `O(φ_N)` for every fixed order `N`. -/
def IsFlat (l : Filter α) (φ : ℕ → α → 𝕜) (r : α → E) : Prop :=
  ∀ N, r =O[l] φ N

/-- The zero function is flat relative to every family of comparison
functions. -/
theorem isFlat_zero (l : Filter α) (φ : ℕ → α → 𝕜) :
    IsFlat l φ (fun _x => (0 : E)) := by
  intro N
  exact isBigO_zero (φ N) l

/-- The sum of two flat functions is flat. -/
theorem IsFlat.add (hr : IsFlat l φ r) (hs : IsFlat l φ s) :
    IsFlat l φ (fun x => r x + s x) := by
  intro N
  exact (hr N).add (hs N)

/-- The negative of a flat function is flat. -/
theorem IsFlat.neg (hr : IsFlat l φ r) :
    IsFlat l φ (fun x => -r x) := by
  intro N
  exact (hr N).neg_left

/-- The difference of two flat functions is flat. -/
theorem IsFlat.sub (hr : IsFlat l φ r) (hs : IsFlat l φ s) :
    IsFlat l φ (fun x => r x - s x) := by
  intro N
  exact (hr N).sub (hs N)

variable [NormedSpace 𝕜 E]

/-- Constant scalar multiplication preserves flatness. -/
theorem IsFlat.const_smul (hr : IsFlat l φ r) (c : 𝕜) :
    IsFlat l φ (fun x => c • r x) := by
  intro N
  exact (hr N).const_smul_left c

/-- The standard exponentially small remainder is flat in every real inverse
power of `x` at `+∞`.  This is the concrete flat term used in
`q0:prop:invisible`. -/
theorem isFlat_exp_neg_rpow_atTop :
    IsFlat atTop (fun (n : ℕ) (x : ℝ) => x ^ (-(n : ℝ)))
      (fun x => Real.exp (-x)) := by
  intro N
  simpa only [neg_one_mul] using
    (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-(N : ℝ))).isBigO

/-- **Core of `q0:prop:invisible`.**  Adding a flat remainder leaves every
coefficient of a Poincaré expansion unchanged. -/
theorem IsPoincareExpansion.add_flat
    (hf : IsPoincareExpansion l φ f a) (hr : IsFlat l φ r) :
    IsPoincareExpansion l φ (fun x => f x + r x) a := by
  intro N
  have h := (hf N).add (hr N)
  apply h.congr_left
  intro x
  exact sub_add_eq_add_sub (f x) (poincarePartialSum φ a N x) (r x)

/-- Two Poincaré expansions with the same coefficient sequence differ by a
flat function.  This statement needs no asymptotic-scale or nondegeneracy
hypothesis. -/
theorem IsPoincareExpansion.sub_same_coeff_isFlat
    (hf : IsPoincareExpansion l φ f a) (hg : IsPoincareExpansion l φ g a) :
    IsFlat l φ (fun x => f x - g x) := by
  intro N
  have h := (hf N).sub (hg N)
  apply h.congr_left
  intro x
  abel

/-- Once one Poincaré expansion is known, another function has the same
coefficient sequence if and only if its difference from the first function is
flat. -/
theorem IsPoincareExpansion.iff_sub_isFlat
    (hf : IsPoincareExpansion l φ f a) :
    IsPoincareExpansion l φ g a ↔ IsFlat l φ (fun x => g x - f x) := by
  constructor
  · intro hg
    exact hg.sub_same_coeff_isFlat hf
  · intro hflat N
    have h := (hf N).add (hflat N)
    apply h.congr_left
    intro x
    abel

/-- A variable scalar multiplier preserves flatness provided that, for every
target order, multiplying some later scale member is absorbed by that target
member.  This explicit absorption premise is essential for a general scale. -/
theorem IsFlat.smul_of_scale_absorption
    {m : α → 𝕜} (hr : IsFlat l φ r)
    (habsorb : ∀ N, ∃ M, (fun x => m x * φ M x) =O[l] φ N) :
    IsFlat l φ (fun x => m x • r x) := by
  intro N
  obtain ⟨M, hM⟩ := habsorb N
  have hmr := (isBigO_refl m l).smul (hr M)
  have hmφ : (fun x => m x • φ M x) =O[l] φ N := by
    simpa only [smul_eq_mul] using hM
  exact hmr.trans hmφ

/-- Polynomial-growth specialization of scale absorption.  On the power
scale `u^n`, a multiplier bounded by `(u⁻¹)^k` preserves flatness whenever
`u` is eventually nonzero.  Taking `u(x) = x⁻¹` recovers the usual statement
that multiplication by a function of at most polynomial growth preserves a
remainder flat in inverse powers of `x`. -/
theorem IsFlat.smul_of_isBigO_inv_pow
    {u m : α → 𝕜} {k : ℕ}
    (hr : IsFlat l (fun n x => u x ^ n) r)
    (hu : ∀ᶠ x in l, u x ≠ 0)
    (hm : m =O[l] fun x => (u x)⁻¹ ^ k) :
    IsFlat l (fun n x => u x ^ n) (fun x => m x • r x) := by
  apply hr.smul_of_scale_absorption
  intro N
  refine ⟨N + k, ?_⟩
  have h := hm.mul (isBigO_refl (fun x => u x ^ (N + k)) l)
  apply h.congr'
  · exact Filter.EventuallyEq.rfl
  · filter_upwards [hu] with x hx
    rw [pow_add]
    calc
      (u x)⁻¹ ^ k * (u x ^ N * u x ^ k) =
          u x ^ N * ((u x)⁻¹ ^ k * u x ^ k) := by ac_rfl
      _ = u x ^ N := by
        rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero k hx), mul_one]

end Fabius
