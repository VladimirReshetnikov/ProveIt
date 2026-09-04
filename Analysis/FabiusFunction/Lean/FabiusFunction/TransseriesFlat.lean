import FabiusFunction.TransseriesPolyLogScale
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

/-! ### Scalar compatibility API

The canonical transseries source also uses a scalar-valued presentation of
flatness.  These declarations preserve that presentation while the core API
above remains valid for functions with values in an arbitrary normed space.
-/

section ScalarCompatibility

variable {f g ε δ h : α → 𝕜} {aₛ : ℕ → 𝕜}

/-- **`q0:prop:invisible`, vector-space clause.**  Scalar-valued functions
flat relative to `φ` form a submodule of the function space. -/
def flatSubmodule (l : Filter α) (φ : ℕ → α → 𝕜) : Submodule 𝕜 (α → 𝕜) where
  carrier := {ε | IsFlat l φ ε}
  add_mem' := by
    intro ε δ hε hδ
    change IsFlat l φ (fun x => ε x + δ x)
    exact hε.add hδ
  zero_mem' := by
    change IsFlat l φ (fun _ => (0 : 𝕜))
    exact isFlat_zero l φ
  smul_mem' := by
    intro c ε hε
    change IsFlat l φ (fun x => c • ε x)
    exact hε.const_smul c

/-- Membership in `flatSubmodule` is flatness relative to its defining scale. -/
@[simp] theorem mem_flatSubmodule_iff : ε ∈ flatSubmodule l φ ↔ IsFlat l φ ε := Iff.rfl

/-- A multiplier absorbs a scale if every requested order can absorb the
multiplier times some (possibly later) scale member. -/
def AbsorbsScale (l : Filter α) (φ : ℕ → α → 𝕜) (h : α → 𝕜) : Prop :=
  ∀ N, ∃ M, (fun x => h x * φ M x) =O[l] φ N

/-- **`q0:prop:invisible`, multiplier clause.**  A scalar flat function
remains flat after multiplication by a scale-absorbing function. -/
theorem IsFlat.mul_absorbsScale (hh : AbsorbsScale l φ h) (hε : IsFlat l φ ε) :
    IsFlat l φ (fun x => h x * ε x) := by
  simpa only [smul_eq_mul] using hε.smul_of_scale_absorption hh

/-- Every constant multiplier absorbs every scale. -/
theorem absorbsScale_const (c : 𝕜) : AbsorbsScale l φ (fun _ => c) :=
  fun N => ⟨N, (isBigO_refl (φ N) l).const_mul_left c⟩

/-- Scalar compatibility alias: adding a flat function preserves a Poincaré
expansion. -/
theorem IsPoincareExpansion.add_isFlat (hf : IsPoincareExpansion l φ f aₛ)
    (hε : IsFlat l φ ε) : IsPoincareExpansion l φ (f + ε) aₛ := by
  change IsPoincareExpansion l φ (fun x => f x + ε x) aₛ
  exact hf.add_flat hε

/-- Scalar compatibility alias: functions with the same Poincaré coefficients
differ by a flat function. -/
theorem isFlat_sub_of_isPoincareExpansion (hf : IsPoincareExpansion l φ f aₛ)
    (hg : IsPoincareExpansion l φ g aₛ) : IsFlat l φ (f - g) := by
  change IsFlat l φ (fun x => f x - g x)
  exact hf.sub_same_coeff_isFlat hg

/-- Scalar compatibility form of the exact same-coefficient criterion. -/
theorem isPoincareExpansion_iff_isFlat_sub (hf : IsPoincareExpansion l φ f aₛ) :
    IsPoincareExpansion l φ g aₛ ↔ IsFlat l φ (g - f) := by
  change IsPoincareExpansion l φ g aₛ ↔ IsFlat l φ (fun x => g x - f x)
  exact hf.iff_sub_isFlat (g := g)

/-- A scalar function is flat exactly when it has the zero Poincaré
coefficient sequence. -/
theorem isPoincareExpansion_zero_iff :
    IsPoincareExpansion l φ ε 0 ↔ IsFlat l φ ε := by
  constructor
  · intro h N
    simpa [poincarePartialSum] using h N
  · intro h N
    simpa [poincarePartialSum] using h N

end ScalarCompatibility

/-! ### The canonical inverse-power scale -/

section PowerScale

open Real

/-- The canonical power scale `X ↦ X⁻ⁿ`, expressed as a power--log
monomial so that the general dominance results apply. -/
noncomputable def powScale (n : ℕ) (X : ℝ) : ℝ := plMonomial (-(n : ℝ)) 0 X

/-- The power-scale monomial is the corresponding real power `X⁻ⁿ`. -/
theorem powScale_eq_rpow (n : ℕ) (X : ℝ) : powScale n X = X ^ (-(n : ℝ)) := by
  rw [powScale, plMonomial, Real.rpow_zero, mul_one]

/-- A function bounded by a fixed natural power absorbs the inverse-power
scale. -/
theorem absorbsScale_of_isBigO_pow {h : ℝ → ℝ} {N : ℕ}
    (hh : h =O[atTop] fun X => X ^ N) : AbsorbsScale atTop powScale h := by
  intro n
  refine ⟨n + N, ?_⟩
  have hcancel : (fun X : ℝ => X ^ N * powScale (n + N) X) =ᶠ[atTop] powScale n := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [powScale_eq_rpow, powScale_eq_rpow, ← Real.rpow_natCast X N, ← Real.rpow_add hX]
    push_cast
    ring_nf
  exact (hh.mul (isBigO_refl (powScale (n + N)) atTop)).trans hcancel.isBigO

/-- The standard exponentially small remainder is flat relative to the
canonical inverse-power scale. -/
theorem isFlat_exp_neg : IsFlat atTop powScale (fun x : ℝ => Real.exp (-x)) := by
  intro n
  rw [show powScale n = (fun X : ℝ => X ^ (-(n : ℝ))) from
    funext (powScale_eq_rpow n)]
  exact isFlat_exp_neg_rpow_atTop n

/-- Adding `exp (-x)` leaves every coefficient of an inverse-power Poincaré
expansion unchanged. -/
theorem isPoincareExpansion_add_exp_neg {f : ℝ → ℝ} {a : ℕ → ℝ}
    (hf : IsPoincareExpansion atTop powScale f a) :
    IsPoincareExpansion atTop powScale (fun x => f x + Real.exp (-x)) a :=
  hf.add_flat isFlat_exp_neg

end PowerScale

end Fabius
