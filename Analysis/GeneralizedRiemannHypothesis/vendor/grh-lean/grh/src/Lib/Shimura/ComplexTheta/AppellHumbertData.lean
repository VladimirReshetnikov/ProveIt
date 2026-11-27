import Lib.Adelic.Adeles.AdditiveCharacter
import Lib.General.Analysis.FourierTransforms
import Lib.General.Topology

/-!
# Theta functions on complex tori: Appell–Humbert data and factors of automorphy

This file defines theta functions on a finite-dimensional complex vector space `V` for a subgroup
`L` and a form `B`. The form has type `ThetaTori.LatticeForm L`, which is `RealComplexForm V`
tagged with `L` and imposes no condition. `B` is real linear in the first argument and complex
linear in the second, and is not assumed hermitian. The file also defines the Riemann form
`E = New.RealComplexForm.riemannForm B`, Appell–Humbert data, twisted translations and the dual
lattice, and proves their first properties. Under the assumption that `L` is a full lattice, it
treats factors of automorphy, positive Riemann forms and theta functions without zeros. Below,
`𝐞 t` is `exp (2πi t)` (`New.coe_fourierChar_eq_exp`).

## Main definitions and results

* `New.RealComplexForm.thetaSpace`: the entire `f` with
  `f (z + l) = χ l * exp (B l z + B l l / 2) * f z` for `l ∈ L`. Products and powers of theta
  functions are theta functions (`New.thetaSpace.mul`, `New.thetaSpace.pow`).
* `New.IsAppellHumbert`: Appell–Humbert data; then `riemannForm B` is integral on `L`
  (`New.IsAppellHumbert.le_dualLattice`).
* `New.RealComplexForm.thetaShift`: translation by `a` twisted by `exp (-(B a z + B a a / 2))`. Two
  of these commute, for Appell–Humbert data, up to `𝐞 (E u v)`
  (`New.IsAppellHumbert.thetaShift_comm`). Those by vectors of the dual lattice
  `New.RealComplexForm.dualLattice` preserve, for such data, the theta functions
  (`New.IsAppellHumbert.thetaShift_mem_of_mem_dualLattice`).

## Relation to the literature

Known; see `Lib.Shimura.ComplexTheta.DimensionFormula` for sources.
-/

noncomputable section

/-!
## Theta functions, Riemann forms and Appell–Humbert data

The definitions (theta functions, the Riemann form, Appell–Humbert data, twisted translations and
the dual lattice) and their first properties.
-/

section ThetaSpace

namespace New

open Complex LinearMap Submodule FourierTransform
open scoped Real

instance : SMulCommClass ℂ ℝ ℂ := inferInstance

instance : ContinuousAdd ℂ := inferInstance

@[simp]
lemma coe_fourierChar_eq_exp (t : ℝ) : 𝐞 t = exp (2 * π * I * t) := by
  simp [Real.fourierChar_apply, mul_right_comm]

/-- A finite-dimensional complex normed space. -/
class FinComplexSpace (V : Type*) extends NormedAddCommGroup V, NormedSpace ℂ V, Module.Finite ℂ V

-- The projections rank low, so that direct instances (on `ℂ`, for example) are found first.
attribute [instance 100] FinComplexSpace.toNormedAddCommGroup FinComplexSpace.toNormedSpace

instance : FinComplexSpace ℂ where

instance {ι V : Type*} [Fintype ι] [FinComplexSpace V] : FinComplexSpace (ι → V) where

/-- The continuous complex-valued forms B(u, v) on V that are real-linear in u and
complex-linear in v. -/
abbrev RealComplexForm (V : Type*) [FinComplexSpace V] : Type _ := V →L[ℝ] V →L[ℂ] ℂ

instance {V V' : Type*} [FinComplexSpace V] [FinComplexSpace V'] : FinComplexSpace (V × V') where

/-- The subgroup `L` of `V` is a lattice of full rank: it is discrete and spans `V` over the
reals. -/
class abbrev IsFullRankLattice {V : Type*} [FinComplexSpace V] (L : Submodule ℤ V) :=
  DiscreteTopology L, IsZLattice ℝ L

variable {V V' : Type*} [FinComplexSpace V] [FinComplexSpace V'] {L : Submodule ℤ V}
  (φ : V' →L[ℂ] V) (B : RealComplexForm V) (χ : V → ℂ) (u v : V)

/-- The type `New.RealComplexForm` V of forms on V, tagged with a subgroup L of V (the lattice).
`New.RealComplexForm.thetaSpace` and `New.RealComplexForm.dualLattice` read L from the type. No
condition is imposed. -/
abbrev ThetaTori.LatticeForm (_ : Submodule ℤ V) : Type _ := RealComplexForm V

/-! ### Definitions -/

/-- The pull-back (u, v) ↦ B(φu, φv) of the form B along the complex-linear map φ. -/
@[simps! apply_apply]
def RealComplexForm.pullForm : V' →L[ℝ] V' →L[ℂ] ℂ :=
  (φ.precomp ℂ).restrictScalars ℝ ∘L B ∘L φ.restrictScalars ℝ

/-- The space of theta functions of type (B, χ) for L: entire f on V with
f(z + l) = χ(l)·exp(B(l,z) + B(l,l)/2)·f(z) for l in L. -/
def RealComplexForm.thetaSpace (B : ThetaTori.LatticeForm L) : Submodule ℂ (V → ℂ) :=
  ofLinearComb
    {f : V → ℂ |
      Differentiable ℂ f ∧
      ∀ l ∈ L, ∀ z : V, f (z + l) = χ l * Complex.exp (B l z + B l l / 2) * f z}
    ⟨0, by simp⟩ (by
      simp +contextual [field]
      fun_prop)

/-- The Riemann form of B: the alternating real form E(u, v) = Im(B(u,v) − B(v,u))/(2π). It is
additive in B, as a map from forms to real bilinear forms on V. -/
def RealComplexForm.riemannForm : RealComplexForm V →+ LinearMap.BilinForm ℝ V :=
  AddMonoidHom.mk'
    (fun B ↦
      mk₂ ℝ (fun u v ↦ (B u v - B v u).im / (2 * π)) (by simp; grind) (by simp; grind)
        (by simp; grind) (by simp; grind))
    (by simp [ext_iff₂]; grind)

/-- The complex number exp(2πi E(u, v)) of modulus one, where E is the Riemann form
`New.RealComplexForm.riemannForm` of B. -/
abbrev RealComplexForm.riemannPhase : ℂ := 𝐞 (B.riemannForm u v)

lemma riemannForm_def : B.riemannForm u v = (B u v - B v u).im / (2 * π) := rfl

/-- Appell–Humbert data: Re B is symmetric, and on L one has |χ| = 1 and
χ(l + m) = χ(l)χ(m)·exp(πi E(m, l)), E the Riemann form of B. -/
@[mk_iff]
class IsAppellHumbert (B : ThetaTori.LatticeForm L) (χ : V → ℂ) where
  /-- The real part of B is symmetric. -/
  re_symm (u v : V) : (B u v).re = (B v u).re
  /-- The multiplier χ has absolute value 1 on L. -/
  norm_eq_one : ∀ l ∈ L, ‖χ l‖ = 1
  /-- χ is a semicharacter of L for the Riemann form E of B:
  χ(l + m) = χ(l) χ(m) exp(π i E(m, l)). -/
  semicharacter : ∀ᵉ (l ∈ L) (m ∈ L), χ (l + m) = χ l * χ m * exp (π * I * B.riemannForm m l)

/-- The Riemann form E of B is positive: E(u, iu) > 0 for every u ≠ 0. -/
@[mk_iff pr_iff]
class IsPosRiemann : Prop where
  /-- E(u, iu) > 0 for every u ≠ 0. -/
  riemannForm_pos : ∀ u ≠ (0 : V), 0 < B.riemannForm u (I • u)

/-- The twisted translation by `a`, a complex-linear map on all functions `V → ℂ`:
`thetaShift B a f z = exp (-(B a z + B a a / 2)) * f (z + a)`. The factor is the inverse of the
exponential in `New.RealComplexForm.thetaSpace`, so for `a ∈ L` it multiplies a theta function by
`χ a`. -/
@[simps! -isSimp apply]
def RealComplexForm.thetaShift (a : V) : (V → ℂ) →ₗ[ℂ] V → ℂ :=
  (fun z ↦ Complex.exp (-(B a z + B a a / 2))) • funLeft ℂ ℂ (· + a)

/-- The dual of L for the Riemann form E of B: the v in V with E(v, l) an integer for all l in
L. -/
def RealComplexForm.dualLattice (B : ThetaTori.LatticeForm L) : Submodule ℤ V :=
  (B.riemannForm.dualSubmodule L).copy {v : V | ∀ l ∈ L, ∃ n : ℤ, B.riemannForm v l = n}
    (by simp [BilinForm.dualSubmodule, eq_comm])

export RealComplexForm (pullForm pullForm_apply_apply riemannForm thetaShift thetaShift_apply
  thetaSpace)

/-- A form B with B(u, v) = B(v, u) is complex linear in both arguments, hence holomorphic. -/
@[fun_prop]
lemma differentiable_of_symm (h_symm : ∀ u v : V, B u v = B v u) : Differentiable ℂ B :=
  -- `B` is complex linear in the second argument, hence by symmetry in the first.
  have h_smul (c : ℂ) (u : V) : B (c • u) = c • B u := by
    ext v
    rw [h_symm (c • u) v, map_smul, h_symm v u, _root_.smul_apply]
  ({ B with map_smul' := h_smul } : V →L[ℂ] V →L[ℂ] ℂ).differentiable

@[fun_prop, local simp]
lemma differentiable_thetaShift {f : V → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (B.thetaShift u f) := by
  exact Differentiable.mul (by fun_prop) (hf.comp (differentiable_id.add_const u))

lemma riemannForm_pullForm (u v : V') :
    riemannForm (B.pullForm φ) u v = B.riemannForm (φ u) (φ v) :=
  rfl

variable {B} {B' : RealComplexForm V} {f g : V → ℂ} (n : ℕ)

lemma riemannForm_swap : B.riemannForm v u = -B.riemannForm u v := by simp [riemannForm, fieldEq]

@[simp] lemma riemannForm_self : B.riemannForm u u = 0 := by simp [riemannForm]

lemma thetaShift_apply_apply (a z : V) :
    B.thetaShift a f z = exp (-(B a z + B a a / 2)) * f (z + a) :=
  rfl

/-- A real linear form φ with 𝐞(φ x) = 1 for every x is zero. -/
lemma eq_zero_of_forall_fourierChar_eq_one {W : Type*} [AddCommGroup W] [Module ℝ W] (φ : W →ₗ[ℝ] ℝ)
    (h_exp : ∀ x : W, (𝐞 (φ x) : ℂ) = 1) :
    φ = 0 := by
  -- A nonzero `φ` is onto, so it takes the value `1 / 2`, where the exponential is `-1`.
  by_contra h_ne
  obtain ⟨x, hx⟩ : ∃ x : W, φ x = 2⁻¹ := φ.surjective h_ne 2⁻¹
  have h_neg : exp (2 * π * I * φ x) = -1 := by simp [hx, mul_right_comm _ _ (2⁻¹ : ℂ)]
  have h_one : exp (2 * π * I * φ x) = 1 := (coe_fourierChar_eq_exp (φ x)).symm.trans (h_exp x)
  norm_num [h_one] at h_neg

@[simp]
lemma thetaShift_zero : B.thetaShift 0 f = f := by
  simp [funext_iff, thetaShift_apply]

@[simp]
lemma thetaShift_mul : (B + B').thetaShift u (f * g) = B.thetaShift u f * B'.thetaShift u g := by
  simp [funext_iff, thetaShift_apply, add_div, add_right_comm, exp_add, exp_neg, fieldEq]

@[simp]
lemma thetaShift_pow : (n • B).thetaShift u (f ^ n) = B.thetaShift u f ^ n := by
  simp [funext_iff, thetaShift_apply, exp_add, exp_neg, mul_pow, ← exp_nsmul, mul_div]

/-- If Re B(u, u) > 0 for every u ≠ 0, the Riemann form of B is positive. -/
lemma isPosRiemann_of_re_pos (h_re_pos : ∀ u ≠ (0 : V), 0 < (B u u).re) : IsPosRiemann B := by
  refine ⟨fun u hu ↦ pos_of_mul_pos_right (a := 2 * π) ?_ (by positivity)⟩
  have h_two_pi : 2 * π * B.riemannForm u (I • u) = (B u u).re + (B (I • u) (I • u)).re := by
    simp [riemannForm_def, field, sub_eq_add_neg]
  rw [h_two_pi]
  exact add_pos (h_re_pos u hu) (h_re_pos (I • u) (smul_ne_zero I_ne_zero hu))

lemma IsPosRiemann.nsmul (h_pos : IsPosRiemann B) {n : ℕ} (hn : n ≠ 0) : IsPosRiemann (n • B) :=
  ⟨fun u hu ↦ by simpa using mul_pos (Nat.cast_pos.2 hn.bot_lt) (h_pos.riemannForm_pos u hu)⟩

instance [h : IsPosRiemann B] [NeZero n] : IsPosRiemann (n • B) := h.nsmul NeZero.out

variable {B B' : ThetaTori.LatticeForm L} {χ} {χ' : V → ℂ} {l : V} {m : ℕ}
  {a : V} [hB : IsAppellHumbert B χ]

/-- The term exp(B(x, y − x + l) − B(l,y) − B(l,l)/2)/χ(l) of the Poincaré series at (x, y), for
l in L. The unnamed argument is the Appell–Humbert data (B, χ), for dot notation. -/
def IsAppellHumbert.poincareTerm (_ : IsAppellHumbert B χ) (x y : V) (l : L) : ℂ :=
  Complex.exp (B x (y - x + l) - B l y - B l l / 2) / χ l

/-- The Poincaré series K(x, y) = ∑_{l ∈ L} exp(B(x, y − x + l) − B(l,y) − B(l,l)/2)/χ(l) of
Appell–Humbert data (B, χ). -/
def IsAppellHumbert.poincareSeries (x y : V) : ℂ := tsum (hB.poincareTerm x y)

omit hB in
/-- Membership in the space of theta functions of type (B, χ), written out. -/
lemma mem_thetaSpace_iff :
    f ∈ B.thetaSpace χ ↔
      Differentiable ℂ f ∧ ∀ l ∈ L, ∀ z : V, f (z + l) = χ l * exp (B l z + B l l / 2) * f z :=
  Iff.rfl

omit hB in
lemma differentiable_of_mem_thetaSpace (hf : f ∈ B.thetaSpace χ) : Differentiable ℂ f :=
  (mem_thetaSpace_iff.mp hf).left

omit hB in
/-- The automorphy law of a theta function of type (B, χ) at `z + l`, for `l` in `L`. -/
lemma apply_add_of_mem_thetaSpace (hf : f ∈ B.thetaSpace χ) (hl : l ∈ L) (z : V) :
    f (z + l) = χ l * exp (B l z + B l l / 2) * f z :=
  (mem_thetaSpace_iff.mp hf).right l hl z

lemma ThetaTori.mem_dualLattice_nsmul : a ∈ (m • B).dualLattice ↔ m • a ∈ B.dualLattice :=
  forall_congr' (by simp)

include hB

/-! ### Consequences of the Appell–Humbert conditions -/

/-- As `Re B` is symmetric, `B u v - B v u` is purely imaginary, equal to `2πi E(u, v)`. -/
lemma IsAppellHumbert.sub_eq_riemannForm : B u v - B v u = 2 * π * I * B.riemannForm u v := by
  apply Complex.ext
  · simp [hB.re_symm u v]
  · suffices (B u v - B v u).im = 2 * π * B.riemannForm u v by simpa
    rw [riemannForm_def]
    field_simp

/-- For Appell–Humbert data (`B`, `χ`) on `L`, the twisted translation
`thetaShift B a f z = exp (-(B a z + B a a / 2)) * f (z + a)` by `v` followed by the one by `u`
equals `exp (π i E(u, v))` times the twisted translation by `u + v`. Here E is the Riemann form of
`B`, and the identity holds for every function `f : V → ℂ`. -/
lemma IsAppellHumbert.thetaShift_thetaShift (u v : V) :
    B.thetaShift u (B.thetaShift v f) =
      exp (π * I * B.riemannForm u v) • B.thetaShift (u + v) f := by
  -- The exponents differ by `(B u v - B v u) / 2`, which `sub_eq_riemannForm` computes.
  have h_exponent (z : V) :
      -(B u z + B u u / 2) + -(B v (z + u) + B v v / 2) =
        π * I * B.riemannForm u v + -(B (u + v) z + B (u + v) (u + v) / 2) := by
    simp only [map_add, _root_.add_apply]
    linear_combination (hB.sub_eq_riemannForm u v) / 2
  funext z
  simp only [thetaShift_apply_apply, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← exp_add, h_exponent z, exp_add, add_assoc]
  ring

/-- The sum of the forms and the product of the multipliers of two Appell–Humbert data are again
Appell–Humbert data. -/
lemma IsAppellHumbert.add (hB' : IsAppellHumbert B' χ') : IsAppellHumbert (B + B') (χ * χ') where
  re_symm u v := by simp [hB.re_symm u v, hB'.re_symm u v]
  norm_eq_one l hl := by simp [hB.norm_eq_one l hl, hB'.norm_eq_one l hl]
  semicharacter l hl m hm := by
    simp [hB.semicharacter l hl m hm, hB'.semicharacter l hl m hm, mul_add, exp_add]
    ring

/-- If `(B, χ)` are Appell–Humbert data, then so are `(-B, χ⁻¹)`. -/
lemma IsAppellHumbert.neg : IsAppellHumbert (-B) χ⁻¹ where
  re_symm u v := by simp [hB.re_symm u v]
  norm_eq_one l hl := by simp [hB.norm_eq_one l hl]
  semicharacter l hl m hm := by simp [hB.semicharacter l hl m hm, exp_neg, mul_comm]

/-- If `(B, χ)` are Appell–Humbert data, then so are `(n • B, χ ^ n)`. -/
instance IsAppellHumbert.nsmul : IsAppellHumbert (n • B) (χ ^ n) where
  re_symm u v := by simp [hB.re_symm u v]
  norm_eq_one l hl := by simp [hB.norm_eq_one l hl]
  semicharacter l hl m hm := by
    simp [hB.semicharacter l hl m hm, mul_pow, ← exp_nat_mul, mul_left_comm]

/-- Multiplying `χ` by the unitary character `l ↦ exp (2πi E(l, a))`, with `E` the Riemann form of
any `C` (by default `B`), keeps the Appell–Humbert conditions. -/
instance IsAppellHumbert.mul_riemannPhase (a : V) (C : RealComplexForm V := B) :
    IsAppellHumbert B fun l : V ↦ χ l * C.riemannPhase l a where
  re_symm := hB.re_symm
  norm_eq_one l hl := by simp [hB.norm_eq_one l hl, norm_exp]
  semicharacter l hl m hm := by
    simp [RealComplexForm.riemannPhase, hB.semicharacter l hl m hm, mul_add, exp_add]
    ring

/-- For Appell–Humbert data, two twisted translations commute up to the phase 𝐞(E(u, v)). -/
lemma IsAppellHumbert.thetaShift_comm (u v : V) :
    B.thetaShift u (B.thetaShift v f) = B.riemannPhase u v • B.thetaShift v (B.thetaShift u f) := by
  -- Both sides are multiples of the twisted translation by `u + v` (`thetaShift_thetaShift`).
  rw [hB.thetaShift_thetaShift, hB.thetaShift_thetaShift v u, add_comm v u, smul_smul,
    riemannForm_swap u v]
  have h_phase : exp (π * I * B.riemannForm u v) =
      B.riemannPhase u v * exp (π * I * ↑(-B.riemannForm u v)) := by
    rw [RealComplexForm.riemannPhase, coe_fourierChar_eq_exp, ← exp_add]
    push_cast
    ring_nf
  rw [h_phase]

lemma IsAppellHumbert.ne_zero (hl : l ∈ L) : χ l ≠ 0 :=
  norm_ne_zero_iff.1 (by simp [hB.norm_eq_one l hl])

/-- For Appell–Humbert data, L lies in its dual lattice: the Riemann form is integral on L. -/
lemma IsAppellHumbert.le_dualLattice : L ≤ B.dualLattice := by
  -- Compare `χ (l + m)` with `χ (m + l)`; as the Riemann form `E` is alternating,
  -- `exp (2πi E(l, m)) = 1`.
  intro l hl m hm
  have h_exp : exp (π * I * B.riemannForm l m) = exp (π * I * B.riemannForm m l) := by
    refine mul_left_cancel₀ (mul_ne_zero (hB.ne_zero hl) (hB.ne_zero hm)) ?_
    rw [← hB.semicharacter l hl m hm, mul_comm (χ l) (χ m), ← hB.semicharacter m hm l hl, add_comm]
  obtain ⟨k, hk⟩ :
      ∃ k : ℤ, π * I * B.riemannForm l m = π * I * B.riemannForm m l + k * (2 * π * I) :=
    exp_eq_exp_iff_exists_int.mp h_exp
  refine ⟨k, ofReal_injective (mul_left_cancel₀ two_pi_I_ne_zero ?_)⟩
  rw [riemannForm_swap l m] at hk
  push_cast at hk ⊢
  linear_combination hk

/-- For Appell–Humbert data, if n • a and m • b lie in L, then exp(πi E(a, b)) is a root of unity
of order dividing 2nm. -/
lemma IsAppellHumbert.exp_riemannForm_pow_eq_one {n m : ℕ} {b : V} (hna : n • a ∈ L)
    (hmb : m • b ∈ L) :
    exp (π * I * B.riemannForm a b) ^ (2 * n * m) = 1 := by
  -- `n * m * E(a, b) = E(n • a, m • b)` is an integer, `E` the Riemann form.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, B.riemannForm (n • a) (m • b) = k := hB.le_dualLattice hna (m • b) hmb
  have h_int : (n : ℂ) * m * B.riemannForm a b = k := by
    rw [← ofReal_intCast, ← hk]
    simp [mul_assoc]
  rw [← exp_nat_mul, exp_eq_one_iff]
  refine ⟨k, ?_⟩
  push_cast
  linear_combination (2 * π * I) * h_int

/-- If `(B, χ)` and `(B', χ')` are Appell–Humbert data with the same Riemann form and the same
multiplier on `L`, then multiplication by `exp ((B' z z - B z z) / 2)` turns theta functions of the
first type into theta functions of the second. -/
lemma IsAppellHumbert.exp_mul_mem_thetaSpace (hB' : IsAppellHumbert B' χ')
    (h_riem : B.riemannForm = B'.riemannForm) (hχ : ∀ l ∈ L, χ l = χ' l) (hf : f ∈ B.thetaSpace χ) :
    (fun z : V ↦ Complex.exp ((B' z z - B z z) / 2) * f z) ∈ B'.thetaSpace χ' := by
  -- As both forms have symmetric real part and the same Riemann form, `B' - B` is symmetric, so
  -- it is complex bilinear and `z ↦ B' z z - B z z` is holomorphic.
  have h_symm (u v : V) : B' u v - B u v = B' v u - B v u := by
    have h_sub : B u v - B v u = 2 * π * I * B'.riemannForm u v := by
      rw [← h_riem]
      exact hB.sub_eq_riemannForm u v
    have h_sub' : B' u v - B' v u = 2 * π * I * B'.riemannForm u v := hB'.sub_eq_riemannForm u v
    linear_combination h_sub' - h_sub
  have h_diff : Differentiable ℂ fun z ↦ (B' - B) z z :=
    (differentiable_of_symm (B' - B) h_symm).clm_apply differentiable_id
  rw [mem_thetaSpace_iff]
  refine ⟨(h_diff.mul_const _).cexp.mul (differentiable_of_mem_thetaSpace hf), fun l hl z ↦ ?_⟩
  -- Compare the exponents: the cross terms `(B' - B) z l` and `(B' - B) l z` agree by `h_symm`.
  have h_exponent :
      (B' (z + l) (z + l) - B (z + l) (z + l)) / 2 + (B l z + B l l / 2) =
        B' l z + B' l l / 2 + (B' z z - B z z) / 2 := by
    simp only [map_add, _root_.add_apply]
    linear_combination h_symm z l / 2
  calc
    ((B' (z + l) (z + l) - B (z + l) (z + l)) / 2).exp * f (z + l) =
      χ l * ((B' (z + l) (z + l) - B (z + l) (z + l)) / 2 + (B l z + B l l / 2)).exp * f z := by
      rw [apply_add_of_mem_thetaSpace hf hl z,
        exp_add ((B' (z + l) (z + l) - B (z + l) (z + l)) / 2) (B l z + B l l / 2)]
      ring
    _ = χ' l * (B' l z + B' l l / 2).exp * (((B' z z - B z z) / 2).exp * f z) := by
      rw [h_exponent, hχ l hl, exp_add]
      ring

omit hB in
lemma thetaShift_of_mem (hf : f ∈ B.thetaSpace χ) (hl : l ∈ L) : B.thetaShift l f = χ l • f := by
  funext z
  rw [thetaShift_apply_apply, apply_add_of_mem_thetaSpace hf hl z, exp_neg]
  simp [field]

/-! ### Translates, products and powers of a theta function -/

/-- On a theta function, adding a lattice vector `l` to `u` changes the translation by `u` only by
a scalar. -/
lemma IsAppellHumbert.thetaShift_add_eq_smul_of_mem (hf : f ∈ B.thetaSpace χ) (u : V) (hl : l ∈ L) :
    B.thetaShift (u + l) f = (exp (-(π * I * B.riemannForm u l)) * χ l) • B.thetaShift u f := by
  -- Translation by `l ∈ L` multiplies `f` by `χ l`; compose it with translation by `u`.
  have h_comp : B.thetaShift u (B.thetaShift l f) =
      exp (π * I * B.riemannForm u l) • B.thetaShift (u + l) f :=
    hB.thetaShift_thetaShift u l
  rw [thetaShift_of_mem hf hl, map_smul] at h_comp
  rw [mul_smul, h_comp, smul_smul, exp_neg, inv_mul_cancel₀ (exp_ne_zero _), one_smul]

/-- For Appell–Humbert data (B, χ) for a subgroup `L` of the complex space `V`, the translate by
`a ∈ V` of a theta function is a theta function for the multiplier `l ↦ χ l * exp (2πi E(l, a))`. -/
lemma IsAppellHumbert.thetaShift_mem (hf : f ∈ B.thetaSpace χ) (a : V) :
    B.thetaShift a f ∈ B.thetaSpace fun l : V ↦ χ l * B.riemannPhase l a := by
  -- The exponents differ by `B l a - B a l = 2πi E(l, a)` (`sub_eq_riemannForm`).
  rw [mem_thetaSpace_iff]
  refine ⟨differentiable_thetaShift B a (differentiable_of_mem_thetaSpace hf), fun l hl z ↦ ?_⟩
  have h_exp :
      exp (-(B a (z + l) + B a a / 2)) * exp (B l (z + a) + B l l / 2) =
        exp (2 * π * I * B.riemannForm l a) * exp (B l z + B l l / 2) *
          exp (-(B a z + B a a / 2)) := by
    rw [← exp_add, ← exp_add, ← exp_add]
    congr 1
    simp only [map_add]
    linear_combination hB.sub_eq_riemannForm l a
  rw [thetaShift_apply_apply, thetaShift_apply_apply, add_right_comm z l a,
    apply_add_of_mem_thetaSpace hf hl (z + a), RealComplexForm.riemannPhase, coe_fourierChar_eq_exp]
  linear_combination (χ l * f (z + a)) * h_exp

/-- For Appell–Humbert data, the twisted translation by a vector a of the dual lattice maps theta
functions of type (B, χ) to theta functions of the same type. -/
lemma IsAppellHumbert.thetaShift_mem_of_mem_dualLattice (ha : a ∈ B.dualLattice)
    (hf : f ∈ B.thetaSpace χ) :
    B.thetaShift a f ∈ B.thetaSpace χ := by
  -- The extra factor in `thetaShift_mem` is `1`, since `B.riemannForm a l` is an integer for
  -- `l ∈ L`.
  have h_mem : B.thetaShift a f ∈ B.thetaSpace fun l : V ↦ χ l * B.riemannPhase l a :=
    hB.thetaShift_mem hf a
  rw [mem_thetaSpace_iff]
  refine ⟨differentiable_of_mem_thetaSpace h_mem, fun l hl z ↦ ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, B.riemannForm a l = k := ha l hl
  have h_one : B.riemannPhase l a = 1 := by simp [riemannForm_swap a, hk, ← zsmul_eq_mul', exp_neg]
  simpa only [h_one, mul_one] using apply_add_of_mem_thetaSpace h_mem hl z

/-- Let (B, χ) be Appell–Humbert data and `a` a vector in the dual lattice of L. This is the twisted
translation `New.RealComplexForm.thetaShift` by `a`, as an endomorphism of the theta functions of
type (B, χ). -/
abbrev IsAppellHumbert.thetaShiftEnd (a : B.dualLattice) : B.thetaSpace χ →ₗ[ℂ] B.thetaSpace χ :=
  (B.thetaShift a).restrict fun _ ↦ hB.thetaShift_mem_of_mem_dualLattice a.prop

omit hB

/-- The product of theta functions of types `(B, χ)` and `(B', χ')` is a theta function of type
`(B + B', χ * χ')`. -/
lemma thetaSpace.mul (hf : f ∈ B.thetaSpace χ) (hg : g ∈ B'.thetaSpace χ') :
    f * g ∈ (B + B').thetaSpace (χ * χ') := by
  refine ⟨(differentiable_of_mem_thetaSpace hf).mul (differentiable_of_mem_thetaSpace hg),
    fun l hl z ↦ ?_⟩
  have h_exp : exp (B l z + B l l / 2) * exp (B' l z + B' l l / 2) =
      exp ((B + B') l z + (B + B') l l / 2) := by
    simp [← exp_add, add_div, add_add_add_comm]
  simp only [Pi.mul_apply, apply_add_of_mem_thetaSpace hf hl z, apply_add_of_mem_thetaSpace hg hl z,
    ← h_exp]
  ring

/-- The `n`-th power of a theta function of type `(B, χ)` is one of type `(n • B, χ ^ n)`. -/
lemma thetaSpace.pow (hf : f ∈ B.thetaSpace χ) (n : ℕ) : f ^ n ∈ (n • B).thetaSpace (χ ^ n) := by
  refine ⟨(differentiable_of_mem_thetaSpace hf).pow n, fun l hl z ↦ ?_⟩
  have h_exp : exp (B l z + B l l / 2) ^ n = exp ((n • B) l z + (n • B) l l / 2) := by
    simp [← exp_nat_mul, mul_add, mul_div_assoc]
  simp only [Pi.pow_apply, apply_add_of_mem_thetaSpace hf hl z, ← h_exp]
  ring

end New

end ThetaSpace

/-!
## Factors of automorphy, positive Riemann forms and theta functions without zeros

`L` is a full lattice in a finite-dimensional complex space `V`, and the form `B` is real-linear in
the first variable and complex-linear in the second.

* `New.exists_factor_of_automorphy`: if `f` has no zero and each quotient `w ↦ f (l + w) / f w` has
  constant logarithmic derivative, then for some `B` with symmetric real part
  `f (z + l) = f z * exp (B l z) * f l / f 0`.
* `New.IsPosRiemann.isDualFamily`: for a positive Riemann form `E` the characters
  `x ↦ exp (2πi E(x, a))`, `a` in the dual lattice, separate the points of `V ⧸ L`.
* `New.IsAppellHumbert.eq_exp_of_ne_zero`: a theta function without zeros is
  `f 0 * exp (B z z / 2)`.
-/

namespace New

open FourierTransform Complex Module MeasureTheory QuotientAddGroup Fintype Quotient
  LinearMap.BilinForm Submodule Finset ComplexConjugate IsZLattice

variable {V : Type} [FinComplexSpace V]
  {L : Submodule ℤ V} [IsFullRankLattice L] {B : ThetaTori.LatticeForm L}
  {χ f : V → ℂ} [hB : IsAppellHumbert B χ] [hp : IsPosRiemann B] (hf : f ∈ B.thetaSpace χ)

/-- Let f : V → ℂ have no zero, and for each l in the lattice L let the quotient w ↦ f(l + w)/f(w)
have as logarithmic derivative a constant complex-linear form. Then there is a form B, real-linear
in the first variable and complex-linear in the second, such that (a) f(z + l) =
f(z)·exp(B(l, z))·f(l)/f(0) for l in L and z in V, and (b) the real part of B is symmetric. -/
lemma exists_factor_of_automorphy (hf_ne : ∀ z : V, f z ≠ 0)
    (h_logDeriv : ∀ l : L, ∃ a : V →L[ℂ] ℂ, ∀ z : V,
      HasFDerivAt (fun w ↦ f (l + w) / f w) ((f (l + z) / f z) • a) z) :
    ∃ B : RealComplexForm V,
      -- (a)
      (∀ l ∈ L, ∀ z : V, f (z + l) = f z * exp (B l z) * f l / f 0) ∧
      -- (b)
      ∀ u v : V, (B u v).re = (B v u).re := by
  -- The logarithmic derivatives `a l` are additive in `l`, so they extend to a real-linear `B`.
  -- Integrating gives the factor of automorphy; computing `f (l + m)` in both orders gives the
  -- symmetry of `Re B` on `L`, which spans `V` over `ℝ`.
  choose a ha using h_logDeriv
  have a_add (l m : L) : a (l + m) = a l + a m := by
    -- The quotient for `l + m` is that for `m` times the translate by `m` of that for `l`.
    have h_quot : (fun w : V ↦ f (↑(l + m) + w) / f w) =
        fun w : V ↦ f (↑m + w) / f w * (f (↑l + (↑m + w)) / f (↑m + w)) := by
      ext w
      simp [add_assoc, field, hf_ne]
    have h_prod : HasFDerivAt (fun w : V ↦ f (↑(l + m) + w) / f w)
        ((f (↑m + 0) / f 0) • (f (↑l + (↑m + 0)) / f (↑m + 0)) • a l +
          (f (↑l + (↑m + 0)) / f (↑m + 0)) • (f (↑m + 0) / f 0) • a m) 0 := by
      rw [h_quot]
      exact (ha m 0).mul ((hasFDerivAt_comp_add_left (m : V)).mpr (ha l ((m : V) + 0)))
    refine (smul_right_inj (div_ne_zero (hf_ne _) (hf_ne 0))).mp
      ((ha (l + m) 0).unique (h_prod.congr_fderiv ?_))
    -- Both coefficients are `f (l + m) / f 0`.
    match_scalars <;> simp [field, hf_ne]
  -- Extend `a` from a `ℤ`-basis of `L`, which is an `ℝ`-basis of `V`.
  obtain ⟨B, rfl⟩ : ∃ B : V →L[ℝ] V →L[ℂ] ℂ, (fun l : L ↦ B l) = a := by
    let F : L →+ V →L[ℂ] ℂ := AddMonoidHom.mk' a a_add
    refine ⟨((finBasis ℤ L).ofZLatticeBasis ℝ L).constrL (F ∘ finBasis ℤ L), ?_⟩
    -- The extension agrees with `F`, that is with `a`, on the basis and hence on `L`.
    have h_F : ∀ l : L, F l = a l := fun _ ↦ rfl
    simpa [Int.cast_smul_eq_zsmul, ← map_sum, ← map_zsmul, funext_iff] using h_F
  have factor (l : V) (hl : l ∈ L) (z : V) : f (z + l) = f z * (B l z).exp * f l / f 0 := by
    -- `w ↦ f (l + w) / f w * exp (-B l w)` has derivative zero, so it is constant.
    have h_deriv (w : V) : HasFDerivAt (fun w : V ↦ f (l + w) / f w * exp (-B l w)) 0 w :=
      ((ha ⟨l, hl⟩ w).mul (-B l).hasFDerivAt.cexp).congr_fderiv (by module)
    have const : f (l + z) / f z * exp (-B l z) = f (l + 0) / f 0 * exp (-B l 0) :=
      is_const_of_fderiv_eq_zero (fun w ↦ (h_deriv w).differentiableAt)
        (fun w ↦ (h_deriv w).fderiv) z 0
    simpa [exp_neg, add_comm, field, hf_ne] using const
  have re_symm (l : V) (hl : l ∈ L) (m : V) (hm : m ∈ L) : (B l m).re = (B m l).re := by
    -- Compute `f (m + l)` by translating `m` by `l` and by translating `l` by `m`.
    have h_two : f m * exp (B l m) * f l / f 0 = f l * exp (B m l) * f m / f 0 := by
      rw [← factor l hl m, ← factor m hm l, add_comm]
    have exp_eq : exp (B l m) = exp (B m l) := by
      simpa [mul_comm, mul_left_comm, field, hf_ne] using h_two
    simpa [norm_exp] using congrArg (‖·‖) exp_eq
  refine ⟨B, factor, fun u v ↦ ?_⟩
  -- Both sides are real-bilinear in `(u, v)`, and `L` spans `V` over `ℝ`.
  have span_top : ∀ x : V, x ∈ span ℝ (L : Set V) := eq_top_iff'.mp IsZLattice.span_top
  induction span_top u, span_top v using span_induction₂ with
  | mem_mem x y hx hy => exact re_symm x hx y hy
  | _ => simp [*]

/-- The torus `V ⧸ L` is compact, as `L` is a full lattice. -/
instance : CompactSpace (V ⧸ L.toAddSubgroup) where
  isCompact_univ := by
    -- `V ⧸ L` is the range of the quotient map, which is periodic under `L`.
    rw [← range_mk]
    exact isCompact_range_of_periodic L _ continuous_mk (by simp)

/-! ### Positive Riemann forms and the dual lattice -/

omit [IsFullRankLattice L] in
/-- A positive Riemann form (instance `hp`) is nondegenerate. -/
lemma IsPosRiemann.nondegenerate : B.riemannForm.Nondegenerate :=
  .ofSeparatingLeft fun u hu ↦ by_contra fun h_ne ↦ (hp.riemannForm_pos u h_ne).ne' (hu _)

omit [IsFullRankLattice L] in
/-- Positivity of the Riemann form is an open condition on `B`: if the Riemann form of `B` is
positive (instance `hp`), so is that of `B - A` for every `A` near `0`. -/
lemma IsPosRiemann.eventually_add_neg :
    ∀ᶠ A : ThetaTori.LatticeForm L in nhds 0, IsPosRiemann (B + -A) := by
  -- Positivity on the unit sphere, a compact set, persists under a small change of the form.
  have sphere_pos : ∀ᶠ A in nhds (0 : RealComplexForm V), ∀ u ∈ Metric.sphere (0 : V) 1,
      (B - A).riemannForm u (I • u) ∈ Set.Ioi 0 := by
    -- At `A = 0` the values lie in the open set `Set.Ioi 0`.
    refine (isCompact_sphere 0 1).eventually_forall_mem (fun A u ↦ (B - A).riemannForm u (I • u)) _
      (fun u hu ↦ Ioi_mem_nhds ?_) ?_
    · simpa using hp.riemannForm_pos u (ne_zero_of_mem_unit_sphere ⟨u, hu⟩)
    · simp [riemannForm]
      fun_prop
  -- Scale a nonzero vector to the sphere.
  filter_upwards [sphere_pos] with A hA
  refine ⟨fun u hu ↦ ?_⟩
  have h_unit : ‖u‖⁻¹ • u ∈ Metric.sphere (0 : V) 1 := by simp [norm_smul, hu]
  simpa [smul_comm I, hu, norm_smul] using hA (‖u‖⁻¹ • u) h_unit

/-- If the Riemann form of `B` is positive (instance `hp`), the dual lattice
`New.RealComplexForm.dualLattice` is a full lattice in `V`. -/
scoped instance IsAppellHumbert.isFullRankLattice_dualLattice :
    IsFullRankLattice B.dualLattice := by
  -- The dual lattice is the `ℤ`-span of the basis dual to a basis of `L`.
  rw [RealComplexForm.dualLattice, copy_eq, ← (finBasis _ L).ofZLatticeBasis_span ℝ,
    dualSubmodule_span_of_basis _ hp.nondegenerate]
  exact {}

/-- For a positive Riemann form `E` of `B` (instance `hp`), `a ↦ (x ↦ exp (2πi E(x, a)))` embeds the
dual lattice in the unitary characters of `V ⧸ L`, and these characters separate the points of
`V ⧸ L`. -/
lemma IsPosRiemann.isDualFamily :
    IsDualFamily L.toAddSubgroup fun (a : B.dualLattice) (x : V) ↦ 𝐞 (B.riemannForm x a) where
  periodic a := by
    refine ⟨by continuity, fun l hl x ↦ ?_⟩
    -- Periodic under `L`, since `B.riemannForm a l` is an integer.
    obtain ⟨n, hn⟩ : ∃ n : ℤ, B.riemannForm a l = n := a.prop l hl
    simp [riemannForm_swap (a : V), hn, exp_add, exp_neg, mul_add, ← zsmul_eq_mul']
  add_left a b x := by simp [exp_add, mul_add]
  add_right a x y := by simp [exp_add, mul_add]
  norm_eq_one a x := by simp [norm_exp]
  mem_of_forall_eq_one x hx := by
    -- The dual of the dual of `L` is `L`, and `x` pairs integrally with the dual lattice.
    have h_double_dual :
        B.riemannForm.flip.dualSubmodule (B.riemannForm.dualSubmodule L) = L := by
      have h_basis := dualSubmodule_flip_dualSubmodule_of_basis (R := ℤ) B.riemannForm
        hp.nondegenerate ((finBasis ℤ L).ofZLatticeBasis ℝ L)
      rwa [(finBasis ℤ L).ofZLatticeBasis_span ℝ] at h_basis
    rw [← h_double_dual, Submodule.mem_toAddSubgroup, mem_dualSubmodule]
    intro a ha
    -- `B.dualLattice` is a copy of `B.riemannForm.dualSubmodule L`.
    have ha_dual : a ∈ B.dualLattice := by rwa [RealComplexForm.dualLattice, copy_eq]
    -- `𝐞 (E(x, a)) = 1` says that `E(x, a)` is an integer; `↓` applies these lemmas before the
    -- character is unfolded to an exponential.
    have h_one : (𝐞 (B.riemannForm x a) : ℂ) = 1 := hx ⟨a, ha_dual⟩
    simpa [↓Circle.coe_eq_one, ↓fourierChar_eq_one_iff, riemannForm_swap x, eq_comm] using h_one
  eq_zero_of_forall_eq_one a ha := by
    -- The linear form `x ↦ B.riemannForm x a` vanishes, and `B.riemannForm` is nondegenerate.
    have h_form_zero : B.riemannForm.flip (a : V) = 0 := eq_zero_of_forall_fourierChar_eq_one _ ha
    simpa using LinearMap.ker_eq_bot'.mp hp.nondegenerate.flip.ker_eq_bot _ h_form_zero

include hB hf

omit hp

/-! ### Theta functions on complex lines -/

/-- Let (B, χ) be Appell–Humbert data (instance `hB`) and f a theta function of that type
(hypothesis `hf`). Then the values ‖thetaShift u f 0‖ = |exp(−B(u, u)/2)·f(u)|, for u in V, form a
compact set. -/
lemma IsAppellHumbert.isCompact_range_norm_thetaShift :
    IsCompact (Set.range fun u : V ↦ ‖B.thetaShift u f 0‖) := by
  have hf_cont : Continuous f := (differentiable_of_mem_thetaSpace hf).continuous
  refine isCompact_range_of_periodic L _ ?_ fun u l hl ↦ ?_
  · simp only [thetaShift_apply_apply]
    fun_prop
  · -- A shift by a lattice vector multiplies `B.thetaShift u f` by a factor of absolute value one.
    have h_factor : ‖exp (-((Real.pi : ℂ) * I * B.riemannForm u l)) * χ l‖ = 1 := by
      simp [norm_exp, hB.norm_eq_one l hl]
    rw [thetaShift_add_eq_smul_of_mem hf u hl, Pi.smul_apply, smul_eq_mul, norm_mul, h_factor,
      one_mul]

/-- Let f be a theta function (hypothesis `hf`) for Appell–Humbert data (B, χ) (instance `hB`) on
the full lattice L in V. If the Riemann form E of B satisfies E(u, iu) ≤ 0, then
f(tu) = exp(t²B(u, u)/2)·f(0) for every complex t. -/
lemma IsAppellHumbert.apply_smul_of_nonpos (u : V) (h_nonpos : B.riemannForm u (I • u) ≤ 0)
    (t : ℂ) :
    f (t • u) = exp (t * t * B u u / 2) * f 0 := by
  -- Liouville's theorem for the entire function `g` on the line through `u`.
  let g (s : ℂ) : ℂ := exp (-(s * s * B u u / 2)) * f (s • u)
  have g_diff : Differentiable ℂ g := by
    have f_diff := differentiable_of_mem_thetaSpace hf
    fun_prop
  -- For `s = x + y I` the left side minus the right side is
  -- `2 π y ^ 2 * B.riemannForm u (I • u) ≤ 0`.
  have re_le (s : ℂ) : (B (s • u) (s • u)).re ≤ (s * s * B u u).re := by
    obtain ⟨x, y⟩ := s
    have h_im : (B u u).re ≤ (B (I • u) u).im := by
      simpa [mul_smul, hB.re_symm, riemannForm, fieldLe] using h_nonpos
    have h_expand :
        ((⟨x, y⟩ : ℂ) * ⟨x, y⟩ * B u u).re - (B ((⟨x, y⟩ : ℂ) • u) ((⟨x, y⟩ : ℂ) • u)).re =
          y ^ 2 * ((B (I • u) u).im - (B u u).re) := by
      simp [mul_smul, hB.re_symm, mk_eq_add_mul_I, add_smul, mul_add]
      ring
    linarith [mul_nonneg (sq_nonneg y) (sub_nonneg.mpr h_im)]
  -- Hence `g` is bounded by the normalised absolute value of `f`, which is bounded on `V`.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C ∈ upperBounds (Set.range fun v : V ↦ ‖B.thetaShift v f 0‖) :=
    (isCompact_range_norm_thetaShift hf).bddAbove
  have g_le (s : ℂ) : ‖g s‖ ≤ C :=
    calc
      ‖g s‖ = Real.exp (-((s * s * B u u).re / 2)) * ‖f (s • u)‖ := by simp [g, norm_exp]
      _ ≤ Real.exp (-((B (s • u) (s • u)).re / 2)) * ‖f (s • u)‖ := by grw [re_le s]
      _ = ‖B.thetaShift (s • u) f 0‖ := by simp [thetaShift, norm_exp]
      _ ≤ C := hC ⟨s • u, rfl⟩
  have g_const : g t = g 0 := g_diff.apply_eq_apply_of_bounded
    (isBounded_iff_forall_norm_le.mpr ⟨C, Set.forall_mem_range.mpr g_le⟩) t 0
  simpa [g, field, exp_neg] using g_const

/-- If a theta function f (hypothesis `hf`) for Appell–Humbert data (B, χ) (instance `hB`) has no
zero on V, then the Riemann form of B vanishes identically, χ is 1 on L, and
f(z) = f(0)·exp(B(z, z)/2) for all z. -/
lemma IsAppellHumbert.eq_exp_of_ne_zero (hf_ne : ∀ z : V, f z ≠ 0) :
    B.riemannForm = 0 ∧ (∀ l ∈ L, χ l = 1) ∧ ∀ z : V, f z = exp (B z z / 2) * f 0 := by
  -- On each complex line, `apply_smul_of_nonpos` applies to `f` or, if
  -- `B.riemannForm z (I • z) ≥ 0`, to `f⁻¹`.
  have hf_auto : ∀ l ∈ L, ∀ z : V, f (z + l) = χ l * exp (B l z + B l l / 2) * f z := hf.2
  have on_line (z : V) (t : ℂ) : f (t • z) = (t * t * B z z / 2).exp * f 0 := by
    rcases le_total (B.riemannForm z (I • z)) 0 with hle | hge
    · exact apply_smul_of_nonpos hf z hle t
    · -- `f⁻¹` is a theta function of type `(-B, χ⁻¹)`, and its Riemann form is `≤ 0` on `z`.
      have h_inv_auto : ∀ l ∈ L, ∀ w : V,
          f⁻¹ (w + l) = χ⁻¹ l * exp ((-B) l w + (-B) l l / 2) * f⁻¹ w := by
        simp_all [exp_add, exp_neg, field, neg_div]
      have inv_mem : f⁻¹ ∈ (-B).thetaSpace χ⁻¹ := ⟨hf.1.inv hf_ne, h_inv_auto⟩
      simpa [exp_neg, field, hf_ne, neg_div] using
        (hB.neg.apply_smul_of_nonpos inv_mem z (by simpa using hge) t).symm
  -- Compare the two formulas for `‖f (I • z)‖`, from the points `(I • z, 1)` and `(z, I)`.
  have re_eq (z : V) : (B z z).re = (B (I • z) z).im := by
    have h_norm : ‖f ((1 : ℂ) • I • z)‖ = ‖(1 * 1 * B (I • z) (I • z) / 2).exp * f 0‖ := by
      rw [on_line (I • z) 1]
    simpa [on_line, hf_ne, norm_exp] using h_norm
  refine ⟨LinearMap.ext₂ fun u v ↦ ?_, fun l hl ↦ ?_, fun z ↦ by simpa using on_line z 1⟩
  · -- Polarise: `re_eq` at `u + I • v` leaves `(B u v).im = (B v u).im`.
    have polar : (B (u + I • v) (u + I • v)).re = (B (I • (u + I • v)) (u + I • v)).im :=
      re_eq (u + I • v)
    have h_im : (B u v).im = (B v u).im := by
      simp [smul_smul, re_eq, hB.re_symm] at polar
      linarith
    simp [riemannForm_def, h_im]
  · have at_l : f l = (B l l / 2).exp * f 0 := by simpa using on_line l 1
    simpa [hf_ne, at_l] using hf_auto l hl 0

omit hf

end New

end
