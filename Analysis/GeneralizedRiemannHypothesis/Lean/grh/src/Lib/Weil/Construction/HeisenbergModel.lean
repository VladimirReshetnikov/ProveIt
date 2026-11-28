import Lib.General.Analysis.HolomorphicIntegrals

/-!
# Heisenberg cocycles, vacua, the reproducing model and Schur's lemma

This file sets up an abstract setting for the Weil representation that covers the real places
and the adeles. The data are a topological abelian group `W` with a measure `μ`, a Heisenberg
cocycle `β` on `W`, and a vacuum `e` for it. It also defines multiplier actions of a group `G` on
`W`. The vacuum defines a space of integrable functions reproduced by a kernel, on which `W` acts
by a Heisenberg representation `ρ`. The file proves superposition and Schur's lemma for this model.

## Main definitions and results

* `New.Heisenberg W`: a continuous alternating bicharacter `β`, the cocycle of a Heisenberg group.
* `New.Heisenberg.IsVacuum`: a function `e` on `W` that plays the part of the matrix coefficient of
  a vacuum vector (a Gaussian, or a lattice indicator times a semicharacter).
* `New.Heisenberg.MultiplierAction`: a group `G` acting on `W` by symmetries, with a multiplier `Δ`
  that turns a double integral of `e` and `β` attached to the action into a given `c` (by default
  `1`).
* `New.Heisenberg.IsVacuum.Model`: integrable v with v x = ∫ v y β(y, x) e(x - y), a Banach space
  for the L¹ norm, with the representation `New.Heisenberg.IsVacuum.heisenbergRep`, the vector
  `New.Heisenberg.IsVacuum.vacElem` and the form `New.Heisenberg.IsVacuum.modelInner`.
* `New.Heisenberg.IsVacuum.form_eq_mul_modelInner`,
  `New.Heisenberg.IsVacuum.eq_smul_one_of_commute`: Schur's lemma. An invariant form is a multiple
  of the inner product, and a bounded operator that commutes with the representation is a scalar.
  `New.Heisenberg.IsVacuum.integral_form_eq_mul_modelInner` treats a form given as an integral.

## Relation to the literature

Known; see `Lib.Weil.Construction.WeilOperators` for sources.
-/

noncomputable section

/-!
## Heisenberg cocycles, representations, vacua and multiplier actions

* `New.Heisenberg.Rep`: isometric operators `ρ x` with `ρ x ∘ ρ y = β x y • ρ (x + y)`.
-/

section Heisenberg

open MeasureTheory ComplexConjugate

variable (W : Type*) [AddCommGroup W] [TopologicalSpace W]

/-- A continuous function β on W × W, W an abelian group with a topology, with values of modulus
one, multiplicative in each variable, and β(x,x) = 1. -/
structure New.Heisenberg where
  /-- The bicharacter `β x y`, a complex-valued function on `W × W`. -/
  β : W → W → ℂ
  /-- `β` is multiplicative in its first variable. -/
  add_left (x x' y : W) : β (x + x') y = β x y * β x' y
  /-- `β` is multiplicative in its second variable. -/
  add_right (x y y' : W) : β x (y + y') = β x y * β x y'
  /-- `β` is alternating: it is `1` on the diagonal. -/
  self_eq_one (x : W) : β x x = 1
  /-- The values of `β` have modulus one. -/
  norm_eq_one (x y : W) : ‖β x y‖ = 1
  /-- `β` is jointly continuous on `W × W`. -/
  cont : Continuous fun p : W × W ↦ β p.1 p.2

namespace New.Heisenberg

variable {W} [MeasurableSpace W]
  (H : Heisenberg W) (μ : outParam (Measure W)) (e : outParam (W → ℂ))

/-- A representation of the Heisenberg datum `H`: linear isometries `ρ x`, `x : W`, of a complex
normed space `X`, with `ρ x ∘ ρ y = β x y • ρ (x + y)` and `(x, v) ↦ ρ x v` continuous. -/
structure Rep (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] where
  /-- The operator `ρ x` on `X` attached to the vector `x` of `W`. -/
  ρ : W → X →L[ℂ] X
  /-- The Heisenberg relation `ρ x ∘ ρ y = β x y • ρ (x + y)`. -/
  mul (x y : W) (v : X) : ρ x (ρ y v) = β H x y • ρ (x + y) v
  /-- Each `ρ x` is an isometry. -/
  norm_map (x : W) (v : X) : ‖ρ x v‖ = ‖v‖
  /-- The map `(x, v) ↦ ρ x v` is jointly continuous on `W × X`. -/
  cont : Continuous fun p : W × X ↦ ρ p.1 p.2

/-- The function e: W → ℂ is a vacuum for β and μ: continuous, integrable, even, real-valued,
e(0) = 1, and ∫ e(z)e(x−y−z)β(z,y)β(z+y,x) dμ(z) = e(y)e(x). -/
class IsVacuum where
  /-- `e` is continuous. -/
  cont : Continuous e
  /-- `e` is normalized to take the value `1` at the origin. -/
  apply_zero : e 0 = 1
  /-- `e` is even. -/
  apply_neg (x : W) : e (-x) = e x
  /-- `e` is real-valued. -/
  conj_apply (x : W) : conj (e x) = e x
  /-- The key identity: the convolution of `e` with itself at `x - y`, twisted by
  `β z y * β (z + y) x`, is `e y * e x`. -/
  twisted_conv (y x : W) :
      ∫ z : W, e z * (β H z y * (β H (z + y) x * e (x - (z + y)))) ∂μ = e y * e x
  /-- `e` is integrable for `μ`. -/
  integrable : Integrable e μ

/-- The action of G on W preserves β and μ, and a continuous multiplier Δ: G → ℂ has Δ(1) = 1,
Δ(g⁻¹) = conj Δ(g), Δ(g)Δ(h)Δ((gh)⁻¹) ∬ e(hx)e(ghy)β(x,y)e(x+y) = c(g,h). -/
structure MultiplierAction (G : Type*) [Group G] [TopologicalSpace G] [DistribMulAction G W]
    (c : G → G → ℂ := 1) where
  /-- The action of `G` on `W` preserves `β`. -/
  beta_smul (g : G) (x y : W) : β H (g • x) (g • y) = β H x y
  /-- The action of `G` on `W` preserves the measure `μ`. -/
  measurePreserving (g : G) : MeasurePreserving (g • ·) μ μ
  /-- The multiplier `Δ`, a complex-valued function on `G`. -/
  Δ : G → ℂ
  /-- The multiplier is continuous. -/
  continuous_delta : Continuous Δ
  /-- The multiplier is `1` at the identity. -/
  Δ_one : Δ 1 = 1
  /-- The multiplier takes inverses to complex conjugates. -/
  Δ_inv (g : G) : Δ g⁻¹ = conj (Δ g)
  /-- The double integral of `e (h • x) * e ((g * h) • y) * β x y * e (x + y)` times
  `Δ g * Δ h * Δ (g * h)⁻¹` is the prescribed value `c g h` (by default `1`). -/
  cocycle (g h : G) :
      Δ g * Δ h * Δ (g * h)⁻¹ *
        ∫ x : W, ∫ y : W, e (h • x) * e ((g * h) • y) * β H x y * e (x + y) ∂μ ∂μ = c g h

end New.Heisenberg

end Heisenberg

/-!
## First properties of cocycles, representations and vacua

* `New.Heisenberg.IsVacuum.integral_norm_sq_eq_one`, `New.Heisenberg.IsVacuum.norm_le_one`: a vacuum
  has `L²` norm one and is bounded by one.
-/

section HeisenbergBasic

open MeasureTheory Complex

namespace New.Heisenberg

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W] {H : Heisenberg W}
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  (R : H.Rep X) (x y : W) (w : X) {mW : MeasurableSpace W} {μ : Measure W} {e : W → ℂ}

attribute [fun_prop] cont Rep.cont

@[simp]
lemma beta_ne_zero : H.β x y ≠ 0 := by simp [← norm_pos_iff, norm_eq_one]

@[simp]
lemma beta_zero_left : H.β 0 y = 1 := by simpa using H.add_left 0 0 y

@[simp]
lemma beta_mul_beta : H.β x y * H.β y x = 1 := by
  -- Expand `β (x + y) (x + y) = 1` in both variables.
  have h_diag : H.β (x + y) (x + y) = 1 := H.self_eq_one _
  simpa [H.add_left, H.add_right, H.self_eq_one] using h_diag

@[simp]
lemma beta_zero_right : H.β y 0 = 1 := by simpa using beta_mul_beta 0 y

@[simp]
lemma beta_neg_left : H.β (-x) y = H.β y x := by
  -- Both sides are inverse to `β x y`.
  have h_inv : H.β x y * H.β (-x) y = 1 := by
    rw [← H.add_left, add_neg_cancel, beta_zero_left]
  exact inv_unique h_inv (beta_mul_beta x y)

@[simp]
lemma beta_neg_right : H.β x (-y) = H.β y x := by rw [← beta_neg_left, neg_neg]

@[simp]
lemma conj_beta : starRingEnd ℂ (H.β x y) = H.β y x := by
  rw [← Complex.inv_eq_conj (H.norm_eq_one x y)]
  exact inv_eq_of_mul_eq_one_right (beta_mul_beta x y)

/-- In a Heisenberg representation, `ρ 0` is the identity. -/
@[simp]
lemma Rep.rho_zero_apply : R.ρ 0 w = w := by
  -- `ρ 0` is idempotent by the Heisenberg relation and an isometry, so it is the identity.
  have h_idem : R.ρ 0 (R.ρ 0 w) = R.ρ 0 w := by rw [R.mul, beta_zero_left, one_smul, add_zero]
  rw [← sub_eq_zero, ← norm_eq_zero, ← R.norm_map 0, map_sub, h_idem, sub_self, norm_zero]

/-- A vacuum has `L²` norm one. -/
lemma IsVacuum.integral_norm_sq_eq_one (he : H.IsVacuum μ e) : ∫ x : W, ‖e x‖ ^ 2 ∂μ = 1 := by
  -- Take the convolution identity at `x = y = 0`: `e` is even and real, with `e 0 = 1`.
  have h_conv : ∫ z : W, e z * e z ∂μ = 1 := by
    simpa [he.apply_zero, he.apply_neg] using he.twisted_conv 0 0
  have h_sq (z : W) : e z * e z = (‖e z‖ : ℂ) ^ 2 := by rw [← mul_conj', he.conj_apply]
  rw [← ofReal_inj, ← integral_complex_ofReal]
  simpa [← h_sq] using h_conv

/-- A vacuum is bounded by one in absolute value. -/
lemma IsVacuum.norm_le_one (he : H.IsVacuum μ e) : ‖e x‖ ≤ 1 := by
  -- `e x * e x` is the integral of a function of norm `‖e z‖ ^ 2`, whose integral is one.
  have h_integrand (z : W) :
      ‖e z * (H.β z x * (H.β (z + x) x * e (x - (z + x))))‖ = ‖e z‖ ^ 2 := by
    simp [norm_eq_one, he.apply_neg, sq]
  refine (sq_le_one_iff₀ (norm_nonneg _)).1 ?_
  calc ‖e x‖ ^ 2 = ‖∫ z : W, e z * (H.β z x * (H.β (z + x) x * e (x - (z + x)))) ∂μ‖ := by
        rw [he.twisted_conv, norm_mul, sq]
    _ ≤ ∫ z : W, ‖e z * (H.β z x * (H.β (z + x) x * e (x - (z + x))))‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = 1 := by simpa only [h_integrand] using he.integral_norm_sq_eq_one

end New.Heisenberg

end HeisenbergBasic

/-!
## A Heisenberg representation twisted by a group element

A group `G` acting on `W` and preserving the bicharacter `β` (a part of
`New.Heisenberg.MultiplierAction`) twists any Heisenberg representation: `New.Heisenberg.Rep.moveBy`
is `x ↦ ρ (g • x)`.
-/

namespace New.Heisenberg.Rep

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W]
  {H : Heisenberg W} [MeasurableSpace W]
  {μ : MeasureTheory.Measure W} {e : W → ℂ}
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (R : H.Rep X)
  {G : Type*} [Group G] [TopologicalSpace G] [DistribMulAction G W] [ContinuousSMul G W]
  {c : G → G → ℂ} (A : H.MultiplierAction μ e G c) (g : G)

/-- The representation `x ↦ R.ρ (g • x)`; it is again a representation of `H` because `g` preserves
`β`. -/
@[simps]
def moveBy : H.Rep X where
  ρ := (R.ρ <| g • ·)
  mul := by simp [A.beta_smul, mul]
  norm_map := by simp [norm_map]
  cont := by fun_prop

@[simp]
lemma moveBy_one : R.moveBy A 1 = R := by simp [moveBy]

end New.Heisenberg.Rep

/-!
## The L¹ reproducing model of a vacuum and Schur's lemma

* `New.Heisenberg.Rep.integrated`: the integrated action ∫ v y • R.ρ y f on any representation R.
* `New.Heisenberg.IsVacuum.map_eq_integral`, `New.Heisenberg.IsVacuum.hom_ext` (superposition):
  every v is the integral of the translates of the vacuum against v, so these translates determine
  bounded maps.
* `New.Heisenberg.IsVacuum.integrated_eq_smul`: in the model itself, the integrated action of v on
  w is w(0) • v.
-/

section Model

open MeasureTheory ComplexConjugate Subtype LinearMap DFunLike

namespace New.Heisenberg

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W]
  (H : Heisenberg W) [MeasurableSpace W] [IsTopologicalAddGroup W] [BorelSpace W]
  [SecondCountableTopology W] {μ : Measure W}
  {e : W → ℂ} [he : IsVacuum H μ e]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-! ### The space and its norm -/

variable {H} in
omit [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] in
include he in
/-- The kernel β(y, x) e(x - y) of the reproducing identity of a vacuum e has norm at most one. -/
lemma IsVacuum.norm_beta_mul_le_one (x y : W) : ‖H.β y x * e (x - y)‖ ≤ 1 := by
  simpa [H.norm_eq_one] using he.norm_le_one (x - y)

variable {H} in
include he in
omit [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] in
/-- Multiplication by the kernel β(y, x) e(x - y) does not increase the absolute value. -/
lemma IsVacuum.norm_mul_beta_mul_le (x y : W) (a : ℂ) : ‖a * (H.β y x * e (x - y))‖ ≤ ‖a‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg a) (norm_beta_mul_le_one x y)

/-- For an integrable f, the function y ↦ f(y) β(y, x) e(x - y) (f times the kernel of the
reproducing identity) is integrable: the kernel is continuous and has norm at most one. -/
lemma IsVacuum.integrable_mul_kernel (x : W) {f : W → ℂ} (hf : Integrable f μ) :
    Integrable (fun y : W ↦ f y * (H.β y x * e (x - y))) μ := by
  -- The kernel `H.β y x * e (x - y)` is continuous and of norm at most one.
  have h_cont : Continuous e := he.cont
  exact hf.mono (by fun_prop) (.of_forall fun y ↦ norm_mul_beta_mul_le x y (f y))

variable [μ.IsAddHaarMeasure]

/-- The complex subspace of integrable functions v on W satisfying the reproducing identity v(x) = ∫
v(y) β(y,x) e(x−y) dμ(y) for every x. -/
def IsVacuum.modelSubmodule : Submodule ℂ (W → ℂ) where
  carrier := {v : W → ℂ | Integrable v μ ∧ ∀ x : W, ∫ y : W, v y * (H.β y x * e (x - y)) ∂μ = v x}
  add_mem' := by simp_all [add_mul, integrable_mul_kernel, integral_add]
  zero_mem' := by simp
  smul_mem' := by simp_all [mul_assoc, Integrable.smul, integral_const_mul]

/-- The space of integrable v with v(x) = ∫ v(y) β(y,x) e(x−y) dμ(y), as a type; it carries the
L¹ norm. -/
def IsVacuum.Model : Type _ := ↥he.modelSubmodule

deriving instance AddCommGroup, Module ℂ for (he.Model)

-- An element of the model is read as a function on `W`.
instance : CoeFun he.Model fun _ ↦ W → ℂ := ⟨val⟩

/-- The complex-linear map sending a function in the reproducing space to its class in L¹(W, μ). -/
def IsVacuum.toL1 : he.Model →ₗ[ℂ] W →₁[μ] ℂ where
  toFun v := v.2.1.toL1
  map_add' := by tauto
  map_smul' := by tauto

instance : NormedAddCommGroup he.Model :=
  .induced _ _ he.toL1 fun v w h ↦ Subtype.ext <| funext fun x ↦ by
    -- functions that agree almost everywhere have the same reproducing integrals
    rw [← v.prop.2 x, ← w.prop.2 x]
    exact integral_congr_ae (.mul_right (by simp_all [IsVacuum.toL1, coe]))

instance : NormedSpace ℂ he.Model := .induced ..

namespace IsVacuum

variable {H} (x : W) (v w : Model H)

section

omit [μ.IsAddHaarMeasure]

@[simp]
lemma add_apply : (v + w) x = v x + w x := rfl

@[simp]
lemma smul_apply (c : ℂ) : (c • v) x = c * v x := rfl

@[simp]
lemma zero_apply : (0 : Model H) x = 0 := rfl

@[ext]
lemma ext {v w : Model H} : (∀ x : W, v x = w x) → v = w := Subtype.ext ∘ funext

/-- For a vacuum `e` of `H` and `μ`, the model `Model H` is the space of integrable `v` with
v(x) = ∫ v(y) β(y,x) e(x−y) dμ(y). The norm of the model is the L¹ norm ∫ ‖v x‖ dμ. -/
lemma norm_eq_integral_norm : ‖v‖ = ∫ x : W, ‖v x‖ ∂μ :=
  L1.norm_of_fun_eq_integral_norm (And.left v.prop)

lemma Model.integrable : Integrable (⇑v) μ := And.left v.prop

/-- The reproducing identity of an element v of the model: ∫ v(y) β(y, x) e(x - y) dμ(y) = v(x). -/
lemma Model.integral_mul_beta_mul_eq : ∫ y : W, v y * (H.β y x * e (x - y)) ∂μ = v x :=
  And.right v.prop x

end

omit [μ.IsAddHaarMeasure] in
/-- An element of the model is bounded by its L¹ norm. -/
@[local simp]
lemma norm_apply_le : ‖v x‖ ≤ ‖v‖ := by
  -- `v x` is the integral of `v` against a kernel of norm at most one
  calc ‖v x‖ = ‖∫ y : W, v y * (H.β y x * e (x - y)) ∂μ‖ := by rw [v.integral_mul_beta_mul_eq x]
    _ ≤ ∫ y : W, ‖v y‖ ∂μ :=
      norm_integral_le_of_norm_le v.integrable.norm
        (.of_forall fun y ↦ norm_mul_beta_mul_le x y (v y))
    _ = ‖v‖ := (norm_eq_integral_norm v).symm

section

omit [μ.IsAddHaarMeasure]

/-- Let e be a vacuum for β and the measure μ. Every element of `Model H`, the space of
integrable v with v(x) = ∫ v(y) β(y,x) e(x−y) dμ(y), is a continuous function on `W`. -/
@[fun_prop]
lemma continuous : Continuous v := by
  -- Dominated convergence in the reproducing identity, whose kernel is continuous in `x`.
  have h_cont : Continuous e := he.cont
  have h_repr (x : W) : ∫ y : W, v y * (H.β y x * e (x - y)) ∂μ = v x :=
    v.integral_mul_beta_mul_eq x
  have h_bound (x : W) : ∀ᵐ y ∂μ, ‖v y * (H.β y x * e (x - y))‖ ≤ ‖v y‖ :=
    .of_forall fun y ↦ norm_mul_beta_mul_le x y (v y)
  have h_meas (x : W) : AEStronglyMeasurable (fun y : W ↦ v y * (H.β y x * e (x - y))) μ :=
    (integrable_mul_kernel H x v.integrable).aestronglyMeasurable
  have h_integral : Continuous fun x : W ↦ ∫ y : W, v y * (H.β y x * e (x - y)) ∂μ :=
    continuous_of_dominated h_meas h_bound v.integrable.norm (.of_forall fun y ↦ by fun_prop)
  exact h_integral.congr h_repr

/-! ### The representation, the vacuum vector and the inner product -/

/-- The Heisenberg representation on the model: y acts by the L¹ isometry that sends v to
x ↦ β(y, x) v(x - y), see `New.Heisenberg.IsVacuum.heisenbergOp_apply`. -/
def heisenbergRep : H.Rep he.Model :=
  -- the twisted translation `x ↦ H.β y x * v (x - y)`, an isometry for the `L¹` norm
  let ρ (y : W) : he.Model →ₗᵢ[ℂ] he.Model :=
    { toFun v :=
        ⟨fun x ↦ H.β y x * v.1 (x - y),
          (v.2.1.comp_sub_right y).bdd_mul (c := 1) (by fun_prop) (by simp [norm_eq_one]),
          fun x ↦ by
            -- translate the variable of integration by `y` and use the equation of `v` at `x - y`
            rw [← integral_add_right_eq_self _ y]
            simp [↓← v.2.2 (x - _), ← integral_const_mul, sub_eq_add_neg, add_right, self_eq_one,
              add_left]
            ac_nf⟩
      map_add' v w := ext fun x ↦ mul_add (H.β y x) (v (x - y)) (w (x - y))
      map_smul' c v := ext fun x ↦ mul_left_comm (H.β y x) c (v (x - y))
      norm_map' v := by simp [↓norm_eq_integral_norm, coe, integral_sub_right_eq_self (‖v.1 ·‖),
        norm_eq_one] }
  { ρ y := (ρ y).toContinuousLinearMap
    mul := by
      simp [↓he.ext_iff, ↓smul_apply, ρ, coe, sub_eq_add_neg, add_right, add_left]
      grind
    norm_map y := (ρ y).norm_map
    cont := by
      -- each `ρ y` is an isometry, so continuity in `y` for each fixed `v` suffices
      refine continuous_prod_of_continuous_lipschitzWith' _ _ (fun y ↦ (ρ y).lipschitzWith) fun v ↦
        continuous_iff_continuousAt.2 fun a ↦ tendsto_iff_norm_sub_tendsto_zero.2 ?_
      have h_int (w : he.Model) : Integrable (‖w ·‖) μ := w.2.1.norm
      -- Scheffé's trick: this integrand is dominated by `‖ρ a v x‖` and continuous in `t`; its
      -- integral is `‖v‖ - ‖ρ t v - ρ a v‖`, which is `‖v‖` at `t = a`
      have h_cont : Continuous fun t : W ↦ ∫ x : W, ‖ρ t v x‖ - ‖(ρ t v + -ρ a v) x‖ ∂μ := by
        refine continuous_of_dominated (fun t ↦ ((h_int _).sub (h_int _)).1) ?_ (h_int (-ρ a v))
          (.of_forall ?_)
        · simp [(abs_norm_sub_norm_le ..).trans]
        · simp [↓add_apply, ρ, coe]
          fun_prop
      simpa [norm_map, integral_sub, h_int, ← norm_eq_integral_norm, ← sub_eq_add_neg] using
        (h_cont.tendsto a).const_sub ‖v‖ }

/-- For `x` in `W`, the bounded operator on the reproducing space sending `v` to the function
`z ↦ β x z * v (z - x)`. -/
abbrev heisenbergOp : Model H →L[ℂ] Model H := heisenbergRep.ρ x

/-- The function e itself, viewed as an element of the reproducing space it defines. -/
def vacElem : Model H := ⟨e, he.integrable, by simpa [he.apply_zero] using he.twisted_conv 0⟩

/-- The continuous linear functional on `Model H` that evaluates an element at the point `x`. -/
def valueAt : Model H →L[ℂ] ℂ := mkContinuous (by use! (· x) <;> simp) 1 (by simp [coe])

/-- For σ an isometric ring endomorphism of ℂ and strongly continuous linear contractions K(y):
X → Y, the bounded σ-semilinear map v ↦ (x ↦ ∫ σ(v(y)) K(y)x dμ(y)) on the reproducing
space. -/
def kernelIntegral (σ : ℂ →+* ℂ) [RingHomIsometric σ] (K : W → X →L[ℂ] Y)
    (hK : ∀ x : X, Continuous (K · x)) (hC : ∀ (y : W) (x : X), ‖K y x‖ ≤ ‖x‖) :
    he.Model →SL[σ] X →L[ℂ] Y :=
  -- the integrand `σ (v y) • K y x` is dominated by `‖v y‖ * ‖x‖`
  have h_dom (v : he.Model) (x : X) : Integrable (fun y : W ↦ ‖v y‖ * ‖x‖) μ :=
    v.2.1.norm.mul_const ‖x‖
  have h_int (v : he.Model) (x : X) : Integrable (fun y : W ↦ σ (v y) • K y x) μ :=
    (h_dom v x).mono'
      ((σ.isometry.continuous.comp' (continuous v)).fun_smul (hK x)).aestronglyMeasurable
      (by simp [hC, norm_smul, mul_le_mul])
  mkContinuous₂
    (mk₂'ₛₗ σ (RingHom.id ℂ) (fun v x ↦ ∫ y : W, σ (v y) • K y x ∂μ)
      (by simp [add_smul, h_int, integral_add]) (by simp [← integral_smul, smul_smul])
      (by simp [h_int, integral_add]) (by simp [← integral_smul, mul_comm, smul_smul]))
    1 fun v x ↦ by
      simpa [norm_eq_integral_norm, integral_mul_const] using
        norm_integral_le_of_norm_le (h_dom v x) (by simp [hC, norm_smul, mul_le_mul])

/-- The bounded sesquilinear form on the reproducing space sending (v, w) to ∫ conj(v) w dμ,
conjugate-linear in the first argument. -/
def modelInner : Model H →L⋆[ℂ] Model H →L[ℂ] ℂ :=
  kernelIntegral (starRingEnd ℂ) valueAt continuous norm_apply_le

@[simp]
lemma valueAt_apply : valueAt x v = v x := rfl

@[simp]
lemma vacElem_apply : he.vacElem x = e x := rfl

end

@[simp]
lemma heisenbergOp_apply (y : W) : heisenbergOp y v x = H.β y x * v (x - y) := rfl

attribute [irreducible] heisenbergRep

omit [μ.IsAddHaarMeasure] in
/-- The function ‖v(·)‖² is integrable for v in the model: v is integrable and bounded by its
norm. -/
lemma integrable_norm_sq : Integrable (‖v ·‖ ^ 2) μ := by
  have h_bound (y : W) : ‖‖v y‖ ^ 2‖ ≤ ‖‖v‖ • v y‖ := by
    simpa [sq, norm_smul] using mul_le_mul_of_nonneg_right (norm_apply_le y v) (norm_nonneg (v y))
  exact (v.integrable.smul ‖v‖).mono (by fun_prop) (.of_forall h_bound)

omit [μ.IsAddHaarMeasure] in
@[local simp]
lemma modelInner_apply : modelInner v w = ∫ x : W, conj (v x) * w x ∂μ := rfl

omit [μ.IsAddHaarMeasure] in
/-- The inner product is Hermitian: conj ⟨v, w⟩ = ⟨w, v⟩. -/
lemma conj_modelInner : conj (modelInner v w) = modelInner w v := by
  simp [← integral_conj, mul_comm]

/-- The Heisenberg operators preserve the inner product of the model. -/
lemma modelInner_heisenbergOp :
    modelInner (heisenbergOp x v) (heisenbergOp x w) = modelInner v w := by
  -- β(x, y) has modulus one, and the integral is invariant under translation by `x`
  have h_point (y : W) : conj (H.β x y * v (y - x)) * (H.β x y * w (y - x)) =
      conj (v (y - x)) * w (y - x) := by simp [mul_mul_mul_comm]
  simp only [modelInner_apply, heisenbergOp_apply, h_point]
  exact integral_sub_right_eq_self (fun y : W ↦ conj (v y) * w y) x

/-- Reproducing property: for v in the reproducing space of a vacuum e and x in W, the inner
product ⟨ρ(x)vac, v⟩ equals v(x). -/
@[simp]
lemma modelInner_heisenbergOp_vacElem : modelInner (heisenbergOp x vacElem) v = v x := by
  -- The integrand is that of the reproducing identity of `v` at `x`, as `e` is real and even.
  have h_point (y : W) : conj (H.β x y * e (y - x)) * v y = v y * (H.β y x * e (x - y)) := by
    rw [map_mul, conj_beta, he.conj_apply, ← he.apply_neg (y - x), neg_sub]
    ring
  simp only [modelInner_apply, heisenbergOp_apply, vacElem_apply, h_point]
  exact v.integral_mul_beta_mul_eq x

omit [μ.IsAddHaarMeasure] in
lemma modelInner_self : modelInner v v = ∫ x : W, ‖v x‖ ^ 2 ∂μ := by
  simp only [modelInner_apply, RCLike.conj_mul]
  -- The integrand is the real function `‖v x‖ ^ 2`, cast to `ℂ`.
  norm_cast

/-- The inner product of the model is definite: if ⟨v, v⟩ = 0, then v = 0. -/
lemma eq_zero_of_modelInner_self {v : he.Model} (h : he.modelInner v v = 0) : v = 0 := by
  ext x
  -- If `v x ≠ 0`, the integral of the continuous function `‖v ·‖ ^ 2` is positive.
  by_contra hx_ne
  have h_pos : 0 < ∫ y : W, ‖v y‖ ^ 2 ∂μ :=
    integral_pos_of_integrable_nonneg_nonzero (x := x) (by fun_prop) (integrable_norm_sq v)
      (fun y ↦ sq_nonneg ‖v y‖) (by simpa using hx_ne)
  exact h_pos.ne' (mod_cast (modelInner_self v).symm.trans h)

end IsVacuum

/-- The model is complete, hence a Banach space. -/
instance : CompleteSpace he.Model := by
  -- An absolutely summable series has a sum in `L¹`, which is represented by the pointwise sum;
  -- that function satisfies the reproducing identity, term by term.
  refine NormedAddCommGroup.completeSpace_of_summable_imp_tendsto fun u hu ↦ ?_
  have h_ae : ⇑(∑' n : ℕ, IsVacuum.toL1 H (u n)) =ᵐ[μ] fun x : W ↦ ∑' n : ℕ, u n x :=
    (Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hu)).trans
      ((ae_all_iff.mpr fun n ↦ (u n).integrable.coeFn_toL1).mono fun _ ↦ tsum_congr)
  have h_int : Integrable (fun x : W ↦ ∑' n : ℕ, u n x) μ := .congr (by fun_prop) h_ae
  have h_repr (x : W) :
      ∫ y : W, (∑' n : ℕ, u n y) * (H.β y x * e (x - y)) ∂μ = ∑' n : ℕ, u n x := by
    -- Exchange the sum and the integral, then use the reproducing identity of each `u n`.
    have h_int_n (n : ℕ) : Integrable (fun y : W ↦ u n y * (H.β y x * e (x - y))) μ :=
      IsVacuum.integrable_mul_kernel H x (u n).integrable
    have h_norm_le (n : ℕ) : ∫ y : W, ‖u n y * (H.β y x * e (x - y))‖ ∂μ ≤ ‖u n‖ := by
      rw [IsVacuum.norm_eq_integral_norm (u n)]
      exact integral_mono (h_int_n n).norm (u n).integrable.norm
        fun y ↦ IsVacuum.norm_mul_beta_mul_le x y (u n y)
    have h_summable : Summable fun n : ℕ ↦ ∫ y : W, ‖u n y * (H.β y x * e (x - y))‖ ∂μ :=
      Summable.of_nonneg_of_le (fun n ↦ integral_nonneg fun y ↦ norm_nonneg _) h_norm_le hu
    calc ∫ y : W, (∑' n : ℕ, u n y) * (H.β y x * e (x - y)) ∂μ
        = ∫ y : W, ∑' n : ℕ, u n y * (H.β y x * e (x - y)) ∂μ := by simp_rw [tsum_mul_right]
      _ = ∑' n : ℕ, ∫ y : W, u n y * (H.β y x * e (x - y)) ∂μ :=
        (integral_tsum_of_summable_integral_norm h_int_n h_summable).symm
      _ = ∑' n : ℕ, u n x := tsum_congr fun n ↦ (u n).integral_mul_beta_mul_eq x
  let v : he.Model := ⟨fun x : W ↦ ∑' n : ℕ, u n x, h_int, h_repr⟩
  have h_tsum_eq : ∑' n : ℕ, IsVacuum.toL1 H (u n) = IsVacuum.toL1 H v :=
    Lp.ext (h_ae.trans h_int.coeFn_toL1.symm)
  have h_sum : HasSum (fun n : ℕ ↦ IsVacuum.toL1 H (u n)) (IsVacuum.toL1 H v) := by
    rw [← h_tsum_eq]
    exact (Summable.of_norm (f := fun n ↦ IsVacuum.toL1 H (u n)) hu).hasSum
  -- The topology of the model is induced from `L¹`.
  exact ⟨v, ((Topology.IsInducing.hasSum_iff ⟨rfl⟩ u v).mp h_sum).tendsto_sum_nat⟩

variable {H} [CompleteSpace X]
  (R : H.Rep X) (T : X →L[ℂ] Y) (x : W) (v w : IsVacuum.Model H) (f : X) [CompleteSpace Y]

/-! ### The integrated action -/

/-- The integrated action of the model on a representation R in a complex Banach space X: the
bounded bilinear map (v, f) ↦ ∫ v(y) • R.ρ y f dμ(y), see `New.Heisenberg.Rep.integrated_apply`. -/
def Rep.integrated : he.Model →L[ℂ] X →L[ℂ] X :=
  he.kernelIntegral (RingHom.id ℂ) R.ρ (by fun_prop) (by simp [norm_map])

omit [μ.IsAddHaarMeasure] [CompleteSpace X] in
lemma Rep.integrated_apply : R.integrated v f = ∫ y : W, v y • R.ρ y f ∂μ := rfl

omit [μ.IsAddHaarMeasure] in
/-- A bounded operator T passes under the integral that defines the integrated action. -/
lemma Rep.map_integrated_eq_integral : T (R.integrated v f) = ∫ y : W, v y • T (R.ρ y f) ∂μ := by
  have h_int : Integrable (fun y : W ↦ v y • R.ρ y f) μ :=
    v.integrable.smul_bdd ‖f‖ (by fun_prop) (.of_forall fun y ↦ (R.norm_map y f).le)
  simp_rw [integrated_apply, ← T.integral_comp_comm h_int, map_smul]

/-- The integrated action turns the operator ρ(x) of the model into the operator R.ρ x. -/
@[simp]
lemma Rep.integrated_heisenbergOp :
    R.integrated (he.heisenbergOp x v) f = R.ρ x (R.integrated v f) := by
  -- After translating the variable of integration by `x`, the integrands agree.
  have h_point (y : W) :
      he.heisenbergOp x v (x + y) • R.ρ (x + y) f = v y • R.ρ x (R.ρ y f) := by
    simp [H.add_right, H.self_eq_one, R.mul, smul_smul, mul_comm (H.β x y)]
  rw [map_integrated_eq_integral, integrated_apply, ← integral_add_left_eq_self _ x]
  exact integral_congr_ae (.of_forall h_point)

omit [μ.IsAddHaarMeasure] in
/-- A bounded operator T from X to Y that intertwines the representations R and R' commutes with
their integrated actions. -/
lemma Rep.map_integrated {R' : H.Rep Y} (hT : ∀ (y : W) (f : X), T (R.ρ y f) = R'.ρ y (T f)) :
    T (R.integrated v f) = R'.integrated v (T f) := by
  simp_rw [map_integrated_eq_integral, hT, integrated_apply]

namespace IsVacuum

/-! ### Bounded maps and invariant forms on the model -/

omit [μ.IsAddHaarMeasure] in
/-- For a representation R on the model itself, the value at x of the integrated action of v on w
is ∫ v(y) (R.ρ y w)(x) dμ(y). -/
lemma integrated_apply_eq_integral (R : H.Rep (Model H)) :
    R.integrated v w x = ∫ y : W, v y * R.ρ y w x ∂μ :=
  R.map_integrated_eq_integral (valueAt x) v w

/-- Integrating the translates ρ(y) vac of the vacuum against v gives back v: the reproducing
identity in operator form. -/
lemma integrated_vacElem : he.heisenbergRep.integrated v vacElem = v := by
  ext x
  rw [integrated_apply_eq_integral]
  show ∫ y : W, v y * heisenbergOp y vacElem x ∂μ = v x
  simp only [heisenbergOp_apply, vacElem_apply]
  exact v.integral_mul_beta_mul_eq x

/-- Superposition: for a bounded linear map T from the reproducing space to a complex Banach space
and any v in the reproducing space, Tv = ∫ v(y) T(ρ(y)vac) dμ(y). -/
lemma map_eq_integral (T : Model H →L[ℂ] Y) :
    T v = ∫ y : W, v y • T (heisenbergOp y vacElem) ∂μ := by
  rw [← Rep.map_integrated_eq_integral, integrated_vacElem]

/-- Two bounded operators from the model to a Banach space that agree on the translates ρ(y) vac
of the vacuum are equal. -/
lemma hom_ext {L L' : Model H →L[ℂ] Y}
    (h : ∀ y : W, L (heisenbergOp y vacElem) = L' (heisenbergOp y vacElem)) : L = L' := by
  ext v
  simp_rw [map_eq_integral v, h]

/-- For v, w in the reproducing space of a vacuum e, with its Heisenberg representation ρ, one
has ∫ v(y) ρ(y)w dμ(y) = w(0)·v.

A special case of the Moyal identity (orthogonality relations for the Heisenberg representation), in
operator form with one vector the vacuum. -/
@[simp]
lemma integrated_eq_smul : he.heisenbergRep.integrated v w = w 0 • v := by
  -- Both sides are bounded linear in `v` and in `w`, so by `hom_ext` it is enough to treat
  -- translates of the vacuum, `v = heisenbergOp y vacElem` and `w = heisenbergOp z vacElem`.
  have h_integrated :
      he.heisenbergRep.integrated = ContinuousLinearMap.smulRightL ℂ (Model H) (Model H)
        (valueAt 0) := by
    refine hom_ext fun y ↦ hom_ext fun z ↦ ext fun x ↦ ?_
    -- The value at `x` is `H.β y x` times the integral in the vacuum identity at `z`, `x - y`.
    simp [integrated_apply_eq_integral, he.apply_neg, he.twisted_conv, field, Rep.mul]
  rw [h_integrated]
  simp

/-- Schur's lemma for the model: a bounded operator that commutes with the Heisenberg operators is a
scalar, namely the value at `0` of the image of the vacuum. -/
lemma eq_smul_one_of_commute (T : Model H →L[ℂ] Model H)
    (hT : ∀ y : W, Commute T (heisenbergOp y)) :
    T = T vacElem 0 • 1 := by
  ext1 v
  calc T v = T (he.heisenbergRep.integrated v vacElem) := by rw [integrated_vacElem]
    _ = he.heisenbergRep.integrated v (T vacElem) :=
      Rep.map_integrated _ T v vacElem fun y f ↦ DFunLike.congr_fun (hT y).eq f
    _ = T vacElem 0 • v := integrated_eq_smul v (T vacElem)

/-- A bounded continuous K from W to a Banach space X yields a bounded linear map L from the model
to X (in the proof, L v = ∫ v y • K y) that behaves as if it sent the translate
`heisenbergOp y vacElem` of the vacuum to K y: if bounded maps M, N into the Banach space Y satisfy
M (K y) = N (heisenbergOp y vacElem) for all y, then M ∘ L = N. -/
lemma exists_lift {K : W → X} (hK : Continuous K) {C : ℝ} (hC : ∀ y : W, ‖K y‖ ≤ C) :
    ∃ L : Model H →L[ℂ] X, ∀ (M : X →L[ℂ] Y) (N : Model H →L[ℂ] Y),
      (∀ y : W, M (K y) = N (heisenbergOp y vacElem)) → ∀ v : Model H, M (L v) = N v := by
  -- `L v = ∫ v y • K y`; the integrand is integrable because `v` is and `K` is bounded.
  have h_int (v : Model H) : Integrable (fun y ↦ (valueAt y).smulRight (K y) v) μ :=
    v.integrable.smul_bdd C (by fun_prop) (.of_forall hC)
  refine ⟨strongIntegral μ fun y ↦ (valueAt y).smulRight (K y), fun M N hMN v ↦ ?_⟩
  -- `M` passes under the integral, and `N v = ∫ v y • N (heisenbergOp y vacElem)`.
  have h_point (y : W) : M ((valueAt y).smulRight (K y) v) = v y • N (heisenbergOp y vacElem) := by
    rw [ContinuousLinearMap.smulRight_apply, valueAt_apply, map_smul, hMN y]
  rw [strongIntegral_apply _ _ h_int, ← M.integral_comp_comm (h_int v), map_eq_integral]
  exact integral_congr_ae (.of_forall h_point)

/-- Uniqueness of the invariant form, a form of Schur's lemma for the Heisenberg representation. Let
W be a locally compact, second countable abelian group with Haar measure μ, and let e be a vacuum
for the bicharacter β of `H` and μ. Let `Model H` be the space of integrable v with v(x) = ∫ v(y)
β(y,x) e(x−y) dμ(y), and let ρ(x) = `heisenbergOp x` send v to z ↦ β(x,z) v(z−x). If B_z (z ∈ Z) are
bounded sesquilinear forms on `Model H`, each z ↦ B_z(v,w) is ν-integrable, and ∫B_z dν is invariant
under all ρ(x), then ∫B_z(v,w) dν = (∫B_z(e,e) dν)·⟨v,w⟩, where ⟨v,w⟩ = ∫ conj(v) w dμ. -/
lemma integral_form_eq_mul_modelInner [LocallyCompactSpace W] {Z : Type*} {m : MeasurableSpace Z}
    {ν : Measure Z} (B : Z → Model H →L⋆[ℂ] Model H →L[ℂ] ℂ)
    (hB_int : ∀ v w : Model H, Integrable (fun z : Z ↦ B z v w) ν)
    (hB_inv : ∀ (x : W) (f g : Model H),
      ∫ z : Z, B z (heisenbergOp x f) (heisenbergOp x g) ∂ν = ∫ z : Z, B z f g ∂ν)
    (v w : Model H) :
    ∫ z : Z, B z v w ∂ν = (∫ z : Z, B z vacElem vacElem ∂ν) * modelInner v w := by
  -- Write `B(f, u) = ∫ B z f u ∂ν`. Expanding the vacuum into its translates and using invariance
  -- and `integrated_eq_smul` gives `B(f, vacElem) = B(vacElem, vacElem) * conj (f 0)`. Translating
  -- this gives the claim for `w = heisenbergOp y vacElem`, which suffices by `hom_ext`.
  have h_right (f u : Model H) : strongIntegral ν (B · f) u = ∫ z : Z, B z f u ∂ν :=
    strongIntegral_apply _ _ (hB_int f) u
  -- By invariance a translation moves from the second argument to the first.
  have h_move (x : W) (f u : Model H) :
      ∫ z : Z, B z f (heisenbergOp x u) ∂ν = ∫ z : Z, B z (heisenbergOp (-x) f) u ∂ν := by
    simpa [Rep.mul, self_eq_one] using hB_inv x (heisenbergOp (-x) f) u
  obtain ⟨T, hT⟩ :
      ∃ T : Model H →L[ℂ] ℂ, ∀ f : Model H, T f = conj (∫ z : Z, B z f vacElem ∂ν) := by
    refine ⟨strongIntegral ν fun z ↦ innerSLFlip ℂ 1 ∘SL (B z).flip vacElem, fun f ↦ ?_⟩
    rw [strongIntegral_apply _ _ fun f ↦ (hB_int f vacElem).inner_const _]
    simp [← integral_conj]
  have h_vac (f : Model H) :
      ∫ z : Z, B z f vacElem ∂ν = (∫ z : Z, B z vacElem vacElem ∂ν) * conj (f 0) := by
    apply (starRingEnd ℂ).injective
    calc conj (∫ z : Z, B z f vacElem ∂ν)
      _ = conj (∫ y : W, e y * ∫ z : Z, B z (heisenbergOp y f) vacElem ∂ν ∂μ) := by
        rw [← h_right, map_eq_integral, ← integral_neg_eq_self]
        simp [h_right, h_move, he.apply_neg]
      _ = T (he.heisenbergRep.integrated vacElem f) := by
        rw [Rep.map_integrated_eq_integral, ← integral_conj]
        simp [hT, he.conj_apply]
      _ = conj ((∫ z : Z, B z vacElem vacElem ∂ν) * conj (f 0)) := by
        simp [hT, mul_comm, integral_const_mul]
  have h_form :
      strongIntegral ν (B · v) = (∫ z : Z, B z vacElem vacElem ∂ν) • modelInner v := by
    refine hom_ext fun y ↦ ?_
    rw [h_right, h_move, h_vac]
    simp [← conj_modelInner (heisenbergOp y vacElem)]
  rw [← h_right v w, h_form, _root_.smul_apply, smul_eq_mul]

/-- Schur's lemma for a single form: if W is locally compact, a bounded sesquilinear form B on the
reproducing space that is invariant under all ρ(x) is B(vac, vac) times the inner product. -/
lemma form_eq_mul_modelInner [LocallyCompactSpace W] (B : Model H →L⋆[ℂ] Model H →L[ℂ] ℂ)
    (hB_inv : ∀ (x : W) (f g : Model H), B (heisenbergOp x f) (heisenbergOp x g) = B f g)
    (v w : Model H) : B v w = B vacElem vacElem * modelInner v w := by
  -- A single form is the integral of a constant family against a point mass.
  simpa using integral_form_eq_mul_modelInner (ν := .dirac ()) (fun _ : Unit ↦ B)
    (fun f g ↦ integrable_const (B f g)) (by simpa using hB_inv) v w

end IsVacuum

end New.Heisenberg

end Model

end
