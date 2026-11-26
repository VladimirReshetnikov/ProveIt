import Lib.Weil.Construction.HeisenbergModel

/-!
# Weil operators, orthogonal sums and transport of the reproducing model

This file defines the Weil operators of a multiplier action of a group `G` on `W` on the
reproducing model of a vacuum. It proves their cocycle relation, and shows that they preserve the
inner product. For cocycle `1` it defines the Weil representation and proves that it intertwines
the Heisenberg operators and is continuous. The file then treats orthogonal sums `W = W₁ × W₂`,
with tensor products of model vectors and Wiener's bound, and the transport of the model along
isomorphisms.

## Main definitions and results

* `New.Heisenberg.IsVacuum.weilOp_mul`, `New.Heisenberg.IsVacuum.modelInner_weilOp`: if c(g, 1) = 1,
  the Weil operators `New.Heisenberg.IsVacuum.weilOp` multiply up to the cocycle c and preserve the
  inner product.
* `New.Heisenberg.IsVacuum.weilRep`: for c = 1 the Weil representation; it intertwines ρ(x) and
  ρ(gx) (`New.Heisenberg.IsVacuum.weilRep_heisenbergOp`) and, for first countable G, is jointly
  continuous (`New.Heisenberg.IsVacuum.continuous_weilRep`). Elements that preserve `e` act by Δ(g)
  times substitution (`New.Heisenberg.IsVacuum.weilRep_apply_of_vacuum_smul`). The operator of g
  has norm at most ‖vac‖ |Δ(g)| (`New.Heisenberg.IsVacuum.norm_weilRep_le`).

Notions from other files:
* `New.Heisenberg.IsVacuum.Model`: the integrable functions v with v x = ∫ v y β(y, x) e(x - y),
  with the L¹ norm and the inner product `New.Heisenberg.IsVacuum.modelInner`.
* `New.Heisenberg.MultiplierAction`: an action of `G` on `W` preserving `β` and `μ`, with a
  multiplier `Δ` and a cocycle `c`.
* `New.Heisenberg.IsVacuum.heisenbergOp`, `New.Heisenberg.IsVacuum.vacElem`: the Heisenberg
  operators ρ(x) on the model and the vacuum `e` as an element of the model.

## Relation to the literature

This file contributes to the adelic Weil representation of a unitary group and the invariant theta
functional. See `Lib.Weil.MixedModel.ZeroTerm`. Sources: Weil; Kudla.

The usual proof of the product rule ω(g) ω(h) = ω(gh) compares ω with a Schrödinger model on a
Siegel parabolic subgroup of a split space, and then uses the Iwasawa decomposition and the sum
V ⊕ V⁻. The proof here does not use a Schrödinger model. The scalar c(g, h) in
ω(g) ω(h) = c(g, h) ω(gh) is an integral of three vacua times values of the multiplier
(`New.Heisenberg.IsVacuum.weilOp_inv_mul_weilOp_mul_weilOp`). Later files show directly that it is
1, from three local facts: a Gaussian determinant at the real places (`New.Fock.realAction`),
positivity at the split places and the sign of a Gauss sum at the inert places
(`New.stdLattice.mem_cocycleRadical`). The formulas of the Schrödinger model are then proved for the
slices in `Lib.Weil.MixedModel.ZeroTerm`.
-/

noncomputable section

/-!
## Weil operators: cocycle relation, unitarity and continuity

Below, `B` is an action of `G` on `W` with multiplier `Δ` and cocycle `c`
(`New.Heisenberg.MultiplierAction`), `A` one with cocycle `1`, `ρ = heisenbergOp` and
`vac = vacElem`.

* `New.Heisenberg.IsVacuum.weilOp`: the operator v ↦ Δ(g) ∫ v(y) ρ(gy) vac dμ(y).
* `New.Heisenberg.IsVacuum.integrated_moveBy_vacElem_eq_smul`: a nonzero overlap with the vacuum
  determines a unitary intertwining operator.
* `New.Heisenberg.IsVacuum.cocycleRadical`: the elements s with c(g, s) = 1 for all g, a subgroup.
-/

namespace New.Heisenberg.IsVacuum

open MeasureTheory Heisenberg.Rep ContinuousLinearMap

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W]
  {H : Heisenberg W} [MeasurableSpace W] [IsTopologicalAddGroup W] [BorelSpace W]
  [SecondCountableTopology W] {μ : Measure W} [μ.IsAddHaarMeasure]
  {e : W → ℂ} [he : IsVacuum H μ e]
  {G : Type*} [Group G] [TopologicalSpace G] [DistribMulAction G W] [ContinuousSMul G W]
  {c : G → G → ℂ} (B : H.MultiplierAction μ e G c) (A : H.MultiplierAction μ e G) (g h k : G)
  (x : W) (v w : Model H)

/-! ### The operators of an action with a cocycle -/

/-- The Weil operator of `g` for the action `B`: the operator v ↦ Δ(g) ∫ v(y) ρ(g • y) vac dμ(y) on
the model space, where `Δ = B.Δ`, `ρ = heisenbergOp` and `vac = vacElem`. The integral is the
integrated action of `v` on `vac` for the representation `y ↦ ρ (g • y)`
(`New.Heisenberg.Rep.moveBy`). -/
def weilOp : Model H →L[ℂ] Model H := B.Δ g • (heisenbergRep.moveBy B g).integrated.flip vacElem

/-- Write P_g(w) for the operator ∫ w(y) ρ(g • y) dμ(y) on the model space, the integrated action
`(heisenbergRep.moveBy B g).integrated w` of `w`. For vectors `v`, `w`, `x` of the model space,
P_g(P_k(w) v) x = P_{gk}(w) (P_g(v) x). -/
lemma integrated_moveBy_integrated (x v w : Model H) :
    (heisenbergRep.moveBy B g).integrated ((heisenbergRep.moveBy B k).integrated w v) x =
      (heisenbergRep.moveBy B (g * k)).integrated w
        ((heisenbergRep.moveBy B g).integrated v x) := by
  -- `v ↦ (heisenbergRep.moveBy B g).integrated v x` intertwines the twists by `k` and `g * k`, so
  -- it commutes with the integral that defines `integrated w`.
  rw [← flip_apply, map_integrated]
  · rfl
  · simp [mul_smul]

/-- For a bounded functional `T` on the model space, `T` of the integrated action of `w` on `v` for
the representation `y ↦ ρ (g • y)` is ∫ w(g⁻¹ • y) T(ρ(y) v) dμ(y). -/
lemma map_integrated_moveBy (T : Model H →L[ℂ] ℂ) :
    T ((heisenbergRep.moveBy B g).integrated w v) =
      ∫ y : W, w (g⁻¹ • y) * T (heisenbergOp y v) ∂μ := by
  -- Substitute `y ↦ g • y`, which preserves `μ`.
  rw [← (B.measurePreserving g).integral_comp' (f := .smul g)]
  simp [map_integrated_eq_integral]

/-- Let `e` be a vacuum for the Heisenberg datum `H` and Haar measure `μ`, and let `Model H` be the
space of integrable `v` with v(x) = ∫ v(y) β(y,x) e(x−y) dμ(y). Then the pairing ∫ conj(e) v dμ
(`modelInner`) of the vacuum `vacElem` (the function `e` itself) with any `v` in `Model H` equals
v(0). -/
@[simp]
lemma modelInner_vacElem : he.modelInner vacElem v = v 0 := by
  simp [← modelInner_heisenbergOp_vacElem]

/-- Let `B` be a multiplier action of `G` on the vacuum datum (`H`, `μ`, `e`), let `g : G`, and on
the model space of `e` let ρ(y) = `heisenbergOp y` and vac = `vacElem`. If `T` is a bounded
surjective operator on the model that preserves `modelInner` and satisfies T ρ(y) = ρ(g • y) T, then
for every model vector `v`, ∫ v(y) ρ(g • y) vac dμ(y) = conj((T vac)(0)) · T v. So the overlap ⟨vac,
T vac⟩ = (T vac)(0) determines `T` when it is not zero. -/
lemma integrated_moveBy_vacElem_eq_smul (T : Model H →L[ℂ] Model H)
    (hT_surj : Function.Surjective T)
    (hT_inner : ∀ v w : Model H, modelInner (T v) (T w) = modelInner v w)
    (hT_heis : ∀ (y : W) (w : Model H), T (heisenbergOp y w) = heisenbergOp (g • y) (T w)) :
    (heisenbergRep.moveBy B g).integrated v vacElem = starRingEnd ℂ (T vacElem 0) • T v := by
  -- Apply `T` to `integrated_eq_smul` for the vector `u` with `T u = vac`.
  obtain ⟨u, hu⟩ : ∃ u : Model H, T u = vacElem := hT_surj vacElem
  have h_overlap : u 0 = starRingEnd ℂ (T vacElem 0) := by
    calc u 0 = modelInner vacElem u := (modelInner_vacElem u).symm
      _ = modelInner (T vacElem) vacElem := by rw [← hT_inner, hu]
      _ = starRingEnd ℂ (T vacElem 0) := by rw [← conj_modelInner, modelInner_vacElem]
  calc (heisenbergRep.moveBy B g).integrated v vacElem
      = (heisenbergRep.moveBy B g).integrated v (T u) := by rw [hu]
    _ = T (heisenbergRep.integrated v u) := (map_integrated heisenbergRep T v u hT_heis).symm
    _ = starRingEnd ℂ (T vacElem 0) • T v := by rw [integrated_eq_smul, map_smul, h_overlap]

/-- The cocycle relation: the product of the Weil operators of (gh)⁻¹, g and h, in this order, is
the scalar c(g, h). -/
lemma weilOp_inv_mul_weilOp_mul_weilOp : weilOp B (g * h)⁻¹ * weilOp B g * weilOp B h = c g h •
  1 := by
  have h_move (k : G) (y : W) :
      weilOp B k * heisenbergOp y = heisenbergOp (k • y) * weilOp B k := by
    ext1 v
    simp [weilOp]
  -- The product moves `ρ(y)` to `ρ((g * h)⁻¹ • g • h • y) = ρ(y)`, so by Schur's lemma it is a
  -- scalar: the value at `0` of the image of the vacuum.
  have h_commute (y : W) :
      Commute (weilOp B (g * h)⁻¹ * weilOp B g * weilOp B h) (heisenbergOp y) := by
    rw [commute_iff_eq, mul_assoc, h_move, ← mul_assoc, mul_assoc _ (weilOp B g), h_move,
      ← mul_assoc, h_move, ← mul_smul g h, inv_smul_smul]
    simp only [mul_assoc]
  -- Write `P k w` for the operator `∫ w y • ρ (k • y)`. By `integrated_moveBy_integrated` the three
  -- integrals rearrange into the double integral that defines the cocycle `c g h`.
  let P (k : G) : Model H →L[ℂ] Model H →L[ℂ] Model H := (heisenbergRep.moveBy B k).integrated
  have hP_apply (k : G) (w v : Model H) (x : W) :
      P k w v x = ∫ y : W, w (k⁻¹ • y) * heisenbergOp y v x ∂μ :=
    map_integrated_moveBy B k v w (valueAt x)
  have hP_comp (k l : G) (x v w : Model H) : P k (P l w v) x = P (k * l) w (P k v x) :=
    integrated_moveBy_integrated B k l x v w
  have hP_one (w v : Model H) : P 1 w v = v 0 • w := by
    simp only [P, moveBy_one, integrated_eq_smul]
  have h_inner (x : W) : P (g * h)⁻¹ vacElem vacElem (-x) =
      ∫ y : W, e ((g * h) • y) * (H.β x y * e (x + y)) ∂μ := by
    simp only [hP_apply, inv_inv, vacElem_apply, heisenbergOp_apply, beta_neg_right, ← neg_add',
      he.apply_neg]
  have h_value : P h⁻¹ vacElem (P (g * h)⁻¹ vacElem vacElem) 0 =
      ∫ x : W, ∫ y : W, e (h • x) * e ((g * h) • y) * H.β x y * e (x + y) ∂μ ∂μ := by
    rw [hP_apply]
    simp only [inv_inv, vacElem_apply, heisenbergOp_apply, beta_zero_right, one_mul, zero_sub,
      h_inner,
      mul_assoc, integral_const_mul]
  have h_scalar : (weilOp B (g * h)⁻¹ * weilOp B g * weilOp B h) vacElem 0 = c g h := by
    calc (weilOp B (g * h)⁻¹ * weilOp B g * weilOp B h) vacElem 0
      _ = B.Δ g * B.Δ h * B.Δ (g * h)⁻¹ *
            P (g * h)⁻¹ (P g (P h vacElem vacElem) vacElem) vacElem 0 := by
        simp only [weilOp, P, mul_def, comp_apply, _root_.smul_apply, flip_apply,
          map_smul, smul_apply]
        ring
      _ = B.Δ g * B.Δ h * B.Δ (g * h)⁻¹ *
            P 1 vacElem (P h⁻¹ vacElem (P (g * h)⁻¹ vacElem vacElem)) 0 := by
        rw [hP_comp g h, hP_comp, hP_comp, inv_mul_cancel, mul_inv_rev, inv_mul_cancel_right]
      _ = c g h := by
        rw [hP_one, smul_apply, vacElem_apply, he.apply_zero, mul_one, h_value, B.cocycle]
  rw [eq_smul_one_of_commute _ h_commute, h_scalar]

omit [μ.IsAddHaarMeasure] in
/-- For a representation R on the model space and a vector v, the operator sending w in the model
space to ∫ w(y) R.ρ(y) v dμ(y) has norm at most ‖v‖. -/
lemma norm_integrated_flip_le (R : H.Rep (Model H)) : ‖R.integrated.flip v‖ ≤ ‖v‖ := by
  -- `integrated` is built by `LinearMap.mkContinuous₂` with the bound `1`; unfold it to use that.
  grw [le_opNorm, opNorm_flip, integrated, kernelIntegral, LinearMap.mkContinuous₂_norm_le]
  · rw [one_mul]
  · exact zero_le_one

lemma weilOp_one : weilOp B 1 = 1 := by
  refine hom_ext fun y ↦ ?_
  simp [weilOp, he.apply_zero, MultiplierAction.Δ_one]

/-- Cocycle relation for the Weil operators ω = `weilOp B` of an action with cocycle c: if
c(g, 1) = 1 for all g, then ω(g)ω(h) = c(g, h)·ω(gh). -/
lemma weilOp_mul (hc_one : ∀ g : G, c g 1 = 1) (h : G) :
    weilOp B g * weilOp B h = c g h • weilOp B (g * h) := by
  -- By `weilOp_inv_mul_weilOp_mul_weilOp` for `(g * h)⁻¹` and `1`, the operator of `g * h` is a
  -- left inverse of that of `(g * h)⁻¹`; multiply `weilOp_inv_mul_weilOp_mul_weilOp` for `g` and
  -- `h` by it.
  have h_inv : weilOp B (g * h) * weilOp B (g * h)⁻¹ = 1 := by
    simpa [weilOp_one, hc_one] using weilOp_inv_mul_weilOp_mul_weilOp B (g * h)⁻¹ 1
  rw [← mul_smul_one, ← weilOp_inv_mul_weilOp_mul_weilOp B g h, ← mul_assoc, ← mul_assoc, h_inv,
    one_mul]

/-- If c(g, 1) = 1, the Weil operator `weilOp B g` preserves the inner product
`New.Heisenberg.IsVacuum.modelInner` (v, w) ↦ ∫ conj(v) w dμ of the model space. -/
@[simp]
lemma modelInner_weilOp (hc_one : c g 1 = 1) :
    modelInner (weilOp B g v) (weilOp B g w) = modelInner v w := by
  -- The operator of `g⁻¹` is both a left inverse and an adjoint of the operator of `g`.
  have h_inv : weilOp B g⁻¹ (weilOp B g v) = v := by
    simpa [weilOp_one, hc_one] using DFunLike.congr_fun (weilOp_inv_mul_weilOp_mul_weilOp B g 1) v
  -- Both sides are `Δ g` times the integral of `w (g⁻¹ • y) * conj (u y)`, as `Δ g⁻¹ = conj (Δ g)`.
  have h_coeff (u : he.Model) (y : W) :
      modelInner u (heisenbergOp y vacElem) = starRingEnd ℂ (u y) := by
    rw [← conj_modelInner, modelInner_heisenbergOp_vacElem]
  have h_adjoint (u : he.Model) :
      modelInner u (weilOp B g w) = starRingEnd ℂ (modelInner w (weilOp B g⁻¹ u)) := by
    calc modelInner u (weilOp B g w)
      _ = B.Δ g * ∫ y : W, w (g⁻¹ • y) * starRingEnd ℂ (u y) ∂μ := by
        simp [weilOp, map_integrated_moveBy _ g, h_coeff]
      _ = starRingEnd ℂ (modelInner w (weilOp B g⁻¹ u)) := by
        simp [weilOp, map_integrated_eq_integral, h_coeff, ← integral_conj, mul_comm,
          MultiplierAction.Δ_inv]
  rw [h_adjoint, h_inv, conj_modelInner]

/-- For an action `B` with cocycle c such that c(g, 1) = 1 for all g, the subgroup of those s in G
with c(g, s) = 1 for every g. -/
def cocycleRadical (h1 : ∀ g : G, c g 1 = 1) : Subgroup G :=
  have h_assoc (g h k : G) := mul_assoc (weilOp B g) (weilOp B h) (weilOp B k)
  -- Apply both products to the vacuum and pair with the unit vector `weilOp B (g * h * k) vacElem`:
  -- by `weilOp_mul` this is the cocycle identity for `c`.
  have h_cocycle (g h k : G) : c g h * c (g * h) k = c h k * c g (h * k) := by
    simpa [weilOp_mul, h1, he.apply_zero, mul_assoc g] using
      congr(modelInner (weilOp B (g * h * k) vacElem) ($(h_assoc g h k) vacElem))
  { carrier := {s : G | ∀ g : G, c g s = 1}
    one_mem' := h1
    mul_mem' {s t} hs ht g := by simpa [hs g, ht _] using (h_cocycle g s t).symm
    inv_mem' {s} hs g := by simpa [hs _, h1] using h_cocycle g s⁻¹ s }

/-! ### The Weil representation -/

/-- The Weil representation of an action `A` with cocycle 1: the homomorphism
g ↦ (v ↦ Δ(g) ∫ v(y) ρ(g • y) vac dμ(y)) from G to the bounded operators on the model space, whose
value at g is `weilOp A g`. -/
def weilRep : G →* Model H →L[ℂ] Model H :=
  MonoidHom.mk ⟨weilOp A, weilOp_one A⟩ (by simp [weilOp_mul])

/-- Let `e` be a vacuum for `H` and `μ`, with model space `Model H` of integrable `v` satisfying
v(x) = ∫ v(y) β(y,x) e(x−y) dμ(y). Let `A` be an action of `G` on `W` that preserves β and μ and has
multiplier Δ and cocycle 1. Then each Weil operator `weilRep A g`, v ↦ Δ(g) ∫ v(y) ρ(g • y) e dμ(y),
preserves the pairing `modelInner` (v, w) = ∫ conj(v) w dμ. -/
lemma modelInner_weilRep : modelInner (weilRep A g v) (weilRep A g w) = modelInner v w := by
  simp [weilRep]

attribute [simp] weilOp modelInner_weilRep

/-- The Weil operator of `g` intertwines ρ(x) with ρ(g • x): ω(g) ρ(x) v = ρ(g • x) ω(g) v. Here
ρ(x) is `heisenbergOp x`, v ↦ (z ↦ β(x,z) v(z − x)), acting on the model space of the vacuum `e`.
`A` is an action of `G` on `W` that preserves β and μ and has multiplier Δ and cocycle 1. -/
lemma weilRep_heisenbergOp :
    weilRep A g (heisenbergOp x v) = heisenbergOp (g • x) (weilRep A g v) := by
  simp [weilRep]

/-- The Weil operator of `g` sends `v` to Δ(g) ∫ v(g⁻¹ • y) ρ(y) vac dμ(y). -/
lemma weilRep_eq_integral :
    weilRep A g v = A.Δ g • ∫ y : W, v (g⁻¹ • y) • heisenbergOp y vacElem ∂μ := by
  -- Substitute `y ↦ g • y`, which preserves `μ`.
  rw [← (A.measurePreserving g).integral_comp' (f := .smul g)]
  simp only [MeasurableEquiv.smul_apply, inv_smul_smul]
  simp [weilRep, Rep.integrated_apply, Rep.moveBy]

/-- The value at `x` of the Weil operator of `g` on `v` is Δ(g) ∫ v(y) β(g • y, x) e(x − g • y)
dμ(y). -/
lemma weilRep_apply_eq_integral :
    weilRep A g v x = A.Δ g * ∫ y : W, v y * (H.β (g • y) x * e (x - g • y)) ∂μ := by
  simp [weilRep, integrated_apply_eq_integral]

/-- Let `A` be a multiplier action of `G` on the vacuum datum (`H`, `μ`, `e`) with cocycle 1 and
multiplier `A.Δ`, and let ω = `weilRep A` be its Weil representation on the model space of `e`. If
`g` preserves the vacuum function, that is e(g • y) = e(y) for all `y`, then `g` acts by
substitution up to its multiplier: for every model vector `v`, `(ω g v) x = Δ g * v (g⁻¹ x)`. -/
lemma weilRep_apply_of_vacuum_smul (hg : ∀ y : W, e (g • y) = e y) (x : W) :
    weilRep A g v x = A.Δ g * v (g⁻¹ • x) := by
  -- Substituting `g` in the kernel turns the integral that defines `ω g v` at `x` into the
  -- reproducing identity of `v` at `g⁻¹ x`.
  have h_kernel (y : W) :
      H.β (g • y) x * e (x - g • y) = H.β y (g⁻¹ • x) * e (g⁻¹ • x - y) := by
    rw [← A.beta_smul g y, ← hg (g⁻¹ • x - y), smul_sub, smul_inv_smul]
  calc weilRep A g v x
    _ = A.Δ g * ∫ y : W, v y * (H.β (g • y) x * e (x - g • y)) ∂μ :=
      weilRep_apply_eq_integral A g x v
    _ = A.Δ g * ∫ y : W, v y * (H.β y (g⁻¹ • x) * e (g⁻¹ • x - y)) ∂μ := by simp_rw [h_kernel]
    _ = A.Δ g * v (g⁻¹ • x) := by rw [v.integral_mul_beta_mul_eq (g⁻¹ • x)]

/-- Let e be a vacuum for β and μ, and let `A` be a multiplier action of G on W with trivial
cocycle, that is, an action preserving β and μ with multiplier Δ. Let ω = `weilRep A` be the Weil
representation on `Model H` (the integrable v with v(x) = ∫ v(y) β(y,x) e(x−y) dμ(y)), given by
ω(g)v = Δ(g) ∫ v(y) ρ(g • y) e dμ(y). Then the overlap ⟨vac, ω(g) vac⟩ = (ω(g) vac)(0) of the Weil
operator of `g` is the inverse of conj Δ(g): conj Δ(g) · (ω(g) e)(0) = 1. -/
lemma conj_delta_mul_weilRep_vacElem : starRingEnd ℂ (A.Δ g) * weilRep A g vacElem 0 = 1 := by
  -- The overlap determines `ω(g)` (`integrated_moveBy_vacElem_eq_smul`); compare with the
  -- definition of `ω(g)` on the unit vector `ω(g) vac`.
  have h_surj : Function.Surjective (weilRep A g) := fun v ↦
    ⟨weilRep A g⁻¹ v, by rw [rep_apply_apply, mul_inv_cancel, map_one, one_apply_eq_self]⟩
  have h_eq : weilRep A g vacElem =
      (A.Δ g * starRingEnd ℂ (weilRep A g vacElem 0)) • weilRep A g vacElem := by
    calc weilRep A g vacElem = A.Δ g • (heisenbergRep.moveBy A g).integrated vacElem vacElem := rfl
      _ = (A.Δ g * starRingEnd ℂ (weilRep A g vacElem 0)) • weilRep A g vacElem := by
        rw [mul_smul, integrated_moveBy_vacElem_eq_smul A g vacElem (weilRep A g) h_surj
          (modelInner_weilRep A g) fun y w ↦ weilRep_heisenbergOp A g y w]
  have h_unit : modelInner (weilRep A g vacElem) (weilRep A g vacElem) = 1 := by
    rw [modelInner_weilRep, modelInner_vacElem, vacElem_apply, he.apply_zero]
  have h_one : A.Δ g * starRingEnd ℂ (weilRep A g vacElem 0) = 1 := by
    calc A.Δ g * starRingEnd ℂ (weilRep A g vacElem 0)
        = modelInner (weilRep A g vacElem)
            ((A.Δ g * starRingEnd ℂ (weilRep A g vacElem 0)) • weilRep A g vacElem) := by
          rw [map_smul, h_unit, smul_eq_mul, mul_one]
      _ = 1 := by rw [← h_eq, h_unit]
  simpa using congrArg (starRingEnd ℂ) h_one

/-- For a multiplier action `A` of `G` on `W` with cocycle 1, preserving β and `μ`, with vacuum `e`,
consider the Weil operator `weilRep A g` on the model space `Model H`, which carries the L¹ norm.
Its operator norm is at most the norm of `he.vacElem` (the vacuum `e` as an element of the model
space) times the modulus of the complex multiplier `A.Δ g`. -/
lemma norm_weilRep_le : ‖weilRep A g‖ ≤ ‖he.vacElem‖ * ‖A.Δ g‖ := by
  have h_def : weilRep A g = A.Δ g • (heisenbergRep.moveBy A g).integrated.flip he.vacElem := rfl
  rw [h_def, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_integrated_flip_le he.vacElem _) (norm_nonneg _)

/-- Let e be a vacuum for β and μ, and let `A` be a multiplier action of G on W with trivial
cocycle, that is, a continuous action preserving β and μ with multiplier Δ. For a first countable
group `G`, the map (g, v) ↦ `weilRep A g v` on `G × Model H` is continuous, where ω(g)v = Δ(g) ∫
v(y) ρ(g • y) e dμ(y) and `Model H` is the space of integrable v with v(x) = ∫ v(y) β(y,x) e(x−y)
dμ(y), with the L¹ norm. -/
@[fun_prop]
lemma continuous_weilRep [FirstCountableTopology G] :
    Continuous ↿(fun (g : G) (v : Model H) ↦ weilRep A g v) := by
  -- `weilRep A g v = Δ g • ∫ v y • heisenbergOp (g • y) vacElem`. The integral is Lipschitz in `v`
  -- with the constant `‖vacElem‖` for every `g`, so it suffices to prove continuity in `g` for
  -- fixed `v`.
  have h_lip (g : G) : LipschitzWith ‖he.vacElem‖₊
    ((heisenbergRep.moveBy A g).integrated.flip vacElem) :=
    lipschitzWith_of_opNorm_le (norm_integrated_flip_le he.vacElem (heisenbergRep.moveBy A g))
  -- Dominated convergence: `heisenbergOp` is isometric, so the integrand has the norm of
  -- `v y • vacElem`.
  have h_cont (v : Model H) :
      Continuous fun g : G ↦ ∫ y : W, v y • he.heisenbergOp (g • y) vacElem ∂μ :=
    continuous_of_dominated (bound := fun y ↦ ‖v y • he.vacElem‖) (by fun_prop)
      (fun g ↦ .of_forall fun y ↦ by simp [norm_smul, Rep.norm_map])
      (v.integrable.smul_const he.vacElem).norm (.of_forall (by fun_prop))
  exact A.continuous_delta.fst'.smul (continuous_prod_of_continuous_lipschitzWith' _ _ h_lip h_cont)

attribute [irreducible] weilRep

end New.Heisenberg.IsVacuum

/-!
## Orthogonal sums, tensor products of model vectors and Wiener's bound

* `New.Heisenberg.IsVacuum.wiener_bound`: a sum of coefficients along a group homomorphism into `W₁`
  is bounded by the number of terms that fall in a fixed compact set, times a constant `M` and the
  norm of the model vector `v`.
* `New.Heisenberg.OrthogonalSum.tmul`: the tensor product of model vectors, a product of functions.
  It is multiplicative for norms and inner products (`New.Heisenberg.OrthogonalSum.norm_tmul`,
  `New.Heisenberg.OrthogonalSum.modelInner_tmul`).
* `New.Heisenberg.OrthogonalSum.weilRep_tmul`, `New.Heisenberg.Rep.integrated_tmul`: the tensor
  product is compatible with the Weil representation and with the integrated action.
-/

namespace New.Heisenberg

open MeasureTheory Heisenberg.Rep IsVacuum Measure ENNReal Set MultiplierAction

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W]
  {H : Heisenberg W} [MeasurableSpace W] [IsTopologicalAddGroup W] [BorelSpace W]
  [SecondCountableTopology W] {μ : Measure W} [μ.IsAddHaarMeasure] {e : W → ℂ}
  {W₁ : Type*} [AddCommGroup W₁] [TopologicalSpace W₁]
  {H₁ : Heisenberg W₁} [MeasurableSpace W₁] [IsTopologicalAddGroup W₁] [BorelSpace W₁]
  [SecondCountableTopology W₁] {μ₁ : Measure W₁} [μ₁.IsAddHaarMeasure] {e₁ : W₁ → ℂ}
  {W₂ : Type*} [AddCommGroup W₂] [TopologicalSpace W₂]
  {H₂ : Heisenberg W₂} [MeasurableSpace W₂] [IsTopologicalAddGroup W₂] [BorelSpace W₂]
  [SecondCountableTopology W₂] {μ₂ : Measure W₂} [μ₂.IsAddHaarMeasure] {e₂ : W₂ → ℂ}
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- An isomorphism φ: W₁ × W₂ → W of topological groups under which the bicharacter of H and the
function e are the products of those of the factors (β₁β₂, e₁e₂). -/
structure OrthogonalSum (H : Heisenberg W) (H₁ : Heisenberg W₁) (H₂ : Heisenberg W₂) (e : W → ℂ)
    [IsVacuum H₁ μ₁ e₁] [IsVacuum H₂ μ₂ e₂] where
  /-- The isomorphism of topological groups from `W₁ × W₂` onto `W`. -/
  equiv : W₁ × W₂ ≃ₜ+ W
  /-- Along `equiv`, the cocycle of `H` is the product of the cocycles of `H₁` and `H₂`. -/
  beta_equiv (x y : W₁ × W₂) : β H (equiv x) (equiv y) = β H₁ x.1 y.1 * β H₂ x.2 y.2
  /-- Along `equiv`, the function `e` is the product of the two vacua `e₁` and `e₂`. -/
  vac_equiv (x : W₁ × W₂) : e (equiv x) = e₁ x.1 * e₂ x.2

variable (R : Rep H X) [IsVacuum H₁ μ₁ e₁] [IsVacuum H₂ μ₂ e₂]
  (S : H.OrthogonalSum H₁ H₂ e) [he : H.IsVacuum μ e]
  (v : Model H₁) (w : Model H₂) (x : W) (f : X)

/-! ### Wiener's bound -/

/-- Wiener's bound. Let `T` be a bounded map from the model space of the vacuum `e` to a space `X`,
and let `W` act on the model space by `ρ = heisenbergOp`. Assume that a vector `u` has `u 0 ≠ 0`,
that `W₁` is Hausdorff, that `κ : W₁ → W` is a continuous homomorphism, and that
`‖T ρ(z + κ x) u‖ = ‖g (t z + x)‖` for all `z` in `W` and `x` in `W₁`, with an integrable `g` on
`W₁` and some function `t : W → W₁`. Then there are a compact set `B` in `W₁` and a constant `M`
with the following property. For every additive group `I`, every homomorphism `φ : I → W₁` and
every `v`, the sum over `i` of `‖T ρ(κ (φ i)) v‖` is at most `M ‖v‖` times the number of `i` with
`φ i ∈ B`. -/
lemma IsVacuum.wiener_bound [LocallyCompactSpace W] [LocallyCompactSpace W₁]
    [T2Space W₁] (T : Model H →L[ℂ] X) {u : Model H} (hu : u 0 ≠ 0)
    (κ : W₁ →ₜ+ W) {g : W₁ → X} (hg : Integrable g μ₁) (t : W → W₁)
    (h_enorm_eq : ∀ (z : W) (x : W₁), ‖T (heisenbergOp (z + κ x) u)‖ₑ = ‖g (t z + x)‖ₑ) :
    ∃ B : Set W₁,
      IsCompact B ∧
      ∃ M : NNReal, ∀ {I : Type*} [AddGroup I] (φ : I →+ W₁) (v : Model H),
        ∑' i : I, ‖T (heisenbergOp (κ (φ i)) v)‖ₑ ≤ (φ ⁻¹' B).encard * M * ‖v‖ₑ := by
  -- Put `G s = ∫ ‖v z‖ ‖T heisenbergOp(z + κ s) u‖ dz`, so that `∫ G = ‖g‖ ‖v‖`. The value at `x`
  -- is bounded by a multiple of the integral of `G` over `x + K`, `K` a compact neighbourhood of
  -- `0`, and a point lies in at most `#φ⁻¹(B)` of the translates `φ i + K`, where `B = -K + K`.
  obtain ⟨K, hK, hK₀⟩ : ∃ K : Set W₁, IsCompact K ∧ K ∈ nhds 0 := exists_compact_mem_nhds 0
  obtain ⟨B, hB, mem_B⟩ : ∃ B : Set W₁, IsCompact B ∧ ∀ a ∈ K, ∀ b ∈ K, -a + b ∈ B :=
    ⟨_, hK.neg.add hK, fun a ha b hb ↦ add_mem_add (neg_mem_neg.mpr ha) hb⟩
  have u_cont : Continuous fun s : W₁ ↦ ‖u (-κ s)‖ₑ :=
    (continuous u).enorm.comp (map_continuous κ).neg
  -- `u (-κ s) ≠ 0` for `s` near `0`, so the integral of its norm over `K` is positive.
  obtain ⟨r, hr⟩ : ∃ r : ℕ, 1 < r * ∫⁻ s in K, ‖u (-κ s)‖ₑ ∂μ₁ := by
    refine exists_nat_mul_gt ((setLIntegral_pos_iff u_cont.measurable).mpr ?_).ne' one_ne_top
    have hu_zero : ‖u (-κ 0)‖ₑ ≠ 0 := by simpa using hu
    exact μ₁.measure_pos_of_mem_nhds ((u_cont.continuousAt.eventually_ne hu_zero).and hK₀)
  obtain ⟨M, hM⟩ : ∃ M : NNReal, ∫⁻ x : W₁, ‖g x‖ₑ ∂μ₁ = M :=
    ⟨_, (coe_toNNReal hg.hasFiniteIntegral.ne).symm⟩
  -- The constant is nonzero, so that the bound is trivial when `φ ⁻¹' B` is infinite.
  refine ⟨B, hB, r * M + 1, fun {I} _ φ v ↦ ?_⟩
  obtain hN | ⟨N, hN⟩ : (φ ⁻¹' B).encard = ⊤ ∨ ∃ N : ℕ, (φ ⁻¹' B).encard = N := by
    cases (φ ⁻¹' B).encard <;> simp
  · by_cases hv : v = 0 <;> simp [hN, hv]
  -- If `y` lies in the translates of `K` by `φ i` and `φ i₀`, then `φ (i - i₀)` lies in `B`.
  have h_encard_le (y : W₁) : {i : I | y ∈ (· - φ i) ⁻¹' K}.encard ≤ N := by
    obtain h_empty | ⟨i₀, hi₀⟩ := {i : I | y ∈ (· - φ i) ⁻¹' K}.eq_empty_or_nonempty
    · rw [h_empty, encard_empty]
      exact zero_le
    · have h_mem (i : I) (hi : y - φ i ∈ K) : φ (i - i₀) ∈ B := by
        simpa using mem_B (y - φ i) hi (y - φ i₀) hi₀
      rw [← hN]
      exact encard_le_encard_of_injOn (f := (· - i₀)) h_mem sub_left_injective.injOn
  let G (s : W₁) : ℝ≥0∞ := ∫⁻ z : W, ‖v z‖ₑ * ‖T (heisenbergOp (z + κ s) u)‖ₑ ∂μ
  have G_int : ∫⁻ s : W₁, G s ∂μ₁ = M * ‖v‖ₑ := by
    -- The norm of a model vector is its `L¹` norm.
    have h_norm_toL1 : ‖Integrable.toL1 (v : W → ℂ) v.integrable‖ₑ = ‖v‖ₑ := rfl
    -- For fixed `z` the integral over `s` is that of a translate of `g`.
    have h_inner (z : W) :
        ∫⁻ s : W₁, ‖v z‖ₑ * ‖T (heisenbergOp (z + κ s) u)‖ₑ ∂μ₁ = M * ‖v z‖ₑ := by
      simp_rw [h_enorm_eq]
      rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_add_left_eq_self (‖g ·‖ₑ), hM, mul_comm]
    calc ∫⁻ s : W₁, G s ∂μ₁
      _ = ∫⁻ z : W, ∫⁻ s : W₁, ‖v z‖ₑ * ‖T (heisenbergOp (z + κ s) u)‖ₑ ∂μ₁ ∂μ :=
        (lintegral_lintegral_swap (by fun_prop)).symm
      _ = M * ∫⁻ z : W, ‖v z‖ₑ ∂μ := by
        simp_rw [h_inner]
        exact lintegral_const_mul' _ _ coe_ne_top
      _ = M * ‖v‖ₑ := by rw [← h_norm_toL1, Integrable.enorm_toL1]
  -- By `integrated_eq_smul`, `∫ v z • heisenbergOp(z) heisenbergOp(κ s) u dz` is `v` times the
  -- value of `heisenbergOp(κ s) u` at `0`, which has norm `‖u (-κ s)‖`; apply
  -- `T ∘ heisenbergOp(κ x)`.
  have G_ge (x s : W₁) : ‖u (-κ s)‖ₑ * ‖T (heisenbergOp (κ x) v)‖ₑ ≤ G (x + s) := by
    have h_bound :
        ‖(T ∘L heisenbergOp (κ x)) (heisenbergRep.integrated v (heisenbergOp (κ s) u))‖ₑ ≤
          ∫⁻ z : W,
            ‖v z • (T ∘L heisenbergOp (κ x)) (heisenbergOp z (heisenbergOp (κ s) u))‖ₑ ∂μ := by
      rw [heisenbergRep.map_integrated_eq_integral (T ∘L heisenbergOp (κ x))]
      exact enorm_integral_le_lintegral_enorm _
    simpa [G, norm_smul, ← ofReal_norm, add_left_comm, mul, norm_eq_one] using h_bound
  -- Multiply `G_ge` by `r`, integrate over `s ∈ K` and use `hr`.
  have h_enorm_le_setLIntegral (i : I) :
      ‖T (heisenbergOp (κ (φ i)) v)‖ₑ ≤ r * ∫⁻ s in (· - φ i) ⁻¹' K, G s ∂μ₁ := by
    grw [← (measurePreserving_add_left μ₁ (φ i)).setLIntegral_comp_preimage_emb
      (measurableEmbedding_addLeft (φ i)), ← one_mul ‖T (heisenbergOp (κ (φ i)) v)‖ₑ, hr, mul_assoc,
      lintegral_mul_const_le]
    gcongr
    · simp [preimage]
    · exact G_ge (φ i) _
  calc ∑' i : I, ‖T (heisenbergOp (κ (φ i)) v)‖ₑ
    _ ≤ ∑' i : I, r * ∫⁻ s in (· - φ i) ⁻¹' K, G s ∂μ₁ :=
        ENNReal.tsum_le_tsum h_enorm_le_setLIntegral
    _ = r * ∫⁻ s : W₁, G s ∂.sum fun i : I ↦ μ₁.restrict ((· - φ i) ⁻¹' K) := by
      rw [lintegral_sum_measure, ENNReal.tsum_mul_left]
    _ ≤ r * ∫⁻ s : W₁, G s ∂N • μ₁ := by
      grw [sum_restrict_le (fun i ↦ measurable_sub_const (φ i) hK.measurableSet) h_encard_le,
        μ₁.restrict_le_self]
    _ = N * (r * M) * ‖v‖ₑ := by simp [G_int, mul_assoc, mul_left_comm]
    _ ≤ (φ ⁻¹' B).encard * (r * M + 1 : NNReal) * ‖v‖ₑ := by
      simp [hN, mul_le_mul_left, mul_le_mul_right]

/-! ### Tensor products along a splitting -/

/-- For a representation `R` of `H` on `X` and an orthogonal splitting `S` with `φ = S.equiv`, the
representation x ↦ R.ρ(φ(x, 0)) of `H₁` on `X`. -/
@[local simp]
def Rep.left : H₁.Rep X where
  ρ x := R.ρ (S.equiv (x, 0))
  mul := by simp [mul, OrthogonalSum.beta_equiv, ← map_add]
  norm_map := by simp [norm_map]
  cont := by fun_prop

/-- For a representation `R` of `H` on `X` and an orthogonal splitting `S` with `φ = S.equiv`, the
representation x ↦ R.ρ(φ(0, x)) of `H₂` on `X`. -/
@[local simp]
def Rep.right : H₂.Rep X where
  ρ x := R.ρ (S.equiv (0, x))
  mul := by simp [mul, OrthogonalSum.beta_equiv, ← map_add]
  norm_map := by simp [norm_map]
  cont := by fun_prop

/-- The tensor product of model vectors, a bounded bilinear map
`Model H₁ →L[ℂ] Model H₂ →L[ℂ] Model H`. With `φ = S.equiv`, it sends `v`, `w` to the iterated
integral `∫ v(y₁) ρ(φ(y₁, 0)) (∫ w(y₂) ρ(φ(0, y₂)) e dμ₂) dμ₁`, where `ρ` acts on the model space of
`e`. As a function it is `φ(x₁, x₂) ↦ v x₁ * w x₂`, see
`New.Heisenberg.OrthogonalSum.tmul_apply`. -/
noncomputable def OrthogonalSum.tmul : Model H₁ →L[ℂ] Model H₂ →L[ℂ] Model H :=
  ((heisenbergRep.left S).integrated.flip ∘L (heisenbergRep.right S).integrated.flip vacElem).flip

/-- Let `S` split `H` along `S.equiv : W₁ × W₂ ≃ W`, with `e` the product of the vacua `e₁` (for
`μ₁`) and `e₂` (for `μ₂`). Then `e` is a vacuum for `H` and the image of `μ₁ × μ₂` under
`S.equiv`. -/
lemma OrthogonalSum.isVacuum [LocallyCompactSpace W₁] [LocallyCompactSpace W₂] :
    H.IsVacuum ((μ₁.prod μ₂).map S.equiv) e := by
  -- Read through `S.equiv`, `e` is the product of the two vacua, and each property holds
  -- factorwise.
  have h₁ : H₁.IsVacuum μ₁ e₁ := inferInstance
  have h₂ : H₂.IsVacuum μ₂ e₂ := inferInstance
  have he_eq : e = (fun x : W₁ × W₂ ↦ e₁ x.1 * e₂ x.2) ∘ S.equiv.symm :=
    funext fun x ↦ by rw [Function.comp_apply, ← S.vac_equiv, S.equiv.apply_symm_apply]
  have h_cont : Continuous e := by
    rw [he_eq]
    exact (h₁.cont.fst'.mul h₂.cont.snd').comp S.equiv.symm.continuous
  exact
    { cont := h_cont
      apply_zero := by simp [he_eq, h₁.apply_zero, h₂.apply_zero]
      apply_neg := by simp [he_eq, h₁.apply_neg, h₂.apply_neg]
      conj_apply := by simp [he_eq, h₁.conj_apply, h₂.conj_apply]
      twisted_conv := S.equiv.surjective.forall₂.mpr fun y x ↦ by
        -- The convolution integral over the product is the product of the two convolutions.
        rw [integral_map (by fun_prop) (by fun_prop), S.vac_equiv, S.vac_equiv, mul_mul_mul_comm,
          ← h₁.twisted_conv, ← h₂.twisted_conv]
        simp [← map_sub, ← map_add, vac_equiv, beta_equiv, ← integral_prod_mul, mul_comm,
          mul_assoc, mul_left_comm]
      integrable := by
        rw [integrable_map_measure (by fun_prop) (by fun_prop)]
        simpa [Function.comp_def, vac_equiv] using h₁.integrable.mul_prod h₂.integrable }

/-- A vacuum fixes the normalisation of the Haar measure, so `S.equiv` carries `μ₁ × μ₂` to `μ`. -/
lemma OrthogonalSum.measurePreserving_equiv [LocallyCompactSpace W] [LocallyCompactSpace W₁]
    [LocallyCompactSpace W₂] : MeasurePreserving S.equiv (μ₁.prod μ₂) μ where
  measurable := by fun_prop
  map_eq :=
    addHaar_eq_of_integral_eq_one he.integral_norm_sq_eq_one S.isVacuum.integral_norm_sq_eq_one

omit [CompleteSpace X] in
lemma OrthogonalSum.integral_eq_integral_prod [LocallyCompactSpace W] [LocallyCompactSpace W₁]
    [LocallyCompactSpace W₂] (f : W → X) :
    ∫ x : W, f x ∂μ = ∫ x : W₁ × W₂, f (S.equiv x) ∂μ₁.prod μ₂ := by
  rw [← S.measurePreserving_equiv.map_eq]
  exact S.equiv.isClosedEmbedding.integral_map f

omit [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure] in
/-- Let `S` be an orthogonal sum, that is, an isomorphism φ = `S.equiv` : W₁ × W₂ → W of topological
groups under which β and e are the products β₁β₂ and e₁e₂. Let v and w lie in the model spaces of e₁
and e₂, the integrable functions reproduced by e₁ and e₂. Read through φ, the tensor product
`S.tmul v w` is the function (x₁, x₂) ↦ v x₁ * w x₂, so its value at x is
v((φ⁻¹x).1) · w((φ⁻¹x).2). -/
@[local simp]
lemma OrthogonalSum.tmul_apply : S.tmul v w x = v (S.equiv.symm x).1 * w (S.equiv.symm x).2 := by
  obtain ⟨⟨a, b⟩, rfl⟩ := S.equiv.surjective x
  -- The translate of the vacuum by `S.equiv (y₁, y₂)` is the product of the two reproducing
  -- kernels, so the double integral that defines `S.tmul` reproduces `v` at `a` and `w` at `b`.
  have h_kernel (y₁ : W₁) (y₂ : W₂) :
      (heisenbergRep.left S).ρ y₁ ((heisenbergRep.right S).ρ y₂ vacElem) (S.equiv (a, b)) =
        H₁.β y₁ a * e₁ (a - y₁) * (H₂.β y₂ b * e₂ (b - y₂)) := by
    simp [mul, beta_equiv, ← map_add, ← map_sub, vac_equiv, mul_mul_mul_comm]
  have h_inner (y₂ : W₂) :
      (heisenbergRep.left S).integrated v ((heisenbergRep.right S).ρ y₂ vacElem) (S.equiv (a, b)) =
        v a * (H₂.β y₂ b * e₂ (b - y₂)) := by
    rw [← valueAt_apply, map_integrated_eq_integral, ← v.integral_mul_beta_mul_eq a,
      ← integral_mul_const]
    simp_rw [valueAt_apply, h_kernel, smul_eq_mul, mul_assoc]
  rw [S.equiv.symm_apply_apply]
  calc S.tmul v w (S.equiv (a, b))
    _ = ∫ y₂ : W₂, w y₂ * (heisenbergRep.left S).integrated v
          ((heisenbergRep.right S).ρ y₂ vacElem) (S.equiv (a, b)) ∂μ₂ :=
      (heisenbergRep.right S).map_integrated_eq_integral
        (valueAt (S.equiv (a, b)) ∘L (heisenbergRep.left S).integrated v) w vacElem
    _ = v a * ∫ y₂ : W₂, w y₂ * (H₂.β y₂ b * e₂ (b - y₂)) ∂μ₂ := by
      simp_rw [h_inner, ← integral_const_mul, mul_left_comm (v a)]
    _ = v a * w b := by rw [w.integral_mul_beta_mul_eq b]

open scoped ComplexConjugate in
/-- Let `S` be an orthogonal sum, that is, an isomorphism φ: W₁ × W₂ → W of topological groups under
which β and e are the products β₁β₂ and e₁e₂. The tensor product `S.tmul` of model vectors (elements
of the reproducing spaces of e₁ and e₂) is multiplicative for the inner products ⟨v, w⟩ = ∫ conj(v)
w dμ: `⟨v ⊗ w, v' ⊗ w'⟩ = ⟨v, v'⟩ ⟨w, w'⟩`. -/
lemma OrthogonalSum.modelInner_tmul [LocallyCompactSpace W] [LocallyCompactSpace W₁]
    [LocallyCompactSpace W₂] (v v' : Model H₁) (w w' : Model H₂) :
    modelInner (S.tmul v w) (S.tmul v' w') = modelInner v v' * modelInner w w' := by
  -- Read through `S.equiv`, the integrand on `W₁ × W₂` is a function of the first coordinate
  -- times a function of the second, and Fubini's theorem splits the integral.
  calc
    modelInner (S.tmul v w) (S.tmul v' w') =
        ∫ x : W₁ × W₂, conj (S.tmul v w (S.equiv x)) * S.tmul v' w' (S.equiv x) ∂μ₁.prod μ₂ := by
      rw [modelInner_apply, S.integral_eq_integral_prod]
    _ = ∫ x : W₁ × W₂, conj (v x.1) * v' x.1 * (conj (w x.2) * w' x.2) ∂μ₁.prod μ₂ := by
      refine integral_congr_ae (.of_forall fun x : W₁ × W₂ ↦ ?_)
      simp only [S.tmul_apply, S.equiv.symm_apply_apply, map_mul]
      ring
    _ = (∫ x₁ : W₁, conj (v x₁) * v' x₁ ∂μ₁) * ∫ x₂ : W₂, conj (w x₂) * w' x₂ ∂μ₂ :=
      integral_prod_mul (fun x₁ : W₁ ↦ conj (v x₁) * v' x₁) fun x₂ : W₂ ↦ conj (w x₂) * w' x₂
    _ = modelInner v v' * modelInner w w' := by
      rw [modelInner_apply, modelInner_apply]

/-- Let `S` present `W` as the orthogonal sum of `W₁` and `W₂`, with `H` and the vacuum `e` being
the products of the data on the factors. For model vectors `v` of `e₁` and `w` of `e₂`, the tensor
product `S.tmul v w` (the function `S.equiv (x₁, x₂) ↦ v x₁ * w x₂`) has L¹ norm ‖v‖ · ‖w‖. -/
lemma OrthogonalSum.norm_tmul [LocallyCompactSpace W] [LocallyCompactSpace W₁]
    [LocallyCompactSpace W₂] : ‖S.tmul v w‖ = ‖v‖ * ‖w‖ := by
  calc ‖S.tmul v w‖ = ∫ x : W₁ × W₂, ‖S.tmul v w (S.equiv x)‖ ∂μ₁.prod μ₂ := by
        rw [norm_eq_integral_norm, ← S.measurePreserving_equiv.integral_comp
          S.equiv.measurableEmbedding]
    _ = ∫ x : W₁ × W₂, ‖v x.1‖ * ‖w x.2‖ ∂μ₁.prod μ₂ := by simp [S.tmul_apply]
    _ = ‖v‖ * ‖w‖ := by
      rw [norm_eq_integral_norm v, norm_eq_integral_norm w]
      exact integral_prod_mul (fun x₁ : W₁ ↦ ‖v x₁‖) fun x₂ : W₂ ↦ ‖w x₂‖

/-- The product rule for the Weil representation of an orthogonal sum. Identify `W` with
`W₁ × W₂` by `S.equiv`, and let `A`, `A₁`, `A₂` be actions with cocycle 1 of groups `G`, `G₁`,
`G₂` on `W`, `W₁`, `W₂`. If `g` acts as `(g₁, g₂)` and its multiplier is the product of theirs,
then the Weil operator of `g` is the tensor product of those of `g₁` and `g₂`. -/
lemma OrthogonalSum.weilRep_tmul [LocallyCompactSpace W] [LocallyCompactSpace W₁]
    [LocallyCompactSpace W₂] {G G₁ G₂ : Type*} [Group G] [TopologicalSpace G]
    [DistribMulAction G W] [ContinuousSMul G W] [Group G₁] [TopologicalSpace G₁]
    [DistribMulAction G₁ W₁] [ContinuousSMul G₁ W₁] [Group G₂] [TopologicalSpace G₂]
    [DistribMulAction G₂ W₂] [ContinuousSMul G₂ W₂] (A : H.MultiplierAction μ e G)
    (A₁ : H₁.MultiplierAction μ₁ e₁ G₁) (A₂ : H₂.MultiplierAction μ₂ e₂ G₂) {g : G} {g₁ : G₁}
    {g₂ : G₂} (h_delta_eq : Δ A g = Δ A₁ g₁ * Δ A₂ g₂)
    (h_smul_equiv : ∀ x : W₁ × W₂, g • S.equiv x = S.equiv (g₁ • x.1, g₂ • x.2)) (v : Model H₁)
    (w : Model H₂) :
    weilRep A g (S.tmul v w) = S.tmul (weilRep A₁ g₁ v) (weilRep A₂ g₂ w) := by
  -- Evaluate at a point `S.equiv (a, b)`: the integral over `W` that defines `weilRep` splits into
  -- the product of the two integrals over `W₁` and `W₂`.
  ext x
  obtain ⟨⟨a, b⟩, rfl⟩ := S.equiv.surjective x
  let F₁ (y : W₁) : ℂ := v y * (H₁.β (g₁ • y) a * e₁ (a - g₁ • y))
  let F₂ (y : W₂) : ℂ := w y * (H₂.β (g₂ • y) b * e₂ (b - g₂ • y))
  have h_split (y : W₁ × W₂) :
      S.tmul v w (S.equiv y) *
          (H.β (g • S.equiv y) (S.equiv (a, b)) * e (S.equiv (a, b) - g • S.equiv y)) =
        F₁ y.1 * F₂ y.2 := by
    simp only [F₁, F₂, h_smul_equiv, ← map_sub, S.beta_equiv, S.vac_equiv, S.tmul_apply,
      S.equiv.symm_apply_apply, Prod.mk_sub_mk]
    ring
  calc weilRep A g (S.tmul v w) (S.equiv (a, b))
    _ = Δ A g * ∫ y : W₁ × W₂, F₁ y.1 * F₂ y.2 ∂μ₁.prod μ₂ := by
      simp_rw [weilRep_apply_eq_integral, S.integral_eq_integral_prod, h_split]
    _ = (Δ A₁ g₁ * ∫ y : W₁, F₁ y ∂μ₁) * (Δ A₂ g₂ * ∫ y : W₂, F₂ y ∂μ₂) := by
      rw [integral_prod_mul, h_delta_eq, mul_mul_mul_comm]
    _ = S.tmul (weilRep A₁ g₁ v) (weilRep A₂ g₂ w) (S.equiv (a, b)) := by
      rw [S.tmul_apply, S.equiv.symm_apply_apply, weilRep_apply_eq_integral,
        weilRep_apply_eq_integral]

/-- Integrating `v ⊗ w` against `R` is integrating `w` against the restriction `R.right S` of `R` to
`W₂`, then `v` against its restriction `R.left S` to `W₁`. -/
lemma Rep.integrated_tmul [LocallyCompactSpace W] [LocallyCompactSpace W₁]
    [LocallyCompactSpace W₂] :
    R.integrated (S.tmul v w) f = (R.left S).integrated v ((R.right S).integrated w f) := by
  -- The left side is an integral over `W₁ × W₂`, the right side the iterated integral. Fubini's
  -- theorem applies: the integrand is the integrable `v ⊗ w` times a continuous function
  -- bounded by `‖f‖`.
  have h_integrable :
      Integrable (fun x : W₁ × W₂ ↦ (v x.1 * w x.2) • R.ρ (S.equiv x) f) (μ₁.prod μ₂) :=
    (v.integrable.mul_prod w.integrable).smul_bdd ‖f‖ (by fun_prop) (by simp [norm_map])
  have h_rho (a : W₁) (b : W₂) :
      (R.left S).ρ a ((R.right S).ρ b f) = R.ρ (S.equiv (a, b)) f := by
    simp [mul, OrthogonalSum.beta_equiv, ← map_add]
  have h_inner (a : W₁) : ∫ b : W₂, (v a * w b) • R.ρ (S.equiv (a, b)) f ∂μ₂ =
      v a • (R.left S).ρ a ((R.right S).integrated w f) := by
    simp_rw [map_integrated_eq_integral, h_rho, ← integral_smul, smul_smul]
  calc R.integrated (S.tmul v w) f
    _ = ∫ x : W₁ × W₂, (v x.1 * w x.2) • R.ρ (S.equiv x) f ∂μ₁.prod μ₂ := by
      simp_rw [integrated_apply, S.integral_eq_integral_prod, S.tmul_apply,
        S.equiv.symm_apply_apply]
    _ = ∫ a : W₁, ∫ b : W₂, (v a * w b) • R.ρ (S.equiv (a, b)) f ∂μ₂ ∂μ₁ :=
      integral_prod _ h_integrable
    _ = (R.left S).integrated v ((R.right S).integrated w f) := by
      simp_rw [h_inner, (R.left S).integrated_apply]

omit [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure] in
/-- Let `S` be an orthogonal sum: an isomorphism φ : W₁ × W₂ ≃ W of topological groups under which
β = β₁β₂ and e = e₁e₂. Then the tensor product `S.tmul`, which sends `v`, `w` to the function φ(x₁,
x₂) ↦ v(x₁) w(x₂) in `Model H`, takes the pair of vacua `vacElem` (e₁ and e₂) to the vacuum
`vacElem` (e). -/
lemma OrthogonalSum.tmul_vacElem : S.tmul vacElem vacElem = vacElem := by
  simp [← S.vac_equiv, IsVacuum.ext_iff]

/-- Let `S` be an orthogonal sum φ : W₁ × W₂ ≃ W, under which β = β₁β₂ and e = e₁e₂, and let
v ⊗ w = `S.tmul v w` be the model vector φ(x₁, x₂) ↦ v(x₁) w(x₂). Then ρ(x) of `v ⊗ w` is ρ₁(x₁)
v ⊗ ρ₂(x₂) w, where (x₁, x₂) = `S.equiv.symm x` and ρ(x) is `heisenbergOp x`, v ↦ (z ↦ β(x,z)
v(z − x)). -/
lemma OrthogonalSum.heisenbergOp_tmul :
    IsVacuum.heisenbergOp x (S.tmul v w) =
      S.tmul (IsVacuum.heisenbergOp (S.equiv.symm x).1 v)
        (IsVacuum.heisenbergOp (S.equiv.symm x).2 w) := by
  simp [map_sub, mul_mul_mul_comm, ← S.beta_equiv, IsVacuum.ext_iff]

/-- A translate of the vacuum is the product of translates of the two vacua. -/
lemma OrthogonalSum.heisenbergOp_equiv_vacElem (a : W₁) (b : W₂) :
    IsVacuum.heisenbergOp (S.equiv (a, b)) vacElem =
      S.tmul (IsVacuum.heisenbergOp a vacElem) (IsVacuum.heisenbergOp b vacElem) := by
  rw [← S.tmul_vacElem, S.heisenbergOp_tmul, S.equiv.symm_apply_apply]

/-- Restriction of functions to `W₂` along `φ = S.equiv` is a bounded map `r` from the model of `e`
to the model of `e₂`, and ∫ v(y) ρ(φ(y, 0)) u dμ₁(y) = v ⊗ r u for `v` in the model of `e₁` and
`u` in the model of `e`. -/
lemma OrthogonalSum.exists_restriction :
    ∃ r : Model H →L[ℂ] Model H₂,
      (∀ (u : Model H) (b : W₂), r u b = u (S.equiv (0, b))) ∧
      ∀ (v : Model H₁) (u : Model H), (heisenbergRep.left S).integrated v u = S.tmul v (r u) := by
  -- Translates of the vacuum are products, so their restrictions `K y` are bounded, and
  -- superposition gives `r`. On products the formula is `integrated_eq_smul`.
  let K (y : W) : Model H₂ :=
    (heisenbergOp (S.equiv.symm y).1 vacElem : Model H₁) 0 • heisenbergOp (S.equiv.symm y).2 vacElem
  have hK_bound (y : W) : ‖K y‖ ≤ ‖(vacElem : Model H₁)‖ * ‖(vacElem : Model H₂)‖ := by
    rw [norm_smul, heisenbergRep.norm_map, ← heisenbergRep.norm_map (S.equiv.symm y).1]
    exact mul_le_mul_of_nonneg_right (norm_apply_le 0 _) (norm_nonneg _)
  have h_cont : Continuous e₁ := IsVacuum.cont H₁
  have hK_cont : Continuous K := by
    simp only [K, heisenbergOp_apply, vacElem_apply]
    fun_prop
  obtain ⟨r, hr⟩ : ∃ r : Model H →L[ℂ] Model H₂, ∀ (M : Model H₂ →L[ℂ] ℂ) (N : Model H →L[ℂ] ℂ),
      (∀ y : W, M (K y) = N (heisenbergOp y vacElem)) → ∀ u : Model H, M (r u) = N u :=
    exists_lift hK_cont hK_bound
  have h_apply (u : Model H) (b : W₂) : r u b = u (S.equiv (0, b)) := by
    refine hr (valueAt b) (valueAt (S.equiv (0, b))) (S.equiv.surjective.forall.mpr ?_) u
    rintro ⟨a, c⟩
    simp only [K, S.heisenbergOp_equiv_vacElem, valueAt_apply, IsVacuum.smul_apply, S.tmul_apply,
      S.equiv.symm_apply_apply]
  have h_tmul (v f : Model H₁) (w : Model H₂) :
      (heisenbergRep.left S).integrated v (S.tmul f w) = S.tmul v (r (S.tmul f w)) := by
    have h_restrict : r (S.tmul f w) = f 0 • w := by
      ext b
      rw [h_apply, S.tmul_apply, S.equiv.symm_apply_apply, IsVacuum.smul_apply]
    have h_intertwine (y : W₁) (f : Model H₁) :
        S.tmul.flip w (heisenbergRep.ρ y f) = (heisenbergRep.left S).ρ y (S.tmul.flip w f) := by
      simpa using (S.heisenbergOp_tmul f w (S.equiv (y, 0))).symm
    simpa [h_restrict] using
      (map_integrated heisenbergRep (S.tmul.flip w) v f h_intertwine).symm
  refine ⟨r, h_apply, fun v u ↦ ?_⟩
  suffices h_eq : (heisenbergRep.left S).integrated v = S.tmul v ∘L r by
    rw [h_eq, ContinuousLinearMap.comp_apply]
  refine hom_ext (S.equiv.surjective.forall.mpr ?_)
  rintro ⟨a, b⟩
  rw [S.heisenbergOp_equiv_vacElem]
  exact h_tmul v (heisenbergOp a vacElem) (heisenbergOp b vacElem)

end New.Heisenberg

/-!
## Transport of the model along a linear or conjugate linear isomorphism

Let `e`, `e'` be vacua (`New.Heisenberg.IsVacuum`) for Heisenberg cocycles on `W`, `W'`, and let
`φ : W' ≃ W` be an isomorphism of topological groups that matches the vacua and matches the cocycles
up to `σ`, the identity or the conjugation of `ℂ`. `New.Heisenberg.IsVacuum.transport` is the
`σ`-semilinear map `v ↦ σ ∘ v ∘ φ` between the models `New.Heisenberg.IsVacuum.Model` (integrable
functions reproduced by the vacuum kernel); `New.Heisenberg.IsVacuum.map_integral_and_map_vacuum` is
the change of variables behind it.
-/

section ModelTransport

open MeasureTheory Measure Complex

namespace New.Heisenberg.IsVacuum

variable {W W' : Type*} [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] [LocallyCompactSpace W]
  [AddCommGroup W'] [TopologicalSpace W'] [MeasurableSpace W'] [IsTopologicalAddGroup W']
  [BorelSpace W']
  {H : Heisenberg W} {μ : Measure W} {e : W → ℂ} {H' : Heisenberg W'} {μ' : Measure W'}
  {e' : W' → ℂ} [IsAddHaarMeasure μ] [IsAddHaarMeasure μ'] [he : IsVacuum H μ e]
  [he' : IsVacuum H' μ' e'] {σ : ℂ →+* ℂ} [RingHomIsometric σ] {φ : W' ≃ₜ+ W}

include he he'

variable (H H') in
/-- Let `e`, `e'` be vacua for the Haar measures `μ`, `μ'`. An isomorphism of topological groups
`φ : W' ≃ W` with `e ∘ φ = e'` carries `μ'` to `μ`. -/
lemma measurePreserving_equiv (hφ : ∀ x : W', e (φ x) = e' x) : MeasurePreserving φ μ' μ := by
  -- Both `μ` and the image of `μ'` are Haar measures, and both give `‖e‖ ^ 2` the integral `1`.
  have h_one : ∫ x : W, ‖e x‖ ^ 2 ∂map φ μ' = 1 := by
    calc ∫ x : W, ‖e x‖ ^ 2 ∂map φ μ'
        = ∫ x : W', ‖e (φ x)‖ ^ 2 ∂μ' := φ.isClosedEmbedding.integral_map _
      _ = ∫ x : W', ‖e' x‖ ^ 2 ∂μ' := by simp_rw [hφ]
      _ = 1 := he'.integral_norm_sq_eq_one
  have h_map : map φ μ' = μ := addHaar_eq_of_integral_eq_one he.integral_norm_sq_eq_one h_one
  exact ⟨by fun_prop, h_map⟩

variable (H H') in
/-- Let `e`, `e'` be vacua for the Haar measures `μ`, `μ'`. Change of variables along an isometric
ring map `σ` of `ℂ` (the identity or the conjugation) and an isomorphism `φ : W' ≃ W` with
`e ∘ φ = e'`: `σ (∫ f dμ) = ∫ σ ∘ f ∘ φ dμ'` for every `f`. -/
lemma map_integral_eq_integral_comp_equiv (hφ : ∀ x : W', e (φ x) = e' x) (f : W → ℂ) :
    σ (integral μ f) = ∫ x : W', σ (f (φ x)) ∂μ' := by
  -- `φ` preserves the measures, and `σ`, the identity or the conjugation, commutes with integrals.
  rw [← (measurePreserving_equiv H H' hφ).integral_comp φ.measurableEmbedding f]
  rcases ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl
  · simp
  · simp [integral_conj]

omit he in
variable (H' μ') in
omit [MeasurableSpace W] [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W]
  [LocallyCompactSpace W] [IsTopologicalAddGroup W'] [BorelSpace W'] [IsAddHaarMeasure μ'] in
/-- For an isometric ring map `σ` of `ℂ` and `φ : W' ≃ W` with `e ∘ φ = e'`, also `σ ∘ e ∘ φ = e'`,
as the vacuum `e'` of `H'` and `μ'` is real-valued. -/
lemma map_vacuum_comp_equiv (hφ : ∀ x : W', e (φ x) = e' x) (x : W') : σ (e (φ x)) = e' x := by
  rcases ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl
  · simp [hφ]
  · simp [hφ, he'.conj_apply]

/-- Change of variables along an isometric ring map `σ` of `ℂ` (the identity or the conjugation)
and an isomorphism `φ : W' ≃ W` that matches the vacua and, up to `σ`, the cocycles:
`σ (∫ f dμ) = ∫ σ ∘ f ∘ φ dμ'` for every `f`, and `σ ∘ e ∘ φ = e'`. The two parts are
`map_integral_eq_integral_comp_equiv` and `map_vacuum_comp_equiv`, which do not need `hβ`. -/
lemma map_integral_and_map_vacuum (_hβ : ∀ x y : W', σ (H.β (φ x) (φ y)) = H'.β x y)
    (hφ : ∀ x : W', e (φ x) = e' x) :
    (∀ f : W → ℂ, σ (integral μ f) = ∫ x : W', σ (f (φ x)) ∂μ') ∧
      ∀ x : W', σ (e (φ x)) = e' x :=
  ⟨map_integral_eq_integral_comp_equiv H H' hφ, map_vacuum_comp_equiv H' μ' hφ⟩

variable [SecondCountableTopology W']

/-- For a topological isomorphism `φ : W' ≃ W` matching the vacua and, up to `σ`, the
bicharacters, the continuous `σ`-semilinear map `v ↦ σ ∘ v ∘ φ` between the reproducing spaces. -/
noncomputable def transport (hβ : ∀ x y : W', σ (H.β (φ x) (φ y)) = H'.β x y)
    (hφ : ∀ x : W', e (φ x) = e' x) : Model H →SL[σ] Model H' :=
  have h_pres : MeasurePreserving φ μ' μ := measurePreserving_equiv H H' hφ
  let σL : ℂ →SL[σ] ℂ := σ.toSemilinearMap.mkContinuous 1 (by simp)
  LinearMap.mkContinuous
    { toFun v :=
        ⟨fun x ↦ σL ((v.1 ∘ φ) x), σL.integrable_comp (h_pres.integrable_comp_of_integrable v.2.1),
          -- Apply `σ` to the reproducing formula of `v` at `φ x` and substitute `φ`.
          fun x ↦ by
            simpa [σL, map_integral_and_map_vacuum hβ hφ, ← map_sub, hβ] using
              congrArg σ (v.2.2 (φ x))⟩
      map_add' := by aesop
      map_smul' := by aesop }
    1 fun v ↦ by
      -- `σ` is isometric and `φ` preserves the measure, so the `L¹` norm is kept.
      refine le_of_eq ?_
      rw [norm_eq_integral_norm, norm_eq_integral_norm, one_mul,
        ← h_pres.integral_comp φ.measurableEmbedding]
      exact integral_congr_ae (.of_forall fun _ ↦ RingHomIsometric.norm_map)

@[simp]
lemma transport_apply (hβ : ∀ x y : W', σ (H.β (φ x) (φ y)) = H'.β x y)
    (hφ : ∀ x : W', e (φ x) = e' x) (v : Model H) (x : W') :
    transport hβ hφ v x = σ (v (φ x)) := rfl

/-- Transport keeps the `L¹` norm, as `σ` is isometric and `φ` preserves the measure. -/
lemma norm_transport (hβ : ∀ x y : W', σ (H.β (φ x) (φ y)) = H'.β x y)
    (hφ : ∀ x : W', e (φ x) = e' x) (v : Model H) : ‖transport hβ hφ v‖ = ‖v‖ := by
  simp only [norm_eq_integral_norm, transport_apply, RingHomIsometric.norm_map]
  exact (measurePreserving_equiv H H' hφ).integral_comp φ.measurableEmbedding fun x ↦ ‖v x‖

end New.Heisenberg.IsVacuum

end ModelTransport

end
