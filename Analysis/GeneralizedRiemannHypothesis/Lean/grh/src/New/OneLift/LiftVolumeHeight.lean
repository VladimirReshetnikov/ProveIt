import New.OneLift.ComparisonOperator.GluingMaps
import New.OneLift.HeckeValues.TwistedValueHeights

/-!
# The cost of one lift: a height bound for Z_j(1)/Z_j(ξ^j)

The comparison operators `U_ϑ = n_Aut hk² glue_ϑ glue_ϑ*` take lifts to forms orthogonal to the
false lifts. The integral Fock columns give coordinates of the adjoint, and the conjugated
pairing bounds its norm. Thus the operators satisfy `IsComparisonOperator`. The product
`Z_j (ϑ) det (pr U_ϑ)` depends on the twist `ϑ` only through Hecke values. Eigenvalue bounds control
the denominator of `det (pr U_ϑ)` at `ι` and the conjugates of `det (pr U_1)`; this bounds the
height of `Z_j (1) / Z_j (ξ_ι ^ j)`, for m-fold twists `ξ_ι`.

Notions from other files:
* `D : Data P` fixes a CM field `E = D.E`, weights at its infinite places, a level, and the ranks:
  `m = D.m` lifts, from hermitian spaces `W_j = D.spaceW j` (`1 ≤ j ≤ m`) of rank `r = D.r` to the
  standard definite space `V_j` of rank `r + t`, where `t = D.t = 5 r`. The datum of the lift at a
  twist `ϑ` is `D.descentPair ϑ j`, and its `FormV` is the space of forms on `V_j`.
* `D.goodLift ϑ j` is the lift at the twist `ϑ` on the good forms on `W_j` (the range of the
  idempotent `D.e₀`), with values in the forms on `V_j`. `D.liftDeterminant ξ j`, written
  `Z_j (ξ ^ j)` for an m-fold twist `ξ`, is, at `ϑ = ξ ^ j`, the Gram determinant of this lift.
* `IsOrthogonalToFalseLifts O D.e₀ Z φ` says that the form `φ` is orthogonal to the false lifts: the
  forms that satisfy the conditions on a lift from `D.e₀` and lie in `Z`, here the complement of the
  lifts.
* `glue j ϑ` is the gluing map `glue_ϑ` from tuples of forms on `V°` (`FormTuples j`) to forms on
  `V_j`; `periodLift j` is `twistFactor j 1` times its adjoint after the lift, at the trivial twist.
  Here `V°` is the standard definite space with basis `D.SecondFactorIndex`.
* `heckeValueProd j ϑ` is a product of three real numbers `Exchange.lValueProd` (norms of places
  times squared moduli of partial Hecke `L`-values at integers), for the three characters of
  `exchangePair j` twisted by `ϑ` or its inverse.

## Relation to the literature

Bounding the norm of a lift by an integral form and a congruence denominator is known in the
literature for one eigenform.

Related work: Böcherer–Dummigan–Schulze-Pillot, Yoshida lifts and Selmer groups, 2012; X. Zhang,
Special L-values and Selmer groups of Siegel modular forms of genus 2, 2018; Hida, Congruences of
cusp forms and special values of their zeta functions, 1981.
-/

namespace New.Data

open Matrix NumberField Function ComplexConjugate IsAlgClosed Module Real Finset DescentPair Rows
open LinearMap Space «GL» LevelPlaces.LevelForm Selmer IsUltrametricDist
open scoped ComplexOrder

/-- Let `u : U → V` be an injective linear map of finite-dimensional complex inner product spaces,
`pr` the orthogonal projection of `V` to the range of `u`, and `T` an operator on `V`. The
determinant of `pr T` on the range of `u`, times `u.normDet ^ 2 = det (u* u)`, is `det (u* T u)`. -/
lemma normDet_sq_mul_det_compression {U V : Type}
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [Module.Finite ℂ U]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Module.Finite ℂ V]
    (T : End ℂ V) {u : U →ₗ[ℂ] V} (hu : Injective u) :
    u.normDet ^ 2 * (u.range.orthogonalProjectionOnto.toLinearMap ∘ₗ T.domRestrict u.range).det =
      (u.adjoint ∘ₗ T ∘ₗ u).det := by
  -- `u*` kills the orthogonal complement of the range, so `u* u (u⁻¹ pr T u) = u* T u`.
  let e : U ≃ₗ[ℂ] u.range := .ofInjective u hu
  let S : End ℂ u.range := u.range.orthogonalProjectionOnto.toLinearMap ∘ₗ T.domRestrict u.range
  have h_apply (z : u.range) : u (e.symm z) = z := congrArg Subtype.val (e.apply_symm_apply z)
  have h_comp : u.adjoint ∘ₗ T ∘ₗ u =
      (u.adjoint ∘ₗ u) ∘ₗ (e.symm.toLinearMap ∘ₗ S ∘ₗ e.symm.symm.toLinearMap) := by
    refine LinearMap.ext fun y ↦ ext_inner_left ℂ fun x ↦ ?_
    have h_proj : inner ℂ (u x) (u.range.starProjection (T (u y))) = inner ℂ (u x) (T (u y)) :=
      u.range.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨u x, x, rfl⟩ (T (u y))
    simpa [adjoint_inner_right, h_apply, S, e] using h_proj.symm
  rw [h_comp, det_comp, LinearMap.det_conj, ← normDet_sq, RCLike.ofReal_pow]
  rfl

/-- A determinant is the product of the eigenvalues. So if `‖f α‖ ≤ B` for every eigenvalue `α` of
`u` (`h_eigen`), then `‖f u.det‖ ≤ B ^ finrank ℂ L`, for the ring map `f : ℂ →+* K` into a normed
field. -/
lemma norm_map_det_le_pow {K L : Type} [NormedField K] [AddCommGroup L] [Module ℂ L]
    [Module.Finite ℂ L] (f : ℂ →+* K) (u : End ℂ L) {B : ℝ}
    (h_eigen : ∀ (α : ℂ) (z : L), u.HasEigenvector α z → ‖f α‖ ≤ B) :
    ‖f u.det‖ ≤ B ^ finrank ℂ L := by
  let N : ℂ →* ℝ := (normHom (α := K)).toMonoidHom.comp f.toMonoidHom
  change N u.det ≤ B ^ finrank ℂ L
  rw [End.det_eq_prod_roots_charpoly_of_splits (splits _), map_multiset_prod,
    ← u.charpoly_natDegree, ← card_roots_eq_natDegree]
  refine Multiset.prod_map_le_pow_card (fun α _ ↦ norm_nonneg (f α)) fun α hα ↦ ?_
  obtain ⟨z, hz⟩ := ((End.hasEigenvalue_iff_isRoot_charpoly u α).2
    (Polynomial.isRoot_of_mem_roots hα)).exists_hasEigenvector
  exact h_eigen α z hz

/-- Multiplying a form on the space `V` of a descent pair `O` by `c` multiplies its squared norm
`normSqAt` at an automorphism `σ` of `ℂ` by `‖σ c‖ ^ 2`. -/
lemma _root_.New.LevelPlaces.LevelForm.normSqAt_smul {E r n : Type} [Field E] [CMType E]
    [WeilData E] [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair E r n}
    (c : ℂ) (φ : O.FormV) (σ : ℂ ≃+* ℂ) :
    (c • φ).normSqAt σ = ‖σ c‖ ^ 2 * φ.normSqAt σ := by
  rw [normSqAt, normSqAt, mul_classSum]
  exact congrArg _ (funext fun g ↦ weylNormSq_comp_smul (φ g) σ c)

/-- The squared norm `φ.normSqAt σ` of a form (the weighted sum over classes of the squared norms
of the values after applying `σ`) is not negative. -/
lemma _root_.New.LevelPlaces.LevelForm.normSqAt_nonneg {E r n : Type} [Field E] [CMType E]
    [WeilData E] [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair E r n}
    (φ : O.FormV) (σ : ℂ ≃+* ℂ) :
    0 ≤ φ.normSqAt σ := by
  rw [normSqAt, classSum]
  exact finsum_nonneg fun _ ↦ smul_nonneg (by positivity) (weylNormSq_nonneg _)

/-- Let `E` be a CM field with a CM type and Weil data, and `O` a descent pair over `E`: the datum
of a lift from a hermitian space `W` with basis indexed by `r` to the standard space `V` with basis
indexed by `n`. For `φ ≠ 0` in `O.FormV`, the algebraic forms on `V` of the weight and level of `O`,
the squared norm `φ.normSqAt σ` is positive at every automorphism `σ` of `ℂ`. -/
lemma _root_.New.LevelPlaces.LevelForm.normSqAt_pos {E r n : Type} [Field E] [CMType E]
    [WeilData E] [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair E r n}
    {φ : O.FormV} (hφ : φ ≠ 0) (σ : ℂ ≃+* ℂ) :
    0 < φ.normSqAt σ := by
  obtain ⟨c, hc⟩ : ∃ c : StdClasses (levelOf O.placeAt
    (descentResidueLevel O.toLevelPlaces O.incl)),
      φ c.out ≠ 0 := by
    by_contra! h
    exact hφ (levelSpace_ext_doubleCosets Quot.out_eq h)
  exact classSum_pos (c := c) (by simp)
    (weylGramOver_posDef.re_dotProduct_pos (by simpa [funext_iff] using hc : σ ∘ φ c.out ≠ 0))

/-- A nonzero form `φ` in the space `O.FormV` of forms on `V` of a descent pair `O` over the CM
field `E` can be scaled to valuation `0` at a place `ι` (an embedding `ι.ιₚ` of `ℂ` into `ℂ_[l]`):
there is `c ≠ 0` such that `c • φ` is integral at `ι`, and `α • c • φ` is integral only if
`‖ι.ιₚ α‖ ≤ 1`. -/
lemma _root_.New.DescentPair.exists_smul_mem_integralForms_maximal {E r n : Type} [Field E]
    [CMType E] [WeilData E] [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]
    {O : DescentPair E r n} {φ : O.FormV} (hφ : φ ≠ 0) {l : ℕ} [Fact l.Prime] (ι : PadicPlace l) :
    ∃ c : ℂ, c ≠ 0 ∧ c • φ ∈ integralForms ι ∧
      ∀ α : ℂ, α • c • φ ∈ integralForms ι → ‖ι.ιₚ α‖ ≤ 1 := by
  -- Divide by a coordinate of least valuation at representatives that are integral above `l`.
  let K : Subgroup (Gf E n) := levelOf O.placeAt (descentResidueLevel O.toLevelPlaces O.incl)
  obtain ⟨s, hs_mk, hs_int⟩ := exists_reps_integralAbove (K := K) l
  obtain ⟨x₁, hx₁⟩ : ∃ x : StdClasses K × WeylIndex n O.columnCount, φ (s x.1) x.2 ≠ 0 := by
    by_contra! h
    exact hφ (levelSpace_ext_doubleCosets hs_mk fun q ↦ funext fun i ↦ h (q, i))
  have : Nonempty (StdClasses K × WeylIndex n O.columnCount) := ⟨x₁⟩
  obtain ⟨x, h_max⟩ :=
    Finite.exists_max fun y : StdClasses K × WeylIndex n O.columnCount ↦ ‖ι.ιₚ (φ (s y.1) y.2)‖
  have hx : 0 < ‖ι.ιₚ (φ (s x.1) x.2)‖ := lt_of_lt_of_le (by simpa using hx₁) (h_max x₁)
  have hx_ne : φ (s x.1) x.2 ≠ 0 := by simpa using hx
  have h_smul (c : ℂ) (ψ : O.FormV) (g : Gf E n) : (c • ψ) g = c • ψ g := rfl
  refine ⟨(φ (s x.1) x.2)⁻¹, inv_ne_zero hx_ne, fun g ↦ ?_, fun α hα ↦ ?_⟩
  · -- Write `g = γ (s q) k` with `γ` rational and `k` in the level; the gauge is that at `s q`.
    let q : StdClasses K := DoubleCoset.mk _ _ g
    let ψ : O.FormV := (φ (s x.1) x.2)⁻¹ • φ
    obtain ⟨_, ⟨γ, rfl⟩, k, hk, hg⟩ :
        ∃ γ' ∈ (stdSpace E n).Γf, ∃ k ∈ K, g = γ' * s q * k :=
      (DoubleCoset.eq ..).1 (hs_mk q)
    have h_char : ‖ι.ιₚ (O.levelChar ⟨k, hk⟩)‖ = 1 :=
      (ι.ιₚ.isOfFinOrder (LevelPlaces.isOfFinOrder_level_char _)).norm_eq_one
    have h_bound (i : WeylIndex n O.columnCount) : ‖ι.ιₚ (ψ (s q) i)‖ ≤ 1 := by
      simpa [ψ, h_smul, ← div_eq_inv_mul] using (div_le_one hx).2 (h_max (q, i))
    have h_value : ψ g =
        O.levelChar ⟨k, hk⟩ • (stdSpace E n).weightRep O.columnCount O.detExp γ (ψ (s q)) := by
      rw [hg]
      exact levelSpace_smoothFormRep_apply ψ.2 γ (s q) ⟨k, hk⟩
    calc weylGauge O.columnCount O.detExp g (ψ g)
      _ = weylGauge O.columnCount O.detExp (s q) (ψ (s q)) := by
        rw [h_value, weylGauge_smul, h_char, one_mul, hg,
          weylGauge_mul_of_mem_integralAbove _ (stdLevel_le_localLevel (levelOf_le_stdLevel hk)),
            weylGauge_embFin]
      _ ≤ 1 := (weylGauge_le_one_iff _ (hs_int q)).2 h_bound
  · simpa [h_smul, hx_ne] using (weylGauge_le_one_iff _ (hs_int x.1)).1 (hα (s x.1)) x.2

section Operator

variable {P : Parameters} {D : Data P}

/-- A comparison operator for the lift from `W_j`: a family of operators `U_ϑ` on the forms on `V_j`
through which the lifts `Θ_ϑ = D.goodLift ϑ j` at the twists `ϑ` are compared with the untwisted
one. In the bound, `f = D.f` is the number of infinite places, `m = D.m` the number of lifts in the
chain and `b = D.b`, with `log b = D.logB`, the weight at the infinite places in `D.bPlaces`. -/
structure IsComparisonOperator (j : D.LiftIndex)
    (U : ∀ ϑ : D.Twist, End ℂ (D.descentPair ϑ j).FormV) : Prop where
  /-- The ratio of the twisted to the untwisted Hecke values of the lift is not `0`. -/
  ratio_ne_zero (ϑ : D.Twist) : heckeValueProd j ϑ / heckeValueProd j 1 ≠ 0
  /-- `⟨Θ_ϑ y', U_ϑ Θ_ϑ y⟩` is this ratio times `⟨y', U° y⟩`, for a positive definite operator `U°`
  on the good forms that does not depend on `ϑ`. The shape of the ratio is given by
  `exists_heckeValueProd_eq_mul_prod_ratio`. -/
  exists_inner_eq : ∃ U₀ : End ℂ (D.goodForms (D.spaceW j)),
    (∀ y : D.goodForms (D.spaceW j), y ≠ 0 → 0 < inner ℂ y (U₀ y)) ∧
    ∀ (ϑ : D.Twist) (y' y : D.goodForms (D.spaceW j)),
      inner ℂ (D.goodLift ϑ j y') (U ϑ (D.goodLift ϑ j y)) =
        heckeValueProd j ϑ / heckeValueProd j 1 * inner ℂ y' (U₀ y)
  /-- `U_ϑ` takes lifts to forms that are orthogonal to the false lifts
  (`IsOrthogonalToFalseLifts`). -/
  isOrthogonalToFalseLifts (ϑ : D.Twist) (z : (D.goodLift ϑ j).range) :
    IsOrthogonalToFalseLifts (D.descentPair ϑ j) D.e₀ (D.goodLift ϑ j).rangeᗮ (U ϑ z)
  /-- `U_ϑ` keeps integrality above every prime that does not divide `ϑ.normQ`, the product
  of the norms of the places in the set `Q` of `ϑ`. -/
  mem_integralForms (ϑ : D.Twist) (l : ℕ) [Fact l.Prime] (ι : PadicPlace l)
    (hl : l.Coprime ϑ.normQ) : ∀ φ ∈ integralForms ι, U ϑ φ ∈ integralForms ι
  /-- `U_1` multiplies norms at every `σ` by at most `exp (3 f m b log² b)`. -/
  normSqAt_le (φ : (D.descentPair (1 : D.Twist) j).FormV) (σ : ℂ ≃+* ℂ) :
    (U 1 φ).normSqAt σ ≤ exp (3 * (D.f * D.m * D.b * D.logB ^ 2)) ^ 2 * φ.normSqAt σ

/-- The operator `U_ϑ = n_Aut hk² glue_ϑ glue_ϑ*` on the forms on `V_j`. Here `glue_ϑ = glue j ϑ`
is the linear map that builds a form on `V_j` from a tuple of forms on `V°`,
`hk = hookNumberMinus j` is the hook number of the diagram `μ⁻` (the weight of the forms on `V°`),
and `n_Aut = D.chosenGroupOrder` is a multiple of the orders of all stabilisers. -/
noncomputable def comparisonOp (j : D.LiftIndex) (ϑ : D.Twist) : End ℂ (D.descentPair ϑ j).FormV :=
  (D.chosenGroupOrder * hookNumberMinus j ^ 2 : ℂ) •
    glue j ϑ ∘ₗ (glue j ϑ).adjoint

/-- The ratio of the twisted to the untwisted product of Hecke values (`heckeValueProd`) is
`|c′_1|² / |c′_ϑ|²`, where `c′_ϑ = twistFactor j ϑ` is the nonzero scalar that normalises the
series of the gluing at the twist `ϑ`. -/
lemma heckeValueProd_div_eq (j : D.LiftIndex) (ϑ : D.Twist) :
    heckeValueProd j ϑ / heckeValueProd j 1 =
      ‖Rows.twistFactor j 1‖ ^ 2 / ‖Rows.twistFactor j ϑ‖ ^ 2 := by
  obtain ⟨C, hC⟩ : ∃ C : ℂ, ∀ ϑ : D.Twist,
      (‖Rows.twistFactor j ϑ‖ : ℂ) ^ 2 = C / heckeValueProd j ϑ := exists_norm_twistFactor_sq_eq j
  have hC_ne : C ≠ 0 := fun h ↦ by simpa [h, twistFactor_ne_zero] using hC 1
  rw [hC, hC, div_div_div_cancel_left' _ _ hC_ne]

/-- The adjoint of the gluing map `glue j ϑ` takes the lift of `y` at the twist `ϑ` to
`c′_ϑ⁻¹ Θ° y`, where `c′_ϑ = twistFactor j ϑ` and `Θ° = periodLift j`. -/
lemma adjoint_glue_goodLift (j : D.LiftIndex) (ϑ : D.Twist) (y : D.goodForms (D.spaceW j)) :
    (glue j ϑ).adjoint (D.goodLift ϑ j y) = (Rows.twistFactor j ϑ)⁻¹ • periodLift j y := by
  rw [eq_inv_smul_iff₀ (twistFactor_ne_zero j ϑ)]
  exact LinearMap.congr_fun (twistFactor_smul_adjoint_glue_comp j ϑ) y

end Operator

/-- Let `D` be the data of the chain of lifts, `1 ≤ j ≤ D.m`, `ϑ` a twist, and `y'`, `y` good forms
on the hermitian space `W_j = D.spaceW j`. Let `Θ_ϑ = D.goodLift ϑ j` be the theta lift to forms on
the definite space `V_j`, and `glue_ϑ = glue j ϑ` the linear map that builds a form on `V_j` from a
tuple of forms on the smaller definite space `V°`, with adjoint `glue_ϑ*`. For
`U_ϑ = comparisonOp j ϑ = n_Aut hk² glue_ϑ glue_ϑ*` we have `⟨Θ_ϑ y', U_ϑ Θ_ϑ y⟩ = n_Aut hk²
|c′_ϑ|⁻² ⟨Θ° y', Θ° y⟩`. Here `n_Aut = D.chosenGroupOrder` is a multiple of the orders of all
stabilisers, `hk = hookNumberMinus j` is the hook number of the weight of the forms on `V°`, and
`c′_ϑ = twistFactor j ϑ` is the nonzero scalar for which `c′_ϑ glue_ϑ* Θ_ϑ` does not depend on `ϑ`;
this common map is `Θ° = periodLift j`. -/
lemma inner_goodLift_comparisonOp {P : Parameters} {D : Data P} (j : D.LiftIndex) (ϑ : D.Twist)
    (y' y : D.goodForms (D.spaceW j)) :
    inner ℂ (D.goodLift ϑ j y') (comparisonOp j ϑ (D.goodLift ϑ j y)) =
      D.chosenGroupOrder * hookNumberMinus j ^ 2 / ‖Rows.twistFactor j ϑ‖ ^ 2 *
        inner ℂ (periodLift j y') (periodLift j y) := by
  calc
    _ = D.chosenGroupOrder * hookNumberMinus j ^ 2 *
        inner ℂ ((glue j ϑ).adjoint (D.goodLift ϑ j y'))
          ((glue j ϑ).adjoint (D.goodLift ϑ j y)) := by
      simp only [comparisonOp, LinearMap.smul_apply, inner_smul_right, LinearMap.comp_apply,
        adjoint_inner_left]
    _ = _ := by
      rw [adjoint_glue_goodLift, adjoint_glue_goodLift, inner_smul_left,
        inner_smul_right, ← Complex.conj_mul', map_inv₀]
      ring

/-- Let `D` be the data of the chain of lifts, `1 ≤ j ≤ D.m` and `ϑ` a twist. Let `z` be a lift: a
form on `V_j` in the range of the theta lift `D.goodLift ϑ j` of the good forms on `W_j`;
`D.descentPair ϑ j` is the datum of this lift. Then the image of `z` under `comparisonOp j ϑ`, a
positive multiple of the gluing map `glue j ϑ` after its adjoint, is orthogonal to the false
lifts. -/
lemma isOrthogonalToFalseLifts_comparisonOp {P : Parameters} {D : Data P} {j : D.LiftIndex}
    {ϑ : D.Twist} (z : (D.goodLift ϑ j).range) :
    IsOrthogonalToFalseLifts (D.descentPair ϑ j) D.e₀ (D.goodLift ϑ j).rangeᗮ
      (comparisonOp j ϑ z) := by
  obtain ⟨y, hy⟩ := LinearMap.mem_range.1 z.2
  have h_op : comparisonOp j ϑ z = ((D.chosenGroupOrder : ℂ) * hookNumberMinus j ^ 2 *
      (Rows.twistFactor j ϑ)⁻¹) • glue j ϑ (periodLift j y) := by
    rw [← hy, comparisonOp, LinearMap.smul_apply, LinearMap.comp_apply, adjoint_glue_goodLift,
      map_smul, smul_smul]
  intro w hw hS
  rw [h_op]
  exact Submodule.smul_mem _ _ (isOrthogonalToFalseLifts_glue_periodLift j ϑ y w hw hS)

variable {P : Parameters} {D : Data P}

section Gluing

/-- The comparison operator preserves integrality above primes prime to the twist conductor.
Integral Fock columns test the coordinates of the scaled adjoint in the translated lattice. -/
lemma comparisonOp_mem_integralForms {j : D.LiftIndex} {ϑ : D.Twist} {l : ℕ} [Fact l.Prime]
    (ι : PadicPlace l) (hl : l.Coprime ϑ.normQ) {φ : (D.descentPair ϑ j).FormV}
    (hφ : φ ∈ integralForms ι) :
    comparisonOp j ϑ φ ∈ integralForms ι := by
  classical
  let B := ChoiceIndex j × D.SecondFactorClasses
  let κ := (untwistedDescentPair j).colsMinus
  let I := WeylIndex D.SecondFactorIndex κ
  let W : Type := I → ℂ
  let K := U (stdSpace D.E D.SecondFactorIndex).J
  have h_exists (c : D.SecondFactorClasses) : ∃ γ : K,
      (stdSpace D.E D.SecondFactorIndex).embFin γ * c.out ∈ integralAbove D.SecondFactorIndex l :=
    (exists_mul_mem_integralAbove l c.out 1).imp fun _ ↦ And.left
  choose δ hδ using h_exists
  let ρ : Representation ℂ K W := (stdSpace D.E D.SecondFactorIndex).weightRep κ 0
  let u (γ : K) : W →ₗ[ℂ] W :=
    { toFun := fun x ↦ star (ρ γ (star x))
      map_add' x y := by rw [star_add, map_add, star_add]
      map_smul' := by simp }
  have h_inv (γ : K) (x : W) : u γ⁻¹ (u γ x) = x := by simp [u]
  have h_unitary (γ : K) (x y : W) : gramForm (u γ⁻¹ x) y = gramForm x (u γ y) := by
    have h : gramForm (u γ⁻¹ x) (u γ⁻¹ (u γ y)) =
        gramForm (star (star x)) (star (star (u γ y))) :=
      gramForm_map_weightRep (e := 0) conj γ⁻¹ (star x) (star (u γ y))
    rwa [h_inv, star_star, star_star] at h
  have h_coords (ι' : PadicPlace l) (w : FormTuples j) :
      IsIntegralFormTuple ι' w ↔ ∀ (b : B) (k : I), ‖ι'.ιₚ (u (δ b.2) (w b) k)‖ ≤ 1 := by
    unfold IsIntegralFormTuple
    refine forall_congr' fun b ↦ ?_
    rw [← weylGauge_embFin (ι := ⟨ι'.ιₚ.comp conj⟩) (g := b.2.out) (δ b.2),
      weylGauge_le_one_iff (ι := ⟨ι'.ιₚ.comp conj⟩) _ (hδ b.2)]
    rfl
  -- Translating to an integral representative makes the gauge a coordinate bound. The k-th
  -- Fock column gives h times its coordinate. A second factor of h gives the comparison scale.
  let H (k : I) : W := fun i ↦ (fockPairing ℤ
    (nablaBasis ℤ (fun _ : NumberField.InfinitePlace D.E ↦ D.SecondFactorIndex) κ i)
    (nablaBasis ℤ (fun _ : NumberField.InfinitePlace D.E ↦ D.SecondFactorIndex) κ k) : ℂ)
  let e (b : B) (k : I) : FormTuples j :=
    .toLp 2 (Pi.single b (u (δ b.2)⁻¹ ((hookNumberMinus j : ℂ) • H k)))
  have h_e (ι' : PadicPlace l) (b : B) (k : I) : IsIntegralFormTuple ι' (e b k) := by
    apply (h_coords ι' (e b k)).2
    intro b' k'
    by_cases hb : b' = b
    · subst b'
      have h := h_inv ((δ b.2)⁻¹) ((hookNumberMinus j : ℂ) • H k)
      simp only [inv_inv] at h
      simp only [e, Pi.single_eq_same, h]
      change ‖ι'.ιₚ ((hookNumberMinus j : ℂ) * ((fockPairing ℤ _ _ : ℤ) : ℂ))‖ ≤ 1
      rw [← Int.cast_mul, map_intCast]
      apply norm_intCast_le_one
    · simp only [e, Pi.single_eq_of_ne hb, map_zero]
      change ‖ι'.ιₚ 0‖ ≤ 1
      simp
  let z := (glue j ϑ).adjoint φ
  let s : ℂ := D.chosenGroupOrder * hookNumberMinus j ^ 2
  have h_scaled : IsIntegralFormTuple ι (s • z) := by
    apply (h_coords ι (s • z)).2
    intro b k
    have h_test := (glue j ϑ (e b k)).norm_nsmul_inner_le_one φ ι
      (D.card_classAut_dvd_chosenGroupOrder
        (card_rowIndex_sum_fin_le_two_mul_n D) levelOf_le_stdLevel)
      (glue_mem_integralForms j ϑ ⟨ι.ιₚ.comp conj⟩ hl (h_e _ b k)) hφ
    have h_inner (x y : SecondFactorFormValues j) : inner ℂ x y = gramForm x y := dotProduct_comm ..
    have h_pair : inner ℂ (e b k) z = gramForm
        (u (δ b.2)⁻¹ ((hookNumberMinus j : ℂ) • H k)) (z b) := by
      rw [← h_inner, PiLp.inner_apply, Fintype.sum_eq_single b fun b' hb ↦ by simp [e, hb]]
      simp [e]
    rw [← adjoint_inner_right, show (glue j ϑ).adjoint φ = z from rfl, h_pair,
      h_unitary] at h_test
    change ‖ι.ιₚ (u (δ b.2) (s • z b) k)‖ ≤ 1
    rw [map_smul]
    change ‖ι.ιₚ (s * u (δ b.2) (z b) k)‖ ≤ 1
    have h_column (v : W) : gramForm (H k) v = (hookNumberMinus j : ℂ) * v k :=
      gramForm_fockColumn (κ := κ) v k
    simpa [s, h_column, nsmul_eq_mul, pow_two, mul_assoc] using h_test
  rw [comparisonOp, LinearMap.smul_apply, LinearMap.comp_apply, ← map_smul]
  exact glue_mem_integralForms j ϑ ι hl h_scaled

/-- An explicit dual test for the gluing adjoint at an arbitrary complex field automorphism. -/
private lemma formTupleNormSq_glue_adjoint_le (j : D.LiftIndex)
    (φ : (D.descentPair (1 : D.Twist) j).FormV) (σ : ℂ ≃+* ℂ) :
    formTupleNormSq σ ((glue j 1).adjoint φ) ≤
      exp (2 * (D.f * D.m * D.b * D.logB ^ 2)) * φ.normSqAt σ := by
  let A : ℝ := D.f * D.m * D.b * D.logB ^ 2
  let z := (glue j (1 : D.Twist)).adjoint φ
  let τ : ℂ ≃+* ℂ := (starRingAut.trans σ).trans starRingAut
  -- The first variable of the conjugated pairing transforms by τ. Choose v so that its
  -- τ-coordinates agree with the σ-coordinates of the adjoint.
  let v : FormTuples j := .toLp 2 fun b k ↦ τ.symm (σ (z b k))
  have h_v (b : ChoiceIndex j × D.SecondFactorClasses) : τ ∘ v b = σ ∘ z b := by
    ext k
    simp [v]
  have h_inner (x y : SecondFactorFormValues j) : inner ℂ x y = gramForm x y := dotProduct_comm ..
  have h_pair : σ (inner ℂ v z) = (formTupleNormSq σ z : ℂ) := by
    rw [PiLp.inner_apply, formTupleNormSq, map_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    calc σ (inner ℂ (v b) (z b))
      _ = gramForm (τ ∘ v b) (σ ∘ z b) := by
        rw [h_inner, map_gramForm]
      _ = _ := by rw [h_v, gramForm_apply, ← coe_weylNormSq]
  set S : ℝ := formTupleNormSq σ z with hS
  have h_v_norm : formTupleNormSq τ v = S := by simp only [hS, formTupleNormSq, h_v]
  have h_nonneg : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ weylNormSq_nonneg _
  have h_φ : 0 ≤ φ.normSqAt σ := φ.normSqAt_nonneg σ
  change S ≤ exp (2 * A) * φ.normSqAt σ
  by_cases hzero : S = 0
  · exact hzero.trans_le (mul_nonneg (exp_pos _).le h_φ)
  have h_bound : S ≤ √(φ.normSqAt σ) * √(exp (2 * A) * S) := by
    calc S = ‖σ (inner ℂ v z)‖ := by rw [h_pair, Complex.norm_real, Real.norm_of_nonneg h_nonneg]
      _ = ‖σ (inner ℂ (glue j 1 v) φ)‖ := by rw [adjoint_inner_right]
      _ ≤ _ := by grw [norm_map_inner_le, normSqAt_glue_le, h_v_norm]
  have h_sq : S ^ 2 ≤ (√(φ.normSqAt σ) * √(exp (2 * A) * S)) ^ 2 :=
    pow_le_pow_left₀ h_nonneg h_bound 2
  rw [mul_pow, sq_sqrt h_φ, sq_sqrt (by positivity)] at h_sq
  exact le_of_mul_le_mul_right (by nlinarith only [h_sq]) (lt_of_le_of_ne h_nonneg (Ne.symm hzero))

/-- The comparison operator has squared norm at most `exp (6 f m b log² b)`. -/
lemma normSqAt_comparisonOp_le (j : D.LiftIndex) (φ : (D.descentPair (1 : D.Twist) j).FormV)
    (σ : ℂ ≃+* ℂ) :
    (comparisonOp j 1 φ).normSqAt σ ≤
      exp (3 * (D.f * D.m * D.b * D.logB ^ 2)) ^ 2 * φ.normSqAt σ := by
  let A : ℝ := D.f * D.m * D.b * D.logB ^ 2
  let z := (glue j (1 : D.Twist)).adjoint φ
  let s : ℝ := (D.chosenGroupOrder : ℝ) * (hookNumberMinus j : ℝ) ^ 2
  have h_hook : 0 ≤ (hookNumberMinus j : ℝ) := (Int.cast_pos.2 hookNumber_pos).le
  have h_scalar : ‖σ (D.chosenGroupOrder * hookNumberMinus j ^ 2 : ℂ)‖ = s := by
    simp [s, norm_pow, abs_of_nonneg h_hook]
  rw [comparisonOp, LinearMap.smul_apply, LinearMap.comp_apply, normSqAt_smul, h_scalar]
  have h_s : s ≤ exp A := by
    calc s ≤ exp (D.x ^ 32) * exp (D.x ^ 999) ^ 2 := by
          dsimp [s]
          gcongr
          · exact le_exp_of_log_le D.log_chosenGroupOrder_le
          · exact hookNumberMinus_le j
      _ = exp (D.x ^ 32 + 2 * D.x ^ 999) := by simp only [two_mul, exp_add, sq]
      _ ≤ exp A := exp_le_exp.2 (by dsimp [A]; exact D.le_of_hasLogBound)
  have h_adj := formTupleNormSq_glue_adjoint_le j φ σ
  have h_φ := φ.normSqAt_nonneg σ
  calc s ^ 2 * (glue j 1 z).normSqAt σ
    _ ≤ exp A ^ 2 * (exp (2 * A) * (exp (2 * A) * φ.normSqAt σ)) := by
      grw [normSqAt_glue_le, h_adj, h_s]
    _ = exp (3 * A) ^ 2 * φ.normSqAt σ := by
      simp only [← exp_nat_mul, ← mul_assoc, ← exp_add]
      ring_nf

/-- The operators `U_ϑ = comparisonOp j ϑ = n_Aut hk² glue_ϑ glue_ϑ*` on the forms on `V_j`, one for
each twist `ϑ`, satisfy `IsComparisonOperator`. Here `glue_ϑ = glue j ϑ` builds a form on `V_j` from
a tuple of forms on `V°`, `n_Aut = D.chosenGroupOrder` and `hk = hookNumberMinus j`. That is, for
the theta lift `Θ_ϑ = D.goodLift ϑ j` and the nonzero ratio
`ρ_ϑ = heckeValueProd j ϑ / heckeValueProd j 1` of Hecke values,
`⟨Θ_ϑ y', U_ϑ Θ_ϑ y⟩ = ρ_ϑ ⟨y', U° y⟩` with `U°` positive definite and independent of `ϑ`. Also,
`U_ϑ` takes lifts to forms orthogonal to the false lifts, which are the forms orthogonal to the
lifts with the same idempotent and Hecke conditions at a split place. `U_ϑ` keeps integrality above
the primes that do not divide `ϑ.normQ`, and `U_1` multiplies norms by at most
`exp (3 f m b log² b)`, with `f = D.f`, `m = D.m` and `b = D.b`. -/
theorem isComparisonOperator_comparisonOp (j : D.LiftIndex) :
    IsComparisonOperator j (comparisonOp j) where
  ratio_ne_zero ϑ := by simp [heckeValueProd_div_eq, twistFactor_ne_zero]
  exists_inner_eq := by
    -- Take `U° = n_Aut hk² |c′_1|⁻² Θ°* Θ°`; it is positive definite, as `Θ°` is injective.
    let scale : ℝ := D.chosenGroupOrder * hookNumberMinus j ^ 2 / ‖Rows.twistFactor j 1‖ ^ 2
    have h_scale_pos : 0 < scale := div_pos (mul_pos (Nat.cast_pos.2 (NeZero.pos _))
      (sq_pos_of_pos (Int.cast_pos.2 hookNumber_pos))) (by simp [twistFactor_ne_zero])
    refine ⟨(scale : ℂ) • (periodLift j).adjoint ∘ₗ periodLift j, fun y hy ↦ ?_, fun ϑ y' y ↦ ?_⟩
    · have h_norm : 0 < ‖periodLift j y‖ :=
        norm_pos_iff.2 ((map_ne_zero_iff _ (periodLift_injective j)).2 hy)
      rw [LinearMap.smul_apply, inner_smul_right, LinearMap.comp_apply, adjoint_inner_right,
        inner_self_eq_norm_sq_to_K]
      exact mul_pos (Complex.zero_lt_real.2 h_scale_pos) (pow_pos (Complex.zero_lt_real.2 h_norm) 2)
    · rw [inner_goodLift_comparisonOp, heckeValueProd_div_eq, LinearMap.smul_apply,
        inner_smul_right, LinearMap.comp_apply, adjoint_inner_right]
      have h_ne : (‖Rows.twistFactor j 1‖ : ℂ) ≠ 0 := by simp [twistFactor_ne_zero]
      push_cast [scale]
      field_simp
  isOrthogonalToFalseLifts _ := isOrthogonalToFalseLifts_comparisonOp
  mem_integralForms ϑ l _ ι hl φ hφ := comparisonOp_mem_integralForms ι hl hφ
  normSqAt_le := normSqAt_comparisonOp_le j

end Gluing

/-- The lift `D.goodLift ϑ j` is injective, so the lifts have the dimension of the good forms on
`W_j`. -/
lemma finrank_range_goodLift (j : D.LiftIndex) (ϑ : D.Twist) :
    finrank ℂ (D.goodLift ϑ j).range = finrank ℂ (D.goodForms (D.spaceW j)) :=
  finrank_range_of_inj (by simp [singleLift_injective])

/-- For a split place `w` off the level, the lifts lie in the image of the idempotent `e₀ = D.e₀`
that cuts out the good forms and are killed by the Hecke polynomial `heckePolyOnForms` at
`liftHeckeRoot w`, a power of the norm of `w` times a power of the value of the Weil data's
character at `w`. -/
lemma range_goodLift_le_range_inf_ker {j : D.LiftIndex} {ϑ : D.Twist} {w : FinPlace D.E}
    (hw : star w ≠ w) (hS : w ∉ (D.descentPair ϑ j).places.conjClosure) :
    (D.goodLift ϑ j).range ≤ ((D.descentPair ϑ j).groupAlgAction D.e₀).range ⊓
      ((D.descentPair ϑ j).heckePolyOnForms hw hS ((D.descentPair ϑ j).liftHeckeRoot w)).ker := by
  refine D.range_goodLift_le fun eigensystem y hy c hc h_mem ↦ ?_
  exact ⟨D.range_tupleIdem_le hc h_mem, D.heckePolyOnForms_liftHeckeRoot_singleLift_eq_zero ϑ hw hS
    y⟩

/-- Let `y` be a form on `V_j` that is orthogonal to the false lifts. Then the orthogonal projection
of `y` to the lifts has norm (`normSqAt`) at most that of `y`, at every automorphism `σ` of `ℂ`. -/
lemma normSqAt_starProjection_range_goodLift_le {j : D.LiftIndex} {ϑ : D.Twist}
    {y : (D.descentPair ϑ j).FormV}
    (hy : (D.descentPair ϑ j).IsOrthogonalToFalseLifts D.e₀ (D.goodLift ϑ j).rangeᗮ y)
    (σ : ℂ ≃+* ℂ) :
    normSqAt ((D.goodLift ϑ j).range.starProjection y) σ ≤ normSqAt y σ := by
  obtain ⟨w, hw, hw_off⟩ := (frequently_isSplit_notMem_places (D.descentPair ϑ j)).exists
  exact normSqAt_starProjection_le _ hw hw_off D.isCentralProj_e₀
    (range_goodLift_le_range_inf_ker hw hw_off) hy σ

/-- For operators `U_ϑ` on the forms on `V_j`, the operator `pr U_ϑ` on the lifts (the range of
`D.goodLift ϑ j`), with `pr` the orthogonal projection to them. -/
noncomputable def liftCompression {j : D.LiftIndex}
    (U : ∀ ϑ : D.Twist, End ℂ (D.descentPair ϑ j).FormV) (ϑ : D.Twist) :
    End ℂ (D.goodLift ϑ j).range :=
  (D.goodLift ϑ j).range.orthogonalProjectionOnto.toLinearMap ∘ₗ
    (U ϑ).domRestrict (D.goodLift ϑ j).range

section Comparison

/-- Let `Θ_ϑ = D.goodLift ϑ j` be the theta lift at the twist `ϑ` to the forms on `V_j`. Its source
is the good forms (the image of the idempotent `D.e₀`, a space of dimension `d`) on the hermitian
space `W_j = D.spaceW j`. Let `ρ_ϑ` be the ratio of the values at `ϑ` and at `1` of
`heckeValueProd j`. Let `U` be a comparison operator, so that `⟨Θ_ϑ y', U_ϑ Θ_ϑ y⟩ = ρ_ϑ ⟨y', U° y⟩`
with `U°` positive definite. Then the Gram determinant `Θ_ϑ.normDet ^ 2 = det (Θ_ϑ* Θ_ϑ)`, times the
determinant of `pr U_ϑ = liftCompression U ϑ`, is `C ρ_ϑ ^ d` for a constant `C ≠ 0` that does not
depend on `ϑ`. -/
lemma IsComparisonOperator.exists_normDet_sq_mul_det_eq {j : D.LiftIndex}
    {U : ∀ ϑ : D.Twist, End ℂ (D.descentPair ϑ j).FormV} (hU : IsComparisonOperator j U) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ ϑ : D.Twist,
      (D.goodLift ϑ j).normDet ^ 2 * (liftCompression U ϑ).det =
        C * (heckeValueProd j ϑ / heckeValueProd j 1) ^ finrank ℂ (D.goodForms (D.spaceW j)) := by
  -- `U₀` is positive definite and gives the inner products `⟨Θ_ϑ y', U_ϑ Θ_ϑ y⟩` up to the ratio.
  obtain ⟨U₀, h_pos, h_inner⟩ := hU.exists_inner_eq
  have h_ker : ker U₀ = ⊥ :=
    ker_eq_bot'.2 fun y hy ↦ by_contra fun hy_ne ↦ by simpa [hy] using h_pos y hy_ne
  have h_det : U₀.det ≠ 0 := fun h ↦ (bot_lt_ker_of_det_eq_zero h).ne' h_ker
  refine ⟨U₀.det, h_det, fun ϑ ↦ ?_⟩
  have h_comp : (D.goodLift ϑ j).adjoint ∘ₗ U ϑ ∘ₗ D.goodLift ϑ j =
      (heckeValueProd j ϑ / heckeValueProd j 1) • U₀ := by
    refine LinearMap.ext fun y ↦ ext_inner_left ℂ fun y' ↦ ?_
    rw [LinearMap.smul_apply, inner_smul_right, ← h_inner]
    exact (D.goodLift ϑ j).adjoint_inner_right y' (U ϑ (D.goodLift ϑ j y))
  rw [liftCompression, normDet_sq_mul_det_compression _ (by simp [singleLift_injective]), h_comp,
    LinearMap.det_smul, mul_comm]

/-- Let `ϑ` be a twist, ramified at a finite set `Q` of places with product of norms `ϑ.normQ`, and
`ι` an isomorphism of `ℂ` with `ℚ̄_l` for a prime `l` that does not divide `ϑ.normQ`. Let `U` be a
comparison operator: `U_ϑ` takes lifts to forms orthogonal to the false lifts and keeps integrality
at `ι`. Let `ClearsProjection` hold with `β`: for some operator `Λ` on the lifts with
`|ι (det Λ)| ≥ exp (-d r β)` and the orthogonal projection `pr` to the lifts, `Λ (pr y)` is integral
at `ι` for all integral `y` orthogonal to the false lifts. Then `det (pr U_ϑ)`, with
`pr U_ϑ = liftCompression U ϑ`, has norm at most `exp (d r β)` at `ι`, with `d` the dimension of the
good forms on `W_j = D.spaceW j` and `r = D.r` the rank of `W_j`. -/
lemma IsComparisonOperator.norm_padic_det_liftCompression_le {j : D.LiftIndex}
    {U : ∀ ϑ : D.Twist, End ℂ (D.descentPair ϑ j).FormV} (hU : IsComparisonOperator j U)
    (ϑ : D.Twist) (ι : PrimePadicIso) (hι : (ι.prime : ℕ).Coprime ϑ.normQ) {β : ℝ}
    (h_clears : D.ClearsProjection ι.iso ϑ j β) :
    ‖ι.iso (liftCompression U ϑ).det‖ ≤
      exp (finrank ℂ (D.goodForms (D.spaceW j)) * (D.r * β)) := by
  -- If `Λ` clears the denominator of the projection, then `Λ pr U_ϑ` keeps the integral lifts, so
  -- its eigenvalues are integral.
  obtain ⟨Λ, h_det, hΛ_integral⟩ := h_clears
  have h_one : ‖ι.iso (Λ * liftCompression U ϑ).det‖ ≤ 1 ^ finrank ℂ (D.goodLift ϑ j).range := by
    refine norm_map_det_le_pow ι.iso.toRingHom _ fun α z hz ↦ ?_
    let ιp : PadicPlace ι.prime := ⟨(algebraMap _ ℂ_[ι.prime]).comp ι.iso.toRingHom⟩
    obtain ⟨c, -, h_int, h_least⟩ : ∃ c : ℂ, c ≠ 0 ∧ c • z.1 ∈ integralForms ιp ∧
        ∀ μ : ℂ, μ • c • z.1 ∈ integralForms ιp → ‖ιp.ιₚ μ‖ ≤ 1 :=
      DescentPair.exists_smul_mem_integralForms_maximal (Subtype.coe_ne_coe.2 hz.2) ιp
    have h_image : (Λ ((D.goodLift ϑ j).range.orthogonalProjectionOnto (U ϑ (c • z.1))) :
        (D.descentPair ϑ j).FormV) ∈ integralForms ιp :=
      -- `U_ϑ (c • z)` is integral and orthogonal to the false lifts.
      hΛ_integral _ (hU.mem_integralForms ϑ ι.prime ιp hι _ h_int)
        (hU.isOrthogonalToFalseLifts ϑ (c • z))
    have h_apply : Λ ((D.goodLift ϑ j).range.orthogonalProjectionOnto (U ϑ z.1)) = α • z :=
      hz.apply_eq_smul
    have h_eigen : (Λ ((D.goodLift ϑ j).range.orthogonalProjectionOnto (U ϑ (c • z.1))) :
        (D.descentPair ϑ j).FormV) = α • c • z.1 := by
      rw [map_smul, map_smul, map_smul, h_apply, smul_comm α c]
      rfl
    rw [h_eigen] at h_image
    -- The place `ιp` is `ι` followed by the isometric inclusion of `ℚ̄_l` into `ℂ_l`.
    have h_norm : ‖algebraMap (PadicAlgCl ι.prime) ℂ_[ι.prime] (ι.iso α)‖ ≤ 1 := h_least α h_image
    simpa using h_norm
  rw [map_mul, map_mul, norm_mul, one_pow] at h_one
  rw [finrank_range_goodLift] at h_det
  set d : ℕ := finrank ℂ (D.goodForms (D.spaceW j))
  have h_mul : exp (-(d * (D.r * β))) * ‖ι.iso (liftCompression U ϑ).det‖ ≤ 1 :=
    (mul_le_mul_of_nonneg_right h_det (norm_nonneg _)).trans h_one
  rwa [Real.exp_neg, inv_mul_le_iff₀ (exp_pos _), mul_one] at h_mul

/-- Let `U` be a comparison operator on the forms on `V_j`, the target of the `j`-th lift, and
`pr U_1 = liftCompression U 1` its compression to the range of the untwisted lift. The image of
`det (pr U_1)` under every ring automorphism `σ` of `ℂ` has modulus at most
`exp (3 d f m b log² b)`. Here `d` is the dimension of the good forms on `W_j = D.spaceW j`,
`f = D.f` the number of infinite places, `m = D.m` the number of lifts in the chain and `b = D.b`,
with `log b = D.logB`, the weight at the infinite places in `D.bPlaces`. -/
lemma IsComparisonOperator.norm_map_det_liftCompression_le {j : D.LiftIndex}
    {U : ∀ ϑ : D.Twist, End ℂ (D.descentPair ϑ j).FormV} (hU : IsComparisonOperator j U)
    (σ : ℂ ≃+* ℂ) :
    ‖σ (liftCompression U 1).det‖ ≤
      exp (finrank ℂ (D.goodForms (D.spaceW j)) * (3 * (D.f * D.m * D.b * D.logB ^ 2))) := by
  rw [exp_nat_mul, ← finrank_range_goodLift j 1]
  refine norm_map_det_le_pow σ.toRingHom _ fun α z hz ↦ ?_
  have hz_pos : 0 < normSqAt z.1 σ := normSqAt_pos (Subtype.coe_ne_coe.2 hz.2) σ
  -- `U_1 z` is orthogonal to the false lifts, so projecting it does not raise its norm at `σ`.
  have h_proj : normSqAt ((D.goodLift (1 : D.Twist) j).range.starProjection (U 1 z)) σ ≤
      normSqAt (U 1 z) σ :=
    normSqAt_starProjection_range_goodLift_le (hU.isOrthogonalToFalseLifts 1 z) σ
  have h_eigen : (D.goodLift (1 : D.Twist) j).range.starProjection (U 1 z) = α • z.1 :=
    congrArg Subtype.val hz.apply_eq_smul
  rw [h_eigen, normSqAt_smul] at h_proj
  have h_sq : ‖σ α‖ ^ 2 ≤ exp (3 * (D.f * D.m * D.b * D.logB ^ 2)) ^ 2 :=
    le_of_mul_le_mul_right (h_proj.trans (hU.normSqAt_le z σ)) hz_pos
  exact le_of_sq_le_sq h_sq (exp_pos _).le

end Comparison

/-- The `j`-th power of the trivial `m`-fold twist, formed as a tame character (`TameChar.pow`), is
the trivial tame character `TameChar.one`. -/
lemma mFoldTwist_one_pow (j : ℕ) : (1 : D.MFoldTwist).pow j = (TameChar.one : D.TameChar) := by
  rw [TameChar.pow]
  congr 1 <;> exact one_pow j

/-- The cost of one lift: for a family of twists `ξ_ι = θ ι` as in `IsRegularFamily`, the ratio
`Z_j (1) / Z_j (ξ_ι ^ j)` has height at most `d k (log b · denominatorBudget - directionAmount)`.
Here `d = D.targetDim` is the dimension of the good forms, `k = D.k = D.r + 1 - D.m`,
`log b = D.logB` is a parameter, `denominatorBudget = D.denominatorBudget` is the budget for
denominators and `directionAmount = D.directionAmount` is the sum over the infinite places `σ`, of
weight `κ = D.weight σ`, of `D.jetSize κ = log κ! + κ log (M / Ω)`, the size of a derivative of
order `κ`, less the prime sum `D.primeSum κ σ` that measures its divisibility. -/
lemma heightLe_liftDeterminant_ratio {θ : PrimePadicIso → D.MFoldTwist} (hθ : D.IsRegularFamily θ)
    (j : D.LiftIndex) :
    HeightLe (D.targetDim * (D.k * (D.logB * D.denominatorBudget - D.directionAmount)))
      fun ι : PrimePadicIso ↦ D.liftDeterminant 1 j / D.liftDeterminant (θ ι) j := by
  -- The ratio is `det (pr U_ξ) / det (pr U_1)` times the `d`-th power of the inverse ratio of
  -- Hecke values.
  obtain ⟨β, hβ_sum, hβ_denom⟩ : ∃ β : ℕ → ℝ, D.IsDenominatorBound θ j β :=
    hθ.exists_denominator_bound j
  rw [D.targetDim_eq_finrank_goodForms_spaceW j]
  have hU : IsComparisonOperator j (comparisonOp j) := isComparisonOperator_comparisonOp j
  set d : ℕ := finrank ℂ (D.goodForms (D.spaceW j))
  obtain ⟨C, hC, h_cancel⟩ : ∃ C : ℂ, C ≠ 0 ∧ ∀ ϑ : D.Twist,
      (D.goodLift ϑ j).normDet ^ 2 * (liftCompression (comparisonOp j) ϑ).det =
        C * (heckeValueProd j ϑ / heckeValueProd j 1) ^ d :=
    hU.exists_normDet_sq_mul_det_eq
  set A : ℝ := D.f * D.m * D.b * D.logB ^ 2
  let Δ (ϑ : D.Twist) : ℂ := (liftCompression (comparisonOp j) ϑ).det
  have h_ratio : ∀ ϑ : D.Twist, heckeValueProd j ϑ / heckeValueProd j 1 ≠ 0 := hU.ratio_ne_zero
  have hΔ_ne (ϑ : D.Twist) : Δ ϑ ≠ 0 :=
    right_ne_zero_of_mul ((h_cancel ϑ).trans_ne (mul_ne_zero hC (pow_ne_zero d (h_ratio ϑ))))
  have h_arch (σ : ℂ ≃+* ℂ) : ‖σ (Δ 1)‖ ≤ exp (d * (3 * A)) := hU.norm_map_det_liftCompression_le σ
  have h_padic (ι : PrimePadicIso) :
      ‖ι.iso (Δ ((θ ι).powTwist j))‖ ≤ exp (d * (D.r * β ι.prime)) :=
    hU.norm_padic_det_liftCompression_le ((θ ι).powTwist j) ι (hθ.coprime ι)
      (hβ_denom ι).clearsProjection
  -- Take `Δ 1` as the denominator; its conjugates and the norms of `Δ ξ` at `ι` bound the height.
  have h_height : HeightLe (d * (3 * A) + d * (D.r * D.denominatorBudget))
      fun ι : PrimePadicIso ↦ Δ ((θ ι).powTwist j) / Δ 1 := by
    refine .of_mul_le (e := fun l : ℕ ↦ d * (D.r * β l)) (hΔ_ne 1) h_arch (fun ι ↦ ?_)
      fun T hT ↦ ?_
    · simpa only [mul_div_cancel₀ _ (hΔ_ne 1)] using h_padic ι
    · grw [← mul_sum, ← mul_sum, hβ_sum T hT]
  refine (h_height.mul ((heightLe_inv_heckeValueProd_div hθ j).pow d)).mono ?_ fun ι ↦ ?_
  · have h_bound : 3 * A + D.r * D.denominatorBudget +
      (10 * D.m * D.x₁ + D.k * (6 * D.denominatorBudget - D.directionAmount)) ≤
        D.k * (D.logB * D.denominatorBudget - D.directionAmount) := by
      simpa [A, mul_sub, add_sub] using D.le_of_hasLogBound
    rw [← mul_add, ← mul_add]
    gcongr
  · set ρ : ℂ := heckeValueProd j ((θ ι).powTwist j) / heckeValueProd j 1
    have h_twist : D.liftDeterminant (θ ι) j * Δ ((θ ι).powTwist j) = C * ρ ^ d :=
      h_cancel ((θ ι).powTwist j)
    have h_trivial : D.liftDeterminant 1 j * Δ 1 = C := by
      rw [liftDeterminant, mFoldTwist_one_pow]
      exact (h_cancel 1).trans (by simp [(div_ne_zero_iff.1 (h_ratio 1)).2])
    have hρ : ρ ≠ 0 := h_ratio ((θ ι).powTwist j)
    have h_eq : D.liftDeterminant 1 j / D.liftDeterminant (θ ι) j =
        Δ ((θ ι).powTwist j) / Δ 1 * ρ⁻¹ ^ d := by
      rw [eq_div_of_mul_eq (hΔ_ne _) h_twist, eq_div_of_mul_eq (hΔ_ne _) h_trivial, inv_pow]
      field [hΔ_ne, pow_ne_zero d hρ]
    rw [h_eq, Pi.mul_apply, Pi.pow_apply]

end New.Data
