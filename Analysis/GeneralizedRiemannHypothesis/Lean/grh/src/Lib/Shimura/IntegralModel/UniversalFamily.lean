import Lib.General.Geometry.GaloisCovers
import Lib.General.Geometry.SerreTheorem
import Lib.Shimura.HeckeTower.Model
import Lib.Shimura.Uniformisation.TorusModel

/-!
# The universal family: models along arcs, rigid fibres and points of linear data

This file studies the universal abelian scheme 𝒜 → S of PEL data D and describes its complex points
by linear algebra. Over an arc `O` (`New.ValuativeArc`, a valuation ring with fraction field `ℂ`), a
description of the generic fibre as a complex torus (`New.ThetaObject.TorusModel`) is also a
description of the object over `O`. The geometric fibres of such a modelled object are rigid
(`New.ThetaObject.HasSpanningCoords`): on each of their pull-backs to a noetherian local ring `B`,
global functions come from the base (`New.HasConstFunctions`), and the coordinates span the sections
of the line bundle `N` of the object over `B`. A linear datum a = (x, ℓ, P)
(`New.Variety.ModuliPoint`) consists of an adelic frame x, a reflection ℓ of ℂⁿ (1 on a line, −1 on
a complement), and vectors P_i.

## Main definitions and results

* `New.Variety.UniversalFamily`: the universal object, with the standing hypotheses.
* `New.ThetaFamily.IsPointOf`, `New.Variety.UniversalFamily.datumPoint`: the point of a fibre power
  of 𝒜 given by a fibre modelled on a, its non-zero 𝔪-torsion points and the images of the P_i.
* `New.ThetaFamily.IsPointOf.eq_iff`, `New.Variety.UniversalFamily.datumPoint_eq_iff`: two such
  points are equal exactly when the data are isomorphic (`New.Variety.ModuliPoint.IsLevelIso`) at
  level K(𝔑) ∩ K(𝔪), where K is the principal level `New.Variety.levelGU` and 𝔑 the level of D. Here
  a ≅ b via z in GL_n(E) means: b.x⁻¹ z a.x lies in the level group, z conjugates a's reflection to
  b's, and z P_i − b.P_i lies in the lattice of b.x.
* `New.Variety.UniversalFamily.GraphClosure`: the closure of the graph of finitely many translations
  a ↦ a·(g_j, 1).
* `New.Variety.UniversalFamily.smooth_and_isDenseFamily_and_exists_comp_eq_act`: at level 1 the
  fibre power is smooth over R, and the points of linear data are dense in it.

Notions from other files:
* `New.ThetaObject`: an object of the family X over a scheme T: a morphism from T to the base of X;
  `x.IsPullbackAlong f y` means x = f ≫ y, the pull-back of y along f.
* `New.Variety.ModuliPoint.act`: a·(g, α) = (x g, ℓ, α_i P_i) for a = (x, ℓ, P), an adelic
  similitude g and integers α_i of E.
* `New.ThetaObject.TorusModel.π`: for a model m, the map from (E ⊗ ℝ)ⁿ to the sections of the
  object; `m.fullStructure.torsionPoint` labels the torsion sections by `New.AdelicTorsion`.
* `New.Variety.NonzeroTorsion`: for a non-zero element 𝔪 of O_E, the set of non-zero elements of
  (𝔸_f / Ô)ⁿ ≅ (E / O_E)ⁿ killed by 𝔪.

## Relation to the literature

Known result: the sections of an ample line bundle on an abelian variety are spanned by theta
functions. Here it is stated for the coordinates of an object with a torus model, on the pull-backs
of its geometric fibres to noetherian local rings (`hasSpanningCoords_of_specMap_comp_eq`). Spanning
of the sections is proved by reduction from the complex numbers rather than by Riemann–Roch, and the
only consequence drawn is that a map of such objects respecting the pairing and the level points
lies over the family, which gives the criterion for equal points (`IsPointOf.eq_iff`). Source: D.
Mumford, On the equations defining abelian varieties I, Invent. Math. 1 (1966), §§1–2; S. W. Shin,
Abelian varieties and Weil representations, Algebra Number Theory 6 (2012), Prop. 2.12 (over a
base); M. Bolognesi, A. Massarenti, Comment. Math. Helv. 91 (2016), Lemma 4.1 (odd type).

See also `Lib.Shimura.ArcExtension` and `Lib.Shimura.IntegralModel.TowerExistence`.
-/

noncomputable section

/-! ## Models of the generic fibre as models along the arc -/

section ModelAlongArc

open CategoryTheory AlgebraicGeometry New.ValuativeArc
open scoped CategoryTheory.MonoidalCategory

/-- Let `O` be a valuation ring with fraction field `ℂ`, `y` an object over `O` and `x` its
pull-back `h_pull` to the generic point. A model `m` of `x` on the period map `Y` (an isomorphism
`Y.realEquiv` of `(E ⊗ ℝ)ⁿ` with `V` and a Hermitian form `Y.automorphyForm`) gives a model `m'` of
`y` on `Y` whose sections `m'.π w` restrict to `m.π w` followed by the map of `h_pull`. A case of
the extension of homomorphisms and line bundles of abelian schemes from the generic fibre. -/
lemma New.ThetaObject.TorusModel.exists_torusModel_of_isPullbackAlong {E V : Type} [Field E]
    [CMBase E]
    [FinComplexSpace V] {D : PEL E} {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ}
    {Z : Scheme} {τ : Z ⟶ Spec (CommRingCat.of (NumberField.RingOfIntegers E))} {O : Type}
    {X : ThetaFamily D Z τ} [CommRing O] [ValuativeArc O]
    {y : ThetaObject X (Spec (CommRingCat.of O))} {x : ThetaObject X (Spec (CommRingCat.of ℂ))}
    {Y : ThetaTori.PeriodMap D g ℓ V} (m : x.TorusModel Y)
    (h_pull : x.IsPullbackAlong (genericPt (O := O)) y) :
    ∃ m' : y.TorusModel Y, ∀ w : Variety.RealVectors E D.Index,
      genericPt ≫ (m'.π w).left = (m.π w).left ≫ h_pull.schemeMap.left := by
  -- By the valuative criterion, restriction to the generic point is an isomorphism `j` from the
  -- sections of `y.groupScheme` over `O` to those of `x.groupScheme` over `ℂ`. The uniformisation
  -- of `x` is carried along `j⁻¹`; the lattice, the theta coordinates and the rest stay the same.
  let j : (𝟙_ (Over (Spec (CommRingCat.of O))) ⟶ y.groupScheme) ≃ₗ[NumberField.RingOfIntegers E]
      (𝟙_ (Over (Spec (CommRingCat.of ℂ))) ⟶ x.groupScheme) :=
    LinearEquiv.ofBijective h_pull.isGroupBaseChange.pullSection
      (h_pull.isGroupBaseChange.pointEquiv.symm.bijective.comp bijective_restrict_genericPt)
  have hj (s : 𝟙_ (Over (Spec (CommRingCat.of O))) ⟶ y.groupScheme) :
      (j s).left ≫ h_pull.schemeMap.left = genericPt ≫ s.left :=
    h_pull.isGroupBaseChange.pullSection_comp s
  let e : V →+ (𝟙_ (Over (Spec (CommRingCat.of O))) ⟶ y.groupScheme) :=
    j.symm.toAddMonoidHom.comp m.uniformisation.expMap
  -- on complex points, `e` is the old uniformisation followed by the map of `h_pull`
  have h_atGeneric_e :
      atGeneric e = fun w : V ↦ atGeneric m.uniformisation.expMap w ≫ h_pull.schemeMap.left := by
    funext w
    have h_comp : (m.uniformisation.expMap w).left ≫ h_pull.schemeMap.left =
        genericPt ≫ (e w).left := by simp [← hj, e]
    exact h_comp.symm
  -- the universal property: restrict `γ` to the generic fibre and use that of `m.uniformisation`
  have h_universal {W : Type} [FinComplexSpace W]
      (γ : W →+ (𝟙_ (Over (Spec (CommRingCat.of O))) ⟶ y.groupScheme))
      (hγ : HolomorphicAt (atGeneric γ) 0) : ∃ F : W →L[ℂ] V, ∀ z : W, e (F z) = γ z := by
    -- analytic coordinates `q` of `γ` are also coordinates of its restriction to the generic fibre
    obtain ⟨q, hq_analytic, hq_coords⟩ :=
      hγ.exists_isHomogeneousCoords y.isProjEmbedding.isLinearSystem
    have hq_coords_x : ∀ᶠ w : W in nhds 0,
        x.lineBundle.IsHomogeneousCoords (atGeneric (j.toAddMonoidHom.comp γ) w) (q w) := by
      filter_upwards [hq_coords] with w hw
      rw [h_pull.lineBundle_eq_pull, LineBundle.IsHomogeneousCoords.pull_iff]
      change y.lineBundle.IsHomogeneousCoords ((j (γ w)).left ≫ h_pull.schemeMap.left) (q w)
      rwa [hj]
    obtain ⟨F, hF⟩ : ∃ F : W →L[ℂ] V, ∀ z : W, m.uniformisation.expMap (F z) = j (γ z) :=
      m.uniformisation.universal (j.toAddMonoidHom.comp γ)
        (.of_isHomogeneousCoords x.isProjEmbedding hq_analytic hq_coords_x fun _ ↦ Over.w _)
    exact ⟨F, fun z ↦ by simp [e, hF]⟩
  let u : Uniformisation y.groupScheme V :=
    { m.uniformisation with
      expMap := e
      surjective := j.symm.surjective.comp m.uniformisation.surjective
      eq_zero_iff := by simp [e, Uniformisation.eq_zero_iff]
      immersive z := by
        rw [h_atGeneric_e]
        exact m.uniformisation.isHolomorphicImmersionAt_of_isPullback
          h_pull.isGroupBaseChange.isPullback z
      universal := h_universal }
  have h_spec : x.IsPullbackAlong (specMap (algebraMap O ℂ)) y := by
    rwa [← ValuativeArc.genericPt_eq]
  -- `x.lineBundle` is the pull-back of `y.lineBundle` along `h_pull.schemeMap`, so the theta
  -- coordinates are unchanged
  have h_theta : HasThetaCoords m.uniformisation.lattice (atGeneric e) y.lineBundle Y.automorphyForm
    m.χ m.θ :=
    { m.hasThetaCoords with
      isLinearSystem := y.isProjEmbedding.isLinearSystem
      hasFieldCoords := fun z ↦ by
        rw [h_atGeneric_e, ← LineBundle.IsHomogeneousCoords.pull_iff, ← h_pull.lineBundle_eq_pull]
        exact m.hasThetaCoords.hasFieldCoords z }
  refine ⟨{ m with
    baseHom_eq c := by simp [← m.baseHom_eq c, IsPullbackAlong.baseHom_eq_comp h_spec]
    uniformisation := u
    hasThetaCoords := h_theta
    equivariant := by simp [u, e, m.equivariant]
    level_eq l := ?_ }, fun w ↦ congrFun h_atGeneric_e (Y.realEquiv w)⟩
  -- the level points of `x` are the pull-backs of those of `y`
  have h_level : j (y.levelPoints l) = m.uniformisation.expMap (Y.torsionLift l) :=
    (h_pull.levelPoints_eq_pullSection l).symm.trans (m.level_eq l)
  exact j.eq_symm_apply.mpr h_level

end ModelAlongArc

/-!
## Rigidity of the geometric fibres of a modelled object

The idea: Serre's theorem `New.Variety.eventually_span_coordSection` gives the sections of
`[c]^* N ≅ N ^ (c ^ 2)` for large `c`, and the trace over the `c`-torsion brings them down to `N`.
-/

section RigidFibres

open CategoryTheory AlgebraicGeometry Submodule New Variety LineBundle Set Nat IsLocalRing Spec
open scoped CategoryTheory.MonoidalCategory

variable {E O W : Type} [Field E] [CMBase E] [CommRing O] [ValuativeArc O] [FinComplexSpace W]
  {D : PEL E} {Z : Scheme} {τ : Z ⟶ Spec (CommRingCat.of (NumberField.RingOfIntegers E))}
  {X : ThetaFamily D Z τ} {y : ThetaObject X (Spec (CommRingCat.of O))}
  {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ} {Y : ThetaTori.PeriodMap D g ℓ W}
  {B : Type} [CommRing B] {x : ThetaObject X (Spec (CommRingCat.of B))}
  {b : CommRingCat.of O ⟶ CommRingCat.of B}

/-- Let `v z = expMap (z / c)` for a model `a` and `c ≠ 0`. Then multiplication by `c` sends the
complex point of `v z` to that of `expMap z`. -/
private lemma atGeneric_comp_nsmul (a : y.TorusModel Y) {c : ℕ} (hc0 : c ≠ 0)
    (v : W → (𝟙_ (Over (Spec (CommRingCat.of O))) ⟶ y.groupScheme))
    (hv_eq : ∀ z : W, v z = a.uniformisation.expMap ((c : ℂ)⁻¹ • z)) (z : W) :
    atGeneric v z ≫ (c • 𝟙 y.groupScheme).left = atGeneric a.uniformisation.expMap z := by
  have hv : c • v z = a.uniformisation.expMap z := by
    simp [hv_eq, ← cast_smul_eq_nsmul ℂ, hc0, ← map_nsmul]
  simp [atGeneric, ← hv, ← Over.comp_left, comp_nsmul]

/-- Let `a` model `y` over `O` on a complex torus (uniformisation `expMap : W → y.groupScheme` with
lattice `L`, theta coordinates `a.θ z i` indexed by `i : D.dualTorsion`), `c ≠ 0` and
`v z = expMap (z / c)`. A section `ω` of `[c]^* N`, `N = y.lineBundle`, whose values along `v` are
`L`-periodic is a theta function along `v`: `ω_i (v z) = f z / θ_i z` where `θ_i z ≠ 0`, for a theta
function `f` for the Hermitian form `Y.automorphyForm` of the period map and the multiplier
`a.χ`. -/
lemma New.ThetaObject.TorusModel.exists_mem_thetaSpace_of_periodic (a : y.TorusModel Y) {c : ℕ}
    (hc0 : c ≠ 0) (v : W → (𝟙_ (Over (Spec (CommRingCat.of O))) ⟶ y.groupScheme))
    (hv_eq : ∀ z : W, v z = a.uniformisation.expMap ((c : ℂ)⁻¹ • z))
    (ω : (y.lineBundle.pull (c • 𝟙 y.groupScheme).left).H0 O)
    (h_per : ∀ l ∈ a.uniformisation.lattice, ∀ (z : W) (i : D.dualTorsion),
      ω.val i (CommRingCat.of ℂ) (atGeneric v (z + l)) =
        ω.val i (CommRingCat.of ℂ) (atGeneric v z)) :
    ∃ f ∈ Y.automorphyForm.thetaSpace (L := a.uniformisation.lattice) a.χ,
      ∀ (i : D.dualTorsion) (z : W), a.θ z i ≠ 0 →
      ω.val i (CommRingCat.of ℂ) (atGeneric v z) = f z / a.θ z i := by
  -- Along `v` the bundle `[c]^* N` has the theta coordinates that `N` has along `expMap`.
  have hθv : HasThetaCoords a.uniformisation.lattice (atGeneric v)
      (y.lineBundle.pull (c • 𝟙 y.groupScheme).left) Y.automorphyForm a.χ a.θ :=
    a.hasThetaCoords.pull 1 (fun z ↦ (atGeneric_comp_nsmul a hc0 v hv_eq z).symm) fun l hl ↦ hl
  have hv_hol (z : W) : HolomorphicAt (atGeneric v) z := by
    rw [funext hv_eq]
    exact (a.uniformisation.holomorphicAt _).comp (by fun_prop)
  have hω_sec : ((y.lineBundle.pull (c • 𝟙 y.groupScheme).left).mul
      (((y.lineBundle.pull (c • 𝟙 y.groupScheme).left).pow 0).inv)).IsSection
        fun q : D.dualTorsion × (Fin 0 → D.dualTorsion) ↦ ω.val q.fst := by
    simpa [IsSection, LineBundle.pow, inf_of_le_left] using ω.prop.left
  -- Compare `[c]^* N` with its power `0`, the trivial bundle with the coordinate `1`: the
  -- theta function of `ω` relative to it is `f`, and `simpa` removes the trivial factor.
  simpa using hθv.exists_theta_of_isSection (hθv.pow 0) hω_sec hv_hol
    fun l hl z q ↦ h_per l hl z q.fst

/-- In the setting of `New.ThetaObject.TorusModel.exists_mem_thetaSpace_of_periodic`, let `ω` be
given by `f` along `v`, that is, `ω_i (v z) = f z / θ_i z` where `θ_i z ≠ 0`. If a section `w` of
`N` is given by `β • f` along `expMap`, for some `β` in `O`, then its pull-back along multiplication
by `c` is `β • ω`: the two agree at the points `v z`, which are dense. -/
lemma New.ThetaObject.TorusModel.pullSections_eq_smul_of_theta (a : y.TorusModel Y) {c : ℕ}
    (hc0 : c ≠ 0) (v : W → (𝟙_ (Over (Spec (CommRingCat.of O))) ⟶ y.groupScheme))
    (hv_eq : ∀ z : W, v z = a.uniformisation.expMap ((c : ℂ)⁻¹ • z))
    (ω : (y.lineBundle.pull (c • 𝟙 y.groupScheme).left).H0 O)
    {f : W → ℂ} (hωf : ∀ (i : D.dualTorsion) (z : W), a.θ z i ≠ 0 →
      ω.val i (CommRingCat.of ℂ) (atGeneric v z) = f z / a.θ z i)
    (w : y.lineBundle.H0 O) (β : O)
    (hw : ∀ (i : D.dualTorsion) (z : W), a.θ z i ≠ 0 →
      w.val i (CommRingCat.of ℂ) (atGeneric a.uniformisation.expMap z) =
        algebraMap O ℂ β * f z / a.θ z i) :
    (pullSections (RingHom.id O) (by simp) rfl :
      y.lineBundle.H0 O →ₗ[O] (y.lineBundle.pull (c • 𝟙 y.groupScheme).left).H0 O) w = β • ω := by
  -- Along `v` the bundle `[c]^* N` has the theta coordinates that `N` has along `expMap`.
  have hθv : HasThetaCoords a.uniformisation.lattice (atGeneric v)
      (y.lineBundle.pull (c • 𝟙 y.groupScheme).left) Y.automorphyForm a.χ a.θ :=
    a.hasThetaCoords.pull 1 (fun z ↦ (atGeneric_comp_nsmul a hc0 v hv_eq z).symm) fun l hl ↦ hl
  have hv_surj : Function.Surjective v := by
    rw [funext hv_eq]
    exact a.uniformisation.surjective.comp (MulAction.surjective₀ (by simpa using hc0))
  -- compare the two sides at the dense points `atGeneric v z` that land in the chart `i`
  have h_dense : IsSeparatingFamily (atGeneric v) :=
    isSeparatingFamily_atGeneric_of_surjective hv_surj
  refine H0_ext fun {i} h_reg h_reg' ↦ h_dense.pointFn_ext h_reg h_reg' fun z hz_lands ↦ ?_
  have hθ_ne : a.θ z i ≠ 0 := ((hθv.hasFieldCoords z i).left.mp hz_lands).ne_zero
  calc (pullSections (RingHom.id O) (by simp) rfl w :
          (y.lineBundle.pull (c • 𝟙 y.groupScheme).left).H0 O).val i (.of ℂ) (atGeneric v z)
      = w.val i (CommRingCat.of ℂ) (atGeneric a.uniformisation.expMap z) := by
        simp [atGeneric_comp_nsmul a hc0 v hv_eq]
    _ = algebraMap O ℂ β * (f z / a.θ z i) := by rw [hw i z hθ_ne, mul_div_assoc]
    _ = algebraMap O ℂ β * ω.val i (CommRingCat.of ℂ) (atGeneric v z) := by rw [hωf i z hθ_ne]
    _ = (β • ω).val i (CommRingCat.of ℂ) (atGeneric v z) := by
        simp [H0_smul, atGeneric, ValuativeArc.genericPt_eq]

/-- Let `O` be a valuation ring with fraction field `ℂ` (`ValuativeArc`), and `a` a model of `y`
over `O` on a complex torus (uniformisation `expMap` with lattice `L`, line bundle
`N = y.lineBundle`). Let `c ≠ 0`, `v z = expMap (z / c)`, and `Λ` the pull-back of sections along
multiplication `[c]`. A section `ω` of `[c]^* N` whose components `ω_i`, `i : D.dualTorsion`,
evaluated at the generic ℂ-points `v z` are `L`-periodic in `z` lies in the image under `Λ` of the
`O`-span of the coordinate sections of `N`. -/
lemma New.ThetaObject.TorusModel.mem_map_span_of_periodic {E O W : Type} [Field E] [CMBase E]
    [CommRing O] [ValuativeArc O] [FinComplexSpace W] {D : PEL E} {Z : Scheme}
    {τ : Z ⟶ Spec (CommRingCat.of (NumberField.RingOfIntegers E))} {X : ThetaFamily D Z τ}
    {y : ThetaObject X (Spec (CommRingCat.of O))} {g : GL D.Index (𝔸f E)}
    {ℓ : Matrix D.Index D.Index ℂ} {Y : ThetaTori.PeriodMap D g ℓ W} (a : y.TorusModel Y) {c : ℕ}
    (hc0 : c ≠ 0) (v : W → (𝟙_ (Over (Spec (CommRingCat.of O))) ⟶ y.groupScheme))
    (hv_eq : ∀ z : W, v z = a.uniformisation.expMap ((c : ℂ)⁻¹ • z))
    (ω : (y.lineBundle.pull (c • 𝟙 y.groupScheme).left).H0 O)
    (h_per : ∀ l ∈ a.uniformisation.lattice, ∀ (z : W) (i : D.dualTorsion),
      ω.val i (CommRingCat.of ℂ) (atGeneric v (z + l)) =
        ω.val i (CommRingCat.of ℂ) (atGeneric v z)) :
    ω ∈ Submodule.map (pullSections (RingHom.id O) (by simp) rfl :
      y.lineBundle.H0 O →ₗ[O] (y.lineBundle.pull (c • 𝟙 y.groupScheme).left).H0 O)
        (span O (range (coordSection y.isProjEmbedding.isLinearSystem))) := by
  -- Suppose not. The periodic section `ω` is a theta function `f` along `v`, and for some `γ ≠ 0`
  -- the theta function `γ • f` comes from a section `w` of the span. As `O` is a valuation ring,
  -- `γ` or `γ⁻¹` is some `β` in `O`. If `γ = β`, then `Λ w = β • ω` by density, so `β` is no unit
  -- of `O`; if `γ⁻¹ = β`, then `Λ (β • w) = ω`. Either case is absurd.
  set Λ : y.lineBundle.H0 O →ₗ[O] (y.lineBundle.pull (c • 𝟙 y.groupScheme).left).H0 O :=
    pullSections (RingHom.id O) (by simp) rfl
  by_contra hω
  have hv (z : W) : c • v z = a.uniformisation.expMap z := by
    simp [hv_eq, ← cast_smul_eq_nsmul ℂ, hc0, ← map_nsmul]
  obtain ⟨f, hf, hωf⟩ : ∃ f ∈ Y.automorphyForm.thetaSpace (L := a.uniformisation.lattice) a.χ,
      ∀ (i : D.dualTorsion) (z : W), a.θ z i ≠ 0 → ω.val i (.of ℂ) (atGeneric v z) = f z / a.θ z
        i :=
    a.exists_mem_thetaSpace_of_periodic hc0 v hv_eq ω h_per
  -- A section `w` of the span whose theta function is `β • f` has `Λ w = β • ω`
  -- (`pullSections_eq_smul_of_theta`), so `β` is no unit.
  have h_nonunit (w : span O (range (coordSection a.hasThetaCoords.isLinearSystem))) (β : O)
      (h_eq : Λ w = β • ω) : ¬IsUnit β := fun hβ ↦
    hω ((smul_mem_iff_of_isUnit _ hβ).mp ⟨w, w.prop, h_eq⟩)
  -- `f ≠ 0`: otherwise `0` has the theta function `1 • f`
  have hf0 : f ≠ 0 := fun hf_zero ↦ h_nonunit 0 1
    (a.pullSections_eq_smul_of_theta hc0 v hv_eq ω hωf 0 1 (by simp [hf_zero])) isUnit_one
  -- By `exists_sections_of_translation_stable`, some `γ • f` comes from a `w` in the span of the
  -- coordinates that vanishes on no orbit of a field-valued point under the dual lattice.
  -- (`hw`: `w` has the theta function `γ • f`; `h_orbit`: it vanishes on no such orbit)
  obtain ⟨γ, hγ, w, hw, h_orbit⟩ := exists_sections_of_translation_stable a.uniformisation
    a.hasThetaCoords y.isThetaStructure.isUnit_card
    (fun b hb ↦ (a.exists_isTranslationLift_of_dualLattice b hb).left)
    (fun b hb ↦ (a.exists_isTranslationLift_of_dualLattice b hb).right)
    (fun j ↦ subset_span ⟨j, rfl⟩) (f := fun _ : Unit ↦ f) (fun _ ↦ hf) () hf0
  -- The valuation ring `O` contains `γ` or `γ⁻¹`.
  obtain ⟨β, hβ⟩ | ⟨β, hβ⟩ : IsLocalization.IsInteger O γ ∨ IsLocalization.IsInteger O γ⁻¹ :=
    ValuationRing.isInteger_or_isInteger O γ
  · -- `γ = β` lies in the maximal ideal, so `w` vanishes at the reductions of all the `expMap z`,
    -- in particular on the orbit of the reduction of `expMap 0`.
    have hw_β (i : D.dualTorsion) (z : W) (hz : a.θ z i ≠ 0) :
        (w () : y.lineBundle.H0 O).val i (.of ℂ) (atGeneric a.uniformisation.expMap z) =
          algebraMap O ℂ β * f z / a.θ z i := by rw [hw () i z hz, hβ]
    have h_eq : Λ (w ()) = β • ω :=
      a.pullSections_eq_smul_of_theta hc0 v hv_eq ω hωf (w ()) β hw_β
    obtain ⟨b, -, _j, i, h_ne⟩ := h_orbit _ (specMap (residue O) ≫ (a.uniformisation.expMap 0).left)
    refine h_ne ?_
    -- the translate of the reduction of `expMap 0 = 0` by `expMap b` is `[c]` of that of `v b`
    have h_point : (specMap (residue O) ≫ (a.uniformisation.expMap 0).left) ≫
          (translation (a.uniformisation.expMap b)).left =
        (specMap (residue O) ≫ (v b).left) ≫ (c • 𝟙 y.groupScheme).left := by
      simp [hv, ← Over.comp_left, comp_add, comp_nsmul]
    -- `β` reduces to `0` in the residue field
    have h_smul_zero :
        (β • ω).val i (CommRingCat.of (ResidueField O)) (specMap (residue O) ≫ (v b).left) = 0 := by
      simp [H0_smul, (residue_eq_zero_iff β).mpr (h_nonunit (w ()) β h_eq)]
    rw [h_point, ← h_smul_zero, ← h_eq]
    simp [Λ]
  · -- `γ⁻¹ = β`: then `β • w` has theta function `1 • f`, so `1` would be no unit.
    have hw_one (i : D.dualTorsion) (z : W) (hz : a.θ z i ≠ 0) :
        (β • w () : y.lineBundle.H0 O).val i (.of ℂ) (atGeneric a.uniformisation.expMap z) =
          algebraMap O ℂ 1 * f z / a.θ z i :=
      calc _ = algebraMap O ℂ β * (γ * f z / a.θ z i) := by
            simp [← hw () i z hz, H0_smul, atGeneric, ValuativeArc.genericPt_eq]
        _ = algebraMap O ℂ 1 * f z / a.θ z i := by
            rw [hβ, map_one, one_mul, ← mul_div_assoc, inv_mul_cancel_left₀ hγ]
    exact h_nonunit (β • w ()) 1
      (a.pullSections_eq_smul_of_theta hc0 v hv_eq ω hωf (β • w ()) 1 hw_one) isUnit_one

/-- Let `a` model `y` over `O` on a complex torus, `c ≠ 0`, `F` an enumeration of the sections
`z` with `c • z = 0`, and `M = [c]^* N` (`N = y.lineBundle`), which `h_transl` identifies with its
pull-backs along the translations by these sections. The trace of a section of `M`, the sum of these
pull-backs, is the pull-back along `[c]` of an `O`-linear combination of the coordinates of `N`. -/
lemma New.ThetaObject.TorusModel.sum_pullSections_translation_mem_map_span
    (a : y.TorusModel Y) {c : ℕ} (hc0 : c ≠ 0) {n : ℕ}
    (F : Fin n ≃ {z : 𝟙_ (Over (Spec (CommRingCat.of O))) ⟶ y.groupScheme // c • z = 0})
    (h_transl : ∀ i : Fin n, y.lineBundle.pull (c • 𝟙 y.groupScheme).left =
      (y.lineBundle.pull (c • 𝟙 y.groupScheme).left).pull (translation (F i).val).left)
    (s : (y.lineBundle.pull (c • 𝟙 y.groupScheme).left).H0 O) :
    (∑ i : Fin n, pullSections (RingHom.id O) (by simp) (h_transl i)) s ∈
      Submodule.map (pullSections (RingHom.id O) (by simp) rfl)
        (span O (range (coordSection y.isProjEmbedding.isLinearSystem))) := by
  -- The trace is periodic along `z ↦ expMap (z / c)`: adding a period `l` there adds the
  -- `c`-torsion section `expMap (l / c)`, which permutes the terms of the sum.
  refine a.mem_map_span_of_periodic hc0 (fun z ↦ a.uniformisation.expMap ((c : ℂ)⁻¹ • z))
    (fun _ ↦ rfl) _ fun l hl z i ↦ ?_
  have hl_tors : c • a.uniformisation.expMap ((c : ℂ)⁻¹ • l) = 0 := by
    simpa [← cast_smul_eq_nsmul ℂ, hc0, a.uniformisation.eq_zero_iff, ← map_nsmul] using hl
  let shift : Equiv.Perm {t : 𝟙_ (Over (Spec (CommRingCat.of O))) ⟶ y.groupScheme // c • t = 0} :=
    (Equiv.addLeft (a.uniformisation.expMap ((c : ℂ)⁻¹ • l))).subtypeEquiv
      (by simp [smul_add, hl_tors])
  simp only [translation, LinearMap.coe_sum, Finset.sum_apply, AddSubmonoidClass.coe_finsetSum,
    pullSections_apply_coe]
  refine Fintype.sum_equiv (F.symm.permCongr shift) _ _ fun j ↦ ?_
  simp [atGeneric, add_assoc, shift, comp_add, ← Over.comp_left]

/-- Let `x` over `B` be the pull-back `hx` of `y`, with constant global functions on fibres, `M`
the pull-back of the line bundle along multiplication by `c`, and `Q` a lift of `hx` from sections
of `M` on `y` to those on `x`. If the pulled-back coordinates of `N ^ (c ^ 2)` span over `B`, a
`B`-linear map `T` that sends every `Q s` into a submodule `S` sends every section into `S`. -/
private lemma apply_mem_of_forall_apply_sectionLift_mem (hx : x.IsPullbackAlong (Spec.map b) y)
    (h_cst : HasConstFunctions x.groupScheme.hom) (c : ℕ)
    (h_lin : (y.lineBundle.pow (c ^ 2)).IsLinearSystem)
    (h_span :
      span B (range (coordSection (X := x.groupScheme) (h_lin.pull hx.schemeMap.left))) = ⊤)
    (Q : (y.lineBundle.pull (c • 𝟙 y.groupScheme).left).H0 O →ₛₗ[b.hom]
      (x.lineBundle.pull (c • 𝟙 x.groupScheme).left).H0 B)
    (hQ : IsSectionLift (x.lineBundle.pull (c • 𝟙 x.groupScheme).left)
      (y.lineBundle.pull (c • 𝟙 y.groupScheme).left) hx.schemeMap.left Q)
    (T : (x.lineBundle.pull (c • 𝟙 x.groupScheme).left).H0 B →ₗ[B]
      (x.lineBundle.pull (c • 𝟙 x.groupScheme).left).H0 B)
    (S : Submodule B ((x.lineBundle.pull (c • 𝟙 x.groupScheme).left).H0 B))
    (hT : ∀ s : (y.lineBundle.pull (c • 𝟙 y.groupScheme).left).H0 O, T (Q s) ∈ S)
    (s : (x.lineBundle.pull (c • 𝟙 x.groupScheme).left).H0 B) : T s ∈ S := by
  -- Compare `M` with `N ^ (c ^ 2)`, which has the same class in `Pic`: by `Φ` over `O`, and back
  -- by `Θ` over `B`.
  have h_class : (y.lineBundle.pull (c • 𝟙 y.groupScheme).left).picClass =
      (y.lineBundle.pow (c ^ 2)).picClass.pull (Over.Hom.left (𝟙 y.groupScheme)) := by
    have h_parallelogram : y.lineBundle.picClass.ParallelogramLaw := y.hasClassLaws.1
    rw [Over.id_left, Pic.pull_id, picClass_pow, ← pull_nsmul_eq_sq_smul h_parallelogram c,
      Pic.pull_picClass]
  obtain ⟨Φ, hΦ⟩ := exists_isSectionLift (𝟙 y.groupScheme) h_class
  have hQΦ : IsSectionLift (x.lineBundle.pull (c • 𝟙 x.groupScheme).left)
      (y.lineBundle.pow (c ^ 2)) (hx.schemeMap.left ≫ Over.Hom.left (𝟙 y.groupScheme)) (Q ∘ Φ) :=
    hQ.comp hΦ
  obtain ⟨Θ, hΘ⟩ := exists_isSectionLift (𝟙 x.groupScheme)
    (L := x.lineBundle.pull (c • 𝟙 x.groupScheme).left) hQΦ.picClass_eq.symm
  -- Plain base change is `u • Θ ∘ Q ∘ Φ` for some `u`, so the monomials of degree `c ^ 2` on `x`,
  -- which span by `h_span`, lie in the image under `Θ` of the sections that `T` sends into `S`.
  obtain ⟨u, hu⟩ :=
    (isSectionLift_pullSections _ hx.schemeMap.w rfl).exists_eq_smul h_cst (hΘ.comp hQΦ)
  have h_coord_mem (j : Fin (c ^ 2) → D.dualTorsion) :
      coordSection (X := x.groupScheme) (h_lin.pull hx.schemeMap.left) j ∈ map Θ (comap T S) :=
    mem_of_eq_of_mem (hu (coordSection h_lin j))
      (smul_mem _ _ ⟨Q (Φ (coordSection h_lin j)), hT (Φ (coordSection h_lin j)), rfl⟩)
  have h_le : span B (range (coordSection (X := x.groupScheme) (h_lin.pull hx.schemeMap.left))) ≤
      map Θ (comap T S) :=
    span_le.mpr (range_subset_iff.mpr h_coord_mem)
  obtain ⟨t, ht, h_eq⟩ : Θ s ∈ map Θ (comap T S) := h_le (eq_top_iff'.mp h_span (Θ s))
  rwa [← hΘ.injective h_eq]

/-- Let `y` over `O` be modelled by `a` on a complex torus, and let `x` over a local ring `B` be the
pull-back of `y` along `b`, with global functions on `x.groupScheme` constant on fibres. Let `c ≠ 0`
be a unit in `B`, and suppose that the coordinates of the pull-back to `x` of `N ^ (c ^ 2)` span its
sections, where `N` is the line bundle of `y`. Then the coordinates of `x` span its sections over
`B`. -/
lemma New.ThetaObject.TorusModel.span_coordSection_eq_top_of_isPullbackAlong
    (a : y.TorusModel Y) [IsLocalRing B] (hx : x.IsPullbackAlong (Spec.map b) y)
    (h_cst : HasConstFunctions x.groupScheme.hom) {c : ℕ} (hc0 : c ≠ 0) (hc_unit : IsUnit (c : B))
    (h_span : span B (range (coordSection (X := x.groupScheme)
      ((a.hasThetaCoords.pow (c ^ 2)).isLinearSystem.pull hx.schemeMap.left))) = ⊤) :
    span B (range (coordSection x.isProjEmbedding.isLinearSystem)) = ⊤ := by
  -- The trace over the `c`-torsion sends the sections of `M x = [c]^* N` into `S x`, the image
  -- under `Λ x` (pull-back along `[c]`) of the span of the coordinates, and multiplies `Λ x σ` by
  -- the unit `c ^ (2 dim W)`; `Q` is the base change of sections from `y` to `x`.
  let M {T : Scheme} (x : ThetaObject X T) : LineBundle x.groupScheme.left D.dualTorsion :=
    x.lineBundle.pull (c • 𝟙 x.groupScheme).left
  let Λ {R : Type} [CommRing R] (x : ThetaObject X (Spec (CommRingCat.of R))) :
      x.lineBundle.H0 R →ₗ[R] (M x).H0 R := pullSections (.id R) (by simp) (refl (M x))
  let S {R : Type} [CommRing R] (x : ThetaObject X (Spec (CommRingCat.of R))) :
      Submodule R ((M x).H0 R) :=
    map (Λ x) (span R (range (coordSection x.isProjEmbedding.isLinearSystem)))
  have hM_pull : M x = (M y).pull hx.schemeMap.left := by
    simp [M, hx.lineBundle_eq_pull, ← pull_comp _, hx.isGroupBaseChange.nsmul_id_comp,
      ← Over.comp_left]
  let Q : (M y).H0 O →ₛₗ[b.hom] (M x).H0 B := pullSections _ hx.schemeMap.w hM_pull
  -- Enumerate the `c`-torsion sections over `O` by `F`. The trace `trace j` is the sum of the
  -- translations by their images under a homomorphism `j`.
  let Tors : Type := {z : 𝟙_ (Over (Spec (CommRingCat.of O))) ⟶ y.groupScheme // c • z = 0}
  have h_card : Nat.card Tors = c ^ (Module.finrank ℂ W * 2) := a.uniformisation.card_torsion hc0
  obtain ⟨F⟩ : Nonempty (Fin (Nat.card Tors) ≃ Tors) :=
    ⟨(equivFinOfCardPos (h_card.trans_ne (pow_ne_zero _ hc0))).symm⟩
  -- `M x` is invariant under translation by the image of a `c`-torsion section.
  have h_transl {R : Type} [CommRing R] {x : ThetaObject X (Spec (CommRingCat.of R))}
      (j : (𝟙_ _ ⟶ y.groupScheme) →+ (𝟙_ _ ⟶ x.groupScheme)) (i : Fin (Nat.card Tors)) :
      M x = (M x).pull (translation (j (F i).val)).left := by
    simp [M, ← pull_comp _, ← comp_nsmul _, (F i).prop, ← Over.comp_left, comp_nsmul, ← map_nsmul]
  let trace {R : Type} [CommRing R] {x : ThetaObject X (Spec (CommRingCat.of R))}
      (j : (𝟙_ _ ⟶ y.groupScheme) →+ (𝟙_ _ ⟶ x.groupScheme)) : (M x).H0 R →ₗ[R] (M x).H0 R :=
    ∑ i, pullSections (.id R) (by simp) (h_transl j i)
  -- Over `O`, a trace lies in `S y`; base change along `hx.schemeMap` maps `S y` into `S x` and
  -- commutes with the trace.
  have h_trace (s : (M y).H0 O) : trace (AddMonoidHom.id _) s ∈ S y :=
    a.sum_pullSections_translation_mem_map_span hc0 F (h_transl (AddMonoidHom.id _)) s
  have hQS : S y ≤ comap Q (S x) := by
    refine (map_span_le ..).mpr (forall_mem_range.mpr fun j ↦
      ⟨coordSection x.isProjEmbedding.isLinearSystem j, subset_span ⟨j, rfl⟩, ?_⟩)
    ext
    simp [Λ, Q, hx.isGroupBaseChange.nsmul_id_comp, coordSection, hx.lineBundle_eq_pull]
  have h_comm (s : (M y).H0 O) :
      trace hx.isGroupBaseChange.pullSection (Q s) = Q (trace (AddMonoidHom.id _) s) := by
    ext
    simp [Q, trace, hx.isGroupBaseChange.translation_comp]
  refine eq_top_iff'.mpr fun σ ↦ ?_
  -- By `h_span` (with `h_cst`, `h_comm`, `hQS`, `h_trace`), every trace over `B` lies in `S x`;
  -- take that of `Λ x σ`.
  obtain ⟨w, hw, hws⟩ : trace hx.isGroupBaseChange.pullSection (Λ x σ) ∈ S x :=
    apply_mem_of_forall_apply_sectionLift_mem hx h_cst c
      (a.hasThetaCoords.pow (c ^ 2)).isLinearSystem h_span Q
      (isSectionLift_pullSections _ hx.schemeMap.w hM_pull) _ (S x)
      (fun s ↦ mem_of_eq_of_mem (h_comm s) (hQS (h_trace s))) (Λ x σ)
  -- `Λ x σ` is invariant under `c`-torsion translations, and `Λ x` is injective because `[c]` is
  -- an isogeny (finite, flat, surjective). Hence `w = c ^ (2 dim W) • σ`, a unit multiple of `σ`.
  have h_isog : IsIsogeny (c • 𝟙 x.groupScheme) :=
    mod_cast x.isIsogeny_smul_id (cast_ne_zero.mpr hc0)
  have hΛ_lift : IsSectionLift (M x) x.lineBundle (c • 𝟙 x.groupScheme).left (Λ x) :=
    isSectionLift_pullSections ..
  have hwσ : w = (c : B) ^ (Module.finrank ℂ W * 2) • σ := by
    refine hΛ_lift.injective (hws.trans ?_)
    ext
    simp [trace, Λ, ← comp_nsmul _, (F _).prop, h_card, ← Over.comp_left, comp_nsmul, ← map_nsmul,
      H0_smul]
  rwa [hwσ, SetLike.mem_coe, smul_mem_iff_of_isUnit _ (hc_unit.pow _)] at hw

/-- Rigidity of geometric fibres: let `O` be a valuation ring with fraction field ℂ, and `a` a model
of the `O`-point `y` on the complex torus of `Y` (a uniformisation of its group scheme compatible
with the `𝓞 E`-action, level points and theta coordinates). The pull-back `x₀` of `y` along
`χ : O →+* k`, `k` algebraically closed, satisfies `HasSpanningCoords`: on its pull-backs to
noetherian local rings, global functions are constant on fibres and the coordinates span the
sections. A case of the spanning of the sections of an ample bundle by theta functions. -/
lemma New.ThetaObject.TorusModel.hasSpanningCoords_of_specMap_comp_eq {E O W : Type} [Field E]
    [CMBase E] [CommRing O] [ValuativeArc O] [FinComplexSpace W] {D : PEL E} {Z : Scheme}
    {τ : Z ⟶ Spec (CommRingCat.of (NumberField.RingOfIntegers E))} {X : ThetaFamily D Z τ}
    {y : ThetaObject X (Spec ⟨O⟩)} {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ}
    {Y : ThetaTori.PeriodMap D g ℓ W} (a : y.TorusModel Y) {k : Type}
    [Field k] [IsAlgClosed k] (χ : O →+* k) {x₀ : ThetaObject X (Spec (CommRingCat.of k))}
    (hχ : specMap χ ≫ y = x₀) : x₀.HasSpanningCoords := by
  -- Let `x` over `B` be a pull-back of the fibre `x₀` over `k`. Global functions on `x` are
  -- constant on fibres because `x₀` lives over a field. Take `c` large and non-zero in `k`; by
  -- Serre's theorem the coordinates of `N ^ (c ^ 2)` span on `x`, and the trace over the
  -- `c`-torsion then shows that the coordinates of `N` span.
  intro B inst_ring inst_local inst_noetherian x b hx₀
  obtain ⟨ϕ, rfl⟩ : ∃ ϕ : CommRingCat.of k ⟶ CommRingCat.of B, Spec.map ϕ = b := map_surjective b
  have hx : x.IsPullbackAlong (Spec.map (CommRingCat.ofHom χ ≫ ϕ)) y := by
    change Spec.map (CommRingCat.ofHom χ ≫ ϕ) ≫ y = x
    rwa [Spec.map_comp_assoc, hχ]
  have h_cst : HasConstFunctions x.groupScheme.hom :=
    hasConstFunctions_of_isPullback hx₀.isGroupBaseChange.isPullback
  -- Serre's theorem: for `n ≥ m` the monomials of degree `n` in the coordinates span `H⁰(N ^ n)`
  obtain ⟨m, h_serre⟩ :
      ∃ m : ℕ, ∀ n ≥ m, ∀ h : ((x₀.lineBundle.pull hx₀.schemeMap.left).pow n).IsLinearSystem,
        span B (range (coordSection (X := x.groupScheme) h)) = ⊤ :=
    (eventually_span_coordSection x.groupScheme x₀.isProjEmbedding
      hx₀.isGroupBaseChange.isPullback).exists_forall_of_atTop
  -- `m + 1` and `m + 2` differ by `1`, so they are not both zero in `k`
  obtain ⟨c, hmc, hc⟩ : ∃ c > m, (c : k) ≠ 0 := by
    by_cases h_succ : ((m + 1 : ℕ) : k) = 0
    · refine ⟨m + 2, by omega, fun h_two ↦ one_ne_zero (α := k) ?_⟩
      push_cast at h_two h_succ
      linear_combination h_two - h_succ
    · exact ⟨m + 1, by omega, h_succ⟩
  -- the bundle `N ^ (c ^ 2)` of `y`, pulled back to `x`, is the one in Serre's theorem
  have h_pow_eq : (x₀.lineBundle.pull hx₀.schemeMap.left).pow (c ^ 2) =
      (y.lineBundle.pow (c ^ 2)).pull hx.schemeMap.left := by
    rw [← hx₀.lineBundle_eq_pull, hx.lineBundle_pow_eq_pull]
  have h_span : ∀ h : ((y.lineBundle.pow (c ^ 2)).pull hx.schemeMap.left).IsLinearSystem,
      span B (range (coordSection (X := x.groupScheme) h)) = ⊤ := by
    rw [← h_pow_eq]
    exact h_serre (c ^ 2) (by nlinarith)
  -- `c` is a unit in `k`, hence in `B`
  have hc_unit : IsUnit (c : B) := by simpa using hc.isUnit.map ϕ.hom
  exact ⟨h_cst, a.span_coordSection_eq_top_of_isPullbackAlong hx h_cst hmc.ne_zero hc_unit
    (h_span ((a.hasThetaCoords.pow (c ^ 2)).isLinearSystem.pull hx.schemeMap.left))⟩

end RigidFibres

/-! ## The universal family, its fibre powers and points of linear data -/

namespace New

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory NumberField
  Variety ThetaFamily Submodule Matrix ThetaObject Obj Over Fintype nonZeroDivisors TorusModel
  ValuativeArc ThetaTori ModuliPoint Function

attribute [local instance low] Fintype.ofFinite

variable {E : Type} [Field E] [CMBase E]

/-- A universal object for the PEL data D: a theta family 𝒜 → S with S projective and smooth of
relative dimension n - 1 over R, where n = `card D.Index`, and a dense set of complex points of S
whose fibres are uniformised by tori. The points are indexed by pairs a = (f, b) of an analytic
family of tori f and a parameter b; the uniformisations are holomorphic in b on the domain
`f.domain` of f. -/
structure Variety.UniversalFamily (D : PEL E) (R : Subalgebra (𝓞 E) E) where
  /-- The ring `R` is a Dedekind domain. -/
  isDedekindDomain : IsDedekindDomain R
  /-- The base S, a scheme over Spec R. -/
  base : Over (Spec ⟨R⟩)
  /-- The theta family: an abelian scheme 𝒜 = `family.total` over the base S = `base.left`. -/
  family : ThetaFamily D base.left (base.hom ≫ specMap (algebraMap (𝓞 E) R))
  /-- S is projective over `R`. -/
  hasProjEmbedding : HasProjEmbedding base.hom
  /-- S is smooth over `R` of relative dimension n - 1, where n is `card D.Index`. -/
  smooth : SmoothOfRelativeDimension (card D.Index - 1) base.hom
  /-- The complex point of S attached to a pair (f, b) of an analytic family `f` and a parameter
  `b`. -/
  obj : AnalyticFamily D × BallBase D.Index → (specOver R ℂ ⟶ base)
  /-- The fibre over `obj a` is modelled on the torus of the family `a.1` at the parameter `a.2`. -/
  model (a : AnalyticFamily D × BallBase D.Index) :
    TorusModel (X := family) (obj a).left (a.1.torus a.2).toPeriodMap
  /-- The uniformisations give complex points of 𝒜 that are holomorphic in `(b, z)`, for `b` in the
  domain of the family. -/
  holomorphic (f : AnalyticFamily D) : ∀ b ∈ f.domain, ∀ z : BallFibre E D.Index,
    HolomorphicAt
      (fun q ↦
        atGeneric (model (f, q.1)).uniformisation.expMap q.2 ≫ (toFamily (obj (f, q.1)).left).left)
      (b, z)
  /-- The points `obj a` are dense in S. -/
  dense : IsDenseFamily (obj · |>.left)

attribute [instance] UniversalFamily.hasProjEmbedding

variable {D : PEL E} {R : Subalgebra (𝓞 E) E} {κ : Sort _} {ν : ℕ} [Finite κ]
  {T Z : Scheme} {τ : Z ⟶ Spec (CommRingCat.of (𝓞 E))} {X : ThetaFamily D Z τ}
  {O : Type} [CommRing O] [ValuativeArc O] {U : UniversalFamily D R} {𝔪 : (𝓞 E)⁰}
  {y : ThetaObject X T} {Q : κ → (𝟙_ (Over T) ⟶ y.groupScheme)} {a : ModuliPoint E D.Index ν}

/-- Finite products exist in `Over S`: a diagram indexed by the finite discrete category of κ has a
limit. -/
instance {S : Scheme} {F : Discrete κ ⥤ Over S} : HasLimit F := inferInstance

/-! ### Fibre powers and the points of linear data -/

/-- For a finite set κ, the κ-fold fibre power of the abelian scheme `X.total` over its base, as a
scheme over the base. -/
abbrev ThetaFamily.fibrePower (κ : Type) [Finite.{1} κ] : Over Z := ∏ᶜ fun _ : κ ↦ X.total

/-- For i in κ, the i-th projection from the κ-fold fibre power of `X.total` to `X.total`, as a
morphism of underlying schemes. -/
abbrev ThetaFamily.proj (i : κ) : (∏ᶜ fun (_ : κ) ↦ X.total).left ⟶ X.total.left :=
  (Pi.π _ i : X.fibrePower κ ⟶ X.total).left

/-- Let y be an object of the family X over T, and Q i, for i in κ, sections of its group scheme
`y.groupScheme` over T. This is the T-point of the κ-fold fibre power of `X.total` whose i-th factor
is the section Q i followed by the map of y to the family. -/
def ThetaObject.pointOf (y : ThetaObject X T) (Q : κ → (𝟙_ (Over T) ⟶ y.groupScheme)) :
    T ⟶ (X.fibrePower κ).left :=
  (Pi.lift fun i ↦ y.isGroupBaseChange.pointEquiv (Q i)).left

/-- Let a = (x, ℓ, P) be a point at infinite level with ν marked vectors, and t an O-point, over the
arc O, of the fibre power of `X.total` with one factor for each non-zero 𝔪-torsion class and one for
each marked vector. `IsPointOf 𝔪 a t` says that t is the point of an object over O that has a torus
model (`TorusModel`) on a period map for the frame x and the reflection ℓ: its factors are the
torsion points of the model at the non-zero 𝔪-torsion classes and the images of the vectors P i. -/
@[mk_iff]
inductive ThetaFamily.IsPointOf (𝔪 : (𝓞 E)⁰) (a : ModuliPoint E D.Index ν)
    (t : Spec ⟨O⟩ ⟶ (X.fibrePower (NonzeroTorsion 𝔪 D.Index ⊕ Fin ν)).left) : Prop
  /-- Builds `ThetaFamily.IsPointOf` from a torus model `m` of an object `x` over the arc on a
  period map `Y` for `a.frame` and `a.reflection`. It requires a proof that `t` is the point of `x`
  given by the torsion points of `m.fullStructure` and the images under `m.π` of the vectors
  `a.markedPoint`. -/
  | mk {x : ThetaObject X (Spec (CommRingCat.of O))} {V : Type} [FinComplexSpace V]
      {Y : PeriodMap D a.frame a.reflection V} (m : TorusModel x Y)
      (h : t = x.pointOf ((fun s : NonzeroTorsion 𝔪 D.Index ↦ m.fullStructure.torsionPoint s.val) ⊕ᵥ
        (fun i : Fin ν ↦ m.π (a.markedPoint i))))

/-- The point `y.pointOf Q` lies over the base point of y. -/
@[reassoc (attr := simp)]
lemma ThetaObject.pointOf_hom : y.pointOf Q ≫ hom (fibrePower κ) = y := by simp [pointOf]

/-- The i-th factor of `y.pointOf Q` is the section Q i followed by the map of y to the family. -/
@[reassoc (attr := simp)]
lemma ThetaObject.pointOf_proj (i : κ) : y.pointOf Q ≫ proj i = (Q i).left ≫ y.toFamily.left :=
  congrArg Hom.left (Pi.lift_comp_π _ i)

/-- For every point a at infinite level there is a complex point t over R of the fibre power of the
family that is the point of a with its 𝔪-torsion (`New.ThetaFamily.IsPointOf`). -/
lemma Variety.UniversalFamily.exists_isPointOf (U : UniversalFamily D R) (𝔪 : (𝓞 E)⁰)
    (a : ModuliPoint E D.Index ν) :
    ∃ t :
          specOver R ℂ ⟶
            (Over.map U.base.hom) (U.family.fibrePower (NonzeroTorsion 𝔪 D.Index ⊕ Fin ν)),
      U.family.IsPointOf 𝔪 a t.left := by
  -- The point a is the member at the parameter 0 of some analytic family f, and the universal
  -- family carries a model of the fibre at (f, 0).
  obtain ⟨f, hf⟩ := exists_isBallFamily a
  rw [← hf.ballPoint_zero]
  exact ⟨homMk _, U.model (f, 0), rfl⟩

/-- For a point a = (x, ℓ, P) at infinite level, a chosen complex point over R of the fibre power of
the family that is the point of a with its 𝔪-torsion (`New.ThetaFamily.IsPointOf`): an object
modelled on (x, ℓ), with its non-zero 𝔪-torsion points and the images of the vectors P i. -/
def Variety.UniversalFamily.datumPoint (𝔪 : (𝓞 E)⁰) (a : ModuliPoint E D.Index ν) :
    specOver R ℂ ⟶ (Over.map U.base.hom) (U.family.fibrePower (NonzeroTorsion 𝔪 D.Index ⊕ Fin ν)) :=
  (U.exists_isPointOf 𝔪 a).choose

/-- Two T-points of the κ-fold fibre power of `X.total` are equal if and only if they have the same
image in the base Z and the same projection to `X.total` for every i in κ. -/
lemma fibrePower_ext_iff {t t' : T ⟶ (X.fibrePower κ).left} :
    t = t' ↔
      t ≫ (X.fibrePower κ).hom = t' ≫ (X.fibrePower κ).hom ∧ ∀ i : κ, t ≫ proj i = t' ≫ proj i := by
  refine ⟨fun h ↦ by simp [h], ?_⟩
  rintro ⟨h_hom, h_proj⟩
  -- Maps with the same base point are maps over the base into a product, which agree when all
  -- their projections agree.
  have h_over :
      (homMk t h_hom : Over.mk (t' ≫ (X.fibrePower κ).hom) ⟶ X.fibrePower κ) = homMk t' :=
    Pi.hom_ext _ _ fun i ↦ OverMorphism.ext (by simpa using h_proj i)
  exact congrArg (fun f ↦ f.left) h_over

variable {t : Spec ⟨O⟩ ⟶ (X.fibrePower (NonzeroTorsion 𝔪 D.Index ⊕ Fin ν)).left}
  {b : ModuliPoint E D.Index ν} {J : Sort _} [Finite J] {γ : J → (𝓞 E)⁰ × GUPlus E D.Index}
  {s : Spec (CommRingCat.of ℂ) ⟶ (X.fibrePower (NonzeroTorsion 𝔪 D.Index ⊕ Fin ν)).left}
  {u : Spec (CommRingCat.of ℂ) ⟶ (U.family.fibrePower (NonzeroTorsion 𝔪 D.Index ⊕ Fin ν)).left}

/-- Let t be an O-point of the fibre power of `X.total` over the arc O. If its generic point
`genericPt ≫ t` is the point of a with its 𝔪-torsion (`New.ThetaFamily.IsPointOf`), then so is t. -/
lemma ThetaFamily.IsPointOf.of_generic (h_generic : IsPointOf 𝔪 a (genericPt ≫ t)) :
    IsPointOf 𝔪 a t := by
  -- The object `x` behind the generic point is the generic fibre of the object `t ≫ hom _` over
  -- the arc, so its model extends.
  obtain @⟨x, V, hV, Y, m, h_pt⟩ := h_generic
  have h_gen : x.IsPullbackAlong genericPt (t ≫ hom _) := ((reassoc_of% h_pt) _).trans pointOf_hom
  obtain ⟨m', hm'⟩ : ∃ m' : TorusModel (t ≫ hom _) Y, ∀ w : RealVectors E D.Index,
      genericPt ≫ (m'.π w).left = (m.π w).left ≫ h_gen.schemeMap.left :=
    m.exists_torusModel_of_isPullbackAlong h_gen
  -- Two maps from the arc over the base into a separated scheme that agree at the generic
  -- point are equal.
  refine ⟨m', ext_of_isDominant_of_isSeparated (hom _) (by simp) genericPt ?_⟩
  -- Compare the base points and then each factor; torsion sections are values of `π` by
  -- definition, so `hm'` covers both kinds of factor.
  refine fibrePower_ext_iff.mpr ⟨by simp, ?_⟩
  rintro (s | i) <;> simp [h_pt, reassoc_of% hm', h_gen.comp_toFamily, fullStructure, ← π.eq_1]

/-- A matrix over the finite adeles that sends every vector with entries in Ô to a vector with
entries in Ô has its entries in Ô. Vectors with entries in Ô are those whose class in the torsion
module (𝔸f / Ô)ⁿ is zero. -/
lemma mem_Ô_of_torsionClass_mulVec_eq_zero {n : Type} [Fintype n] [DecidableEq n]
    {l : Matrix n n (𝔸f E)}
    (h_zero : ∀ y : n → 𝔸f E, torsionClass y = 0 → torsionClass (l *ᵥ y) = 0) (i j : n) :
    l i j ∈ Ô E := by
  -- Apply `l` to the `j`-th standard basis vector.
  simpa using torsionClass_eq_zero.mp (h_zero (Pi.single j 1)
    (torsionClass_eq_zero.mpr fun k ↦ by simp [Pi.single_apply, ite_mem])) i

/-- Let `k` be an adelic similitude (a member of `GU`) with integral entries and integral inverse,
and `𝔞` a non-zero integer of E. If `k` fixes the class in (𝔸f / Ô)ⁿ of every vector whose class is
killed by `𝔞`, then `k` is congruent to 1 modulo `𝔞`: it lies in the level group `levelGU n 𝔞`. -/
lemma mem_levelGU_of_torsionClass_mulVec_eq {n : Type} [Fintype n] [DecidableEq n]
    {k : GL n (𝔸f E)} {𝔞 : 𝓞 E} (h𝔞 : 𝔞 ≠ 0) (h_sim : k ∈ GU E n) (h_int : k ∈ intGL n (Ô E))
    (h_fix : ∀ y : n → 𝔸f E, 𝔞 • torsionClass y = 0 → torsionClass (k.val *ᵥ y) = torsionClass y) :
    k ∈ levelGU n 𝔞 := by
  refine ⟨h_sim, h_int, fun i j ↦ mem_span_singleton_iff_exists_mul.mpr ?_⟩
  -- Test `h_fix` on the vector `y = 𝔞⁻¹ e_j`, whose class is killed by `𝔞`: the difference
  -- `k y - y = 𝔞⁻¹ (k - 1) e_j` is integral.
  let y : n → 𝔸f E := Pi.single j ((isUnit_algebraMap_finAdele h𝔞).unit⁻¹ : (𝔸f E)ˣ)
  have hy : 𝔞 • torsionClass y = 0 := by
    rw [← map_smul, torsionClass_eq_zero]
    simp [y, ite_mem, Algebra.smul_def, Pi.single_apply]
  refine ⟨(k.val *ᵥ y) i - y i, torsionClass_eq_iff.mp (h_fix y hy) i, ?_⟩
  simp [y, mul_sub, mul_left_comm, Matrix.one_apply, Pi.single_apply]

/-- A matrix `k` in the level group `levelGU n 𝔞`, congruent to 1 modulo `𝔞`, fixes the class in
(𝔸f / Ô)ⁿ of every vector whose class is killed by `𝔞`. -/
lemma torsionClass_mulVec_eq_of_mem_levelGU {n : Type} [Fintype n] [DecidableEq n]
    {k : GL n (𝔸f E)} {𝔞 : 𝓞 E} (hk : k ∈ levelGU n 𝔞) {y : n → 𝔸f E}
    (hy : 𝔞 • torsionClass y = 0) :
    torsionClass (k.val *ᵥ y) = torsionClass y := by
  obtain ⟨-, -, hk_cong⟩ := hk
  -- Write `k = 𝔞 • M + 1` with `M` integral; then `k y = M (𝔞 • y) + y`, and `𝔞 • y` is integral.
  have h_entry : ∀ i j : n, ∃ c ∈ Ô E, (k.val - 1) i j = algebraMap (𝓞 E) (𝔸f E) 𝔞 * c :=
    fun i j ↦ mem_span_singleton_iff_exists_mul.mp (hk_cong i j)
  choose M hM_int hM_eq using h_entry
  have hk_eq : k.val = 𝔞 • Matrix.of M + 1 := eq_add_of_sub_eq (Matrix.ext hM_eq)
  have hy_int : torsionClass (𝔞 • y) = 0 := by rwa [map_smul]
  rw [hk_eq, add_mulVec, smul_mulVec, ← mulVec_smul, map_add,
    torsionClass_mulVec_eq_zero (h := Matrix.of M) hM_int hy_int, zero_add, one_mulVec]

/-- The polarisation form of the PEL data D determines its matrix: matrices β, β' over E with the
same polarisation form are equal. The proof compares the forms on the vectors c eⱼ and (ξ⁻¹)* eᵢ,
and uses that the trace form of E is non-degenerate and that ξ ≠ 0. -/
lemma eq_of_polarisationForm_eq {β β' : Matrix D.Index D.Index E}
    (h_form : ∀ y w : RealVectors E D.Index,
      polarisationForm D β y w = polarisationForm D β' y w) :
    β = β' := by
  have hξ : D.ξ ≠ 0 := fun hξ_zero ↦ by
    simpa [hξ_zero] using D.xi_im_pos_and_re_eq_zero v₀
  ext i j
  refine sub_eq_zero.mp ((traceForm_nondegenerate ℚ E).1 (β i j - β' i j) fun c ↦ ?_)
  simpa [hξ, mul_assoc, mul_comm c, sub_eq_zero] using
    h_form (toRealVectors (Pi.single j c)) (toRealVectors (Pi.single i (star D.ξ⁻¹)))

/-- One direction of `New.ThetaFamily.IsPointOf.eq_iff`: if z in GL_n(E) is an isomorphism of level
K(𝔑) ∩ K(𝔪) from a to b (`b.frame⁻¹ * toFinGL z * a.frame` in both level groups, `ratConj z` taking
a's reflection to b's, `m'.π` equal on z·(a.markedPoint i) and b.markedPoint i) for the torus models
m of x and m' of x', then x = x' and the two models give the same points of the family at the
𝔪-torsion classes and at the marked vectors. -/
lemma ThetaObject.TorusModel.eq_and_comp_toFamily_eq_of_mem_levelGU
    {x x' : ThetaObject X (Spec (CommRingCat.of ℂ))} {V V' : Type} [FinComplexSpace V]
    [FinComplexSpace V'] {Y : PeriodMap D a.frame a.reflection V}
    {Y' : PeriodMap D b.frame b.reflection V'} (m : TorusModel x Y) (m' : TorusModel x' Y')
    {z : GL D.Index E} (h𝔑 : b.frame⁻¹ * toFinGL z * a.frame ∈ levelGU D.Index D.level)
    (h𝔪 : b.frame⁻¹ * toFinGL z * a.frame ∈ levelGU D.Index 𝔪)
      (hz : ratConj z a.reflection = b.reflection)
    (hP : ∀ i : Fin ν, m'.π (realVecAction z (a.markedPoint i)) = m'.π (b.markedPoint i)) :
    x = x' ∧
      (∀ s : AdelicTorsion E D.Index, (𝔪 : 𝓞 E) • s = 0 →
        (m.fullStructure.torsionPoint s).left ≫ x.toFamily.left =
          (m'.fullStructure.torsionPoint s).left ≫ x'.toFamily.left) ∧
      ∀ i : Fin ν,
        (m.π (a.markedPoint i)).left ≫ x.toFamily.left = (m'.π (b.markedPoint i)).left ≫
          x'.toFamily.left := by
  -- An isomorphism z of level K(𝔑) gives a map ψ of multiplier 1 that acts on torsion classes by
  -- the matrix `b.frame⁻¹ z a.frame`.
  have ⟨_, hk_intGL, _⟩ := h𝔑
  obtain ⟨h_base, ψ, hψ_isog, hψ_lin, h_cls, h_ev, hπ⟩ :=
    exists_isogeny z hz m m' rfl hk_intGL.isIntMatrix (levelGU.isScalarFrame_inv_one h𝔑)
  -- A matrix congruent to 1 modulo 𝔞 acts trivially on the 𝔞-torsion.
  have h_tors {𝔞 : 𝓞 E} (hk : b.frame⁻¹ * toFinGL z * a.frame ∈ levelGU D.Index 𝔞) :
      ∀ s ∈ torsionBy (𝓞 E) (AdelicTorsion E D.Index) 𝔞,
        m.fullStructure.torsionPoint s ≫ ψ = m'.fullStructure.torsionPoint s := by
    rintro ⟨y⟩ (hy : 𝔞 • torsionClass y = 0)
    change m.fullStructure.torsionPoint (torsionClass y) ≫ ψ =
      m'.fullStructure.torsionPoint (torsionClass y)
    rw [h_ev, torsionClass_mulVec_eq_of_mem_levelGU hk hy]
  -- ψ respects the pairing (its multiplier is 1) and the level points, so by rigidity it lies
  -- over the family.
  have h_pair : ∀ ⦃S : Over (Spec (CommRingCat.of ℂ))⦄ (y w : S ⟶ x.groupScheme),
      x.lineBundle.picClass.pairing y w = x'.lineBundle.picClass.pairing (y ≫ ψ) (w ≫ ψ) := by
    simp [← pairing_comp, h_cls]
  have h_level_pts : ∀ l : D.levelTorsion, x.levelPoints l ≫ ψ = x'.levelPoints l := fun l ↦ by
    rw [m.fullStructure.levelPoints_eq, m'.fullStructure.levelPoints_eq, h_tors h𝔑 _ l.prop]
  obtain ⟨hx, hp⟩ : x = x' ∧ ψ.left ≫ x'.toFamily.left = x.toFamily.left :=
    (m.hasSpanningCoords_of_specMap_comp_eq (RingHom.id ℂ)
      (by simp [specMap])).eq_and_comp_toFamily_eq_of_hom (Category.id_comp _)
      h_base.symm ψ h_pair h_level_pts
  -- The torsion points and the marked points of the two models now agree in the family.
  exact ⟨hx, fun s hs ↦ by rw [← hp, ← comp_left_assoc, h_tors h𝔪 s hs],
    fun i ↦ by rw [← hp, ← comp_left_assoc, hπ, hP]⟩

/-- Let s and u be complex points of the fibre power of `X.total` that are the points of a and of b
with their 𝔪-torsion (`New.ThetaFamily.IsPointOf`). Then s = u exactly when some z in GL_n(E) is an
isomorphism from a to b at level K(𝔑) ∩ K(𝔪), where 𝔑 is the level of D. -/
lemma ThetaFamily.IsPointOf.eq_iff
    {u : Spec (CommRingCat.of ℂ) ⟶ (X.fibrePower (NonzeroTorsion 𝔪 D.Index ⊕ Fin ν)).left}
    (hs : X.IsPointOf 𝔪 a s) (hu : X.IsPointOf 𝔪 b u) :
    s = u ↔ ∃ z : GL D.Index E, a.IsLevelIso (levelGU D.Index D.level ⊓ levelGU D.Index 𝔪) z b := by
  classical
  -- Both directions translate between maps of modelled objects and rational matrices: a matrix z
  -- comes from the identity map (`exists_matrix_of_hom`), and conversely z gives a map that lies
  -- over the family (`eq_and_comp_toFamily_eq_of_mem_levelGU`).
  -- The level of z is read off from the action of `b.frame⁻¹ * toFinGL z * a.frame` on torsion
  -- classes.
  obtain @⟨x, V, hV, Y, m, rfl⟩ := hs
  obtain @⟨x', V', hV', Y', m', rfl⟩ := hu
  have h_lat (w : RealVectors E D.Index) :
    w ∈ frameLattice b.frame ↔ Y'.realEquiv w ∈ m'.uniformisation.lattice := by
    simp [m'.lattice_eq, mem_classLattice, frameLattice]
  -- s = u says: same base point, same points at the non-zero 𝔪-torsion classes, same marked
  -- points; the level condition says: two level groups, the reflection, the marked points.
  suffices h_iff :
      (x = x' ∧
        (∀ s : AdelicTorsion E D.Index, (𝔪 : 𝓞 E) • s = 0 → s ≠ 0 →
          (m.fullStructure.torsionPoint s).left ≫ x.toFamily.left =
            (m'.fullStructure.torsionPoint s).left ≫ x'.toFamily.left) ∧
        ∀ i : Fin ν,
          (m.π (a.markedPoint i)).left ≫ x.toFamily.left = (m'.π (b.markedPoint i)).left ≫
            x'.toFamily.left) ↔
      ∃ z : GL D.Index E,
        (b.frame⁻¹ * toFinGL z * a.frame ∈ levelGU D.Index D.level ∧
          b.frame⁻¹ * toFinGL z * a.frame ∈ levelGU D.Index 𝔪) ∧
        ratConj z a.reflection = b.reflection ∧
        ∀ i : Fin ν, m'.π (realVecAction z (a.markedPoint i)) = m'.π (b.markedPoint i) by
    simpa [h_lat, ← π.eq_1, fibrePower_ext_iff, isLevelIso_iff, sub_eq_zero] using h_iff
  constructor
  · rintro ⟨rfl, h_tor, hP⟩
    -- A section of the object is determined by its image in the family.
    have p_inj : Injective fun s : 𝟙_ (Over (Spec (CommRingCat.of ℂ))) ⟶ x.groupScheme ↦
        s.left ≫ x.toFamily.left :=
      (Over.forget _).map_injective.comp
        (x.isGroupBaseChange.pointEquiv (T := 𝟙_ (Over (Spec (CommRingCat.of ℂ))))).injective
    -- The identity of the object is induced by a rational matrix z.
    obtain ⟨z, hz_π, hz_form, hz⟩ :=
      m.exists_matrix_of_hom m' (𝟙 x.groupScheme) (hψ := ⟨by simp⟩) one_ne_zero (by simp)
    set k : GL D.Index (𝔸f E) := b.frame⁻¹ * toFinGL z * a.frame
    have hz_tor (y : D.Index → 𝔸f E) :
        m.fullStructure.torsionPoint (torsionClass y) =
          m'.fullStructure.torsionPoint (torsionClass (k.val *ᵥ y)) := by
      simpa [k] using m.torsionPoint_comp m' hz_π y
    -- Equal forms have equal matrices, so k is a similitude: `a.frame` is a frame for
    -- `Y.formMatrix = zᴴ Y'.formMatrix z`, and `b.frame` one for `Y'.formMatrix`.
    have hβ : Y.formMatrix = z.valᴴ * Y'.formMatrix * z :=
      eq_of_polarisationForm_eq fun y w ↦ by simpa using hz_form y w
    have h_sim : k ∈ GU E D.Index := by
      refine ⟨(1 : ℚ), one_pos, ?_⟩
      have h_bx_k : b.frame * k = toFinGL z * a.frame := by simp [k, mul_assoc]
      rw [Rat.cast_one, ← Y'.isFrameFor.mul_iff, one_smul, h_bx_k, ← IsFrameFor.conj_iff, ← hβ]
      exact Y.isFrameFor
    -- `k` and its inverse send integral vectors to integral vectors, so they are integral.
    have h_int : k ∈ intGL D.Index (Ô E) := mem_intGL.mpr
      ⟨mem_Ô_of_torsionClass_mulVec_eq_zero fun y hy ↦
        m'.fullStructure.injective (by simp [← hz_tor, hy]),
      mem_Ô_of_torsionClass_mulVec_eq_zero fun y hy ↦
        m.fullStructure.injective (by simp [hz_tor, hy])⟩
    -- If the two models agree on the 𝔞-torsion, k fixes every class killed by 𝔞, so it is
    -- congruent to 1 modulo 𝔞.
    have h_level {𝔞 : 𝓞 E} (h𝔞 : 𝔞 ≠ 0)
        (h_ev : ∀ s : AdelicTorsion E D.Index, 𝔞 • s = 0 →
          m.fullStructure.torsionPoint s = m'.fullStructure.torsionPoint s) :
        k ∈ levelGU D.Index 𝔞 :=
      mem_levelGU_of_torsionClass_mulVec_eq h𝔞 h_sim h_int fun y hy ↦
        m'.fullStructure.injective ((hz_tor y).symm.trans (h_ev _ hy))
    refine ⟨z, ⟨h_level D.level_ne_zero fun s hs ↦ ?_, h_level (by simp) fun s hs ↦ ?_⟩, hz,
      fun i ↦ ?_⟩
    -- On the 𝔑-torsion both models extend the level points of x.
    · exact (m.fullStructure.levelPoints_eq ⟨s, hs⟩).symm.trans
        (m'.fullStructure.levelPoints_eq ⟨s, hs⟩)
    -- They agree on the 𝔪-torsion: at 0 trivially, elsewhere by `h_tor`.
    · by_cases hs_zero : s = 0
      · simp [hs_zero]
      · exact p_inj (h_tor s hs hs_zero)
    -- `m.π (a.markedPoint i)` is `m'.π (z (a.markedPoint i))` by `hz_π`, and has the image of
    -- `m'.π (b.markedPoint i)` by `hP`.
    · rw [← hz_π, Category.comp_id]
      exact p_inj (hP i)
  · rintro ⟨z, ⟨h𝔑, h𝔪⟩, hz, hP⟩
    obtain ⟨hx, h_tors, h_marked⟩ := m.eq_and_comp_toFamily_eq_of_mem_levelGU m' h𝔑 h𝔪 hz hP
    exact ⟨hx, fun s hs _ ↦ h_tors s hs, h_marked⟩

namespace Variety.UniversalFamily

/-! ### Closures of graphs, smoothness and density -/

/-- For a finite family γ of pairs (𝔪_j, g_j) of a non-zero integer and a similitude whose inverse
has entries in Ô (`GUPlus`), the reduced closure, in a product of fibre powers of the family, of the
tuples (over j) of the points `datumPoint 𝔪_j (a.act g_j)` of the translates of the points a at
infinite level. -/
abbrev GraphClosure (γ : J → (𝓞 E)⁰ × GUPlus E D.Index) (ν : ℕ) : Type 1 :=
  ReducedClosure fun j a ↦ U.datumPoint (ν := ν) (γ j).1 (ModuliPoint.act a (γ j).2)


/-- The chosen point `datumPoint 𝔪 a` is the point of a with its 𝔪-torsion. -/
lemma isPointOf_datumPoint : U.family.IsPointOf 𝔪 a (datumPoint 𝔪 a).left :=
  (U.exists_isPointOf 𝔪 a).choose_spec

/-- The point of a with its 𝔪-torsion is unique: every such point u is
`New.Variety.UniversalFamily.datumPoint 𝔪 a`, as the identity is an isomorphism from a to itself
at every level. -/
lemma IsPointOf.eq_datumPoint (h_pt : U.family.IsPointOf 𝔪 a u) : u = (datumPoint 𝔪 a).left := by
  have h_iso : a.IsLevelIso (levelGU D.Index D.level ⊓ levelGU D.Index 𝔪) 1 a := by
    simp [ratConj, isLevelIso_iff]
  exact (h_pt.eq_iff isPointOf_datumPoint).mpr ⟨1, h_iso⟩

/-- The points attached to a and b with their 𝔪-torsion are equal if and only if a and b are
isomorphic at level K(𝔑) ∩ K(𝔪), where 𝔑 is the level of D. -/
lemma datumPoint_eq_iff :
    U.datumPoint 𝔪 a = datumPoint 𝔪 b ↔
      ∃ z : GL D.Index E, a.IsLevelIso (levelGU D.Index D.level ⊓ levelGU D.Index 𝔪) z b :=
  OverMorphism.ext_iff.trans (isPointOf_datumPoint.eq_iff isPointOf_datumPoint)

/-- The abelian scheme of a theta family is projective over the base, by its embedding. -/
instance : HasProjEmbedding X.total.hom := ⟨X.embeds⟩

/-- A fibre power of the abelian scheme of a theta family is projective over the base. -/
instance : HasProjEmbedding (X.fibrePower κ).hom := .of_isClosedImmersion_pi (𝟙 _)

/-- The closure `C.scheme` is projective over the base, as a closed subscheme of a product of fibre
powers. -/
instance (C : U.GraphClosure γ ν) : HasProjEmbedding C.scheme.hom := .of_isClosedImmersion_pi C.incl

/-- There is a level m such that the point of the closure C attached to a depends only on the
isomorphism class of a at level K(m). -/
lemma GraphClosure.exists_level_point_eq (C : U.GraphClosure γ ν) :
    ∃ m : (𝓞 E)⁰, ∀ {a b : ModuliPoint E D.Index ν} {z : GL D.Index E},
      ModuliPoint.IsLevelIso (levelGU D.Index m) z a b → C.point a = C.point b := by
  classical
  -- Take a level `m` so deep that every `γ j` conjugates `K(m)` into `K(𝔑) ⊓ K((γ j).1)`.
  obtain ⟨m, hm⟩ := exists_level_conj_mem D.level_ne_zero (Finset.image γ Finset.univ)
  refine ⟨m, fun {a b z} h_iso ↦ C.hom_ext fun j ↦ ?_⟩
  -- Then `z` is also an isomorphism of the translates by `γ j` at that level.
  have h_iso_γ : IsLevelIso (levelGU D.Index D.level ⊓ levelGU D.Index (γ j).1) z (a.act (γ j).2)
      (b.act (γ j).2) := by
    constructor
    · simpa [mul_assoc, act] using hm (γ j) (by simp) _ h_iso.mem_level
    · exact h_iso.reflection_eq
    · intro i
      -- the inverse of `(γ j).2` is integral, so `(γ j).2` enlarges the lattice
      obtain ⟨-, (h_int : ∀ k l : D.Index, ((γ j).2 : GL D.Index (𝔸f E))⁻¹ k l ∈ Ô E)⟩ :=
        (γ j).2.prop
      simpa [act] using
        realVecAction_mem_frameLattice (A := 1) (by simpa using h_int) (h_iso.sub_mem_lattice i)
  rw [C.point_comp_proj, C.point_comp_proj]
  exact datumPoint_eq_iff.mpr ⟨z, h_iso_γ⟩

/-- For κ with m elements, the κ-fold fibre power of the abelian scheme 𝒜 over the base S is smooth
over S of relative dimension m times the dimension of 𝒜 (`New.Variety.abelianDim`). -/
lemma smooth_fibrePower {m : ℕ} (e : κ ≃ Fin m) :
    SmoothOfRelativeDimension (m * abelianDim E D.Index) (U.family.fibrePower κ).hom := by
  -- Build one `m`-fold product by induction, one binary product at a time.
  obtain ⟨F, hF⟩ : ∃ F : LimitCone (Discrete.functor fun _ : Fin m ↦ U.family.total),
      SmoothOfRelativeDimension (m * abelianDim E D.Index) F.cone.pt.hom := by
    clear e
    induction m with
    | zero =>
      refine ⟨⟨Fan.mk (𝟙_ _) nofun, .mk fun s ↦ toUnit s.pt⟩, ?_⟩
      simpa using (inferInstance : SmoothOfRelativeDimension 0 (𝟙 _))
    | succ m ih =>
      obtain ⟨F, hF⟩ := ih
      refine ⟨⟨_, extendFanIsLimit _ F.isLimit (tensorProductIsBinaryProduct ..)⟩, ?_⟩
      -- the structure map is a base change of that of `U.family.total` followed by that of `F`
      simpa [extendFan, add_mul, pullback.condition, add_comm] using (inferInstance :
        SmoothOfRelativeDimension (abelianDim E D.Index + m * abelianDim E D.Index)
          (pullback.snd U.family.total.hom F.cone.pt.hom ≫ F.cone.pt.hom))
  -- The chosen product is isomorphic to it over the base.
  let i : U.family.fibrePower κ ≅ F.cone.pt :=
    Pi.reindex e (fun _ ↦ U.family.total) ≪≫ limit.isoLimitCone F
  simpa using smoothOfRelativeDimension_comp 0 (f := i.hom.left) (hg := hF)

/-- At level `1` there is no non-zero torsion class, so the fibre power with one factor for each
of `ν` marked vectors is smooth of relative dimension `ν` times that of 𝒜. -/
private lemma smoothOfRelativeDimension_fibrePower_one (ν : ℕ) :
  SmoothOfRelativeDimension (ν * abelianDim E D.Index)
    (U.family.fibrePower (NonzeroTorsion (E := E) 1 D.Index ⊕ Fin ν)).hom := by
  have h_empty : IsEmpty (NonzeroTorsion (E := E) 1 D.Index) := ⟨by simp⟩
  exact smooth_fibrePower (Equiv.emptySum _ _)

/-- The fibre power of 𝒜 with one factor for each of `ν` marked vectors is smooth over `R` of
relative dimension `card D.Index - 1 + ν * abelianDim`. -/
lemma smoothOfRelativeDimension_fibrePower (ν : ℕ) :
    SmoothOfRelativeDimension (card D.Index - 1 + ν * abelianDim E D.Index)
      ((Over.map U.base.hom)
        (U.family.fibrePower (NonzeroTorsion (E := E) 1 D.Index ⊕ Fin ν))).hom := by
  -- relative dimensions add up in the composite with the structure map of the base
  rw [Nat.add_comm]
  exact smoothOfRelativeDimension_comp (hf := smoothOfRelativeDimension_fibrePower_one ν)
    (hg := U.smooth) ..

/-- The points `datumPoint 1 a` of the points `a` at infinite level with `ν` marked vectors are
dense in the fibre power of 𝒜 with one factor for each marked vector. -/
lemma isDenseFamily_datumPoint (ν : ℕ) :
    IsDenseFamily fun a : ModuliPoint E D.Index ν ↦ (U.datumPoint 1 a).left := by
  -- The base points from `U.dense`, indexed by pairs `(f, p)`, are dense. A point `y` above the
  -- base point of `(f, p)` is a tuple of points of its fibre, each the image of a vector `P i`.
  have h_empty : IsEmpty (NonzeroTorsion (E := E) 1 D.Index) := ⟨by simp⟩
  refine U.dense.of_fibres _ (s := (smoothOfRelativeDimension_fibrePower_one ν).smooth) fun ⟨f, p⟩ y
    hy ↦ ?_
  obtain ⟨P, hP⟩ : ∃ P : Fin ν → BallFibre E D.Index, ∀ i : Fin ν,
      (U.model (f, p)).uniformisation.expMap (P i) =
        (ThetaObject.isGroupBaseChange _).pointEquiv.symm (homMk (y ≫ U.family.proj (.inr i))) :=
    Classical.skolem.mp fun i ↦ (U.model (f, p)).uniformisation.surjective _
  -- `y` is the point of the datum `f.ballPoint 0 (p, P)`: it lies over the base point of
  -- `(f, p)`, there is no non-zero 1-torsion class, and its `i`-th factor is the image of `P i`
  have h_pt : U.family.IsPointOf 1 (f.ballPoint 0 (p, P)) y := by
    refine ⟨U.model (f, p), fibrePower_ext_iff.mpr ⟨by rwa [pointOf_hom], ?_⟩⟩
    rintro (s | i)
    · exact isEmptyElim s
    · simp [π, IsGroupBaseChange.pointEquiv, hP i]
  exact ⟨f.ballPoint 0 (p, P), (IsPointOf.eq_datumPoint h_pt).symm⟩

/-- There is, for each family `α` of integers of `E`, a self-map `m α` of the fibre power of 𝒜
with one factor for each of `ν` marked vectors that sends `datumPoint 1 (a.act g)` to
`datumPoint 1 (a.act g α)`. -/
lemma exists_comp_datumPoint_act (ν : ℕ) :
    ∃ m : (Fin ν → 𝓞 E) →
        ((Over.map U.base.hom) (U.family.fibrePower (NonzeroTorsion (E := E) 1 D.Index ⊕ Fin ν)) ⟶
          (Over.map U.base.hom) (U.family.fibrePower (NonzeroTorsion (E := E) 1 D.Index ⊕ Fin ν))),
      ∀ (g : GUPlus E D.Index) (α : Fin ν → 𝓞 E) (a : ModuliPoint E D.Index ν),
        U.datumPoint 1 (ModuliPoint.act a g) ≫ m α = U.datumPoint 1 (a.act g α) := by
  -- `m α` multiplies the factor of the `i`-th marked point by `α i` and the other factors by `1`.
  -- A model at `a.act g` is also one at `a.act g α` (same frame and reflection), and its
  -- `𝓞 E`-linear uniformisation turns the new marked points into the scaled factors.
  refine ⟨fun α ↦ (Over.map _).map (Limits.Pi.map fun i ↦ Sum.elim (fun _ ↦ 1) α i • 𝟙 _),
    fun g α a ↦ ?_⟩
  obtain ⟨model, h_pt⟩ := U.isPointOf_datumPoint (𝔪 := 1) (a := a.act g)
  ext
  refine IsPointOf.eq_datumPoint ⟨model, (h_pt =≫ _).trans ?_⟩
  refine congrArg Hom.left (Pi.hom_ext (_ ≫ _) _ ?_)
  rintro (s | i) <;> simp [π, model.equivariant, act]

/-- Let Z be the fibre power of 𝒜 with one factor for each of ν marked vectors, over R, and
`c a = datumPoint 1 a`. Then (a) Z is smooth over R of relative dimension
`card D.Index - 1 + ν * abelianDim`; (b) the points `c a` are dense in Z; (c) for each family α of
integers of E a self-map `m α` of Z sends `c (a.act g)` to `c (a.act g α)`. -/
lemma smooth_and_isDenseFamily_and_exists_comp_eq_act (ν : ℕ) :
    let Z := (Over.map U.base.hom) (fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin ν))
    let c : ModuliPoint E D.Index ν → (specOver R ℂ ⟶ Z) := datumPoint 1
    -- (a)
    SmoothOfRelativeDimension (card D.Index - 1 + ν * abelianDim E D.Index) Z.hom ∧
    -- (b)
    IsDenseFamily (fun a : ModuliPoint E D.Index ν ↦ (c a).left) ∧
    -- (c)
    ∃ m : (Fin ν → 𝓞 E) → (Z ⟶ Z), ∀ (g : GUPlus E D.Index) (α : Fin ν → 𝓞 E)
        (a : ModuliPoint E D.Index ν),
      c (ModuliPoint.act a g) ≫ m α = c (a.act g α) :=
  ⟨smoothOfRelativeDimension_fibrePower ν, isDenseFamily_datumPoint ν, exists_comp_datumPoint_act ν⟩

end Variety.UniversalFamily


end New

end
