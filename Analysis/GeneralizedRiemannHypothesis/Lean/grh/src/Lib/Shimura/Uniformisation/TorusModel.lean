import Lib.Shimura.AbelianScheme.IsogenyFlatness
import Lib.Shimura.ArcExtension
import Lib.Shimura.ThetaModuli.ThetaFamilyRigidity
import Lib.Shimura.Uniformisation.AppellHumbert
import Lib.Shimura.Uniformisation.BallModel
import Lib.Shimura.Uniformisation.LieExponential

/-!
# Objects modelled on complex tori and their homomorphisms as rational matrices

This file models the objects of a PEL family `X` (`New.ThetaFamily`) over a valuation ring with
fraction field ℂ on complex tori `V` modulo a lattice given by a polarised period map. It then
describes homomorphisms of modelled objects by matrices `z ∈ GL_n(E)`.

## Main definitions and results

* `New.ThetaObject.TorusModel`: `y.groupScheme` is uniformised by `V` modulo that lattice, with
  theta coordinates.
* `New.ThetaTori.PeriodMap.exists_uniformisation_of_isSeparatingFamily`: a dense map given by theta
  functions is a uniformisation.
* `New.ThetaObject.TorusModel.fullStructure`: a model trivialises all torsion, compatibly with the
  Weil pairing. `New.ThetaObject.TorusModel.exists_unit_on_roots_of_unity` supplies the unit of Ẑ
  through which a ring homomorphism `O → ℂ` acts on roots of unity.
* `New.ThetaObject.TorusModel.exists_isTranslationLift_of_dualLattice` (with its parts
  `New.ThetaObject.TorusModel.card_nsmul_mem_of_mem_dualLattice` and
  `New.ThetaObject.TorusModel.exists_isTranslationLift_of_mem_dualLattice`),
  `New.ThetaObject.TorusModel.multiplier_eq_canonicalMultiplier`: translations by the dual lattice
  lift to `y.lineBundle`, and the multiplier of the theta coordinates is the canonical one.
* `New.ThetaObject.TorusModel.exists_matrix_of_hom`: a linear `ψ` of multiplier `μ ≠ 0` comes from a
  `z`.
* `New.ThetaObject.TorusModel.exists_isIsogenyOfMatrix`,
  `New.ThetaObject.TorusModel.exists_isogeny`: a `z` with `z ℓ z⁻¹ = ℓ'` and `g'⁻¹ z g` an integral
  similitude of multiplier `μ` gives an isogeny (`New.ThetaObject.TorusModel.IsIsogenyOfMatrix`);
  objects with models have the same map from `𝓞 E`
  (`New.ThetaObject.TorusModel.baseHom_eq_baseHom`).

Notions from other files:
* `New.ThetaTori.PeriodMap`: the linear part of a model: a real isomorphism Q from (E ⊗ ℝ)ⁿ onto V,
  a form β with frame g, and a form B on V whose Riemann form pulls back to
  `New.Variety.polarisationForm`.
* `New.Variety.frameCoords`: the map y ↦ g⁻¹y from Eⁿ to n-tuples of finite adeles.
* `New.Variety.realVecAction`: the action of a matrix A over E on (E ⊗ ℝ)ⁿ, through Φ_v(A) at the
  infinite place v.

## Relation to the literature

Known; see `Lib.Shimura.Uniformisation.AppellHumbert` and `Lib.Shimura.ThetaModuli.UniversalFamily`
for sources.
-/

/-!
## Theta uniformisation, Weil pairing and canonical multiplier

Complex tori as models of the objects of a PEL family `X` (`New.ThetaFamily`). An object `y` over a
valuation ring `O` with fraction field ℂ (`New.ValuativeArc`) is an `O`-point of the base of `X`. It
carries an abelian scheme `y.groupScheme`, a linear system `y.lineBundle` and level points
`y.levelPoints`. A polarised period map (`New.ThetaTori.PeriodMap`) is an isomorphism
`Q : (E ⊗ ℝ)ⁿ ≃ V` with a form `B`. Its lattice consists of the `Q (toRealVectors z)` for `z ∈ Eⁿ`
with `g⁻¹ z` integral.
-/

namespace New

open CategoryTheory Complex LinearMap Submodule NumberField LineBundle Variety ThetaTori Set
  AlgebraicGeometry Polynomial AddChar IsIntegrallyClosed

variable {E : Type} [Field E] [CMBase E]
  {D : PEL E} {Z : Scheme} {τ : Z ⟶ Spec (CommRingCat.of (𝓞 E))} {X : ThetaFamily D Z τ}
  {O : Type} [CommRing O] [ValuativeArc O] (y : ThetaObject X (Spec ⟨O⟩))
  {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ} {V : Type} [FinComplexSpace V]
  (Y : PeriodMap D g ℓ V)

/-- The object `y` is modelled on the torus of the polarised period map `Y` onto `V`. The model is a
uniformisation of `y.groupScheme` by `V`. It is compatible with the action of `𝓞 E` and the level
points. Its kernel is the period lattice. Along it, `y.lineBundle` has theta coordinates. -/
structure ThetaObject.TorusModel where
  /-- The map `𝓞 E → O → ℂ` is the embedding `Φ v₀`. -/
  baseHom_eq (c : 𝓞 E) : algebraMap O ℂ (y.baseHom c) = Φ v₀ c.val
  /-- The uniformisation of `y.groupScheme` by `V`. -/
  uniformisation : Uniformisation y.groupScheme V
  /-- The multiplier of the theta coordinates. -/
  χ : V → ℂ
  /-- The theta coordinates, indexed by `D.dualTorsion`. -/
  θ : V → D.dualTorsion → ℂ
  /-- Along the uniformisation, `θ` are coordinates of `y.lineBundle` and theta functions of type
  `(B, χ)`. -/
  hasThetaCoords :
      HasThetaCoords uniformisation.lattice (atGeneric uniformisation.expMap) y.lineBundle
        Y.automorphyForm χ θ
  /-- The composite of `Q` and the uniformisation commutes with the action of `𝓞 E`. -/
  equivariant (c : 𝓞 E) (w : RealVectors E D.Index) :
      uniformisation.expMap (Y.realEquiv (cmEmbedding c.val • w)) = c • uniformisation.expMap
        (Y.realEquiv w)
  /-- The level points are the images of the chosen rational vectors. -/
  level_eq (l : D.levelTorsion) : y.levelPoints l = uniformisation.expMap (Y.torsionLift l)
  /-- The kernel of the uniformisation is the period lattice. -/
  lattice_eq : uniformisation.lattice = Y.periodLattice

/-- Let `A` be an abelian scheme over `ℂ` embedded in projective space by `N`, and let
`e : V → A(ℂ)` be additive with image dense in the reduced scheme `A`, killing `Y.periodLattice`,
along which `N` has theta coordinates `Y.thetaCoord` of type `(Y.automorphyForm, Y.multiplier)`. Let
`u` be a uniformisation of `A` by `W` along which `N` has theta coordinates of type `(B', χ')`, and
let `F : V → W` be complex linear with `u.expMap ∘ F = e`, pulling the Riemann form of `B'` back to
that of `Y.automorphyForm`. If a line bundle `M` has theta coordinates of type `(B', χ)` along `u`
and `χ ∘ F = Y.multiplier` on `Y.periodLattice`, then `χ = χ'` on `u.lattice`. -/
lemma ThetaTori.PeriodMap.multiplier_eq_of_pullback {A : Over (Spec (CommRingCat.of ℂ))} {W : Type}
    {N M : LineBundle A.left D.dualTorsion} {χ χ' : W → ℂ} {θ θ' : W → D.dualTorsion → ℂ}
    [IsAbelianScheme A] [FinComplexSpace W] (hN : IsProjEmbedding N A.hom)
    {e : V →+ ComplexPoint A} (h_sep : IsSeparatingFamily (atGeneric e))
    (hY : HasThetaCoords Y.periodLattice (atGeneric e) N Y.automorphyForm Y.multiplier
      (flip Y.thetaCoord))
    (h_kill : ∀ l ∈ Y.periodLattice, e l = 0)
    {u : Uniformisation A W} {B' : LatticeForm u.lattice}
    (hu : HasThetaCoords u.lattice (atGeneric u.expMap) N B' χ' θ')
    {F : V →L[ℂ] W} (hF : ∀ z : V, u.expMap (F z) = e z)
    (h_riem : RealComplexForm.riemannForm (B'.pullForm F) = Y.automorphyForm.riemannForm)
    (hM : HasThetaCoords (ι := D.dualTorsion) u.lattice (atGeneric u.expMap) M B' χ θ)
    (hχ : ∀ l ∈ Y.periodLattice, χ (F l) = Y.multiplier l) (l : W) (hl : l ∈ u.lattice) :
    χ l = χ' l := by
  -- The coordinates of `M`, pulled back by `F` and normalised, are sections of `N`; together they
  -- form a section of `N ⊗ M⁻¹`, which is a theta function `G` of type `(0, χ' / χ)` along `u`.
  -- Such a `G` is constant on lines through `0` and `G 0 ≠ 0`; so `χ' / χ` is `1` on `u.lattice`.
  have h_lifts (z : V) : N.IsHomogeneousCoords (e z).left fun i : D.dualTorsion ↦
    Y.thetaCoord i z :=
    hY.hasFieldCoords z
  have h_pull {M : LineBundle A.left D.dualTorsion} {χ : W → ℂ} {θ : W → D.dualTorsion → ℂ}
      (hM : HasThetaCoords (ι := D.dualTorsion) u.lattice (atGeneric u.expMap) M B' χ θ) :
      HasThetaCoords Y.periodLattice (fun z : V ↦ (e z).left) M (B'.pullForm F) (χ ∘ F) (θ ∘ F) :=
    hM.pull F (f := 𝟙 _) (fun z ↦ congrArg CommaMorphism.left (hF z))
      fun l hl ↦ by rw [u.eq_zero_iff, hF, h_kill l hl]
  -- Evaluation along `e` sends sections of `N` to functions on `V`, and the coordinates to
  -- `Y.thetaCoord`.
  obtain ⟨ev, h_ev, h_ev_coord, -⟩ := exists_theta_evaluation hY
  -- The range of `ev` contains the translates of `Y.thetaCoord 0` by the dual lattice
  -- (`Y.thetaShift_thetaCoord`), so by irreducibility it contains every theta function of type
  -- `(Y.automorphyForm, Y.multiplier)`.
  have h_range : Y.automorphyForm.thetaSpace Y.multiplier ≤ ev.range := by
    refine Y.isAppellHumbert_periodLattice.thetaSpace_le_of_thetaShift_mem
      (Y.thetaCoord_mem_thetaSpace 0) (Y.thetaCoord_ne_zero 0) ev.range ?_
    rw [Y.dualLattice_periodLattice]
    rintro _ ⟨w, hw, rfl⟩
    change Y.automorphyForm.thetaShift (Y.periodPoint w) (Y.thetaCoord 0) ∈ ev.range
    rw [Y.thetaShift_thetaCoord (s := ⟨_, hw⟩) rfl 0]
    exact ev.range.smul_mem _ ⟨_, h_ev_coord _⟩
  -- The normalised pull-backs of the coordinates of `M` are such theta functions, so they come
  -- from sections `σ a` of `N`.
  let q (z : V) : ℂ := exp ((Y.automorphyForm z z - B'.pullForm F z z) / 2)
  have h_mem_range (a : D.dualTorsion) : (fun z : V ↦ q z * (θ ∘ F) z a) ∈ ev.range :=
    h_range <| (h_pull hM).isAppellHumbert.exp_mul_mem_thetaSpace Y.isAppellHumbert_periodLattice
      h_riem
      hχ ((h_pull hM).mem_thetaSpace a)
  choose σ hσ using h_mem_range
  have hσ_val (a i : D.dualTorsion) (z : V) (hz : Y.thetaCoord i z ≠ 0) :
      (σ a).val i (CommRingCat.of ℂ) (e z).left = q z * θ (F z) a / Y.thetaCoord i z :=
    (h_ev (σ a) _).mp (hσ a) i z hz
  -- By density of the points `e z`, the `σ a` transform in `a` by the cocycle of `M`; so they
  -- glue to a section of `N ⊗ M⁻¹`, given on `u` by a theta function `G` of type `(0, χ' / χ)`.
  have h_reg (p : D.dualTorsion × D.dualTorsion) :
    PointFn.IsRegularOn ((σ p.2).val p.1) ((N.mul M.inv).opens p) :=
    -- The components of a section are regular on their charts.
    ((σ p.2).prop.left.left p.1).mono inf_le_left
  have h_sec : (N.mul M.inv).IsSection fun p : D.dualTorsion × D.dualTorsion ↦ (σ p.2).val p.1 := by
    refine ⟨h_reg, fun p p' R x hp hp' ↦ h_sep.pointFn_ext ((h_reg p).mono (by order))
      (.mul (regular ..) (h_reg p')) ?_ R x (by simp_all)⟩
    -- At the points `e z` both sides are computed from `hσ_val` and the coordinates of `N`, `M`.
    simp +contextual [h_lifts .., hσ_val, (h_pull hM).hasFieldCoords .., field]
  obtain ⟨G, hG, hG_val⟩ := hu.exists_theta_of_isSection hM h_sec (hu.holomorphicAt hN)
    fun l hl z p ↦ by rw [u.atGeneric_add_of_mem l hl z]
  -- `G` has no zero on the image of `F`: where `Y.thetaCoord i z` and `θ (F z) a` are nonzero, the
  -- value of `σ a` is nonzero by `hσ_val` and a multiple of `G (F z)` by `hG_val`.
  have hG_ne (z : V) : G (F z) ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i : D.dualTorsion, Y.thetaCoord i z ≠ 0 := (h_lifts z).exists_ne_zero
    obtain ⟨a, ha⟩ : ∃ i : D.dualTorsion, (θ ∘ F) z i ≠ 0 :=
      ((h_pull hM).hasFieldCoords z).exists_ne_zero
    -- Both systems of coordinates are units exactly on the same chart `i`.
    have hi' : θ' (F z) i ≠ 0 := by
      obtain ⟨h_lands_iff, -⟩ := h_lifts z i
      obtain ⟨h_lands_iff', -⟩ := (h_pull hu).hasFieldCoords z i
      exact (h_lands_iff'.mp (h_lands_iff.mpr hi.isUnit)).ne_zero
    intro h_zero
    apply ha
    simpa [h_zero, hσ_val, hF, hi, q] using hG_val i a (F z) hi'
  -- The form `B' - B'` of `G` is zero, so `G` is constant on lines through `0`; its functional
  -- equation at `0` then forces the multiplier `χ' l / χ l` to be `1`.
  have hG_const : G l = G 0 := by
    simpa using
      (hu.isAppellHumbert.add hM.isAppellHumbert.neg).apply_smul_of_nonpos hG l (by simp) 1
  have hG_zero : G 0 ≠ 0 := by simpa using hG_ne 0
  obtain ⟨-, hG_shift⟩ : Differentiable ℂ G ∧ ∀ l ∈ u.lattice, ∀ z : W,
      G (z + l) = (χ' * χ⁻¹) l * Complex.exp ((B' + -B') l z + (B' + -B') l l / 2) * G z := hG
  simpa [hG_const, hG_zero, hM.isAppellHumbert.ne_zero hl, field, eq_comm] using hG_shift l hl 0

/-- Let `A` be an abelian scheme over `ℂ`, smooth of relative dimension `d`, embedded in projective
space by `N` whose class satisfies the parallelogram law. Let the homomorphism `e : V → A(ℂ)` have
dense image in `A` (with `A` reduced), kill `Y.periodLattice` and carry `Y.thetaCoord` as
homogeneous coordinates. Then there is a uniformisation `u` of `A` by `V` with (a) theta coordinates
`Y.thetaCoord` of type `(Y.automorphyForm, Y.multiplier)`, (b) map `e` and kernel `Y.periodLattice`;
and (c) `d = New.Variety.abelianDim E D.Index`, which is `|D.Index|` times the number of infinite
places of `E`. -/
lemma ThetaTori.PeriodMap.exists_uniformisation_of_isSeparatingFamily
    {A : Over (Spec (CommRingCat.of ℂ))}
    {N : LineBundle A.left D.dualTorsion} [IsAbelianScheme A] (d : ℕ)
    (h_smooth : SmoothOfRelativeDimension d A.hom) (hN : IsProjEmbedding N A.hom)
    (h_par : N.picClass.ParallelogramLaw)
    (e : V →+ ComplexPoint A) (h_sep : IsSeparatingFamily (atGeneric e))
    (h_lifts : ∀ z : V, N.IsHomogeneousCoords (e z).left fun i : D.dualTorsion ↦ Y.thetaCoord i z)
    (h_kill : ∀ l ∈ Y.periodLattice, e l = 0) :
    ∃ u : Uniformisation A V,
      HasThetaCoords u.lattice (atGeneric u.expMap) N Y.automorphyForm Y.multiplier
        (flip Y.thetaCoord) ∧
      u.expMap = e ∧
      u.lattice = Y.periodLattice ∧
      d = abelianDim E D.Index := by
  -- Take any uniformisation `u` of `A`, with theta coordinates of type `(B', χ')`, and the linear
  -- lift `F` of `e`. It pulls the Riemann form of `B'` back to that of `Y.automorphyForm`. The main
  -- step shows that a vector dual to `F Y.periodLattice` is dual to all of `u.lattice`; it follows
  -- that `F` is bijective and that `Y.periodLattice` is the kernel of `e = u.expMap ∘ F`, so `e` is
  -- itself a uniformisation.
  obtain ⟨u⟩ : Nonempty (Uniformisation A (Fin d → ℂ)) := hN.nonempty_uniformisation h_smooth
  have hY : HasThetaCoords Y.periodLattice (atGeneric e) N Y.automorphyForm Y.multiplier
    (flip Y.thetaCoord) :=
    .mk hN.isLinearSystem Y.isAppellHumbert_periodLattice Y.thetaCoord_mem_thetaSpace h_lifts
  obtain ⟨B', χ', θ', hu, h_pos⟩ := u.appell_humbert hN h_par
  obtain ⟨F, hF⟩ := u.universal e (hY.holomorphicAt hN 0)
  -- Along `e`, `N` now has two systems of theta coordinates; so their Riemann forms agree
  -- (`h_riem`), and so do their multipliers on `Y.periodLattice` (`hχ'`).
  have hF_mem : ∀ l ∈ Y.periodLattice, F l ∈ u.lattice := fun l hl ↦ by
    rw [u.eq_zero_iff, hF, h_kill l hl]
  have h_pull : HasThetaCoords Y.periodLattice (atGeneric e) N (B'.pullForm F) (χ' ∘ F) (θ' ∘ F) :=
    hu.pull F (f := 𝟙 _) (fun z ↦ congrArg CommaMorphism.left (hF z)) hF_mem
  -- `N ⊗ N⁻¹` has a frame, as the class of `N` is equal to itself.
  obtain ⟨w, h_frame⟩ := picClass_eq_iff.mp (rfl : N.picClass = N.picClass)
  obtain ⟨h_riem, hχ', -⟩ := h_pull.riemannForm_eq_of_isFrame hY h_frame (hY.holomorphicAt hN)
    fun l hl ↦ atGeneric_add_of_map_eq_zero e (h_kill l hl)
  -- Main step: the translate of `N` by `u.expMap b` has multiplier `χ' l * B'.riemannPhase l b`, so
  -- by `multiplier_eq_of_pullback` a vector dual to `F Y.periodLattice` is dual to `u.lattice`.
  have h_dual (b : Fin d → ℂ) (hb : ∀ l ∈ Y.periodLattice, B'.riemannPhase (F l) b = 1)
      (l : Fin d → ℂ) (hl : l ∈ u.lattice) : B'.riemannPhase l b = 1 := by
    simpa [hu.isAppellHumbert.ne_zero hl] using
      Y.multiplier_eq_of_pullback hN h_sep hY h_kill hu hF h_riem
        (hu.pull_translate (u.atGeneric_add b)) (by aesop) l hl
  -- `F` is bijective: with `T b = B'.riemannForm (F ·) b`, the map `T ∘ F` is bijective since the
  -- pulled-back form is nondegenerate, and `T` is injective: the real subspace `ker T` pairs
  -- integrally, hence trivially, with `u.lattice`, which spans, and `B'.riemannForm` is
  -- nondegenerate.
  let T : (Fin d → ℂ) →ₗ[ℝ] V →ₗ[ℝ] ℝ := (B'.riemannForm ∘ₗ F.toLinearMap.restrictScalars ℝ).flip
  have h_nondeg : (RealComplexForm.riemannForm (B'.pullForm F)).Nondegenerate := by
    simpa only [h_riem] using Y.isPosRiemann.nondegenerate (L := Y.periodLattice)
  have hTF : Function.Bijective (T ∘ F) := (BilinForm.toDual _ h_nondeg.flip).bijective
  have hT : Function.Injective T := by
    rw [← ker_eq_bot, eq_bot_iff, ← h_pos.nondegenerate.flip.ker_eq_bot]
    refine le_ker_iff_comp_subtype_eq_zero.mpr
      (flip_inj (ext_on (IsZLattice.span_top (L := u.lattice)) fun l hl ↦ ?_))
    refine eq_zero_of_forall_fourierChar_eq_one _ fun ⟨b, hb⟩ ↦ ?_
    have hb_dual : ∀ l ∈ Y.periodLattice, B'.riemannPhase (F l) b = 1 := by
      simp_all [T, LinearMap.ext_iff]
    exact h_dual b hb_dual l hl
  let F_equiv : V ≃ₗ[ℂ] (Fin d → ℂ) := .ofBijective F.toLinearMap (.of_comp_left hTF hT)
  have he : ⇑e = u.expMap ∘ F_equiv := (funext hF).symm
  -- If `e z = 0` then `F z ∈ u.lattice` pairs integrally with `F y` for `y` in the dual of
  -- `Y.periodLattice`; so `z` pairs integrally with that dual, and `z ∈ Y.periodLattice`.
  have h_ker (z : V) (hz : e z = 0) : z ∈ Y.periodLattice := by
    have hFz_mem : F z ∈ u.lattice := by rw [u.eq_zero_iff, hF, hz]
    refine Y.isPosRiemann.isDualFamily.mem_of_forall_eq_one z fun y ↦ ?_
    have h_dual_y : ∀ l ∈ Y.periodLattice, B'.riemannPhase (F l) (F y) = 1 := fun l hl ↦ by
      simpa [← h_riem, riemannForm_pullForm] using (Y.isPosRiemann.isDualFamily.periodic y).2 l hl 0
    rw [← h_riem]
    exact h_dual (F y) h_dual_y (F z) hFz_mem
  -- Immersivity and the universal property pass from `u.expMap` to `e` along the isomorphism `F`.
  have h_imm (z v : V) (hv : IsFirstOrderConst (atGeneric e) z v) : v = 0 := by
    obtain ⟨h_hol, h_only_zero⟩ := u.immersive (F z)
    rw [he] at hv
    have h_Fv : IsFirstOrderConst (atGeneric u.expMap) (F z) (F v) :=
      (isJet_comp_iff F.hasFDerivAt h_hol).mp hv
    exact F_equiv.ker.le (h_only_zero (F v) h_Fv)
  refine ⟨{ expMap := e
            lattice := Y.periodLattice
            surjective := by simpa only [he] using u.surjective.comp F_equiv.surjective
            eq_zero_iff := fun z ↦ ⟨h_kill z, h_ker z⟩
            immersive := fun z ↦ ⟨hY.holomorphicAt hN z, h_imm z⟩
            universal := fun γ hγ ↦ ?_ }, hY, rfl, rfl,
    by simp [← Y.isPeriodMap.finrank_eq_abelianDim, F_equiv.finrank_eq]⟩
  obtain ⟨F', hF'⟩ := u.universal γ hγ
  refine ⟨F_equiv.symm.toContinuousLinearEquiv ∘L F', fun w ↦ ?_⟩
  simp [he, hF']

end New

namespace New.ThetaObject.TorusModel

open CategoryTheory Complex LinearMap Submodule NumberField LineBundle Variety ThetaTori Set
  AlgebraicGeometry Polynomial AddChar IsIntegrallyClosed

variable {E : Type} [Field E] [CMBase E]
  {D : PEL E} {Z : Scheme} {τ : Z ⟶ Spec (CommRingCat.of (𝓞 E))} {X : ThetaFamily D Z τ}
  {O : Type} [CommRing O] [ValuativeArc O] {y : ThetaObject X (Spec ⟨O⟩)}
  {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ} {V : Type} [FinComplexSpace V]
  {Y : PeriodMap D g ℓ V} (m : y.TorusModel Y)

/-! ### The full structure of a model -/

/-- The map `π` of a model `m` sends (E ⊗ ℝ)ⁿ to the sections of `y.groupScheme` over `O`. It is the
period map `Q` followed by the uniformisation. -/
noncomputable def π (w : RealVectors E D.Index) :
    MonoidalCategoryStruct.tensorUnit (Over (Spec (CommRingCat.of O))) ⟶ y.groupScheme :=
  m.uniformisation.expMap (Y.realEquiv w)

/-- A ring homomorphism `φ : O → ℂ` acts on roots of unity through a unit of Ẑ. Here `ψf E` is the
standard additive character of the finite adeles of `E`, whose values are roots of unity. There is
a unit `ε` of Ẑ such that each value `ψf E t` is the image of some `c ∈ O` with
`φ c = ψf E (t ε)`. -/
lemma exists_unit_on_roots_of_unity (φ : O →+* ℂ) :
    ∃ ε : (Ô ℚ)ˣ, ∀ t : 𝔸f E, ∃ c : O,
      algebraMap O ℂ c = ψf E t ∧ φ c = ψf E (t * finAdeleIncl ℚ E ε) := by
  -- Roots of unity are integral, so they lie in `O`: `ζ z` is the preimage of `z`.
  have h_lift (z : ℂ) (hz : IsOfFinOrder z) : ∃ c : O, algebraMap O ℂ c = z :=
    isIntegral_iff (R := O).mp
      ((IsPrimitiveRoot.orderOf z).isIntegral (orderOf_pos_iff.mpr hz)).tower_top
  choose! ζ hζ using h_lift
  -- The sets `C t` of pairs `(ε, ε')` with `φ (ζ (ψf E t)) = ψf E (t ε)` and
  -- `ψf E (t ε ε') = ψf E t` are closed; by compactness of `Ẑ × Ẑ` it is enough to treat finitely
  -- many `t` at a time.
  let ι : 𝔸f ℚ →+* 𝔸f E := finAdeleIncl ℚ E
  let C (t : 𝔸f E) : Set (𝔸f ℚ × 𝔸f ℚ) :=
    {p : 𝔸f ℚ × 𝔸f ℚ |
      φ (ζ (ψf E t)) = ψf E (t * ι p.fst) ∧ ψf E (t * ι (p.fst * p.snd)) = ψf E t}
  have hC_closed (t : 𝔸f E) : IsClosed (C t) := by
    apply (isClosed_eq _ (.subtype_val _)).and (isClosed_eq ..) <;> fun_prop
  have h_fin (U : Finset (𝔸f E)) : ((Ô ℚ : Set _) ×ˢ (Ô ℚ : Set _) ∩ ⋂ t ∈ U, C t).Nonempty := by
    -- All `ψf E t`, `t ∈ U`, are `N`-th roots of unity.
    obtain ⟨N, hN, hU⟩ := exists_forall_mul_mem_Ô fun t : U ↦ (t : 𝔸f E)
    have hN_ne : NeZero N := ⟨hN⟩
    have h_inj : Function.Injective (algebraMap O ℂ) := IsFractionRing.injective O ℂ
    obtain ⟨ω, hω⟩ : ∃ ω : ℂ, IsPrimitiveRoot ω N := ⟨_, isPrimitiveRoot_exp N hN⟩
    have hω_alg : algebraMap O ℂ (ζ ω) = ω := hζ ω (hω.isOfFinOrder hN)
    have hζω : IsPrimitiveRoot (ζ ω) N := .of_map_of_injective (by rwa [hω_alg]) h_inj
    -- `φ (ζ ω)` is a root of the cyclotomic polynomial, so it and `ω` are powers of each other.
    have hφω : IsPrimitiveRoot (φ (ζ ω)) N := by
      rw [← isRoot_cyclotomic_iff, ← map_cyclotomic N φ]
      exact (hζω.isRoot_cyclotomic hN.pos).map
    obtain ⟨k, -, hk⟩ := hω.eq_pow_of_pow_eq_one hφω.pow_eq_one
    obtain ⟨l, -, hl⟩ := hφω.eq_pow_of_pow_eq_one hω.pow_eq_one
    refine ⟨(k, l), by simp, Set.mem_biInter fun t ht ↦ ?_⟩
    have ht_alg : algebraMap O ℂ (ζ (ψf E t)) = ψf E t := hζ _ (isOfFinOrder_ψf t)
    have ht_pow : ζ (ψf E t) ^ N = 1 := by
      apply h_inj
      simp [ht_alg, ← Circle.coe_pow, ← map_nsmul_eq_pow, ψf_eq_one_of_mem (hU ⟨t, ht⟩)]
    -- So `ζ (ψf E t)` is a power of `ζ ω`: `φ` acts on it as the `k`-th power, undone by `l`.
    obtain ⟨a, -, ha⟩ := hζω.eq_pow_of_pow_eq_one ht_pow
    have h_act : φ (ζ (ψf E t)) = ψf E t ^ k := by grind [pow_right_comm]
    have h_undo : ((ψf E t : ℂ) ^ k) ^ l = ψf E t := by grind [pow_right_comm]
    -- Without the flag, `simp` turns the `•` of `← nsmul_eq_mul'` back into a product.
    simpa [C, ι, Circle.ext_iff, -nsmul_eq_mul, ← nsmul_eq_mul', map_nsmul_eq_pow] using
      And.intro h_act h_undo
  obtain ⟨⟨ε, ε'⟩, ⟨hε, hε'⟩, h_mem⟩ :=
    (isCompact_Ô.prod isCompact_Ô).inter_iInter_nonempty C hC_closed h_fin
  rw [Set.mem_iInter] at h_mem
  -- `ψf` separates finite adeles, so `ε * ε' = 1`.
  have h_unit : ε * ε' = 1 :=
    adeleMap_injective (algebraMap _ E) (eq_of_forall_ψf_mul_eq fun t ↦ by
      simpa [ι] using (h_mem t).right)
  exact ⟨.mkOfMulEqOne ⟨ε, hε⟩ ⟨ε', hε'⟩ (Subtype.ext h_unit), fun t ↦
    ⟨ζ (ψf E t), hζ (ψf E t) (isOfFinOrder_ψf t), (h_mem t).left⟩⟩

/-- Two rational vectors `a`, `b` give the same point of `y.groupScheme` (the images of their
periods under the uniformisation of the model `m`) exactly when their torsion classes g⁻¹a and g⁻¹b
in (𝔸_f / Ô)ⁿ agree. -/
lemma expMap_periodPoint_eq_iff (a b : D.Index → E) :
    m.uniformisation.expMap (Y.periodPoint a) = m.uniformisation.expMap (Y.periodPoint b) ↔
      Variety.frameTorsionClass g a = Variety.frameTorsionClass g b := by
  simpa [← m.lattice_eq, sub_eq_zero] using Y.sub_mem_periodLattice_iff (y := a) (z := b)

/-- The full structure of a model: the class of g⁻¹a in (𝔸_f / Ô)ⁿ, for a in Eⁿ, is sent to the
torsion section `expMap (Q (toRealVectors a))`, computed at the chosen rational lift `ratLift g` of
the class. -/
noncomputable def fullStructure : y.FullLevelStructure where
  torsionPoint :=
    { toFun x := m.uniformisation.expMap (Y.periodPoint (ratLift g x))
      map_add' := by simp [m.expMap_periodPoint_eq_iff, ← map_add, map_add (frameTorsionClass g)]
      map_smul' := by simp [← equivariant, ← toRealVectors_smul, m.expMap_periodPoint_eq_iff] }
  injective _ := by simp [m.expMap_periodPoint_eq_iff]
  levelPoints_eq := m.level_eq
  weil_pairing ι := by
    -- The frame `g` scales the form by a unit `a`, and `ι` acts on roots of unity through `ε`.
    obtain ⟨a, ha⟩ := Y.isFrameFor
    obtain ⟨ε, hε⟩ := exists_unit_on_roots_of_unity (E := E) ι
    refine ⟨a * ε, fun k s t hs ht ↦ ?_⟩
    obtain ⟨c, hc, hιc⟩ := hε (finAdeleIncl ℚ E a * (k * xiForm D.ξ s t))
    refine ⟨c, by simpa [mul_right_comm] using hιc, fun Φ Ψ hΦ hΨ ↦
      (lift_commutator_iff_weil_pairing _ m.hasThetaCoords hΦ hΨ).2 ?_⟩
    -- It remains to see that `c` is `Real.fourierChar` of `polarisationForm` at `s'` and `k • t'`,
    -- where `s'`, `t'` are rational lifts of the classes of `s` and `t`.
    -- `fourierChar_polarisationForm` rewrites this through `ψf`.
    set s' := ratLift g (torsionClass s) with hs'
    set t' := ratLift g (torsionClass t) with ht'
    have h_repr :
        ψf E (finAdeleIncl ℚ E a * xiForm D.ξ (frameCoords g s') (frameCoords g (k • t'))) =
          Real.fourierChar (polarisationForm D Y.formMatrix (toRealVectors s')
            (toRealVectors (k • t'))) :=
      (fourierChar_polarisationForm ha s' (k • t')).symm
    -- Up to the main term, the form pairs integral vectors, on which `ψf` is trivial
    -- (`D.mem_dualTorsion`).
    have h_form (ξ : E) (v : D.Index → E) (w : D.Index → 𝔸f E) :
        xiForm ξ (frameCoords g v) (k • w) =
          k * xiForm ξ s t + xiForm ξ (k • s) (w - t) + xiForm ξ (frameCoords g v - s) (k • w) := by
      simp [star_trivial, xiForm, -nsmul_eq_mul]
      grind
    simpa [hc, hs, ht, hs', ht', h_form, mul_add, map_add_eq_mul, (ψf_unit_mul_eq_one_iff _).2,
      (D.mem_dualTorsion _).1, Y.riemannForm_eq, -nsmul_eq_mul, ← frameTorsionClass_apply,
      Circle.ext_iff] using h_repr

/-- The torsion point of a class under `New.ThetaObject.TorusModel.fullStructure` is the section at
the period of its chosen rational lift `ratLift g`. -/
private lemma fullStructure_torsionPoint_apply (s : AdelicTorsion E D.Index) :
    m.fullStructure.torsionPoint s = m.uniformisation.expMap (Y.periodPoint (ratLift g s)) :=
  rfl

/-- `New.ThetaObject.TorusModel.fullStructure` sends the class of g⁻¹z to the section at the period
of z for every z in Eⁿ, not only for the chosen representative of the class. -/
lemma torsionPoint_frameTorsionClass (z : D.Index → E) :
    m.fullStructure.torsionPoint (Variety.frameTorsionClass g z) =
      m.uniformisation.expMap (Y.periodPoint z) := by
  rw [fullStructure_torsionPoint_apply, m.expMap_periodPoint_eq_iff, frameTorsionClass_ratLift]

/-! ### The dual lattice and the multiplier of a model -/

/-- The order of `D.dualTorsion` kills the lattice dual to `m.uniformisation.lattice` (for the
Riemann form) modulo `m.uniformisation.lattice`. -/
lemma card_nsmul_mem_of_mem_dualLattice :
    ∀ b ∈ Y.automorphyForm.dualLattice (L := m.uniformisation.lattice),
      Nat.card D.dualTorsion • b ∈ m.uniformisation.lattice := by
  -- The dual lattice consists of the periods of the vectors `w` whose class lies in
  -- `D.dualTorsion`.
  rw [m.lattice_eq, Y.dualLattice_periodLattice]
  exact fun b hb ↦ Y.card_nsmul_mem_periodLattice hb

/-- Let `S` be the `O`-span of the coordinates of `y.lineBundle` and `b` a vector of the lattice
dual to `m.uniformisation.lattice` for the Riemann form. Then the translation by the section
`m.uniformisation.expMap b` has a lift `Φ` to the sections of `y.lineBundle` with `Φ S ⊆ S`. -/
lemma exists_isTranslationLift_of_mem_dualLattice :
    ∀ b ∈ Y.automorphyForm.dualLattice (L := m.uniformisation.lattice), ∃ Φ :
      Module.End O ↥(y.lineBundle.H0 O),
      IsTranslationLift y.lineBundle (m.uniformisation.expMap b) Φ ∧
      span O (Set.range (coordSection y.isProjEmbedding.isLinearSystem)) ∈ Φ.invtSubmodule := by
  -- The dual lattice consists of the periods of the vectors `w` whose class lies in
  -- `D.dualTorsion`.
  rw [m.lattice_eq, Y.dualLattice_periodLattice]
  rintro _ ⟨w, hw, rfl⟩
  -- The theta structure lifts translation by the level point of that class; the lift permutes
  -- the coordinates up to scalars, the cocycle chosen inside the theta structure.
  obtain ⟨Φ, h_lift, h_coord⟩ := y.isThetaStructure.theta_law 1 ⟨frameTorsionClass g w, hw⟩
  have h_point :
      y.levelPoints (AddSubgroup.inclusion D.dualTorsion_le_levelTorsion
        ⟨frameTorsionClass g w, hw⟩) =
        m.uniformisation.expMap (Y.periodPoint w) :=
    (m.fullStructure.levelPoints_eq _).trans (m.torsionPoint_frameTorsionClass w)
  refine ⟨Φ, by simpa [← h_point] using h_lift, span_le.mpr ?_⟩
  simp [h_coord, range_subset_iff, smul_mem, mem_span_of_mem]

/-- Let `S` be the `O`-span of the coordinates of `y.lineBundle` and `b` a vector of the lattice
dual to `m.uniformisation.lattice` for the Riemann form. Then `|D.dualTorsion| • b` lies in
`m.uniformisation.lattice`, and the translation by the section `m.uniformisation.expMap b` has a
lift `Φ` to the sections of `y.lineBundle` with `Φ S ⊆ S`. -/
lemma exists_isTranslationLift_of_dualLattice :
    ∀ b ∈ Y.automorphyForm.dualLattice (L := m.uniformisation.lattice),
      Nat.card D.dualTorsion • b ∈ m.uniformisation.lattice ∧
      ∃ Φ : Module.End O ↥(y.lineBundle.H0 O),
        IsTranslationLift y.lineBundle (m.uniformisation.expMap b) Φ ∧
        span O (Set.range (coordSection y.isProjEmbedding.isLinearSystem)) ∈ Φ.invtSubmodule :=
  fun b hb ↦
    ⟨m.card_nsmul_mem_of_mem_dualLattice b hb, m.exists_isTranslationLift_of_mem_dualLattice b hb⟩

/-- Let `m` model the object `y` on the torus of the polarised period map `Y`. On the period lattice
`m.uniformisation.lattice`, the multiplier `m.χ` of the theta coordinates is χ(l) = exp(πi·e(βl,
l)). Here e is the Riemann form of B = `Y.automorphyForm`, and β = `D.β` ∈ `𝓞 E` acts on V through
`Y.intAction`, the action of `𝓞 E` transported through the period map. -/
lemma multiplier_eq_canonicalMultiplier (l : V) (hl : l ∈ m.uniformisation.lattice) :
    m.χ l = canonicalMultiplier Y.automorphyForm (Y.intAction D.β) l := by
  -- The bundles `N ⊗ N ⊗ β^* N` and `(β + 1)^* N` are isomorphic (the class law `y.hasClassLaws.2`
  -- at the identity of `y.groupScheme`), so their multipliers agree: `χ(l)² χ(βl) = χ(l + βl)`. The
  -- cocycle rule expands the right side as `χ(l) χ(βl) exp(πi e(βl, l))`; cancel `χ(l) χ(βl)`.
  let F : 𝓞 E →+* V →L[ℂ] V := Y.intAction
  have hF (c : 𝓞 E) : ∀ l ∈ m.uniformisation.lattice, F c l ∈ m.uniformisation.lattice := by
    simpa [m.lattice_eq] using Y.intAction_mem_periodLattice c
  -- `F c` lifts the action of `c` on `y.groupScheme`, read at the generic point.
  have h_generic (c : 𝓞 E) (v : V) :
      atGeneric m.uniformisation.expMap (F c v) =
        atGeneric m.uniformisation.expMap v ≫ (c • 𝟙 y.groupScheme).left := by
    simp [F, PeriodMap.intAction, m.equivariant, atGeneric, ← Over.comp_left]
  have h_pull (c : 𝓞 E) : HasThetaCoords m.uniformisation.lattice
    (atGeneric m.uniformisation.expMap)
      (y.lineBundle.pull (c • 𝟙 y.groupScheme).left) (Y.automorphyForm.pullForm (F c)) (m.χ ∘ F c)
        (m.θ ∘ F c) :=
    m.hasThetaCoords.pull (F c) (h_generic c) (hF c)
  have h_cls :
      ((y.lineBundle.mul y.lineBundle).mul
          (y.lineBundle.pull (D.β • 𝟙 y.groupScheme).left)).picClass =
        (y.lineBundle.pull ((D.β + 1) • 𝟙 y.groupScheme).left).picClass := by
    -- `using!`, because the class law is stated with `Pic.atPoint`, a pullback by definition,
    -- and unfolding it leaves the terms at `0` that `atPoint_zero` would remove.
    simpa [Pic.pairing, add_smul, eq_sub_iff_add_eq] using! y.hasClassLaws.2 0 (𝟙 _)
  -- Isomorphic bundles with theta coordinates have the same multiplier on the lattice.
  obtain ⟨-, h_mult_on_L, -⟩ :=
    ((m.hasThetaCoords.mul m.hasThetaCoords).mul (h_pull _)).riemannForm_eq_of_isFrame (h_pull _)
      (picClass_eq_iff.mp h_cls).choose_spec m.uniformisation.holomorphicAt
      m.uniformisation.atGeneric_add_of_mem
  have h_mult : m.χ l * m.χ l * m.χ (F D.β l) = m.χ (F (D.β + 1) l) := h_mult_on_L l hl
  have h_add : m.χ (F (D.β + 1) l) = m.χ l * m.χ (F D.β l) * canonicalMultiplier Y.automorphyForm
    (F D.β) l := by
    simpa [F, add_comm l, canonicalMultiplier] using
      m.hasThetaCoords.isAppellHumbert.semicharacter l hl _ (hF D.β l hl)
  have h_ne : m.χ l * m.χ (F D.β l) ≠ 0 :=
    mul_ne_zero (m.hasThetaCoords.isAppellHumbert.ne_zero hl)
      (m.hasThetaCoords.isAppellHumbert.ne_zero (hF D.β l hl))
  have h_eq :
      m.χ l * m.χ (F D.β l) * m.χ l =
        m.χ l * m.χ (F D.β l) * canonicalMultiplier Y.automorphyForm (F D.β) l := by
    rw [← h_add, ← h_mult]
    ring
  exact mul_left_cancel₀ h_ne h_eq

end New.ThetaObject.TorusModel

/-!
## Homomorphisms of modelled objects and rational matrices

Objects `x`, `x'` over a valuation ring `O` with fraction field `ℂ` are modelled on the tori of
`(g, ℓ)` and `(g', ℓ')`, with `g`, `g'` adelic frames and `ℓ`, `ℓ'` complex matrices.
-/

namespace New.ThetaObject.TorusModel

open CategoryTheory AlgebraicGeometry NumberField Matrix Category LineBundle ThetaTori Variety
  LinearMap Function

variable {E : Type} [Field E] [CMBase E]
  {V V' : Type} [FinComplexSpace V] [FinComplexSpace V']
  {D : PEL E} {g g' : GL D.Index (𝔸f E)} {ℓ ℓ' : Matrix D.Index D.Index ℂ} {Z : Scheme}
  {τ : Z ⟶ Spec (CommRingCat.of (𝓞 E))} {X : ThetaFamily D Z τ}
  {O : Type} [CommRing O] [ValuativeArc O]
  {x x' : ThetaObject X (Spec ⟨O⟩)} {Y : PeriodMap D g ℓ V} {Y' : PeriodMap D g' ℓ' V'}

/-- If `ψ` carries `m.π w` to `m'.π (z w)` for all `w`, then it carries the torsion point of the
class of `y` in (𝔸_f / Ô)ⁿ to the torsion point of the class of `g'⁻¹ z g y` (with `toFinGL z` the
image of `z` over 𝔸_f), for every finite adelic vector `y`. -/
lemma torsionPoint_comp (m : x.TorusModel Y) (m' : x'.TorusModel Y') {z : GL D.Index E}
    {ψ : x.groupScheme ⟶ x'.groupScheme}
    (h_periods : ∀ w : RealVectors E D.Index, m.π w ≫ ψ = m'.π (realVecAction z.val w))
    (y : D.Index → 𝔸f E) :
    m.fullStructure.torsionPoint (torsionClass y) ≫ ψ =
      m'.fullStructure.torsionPoint (torsionClass ((g'⁻¹ * toFinGL z * g).val *ᵥ y)) := by
  -- Both sides are locally constant in `y`, so the set of good `y` is closed; by `h_periods` it
  -- contains the dense range of `frameCoords g`.
  refine denseRange_frameCoords (g := g).induction_on y ⟨?_⟩ fun w ↦ ?_
  · exact IsLocallyConstant.comp₂ isOpen_preimage_torsionClass
      (.comp_continuous isOpen_preimage_torsionClass (by fun_prop))
      (fun t t' ↦ m.fullStructure.torsionPoint t ≫ ψ = m'.fullStructure.torsionPoint t') Not
  · simpa [← torsionPoint_frameTorsionClass, frameTorsionClass_apply, frameCoords,
      LinearMap.compLeft, comp_def, RingHom.map_mulVec, π] using h_periods (toRealVectors w)

/-- Let `x`, `x'` be objects over `O` with torus models `m`, `m'` on the polarised period maps `Y`
(frame `g`, matrix `ℓ`) and `Y'` (frame `g'`, matrix `ℓ'`), with period maps `m.π`, `m'.π` from
`(E ⊗ ℝ)ⁿ`. Let `ψ : x.groupScheme ⟶ x'.groupScheme` be an `𝓞 E`-linear homomorphism that pulls the
Picard class of `x'.lineBundle` back to `μ ≠ 0` times that of `x.lineBundle`. Then `ψ` comes from
some `z ∈ GL_n(E)`: (a) `m.π w ≫ ψ = m'.π (z·w)` for all `w`; (b) with `Y.formMatrix` the matrix of
the form β of `Y` (not the element `D.β` of `𝓞 E`), `μ` times the polarisation form of
`Y.formMatrix` is the polarisation form of `zᴴ Y'.formMatrix z`; (c) `z ℓ z⁻¹ = ℓ'` (conjugation
through `Φ v₀`). -/
lemma exists_matrix_of_hom (m : x.TorusModel Y) (m' : x'.TorusModel Y')
    (ψ : x.groupScheme ⟶ x'.groupScheme) [hψ : IsLinear ψ] {μ : ℕ} (hμ : μ ≠ 0)
    (hψ_cls : x'.lineBundle.picClass.pull ψ.left = μ • x.lineBundle.picClass) :
    ∃ z : GL D.Index E,
      -- (a) `ψ` acts on periods by `z`
      (∀ w : RealVectors E D.Index, m.π w ≫ ψ = m'.π (realVecAction z w)) ∧
      -- (b) `z` pulls the form of `Y'` back to `μ` times the form of `Y`
      (∀ y w : RealVectors E D.Index,
        μ * polarisationForm D Y.formMatrix y w = polarisationForm D (z.valᴴ * Y'.formMatrix * z) y
          w) ∧
      -- (c) `z` carries `ℓ` to `ℓ'`
      ratConj z ℓ = ℓ' := by
  -- `ψ` lifts to a complex linear map `F` of the universal covers. `F` keeps rational points and
  -- commutes with `𝓞 E`, so it is given by a matrix `z` over `E`; the theta data give the forms.
  obtain ⟨F, hF : ∀ w : V, m'.uniformisation.expMap (F w) = m.uniformisation.expMap w ≫ ψ⟩ :=
    m'.uniformisation.universal ((IsAddMonHom.addMonoidHom ψ _).comp _)
      ((m.uniformisation.immersive 0).1.comp_hom _)
  -- Isomorphic bundles with theta coordinates have the same Riemann form
  -- (`riemannForm_eq_of_isFrame`); here `x.lineBundle ^ μ` and `ψ^* x'.lineBundle`.
  have hF_mem : ∀ l ∈ m.uniformisation.lattice, F l ∈ m'.uniformisation.lattice := by simp_all
  have h_cls : (x.lineBundle.pow μ).picClass = (x'.lineBundle.pull ψ.left).picClass := by
    simp [← Pic.pull_picClass, hψ_cls]
  have h_generic (w : V) :
      atGeneric m'.uniformisation.expMap (F w) = atGeneric m.uniformisation.expMap w ≫ ψ.left := by
    simp [atGeneric, hF, ← Over.comp_left]
  obtain ⟨_, h_frame⟩ := picClass_eq_iff.mp h_cls
  obtain ⟨h_riem, -⟩ :
      RealComplexForm.riemannForm (μ • Y.automorphyForm) = RealComplexForm.riemannForm
        (Y'.automorphyForm.pullForm F) ∧ _ :=
    (m.hasThetaCoords.pow μ).riemannForm_eq_of_isFrame (m'.hasThetaCoords.pull F h_generic hF_mem)
      h_frame m.uniformisation.holomorphicAt m.uniformisation.atGeneric_add_of_mem
  -- A rational point maps to a torsion point of `x'`, which is again a rational point.
  have h_rat (y : D.Index → E) :
      ∃ y', toRealVectors y' = Y'.realEquiv.symm (F (Y.realEquiv (toRealVectors y))) := by
    obtain ⟨k, hk, hky⟩ := exists_nsmul_adelicTorsion_eq_zero (frameTorsionClass g y)
    have h_ker : k • F (Y.realEquiv (toRealVectors y)) ∈ Y'.latticeOver ⊥ := by
      simp [← m'.lattice_eq, ← torsionPoint_frameTorsionClass, ← nsmul_comp,
        ← map_nsmul m.fullStructure.torsionPoint, hky, hF]
    obtain ⟨y', -, hy'⟩ := (Y'.nsmul_mem_latticeOver hk).mp h_ker
    exact ⟨y', Y'.realEquiv.eq_symm_apply.mpr hy'⟩
  choose f hf using h_rat
  have h_lin (c : 𝓞 E) (w : RealVectors E D.Index) :
      F (Y.realEquiv (cmEmbedding (algebraMap (𝓞 E) E c) • w)) =
        Y'.realEquiv (cmEmbedding (algebraMap (𝓞 E) E c) • Y'.realEquiv.symm
          (F (Y.realEquiv w))) := by
    have h_comp : F ∘L Y.intAction c = Y'.intAction c ∘L F :=
      m'.uniformisation.linear_ext (by simp [equivariant, hF, PeriodMap.intAction])
    simpa [PeriodMap.intAction] using DFunLike.congr_fun h_comp (Y.realEquiv w)
  -- `f` is `𝓞 E`-linear, hence `E`-linear; rational points are dense, so its matrix gives `F`.
  obtain ⟨z, hz⟩ : ∃ z : Matrix D.Index D.Index E, ∀ w,
    F (Y.realEquiv w) = Y'.realEquiv (realVecAction z w) := by
    let f₀ : (D.Index → E) →ₗ[𝓞 E] D.Index → E :=
      { toFun := f
        map_add' := by simp [hf, ← toRealVectors_injective.eq_iff]
        map_smul' := by simp [hf, h_lin, ← toRealVectors_injective.eq_iff] }
    refine ⟨toMatrix' (f₀.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 E)) E),
      denseRange_toRealVectors.eq fun y ↦ ?_⟩
    simp [f₀, hf, realVecAction_toRealVectors]
  -- `z` is invertible because it pulls a form back to the nondegenerate form of
  -- `μ • Y.automorphyForm`.
  have hz_inj : Injective z.mulVec := by
    intro a b hab
    obtain ⟨h_left_nondeg, -⟩ : (RealComplexForm.riemannForm
      (Y'.automorphyForm.pullForm F)).Nondegenerate := by
      simpa only [← h_riem] using (Y.isPosRiemann.nsmul hμ).nondegenerate (L := Y.periodLattice)
    -- `F (Y.realEquiv (a - b)) = 0` pairs to zero with everything.
    have h_pair_zero (v : V) :
        RealComplexForm.riemannForm (Y'.automorphyForm.pullForm F)
          (Y.realEquiv (toRealVectors a) - Y.realEquiv (toRealVectors b)) v = 0 := by
      simp [hz, hab, riemannForm_pullForm]
    exact toRealVectors_injective (Y.realEquiv.injective
      (sub_eq_zero.mp (h_left_nondeg _ h_pair_zero)))
  lift z to GL D.Index E using mulVec_injective_iff_isUnit.mp hz_inj
  -- `z` conjugates `ℓ` to `ℓ'` as `F` is complex linear.
  have h_periods (w : RealVectors E D.Index) : m.π w ≫ ψ = m'.π (realVecAction z w) := by
    simp [← hF, hz, π]
  refine ⟨z, h_periods, ?_, Y.isPeriodMap.ratConj_eq Y'.isPeriodMap F hz⟩
  -- (b) is `h_riem` read through `Y.riemannForm_eq` and `Y'.riemannForm_eq`.
  intro y w
  calc
    _ = RealComplexForm.riemannForm (μ • Y.automorphyForm) (Y.realEquiv y) (Y.realEquiv w) := by
      simp [Y.riemannForm_eq]
    _ = RealComplexForm.riemannForm (Y'.automorphyForm.pullForm F) (Y.realEquiv y)
      (Y.realEquiv w) := by rw [h_riem]
    _ = _ := by
      rw [riemannForm_pullForm, hz, hz, Y'.riemannForm_eq]
      -- `↓`: the map of the product `zᴴ β' z` is split before `simp` distributes it entrywise.
      simp [polarisationForm, ↓map_conjTranspose_mul_mul, dotProduct_mulVec, star_mulVec]

/-- Objects with models have the same map from `𝓞 E`: after the injective map `O → ℂ`, both are
the embedding `Φ v₀`. -/
lemma baseHom_eq_baseHom (m : x.TorusModel Y) (m' : x'.TorusModel Y') :
    x'.baseHom = x.baseHom :=
  RingHom.ext fun c ↦ IsFractionRing.injective O ℂ (by rw [m'.baseHom_eq, m.baseHom_eq])

/-- `ψ` is an `𝓞 E`-linear isogeny from `x` to `x'` of multiplier `μ` that acts on torsion by
the adelic matrix `k` and on periods by the rational matrix `z`. -/
structure IsIsogenyOfMatrix (m : x.TorusModel Y) (m' : x'.TorusModel Y') (z : GL D.Index E)
    (k : GL D.Index (𝔸f E)) (μ : ℕ) (ψ : x.groupScheme ⟶ x'.groupScheme) : Prop where
  /-- `ψ` is an isogeny. -/
  isIsogeny : IsIsogeny ψ
  /-- `ψ` commutes with the action of `𝓞 E`. -/
  isLinear : IsLinear ψ
  /-- `ψ` pulls the class of `x'.lineBundle` back to `μ` times that of `x.lineBundle`. -/
  pull_picClass : x'.lineBundle.picClass.pull ψ.left = μ • x.lineBundle.picClass
  /-- `ψ` sends the torsion point of the class of `y` to that of `k y`. -/
  torsionPoint_comp (y : D.Index → 𝔸f E) :
    m.fullStructure.torsionPoint (torsionClass y) ≫ ψ =
      m'.fullStructure.torsionPoint (torsionClass (k.val *ᵥ y))
  /-- `ψ` sends `m.π w` to `m'.π (z w)`. -/
  π_comp (w : RealVectors E D.Index) : m.π w ≫ ψ = m'.π (realVecAction z w)

/-- Let `x`, `x'` be objects over `O` with torus models `m`, `m'` on the polarised period maps `Y`
(frame `g`, matrix `ℓ`) and `Y'` (frame `g'`, matrix `ℓ'`). Let `z ∈ GL_n(E)` satisfy `z ℓ z⁻¹ = ℓ'`
(conjugation through `Φ v₀`), and let `k = g'⁻¹ z g` have entries in `Ô E` (the integral finite
adeles of `E`) with `IsScalarFrame k⁻¹ μ`, i.e. `μ > 0` and `μ (k⁻¹)ᴴ k⁻¹ = ε·1` for a unit `ε` of
`Ẑ`. Then some `ψ : x.groupScheme ⟶ x'.groupScheme` is an `𝓞 E`-linear isogeny from `x` to `x'` of
multiplier `μ`, acting by `k` on torsion and by `z` on periods. -/
lemma exists_isIsogenyOfMatrix (z : GL D.Index E) (hz : ratConj z ℓ = ℓ')
    (m : x.TorusModel Y) (m' : x'.TorusModel Y') {k : GL D.Index (𝔸f E)} {μ : ℕ}
    (hk : g'⁻¹ * toFinGL z * g = k) (hk_int : ∀ i j : D.Index, k i j ∈ Ô E)
    (hμ : IsScalarFrame k⁻¹ μ) :
    ∃ ψ : x.groupScheme ⟶ x'.groupScheme, IsIsogenyOfMatrix m m' z k μ ψ := by
  -- `z` defines a complex linear map `F` of the universal covers that respects the lattices and
  -- multiplies the type of the theta functions by `μ`; `exists_hom_of_hasThetaCoords` makes it a
  -- homomorphism `ψ`.
  subst hk
  have hQ : Function.Surjective Y.realEquiv := Y.realEquiv.surjective
  -- `F` is complex linear because `z` carries `ℓ` to `ℓ'`.
  have h_conj : z.map (Φ v₀) * ℓ = ℓ' * z.map (Φ v₀) := (z.map _).mul_inv_eq_iff_eq_mul.mp hz
  let F : V →L[ℂ] V' :=
    { Y.realEquiv.arrowCongr Y'.realEquiv (realVecAction z.val).toContinuousLinearMap with
      map_smul' a := by
        -- `↓`: the quantifier is moved to `Y.realEquiv` before `simp_all` rewrites under it;
        -- without it the goal is left with a spurious disjunction.
        simp_all [↓hQ.forall, ← Y'.realEquiv.symm.injective.eq_iff, smul_eq_re_smul_add_im_smul a,
          ← PeriodMap.isPeriodMap _ _, funext_iff, mulVec_add, mulVec_smul] }
  -- `F` maps lattice to lattice because `g'⁻¹ z g` is integral.
  have h_lat : ∀ l ∈ m.uniformisation.lattice, F l ∈ m'.uniformisation.lattice := by
    simpa [lattice_eq, F, frameLattice, mem_classLattice] using fun P ↦
      realVecAction_mem_frameLattice hk_int (P := P)
  -- `z` pulls the form `Y'.formMatrix` back to `μ • Y.formMatrix`, by positivity and `hμ`
  -- (`conjTranspose_mul_mul_eq_smul`).
  have hF_Q (w : RealVectors E D.Index) :
    F (Y.realEquiv w) = Y'.realEquiv (realVecAction z.val w) := by simp [F]
  have h_riem :
      RealComplexForm.riemannForm (Y'.automorphyForm.pullForm F) = RealComplexForm.riemannForm
        (μ • Y.automorphyForm) := by
    -- At `Y.realEquiv y`, `Y.realEquiv w` the left side is the polarisation form of `Y'.formMatrix`
    -- at `z y`, `z w`.
    refine LinearMap.ext₂ (hQ.forall.mpr fun y ↦ hQ.forall.mpr fun w ↦ ?_)
    rw [riemannForm_pullForm, hF_Q, hF_Q, Y'.riemannForm_eq]
    -- The sums over the infinite places after `conjTranspose_mul_mul_eq_smul` are matched by
    -- `grind`.
    simp [PeriodMap.riemannForm_eq, ← map_conjTranspose_mul_mul, vecMul_smul, map_smul',
      Finset.mul_sum, Y.isSignedFrameFor.conjTranspose_mul_mul_eq_smul Y'.isSignedFrameFor hμ,
        polarisationForm,
      dotProduct_mulVec, star_mulVec]
    grind
  -- Both multipliers are canonical, `χ l = exp (π i e(β l, l))` with `e` the Riemann form and
  -- `β = D.β`, so `h_riem` compares them.
  have h_char : ∀ l ∈ m.uniformisation.lattice, (m'.χ ∘ F) l = (m.χ ^ μ) l := by
    simp_all [multiplier_eq_canonicalMultiplier, canonicalMultiplier, mul_left_comm, hQ.forall, F,
      ← Complex.exp_nat_mul, ← mulVec_smul, ext_iff₂, riemannForm_pullForm, PeriodMap.intAction]
  -- Pull the theta coordinates of `x'` back along `F`.
  have h_pull :
      HasThetaCoords m.uniformisation.lattice (fun v : V ↦ atGeneric m'.uniformisation.expMap (F v))
        (x'.lineBundle.pull (𝟙 x'.groupScheme.left)) (Y'.automorphyForm.pullForm F) (m'.χ ∘ F)
          (m'.θ ∘ F) :=
    m'.hasThetaCoords.pull F (fun _ ↦ .symm (comp_id _)) h_lat
  -- Corrected by an exponential factor, they are theta coordinates of `x'.lineBundle` of type
  -- `(μ • Y.automorphyForm, m.χ ^ μ)`.
  obtain ⟨θ₀, h_coords⟩ : ∃ θ₀ : V → D.dualTorsion → ℂ, HasThetaCoords m.uniformisation.lattice
      (atGeneric (m'.uniformisation.expMap.comp F.toAddMonoidHom)) x'.lineBundle
        (μ • Y.automorphyForm) (m.χ ^ μ)
      θ₀ :=
    have h_AH : IsAppellHumbert (L := m.uniformisation.lattice) (μ • Y.automorphyForm) (m.χ ^ μ) :=
      m.hasThetaCoords.isAppellHumbert.nsmul μ
    ⟨_, h_pull.isLinearSystem, h_AH,
      fun i ↦ h_pull.isAppellHumbert.exp_mul_mem_thetaSpace h_AH h_riem h_char
        (h_pull.mem_thetaSpace i),
      fun w ↦ (m'.hasThetaCoords.hasFieldCoords (F w)).smul (by simp)⟩
  -- `F` sends the lattice of `m` into that of `m'`, which the uniformisation of `x'` kills.
  have h_kill : ∀ l ∈ m.uniformisation.lattice, m'.uniformisation.expMap (F l) = 0 :=
    fun l hl ↦ (m'.uniformisation.eq_zero_iff (F l)).mp (h_lat l hl)
  -- Translations by the dual lattice lift to `x.lineBundle`, so the theta coordinates give `ψ`.
  obtain ⟨ψ, h_add, hψ, h_cls⟩ :
      ∃ ψ : x.groupScheme ⟶ x'.groupScheme,
        IsAdditive ψ ∧
        (∀ v : V, m.uniformisation.expMap v ≫ ψ = m'.uniformisation.expMap (F v)) ∧
        x'.lineBundle.picClass.pull ψ.left = μ • x.lineBundle.picClass :=
    exists_hom_of_hasThetaCoords _ m.hasThetaCoords h_kill x.isThetaStructure.isUnit_card
      (by grind [exists_isTranslationLift_of_dualLattice]) x'.isProjEmbedding
      x.isProjEmbedding x.hasClassLaws.1 x'.hasClassLaws.1 h_coords
  have hψ_π (w : RealVectors E D.Index) : m.π w ≫ ψ = m'.π (realVecAction z w) := by simp [F, hψ, π]
  -- The image of `ψ` contains the dense set of sections of `x'`.
  have h_surj : AlgebraicGeometry.Surjective ψ.left :=
    (isSeparatingFamily_atGeneric_of_surjective m'.uniformisation.surjective).2.surjective _
      (atGeneric m.π ∘ realVecAction z⁻¹ ∘ Y'.realEquiv.symm)
      (by simp [atGeneric, ← Over.comp_left, F, hψ, π])
  have h_isog : IsIsogeny ψ := isIsogeny_of_locallyQuasiFinite ψ
    (locallyQuasiFinite_of_pull_picClass x.isProjEmbedding (Nat.cast_pos.mp hμ.left).ne' h_cls)
    h_surj
  -- Linearity is tested on the dense set of sections of `x`.
  have h_lin : IsLinear ψ := by
    refine ⟨fun c ↦ (isSeparatingFamily_atGeneric_of_surjective
      (m.uniformisation.surjective.comp hQ)).hom_ext ?_⟩
    simp [← assoc (m.uniformisation.expMap _), ← equivariant, F, hψ]
  exact ⟨ψ, h_isog, h_lin, h_cls, m.torsionPoint_comp m' hψ_π, hψ_π⟩

/-- Let `z ∈ GL_n(E)` satisfy `z ℓ z⁻¹ = ℓ'` (`hz`), and let `k = g'⁻¹ z g` have integral entries
with `IsScalarFrame k⁻¹ μ` (μ > 0 and `k⁻¹` is a frame for the scalar matrix μ). Then `x` and `x'`
have the same map from `𝓞 E`, and there is an `𝓞 E`-linear isogeny `ψ` that pulls the class of
`x'.lineBundle` back to `μ` times that of `x.lineBundle` and satisfies `ψ π = π' z`. It sends the
torsion point of the class of `y` to that of `k y`, for every finite adelic vector `y`. -/
lemma exists_isogeny (z : GL D.Index E) (hz : ratConj z ℓ = ℓ') (m : x.TorusModel Y)
    (m' : x'.TorusModel Y') {k : GL D.Index (𝔸f E)} {μ : ℕ} (hk : g'⁻¹ * toFinGL z * g = k)
    (hk_int : ∀ i j : D.Index, k i j ∈ Ô E) (hμ : IsScalarFrame k⁻¹ μ) :
    x'.baseHom = x.baseHom ∧
    ∃ ψ : x.groupScheme ⟶ x'.groupScheme,
      IsIsogeny ψ ∧ IsLinear ψ ∧
      -- (a) the multiplier is `μ`
      x'.lineBundle.picClass.pull ψ.left = μ • x.lineBundle.picClass ∧
      -- (b) `ψ` acts on torsion by `k`
      (∀ y : D.Index → 𝔸f E,
        m.fullStructure.torsionPoint (torsionClass y) ≫ ψ =
          m'.fullStructure.torsionPoint (torsionClass (k.val *ᵥ y))) ∧
      -- (c) `ψ` acts on periods by `z`
      ∀ w : RealVectors E D.Index, m.π w ≫ ψ = m'.π (realVecAction z w) := by
  obtain ⟨ψ, hψ⟩ := exists_isIsogenyOfMatrix z hz m m' hk hk_int hμ
  exact ⟨baseHom_eq_baseHom m m', ψ, hψ.isIsogeny, hψ.isLinear, hψ.pull_picClass,
    hψ.torsionPoint_comp, hψ.π_comp⟩

end New.ThetaObject.TorusModel
