import Lib.General.Geometry.SerreTheorem
import Lib.Shimura.ThetaNormality.RiemannRelation
import Lib.Shimura.Uniformisation.TorusModel

/-!
# Linear systems and theta families from dense complex points carrying theta tori

This file builds objects from their values at a dense family of complex points. A linear system is a
line bundle whose transition functions are the ratios `s j / s i`, that is, a map to projective
space. `New.Variety.ThetaNull.exists_isLinearSystem` extends coordinates given at a dense family `ξ`
of complex points of a reduced scheme (`New.IsSeparatingFamily`) to a linear system. It needs a
linear system `M` with homogeneous coordinates `m a` at each `ξ a`. It also needs each of `w`, `m`
to be locally a regular function times sums of the other. The result has the Picard class of `M`.
The second part builds a family of theta-embedded abelian schemes `New.ThetaFamily D` over a base
`S` from complex points `η k` of `S` that carry theta tori `x k`. The scheme `A` is the closure of
the theta points. The group law, the action and all identities extend from these points by density,
using Riemann's relation for theta functions.

## Main definitions and results

* `New.exists_isAbelianScheme`: group and module axioms pass from dense families of vector spaces to
  `A`.
* `New.Variety.exists_maps_of_riemann_relation`: the extension step along Riemann's relation.
* `New.Variety.exists_add_and_intAction`: the addition and the action of `𝓞 E` extend to `A`.
* `New.Variety.exists_isThetaStructure`: the theta law on base changes to local rings.
* `New.Variety.exists_thetaFamily_of_points`: the family exists, modelled on `x i` at each `η i`.
  The remaining lemmas of the second part are steps of its proof.

Notions from other files:
* `New.LineBundle.IsHomogeneousCoords`: a vector `v` gives homogeneous coordinates of a point `t`
  for a line bundle: `v j` is a unit exactly when `t` lands in chart `j`, and there the transitions
  from chart `j` are the ratios `v k / v j`.
* `New.LineBundle.IsLinearSystem`: a line bundle whose transitions are regular on their charts,
  vanish off them, and are homogeneous coordinates of every point of the chart.
* `New.PointFn.IsRegularOn`: a function `f` is regular on an open `U`: at points `t : Spec A → X`
  that land in `U`, its value commutes with all ring maps `φ : A → B`.
* `New.Variety.AllSpecializeTo S Q`: every point of `S` specialises to the image of a point over an
  algebraically closed field with the property `Q`.
* `New.ThetaTori.ThetaTorus.IsRiemannTuple`: coefficient tuples for Riemann's relation.

## Relation to the literature

Known; see `Lib.Shimura.ThetaModuli.UniversalFamily` for sources.
-/

/-! ## Linear systems from coordinates at dense points -/

section LinearSystemExtension

open AlgebraicGeometry New PointFn LineBundle Finset CategoryTheory

/-- The family `w` is a local combination of the family `m`: for every index `j` and every point
`s` of `Z` there are an open `U` containing `s`, indices `e : Q → J` and a function `c` regular
on `U` such that `w a j = c (ξ a) * ∑ q, m a (e q)` at every complex point `ξ a` that lands in `U`.
Here `w a` and `m a` are vectors of complex coordinates attached to the point `ξ a`. -/
def New.Variety.ThetaNull.IsLocalCombination {Z : Scheme} {J X : Type} (Q : Type*) [Fintype Q]
    (ξ : X → (Spec (CommRingCat.of ℂ) ⟶ Z)) (w m : X → J → ℂ) : Prop :=
  ∀ (j : J) (s : Z), ∃ U : Z.Opens, s ∈ U ∧ ∃ (e : Q → J) (c : PointFn Z), IsRegularOn c U ∧
    ∀ a : X, LandsIn (ξ a) U → c (CommRingCat.of ℂ) (ξ a) * ∑ q : Q, m a (e q) = w a j

/-- Let the points `ξ a` separate `Z`, with homogeneous coordinates `m a` for the linear system
`M`. If each of the families `w` and `m` is a local combination of the other, then the `w a` are
homogeneous coordinates of the `ξ a` for a linear system `N` in the class of `M`. -/
lemma New.Variety.ThetaNull.exists_isLinearSystem {Z : Scheme} {J X : Type} {Q : Type*}
    [Fintype J] [Fintype Q] {M : LineBundle Z J} {ξ : X → (Spec (CommRingCat.of ℂ) ⟶ Z)}
    {m w : X → J → ℂ} (hξ : IsSeparatingFamily ξ) (hM : M.IsLinearSystem)
    (hm : ∀ a : X, M.IsHomogeneousCoords (ξ a) (m a))
    (h_wm : IsLocalCombination Q ξ w m) (h_mw : IsLocalCombination Q ξ m w) :
    ∃ N : LineBundle Z J,
      N.IsLinearSystem ∧ (∀ a : X, N.IsHomogeneousCoords (ξ a) (w a)) ∧
        N.picClass = M.picClass := by
  -- Each `w · j` defines a section `σ j` of `M` on a finer cover. By `h_mw` these sections have
  -- no common zero, so they are the coordinates of a map `f` to projective space, and the
  -- pull-back of the hyperplane bundle along `f` is the required linear system.
  choose U hU e c hc h_sum using h_wm
  have h_cover (j : J) : ⨆ s : Z, U j s = ⊤ := top_unique fun s _ ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hU j s⟩
  -- `L` is `M` on the cover by the sets `M.opens k ⊓ ⨅ j, U j (s j)`.
  let L : LineBundle Z (J × (J → Z)) := M.mul (pi (fun j : J ↦ mk (U j) 1 (h_cover j)) ∅)
  have L_opens {A : CommRingCat} {t : Spec A ⟶ Z} (k : J × (J → Z)) :
      LandsIn t (L.opens k) ↔ LandsIn t (M.opens k.fst) ∧ ∀ j : J, LandsIn t (U j (k.snd j)) := by
    simp [L, landsIn_iInf]
  have L_transition (i k : J × (J → Z)) : L.transition i k = M.transition i.fst k.fst := by
    simp [L, LineBundle.mul]
  let σ (j : J) (k : J × (J → Z)) : PointFn Z :=
    c j (k.snd j) * ∑ q : Q, M.transition k.fst (e j (k.snd j) q)
  have σ_reg (j : J) (k : J × (J → Z)) : (σ j k).IsRegularOn (L.opens k) := by
    intro A B φ t ht
    obtain ⟨ht_M, ht_U⟩ := (L_opens k).mp ht
    have h_trans (l : J) :
        M.transition k.fst l B (Spec.map φ ≫ t) = φ (M.transition k.fst l A t) :=
      hM.isRegularOn_transition k.fst l φ t ht_M
    simp [σ, h_trans, hc j (k.snd j) φ t (ht_U j)]
  -- In the chart `k` the coordinate `m a k.fst` is nonzero and the transitions are ratios.
  have m_ne (k : J × (J → Z)) (a : X) (ha : LandsIn (ξ a) (L.opens k)) : m a k.fst ≠ 0 :=
    (((hm a).landsIn_iff_isUnit k.fst).mp ((L_opens k).mp ha).left).ne_zero
  have M_transition (k : J × (J → Z)) (l : J) (a : X) (ha : LandsIn (ξ a) (L.opens k)) :
      M.transition k.fst l (CommRingCat.of ℂ) (ξ a) = m a l / m a k.fst := by
    simpa [div_eq_mul_inv] using (hm a).transition_eq_mul_inverse (m_ne k a ha).isUnit l
  have σ_val (j : J) (k : J × (J → Z)) (a : X) (ha : LandsIn (ξ a) (L.opens k)) :
      σ j k (CommRingCat.of ℂ) (ξ a) = w a j / m a k.fst := by
    obtain ⟨-, ha_U⟩ := (L_opens k).mp ha
    simp [σ, M_transition k _ a ha, ← sum_div, ← mul_div_assoc, ← h_sum j _ a (ha_U j)]
  -- The local expressions `σ j k` are compatible because they are so at the points `ξ a`.
  have σ_section (j : J) : L.IsSection (σ j) := by
    refine ⟨σ_reg j, fun i k A t hi hk ↦ ?_⟩
    have h_agree (a : X) (ha : LandsIn (ξ a) (L.opens i ⊓ L.opens k)) :
        σ j i (CommRingCat.of ℂ) (ξ a) =
          (L.transition i k * σ j k) (CommRingCat.of ℂ) (ξ a) := by
      obtain ⟨ha_i, ha_k⟩ := landsIn_inf.mp ha
      simp [L_transition, M_transition, σ_val, m_ne, ha_i, ha_k, field]
    exact hξ.pointFn_ext ((σ_reg j i).mono inf_le_left)
      (((L.regular i k).mul (σ_reg j k)).mono (by simp)) h_agree A t (landsIn_inf.mpr ⟨hi, hk⟩)
  -- No common zero: near a point of `L.opens k`, the function `1` is a combination of the `σ j k`.
  have σ_ne (k : J × (J → Z)) (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Z)
      (ht : LandsIn t (L.opens k)) : ∃ j : J, σ j k (CommRingCat.of K) t ≠ 0 := by
    obtain ⟨V, hV, e', c', hc', h_sum'⟩ := h_mw k.fst (t (IsLocalRing.closedPoint K))
    have h_reg : (c' * ∑ q : Q, σ (e' q) k).IsRegularOn (L.opens k ⊓ V) := by
      intro A B φ u hu
      obtain ⟨hu_L, hu_V⟩ := landsIn_inf.mp hu
      simp [hc' φ u hu_V, σ_reg _ k φ u hu_L]
    -- At `ξ a` the combination is `(c' * ∑ q, w a (e' q)) / m a k.fst`, and `h_sum'` says that the
    -- numerator is `m a k.fst`.
    have h_agree (a : X) (ha : LandsIn (ξ a) (L.opens k ⊓ V)) :
        (c' * ∑ q : Q, σ (e' q) k) (CommRingCat.of ℂ) (ξ a) = 1 := by
      obtain ⟨ha_L, ha_V⟩ := landsIn_inf.mp ha
      simpa [σ_val, ← sum_div, ← mul_div_assoc, m_ne, ha_L, div_eq_one_iff_eq] using h_sum' a ha_V
    have h_one : (c' * ∑ q : Q, σ (e' q) k) (CommRingCat.of K) t = 1 :=
      hξ.pointFn_ext (g := 1) h_reg (by simp [IsRegularOn]) h_agree _ t
        (landsIn_inf.mpr ⟨ht, landsIn_iff_mem.mpr hV⟩)
    by_contra! h_zero
    simp [h_zero] at h_one
  obtain ⟨f, h_class, h_coords⟩ :
      ∃ f : Z ⟶ ProjSpace J, L.picClass = ((ProjSpace.hyperplaneBundle J).pull f).picClass ∧
        ∀ (k : J × (J → Z)) (A : CommRingCat) (t : Spec A ⟶ Z), LandsIn t (L.opens k) →
          ((ProjSpace.hyperplaneBundle J).pull f).IsHomogeneousCoords t fun j : J ↦ σ j k A t :=
    L.exists_picClass_eq_pull_hyperplane (𝟙 Z) σ_section fun k K _ t ↦ σ_ne k K (t ≫ 𝟙 Z)
  refine ⟨_, ProjSpace.isLinearSystem_hyperplaneBundle.pull f, fun a ↦ ?_,
    by simpa [L] using h_class.symm⟩
  -- In a chart `k` containing `ξ a` the vector `w a / m a k.fst` gives coordinates; scale it by
  -- the unit `m a k.fst`.
  obtain ⟨k, hk⟩ := L.exists_landsIn (ξ a)
  have h_div : ((ProjSpace.hyperplaneBundle J).pull f).IsHomogeneousCoords (ξ a)
      fun j : J ↦ w a j / m a k.fst := by simpa only [σ_val _ k a hk] using h_coords k _ _ hk
  have h_scale : w a = m a k.fst • fun j : J ↦ w a j / m a k.fst :=
    funext fun j ↦ (mul_div_cancel₀ (w a j) (m_ne k a hk)).symm
  rw [h_scale]
  exact h_div.smul (m_ne k a hk).isUnit

end LinearSystemExtension

/-!
## Theta families from dense complex points carrying theta tori

Smoothness and the group axioms by density, the level coordinates of a theta torus, padding tuples,
and the extension of the group law and of the theta structure from the points `η i` to `A`.
-/

namespace New

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory NumberField
  ThetaObject Obj LineBundle PointFn AddObj Variety ThetaNull Scheme ThetaTori ThetaTorus PeriodMap
  Category Over Spec IsLocalRing

attribute [local instance low] Fintype.ofFinite

variable {V ι κ : Type} [FinComplexSpace V] {S : Scheme} [IsReduced S] [IsLocallyNoetherian S]
  [Finite ι] {η : κ → (Spec (CommRingCat.of ℂ) ⟶ S)}

omit [Finite ι] in
/-- Homogeneous coordinates for a product of line bundles: if for each factor `l : K` the values
`θ k (w l)`, `k : ι`, are homogeneous coordinates of `t` for `M l`, then the products
`∏ l, θ (μ l) (w l)`, indexed by `μ : K → ι`, are homogeneous coordinates of `t` for the product
bundle `LineBundle.pi M`. Here `V` is any type. -/
lemma LineBundle.IsHomogeneousCoords.pi {K : Type} {X : Scheme} {t : Spec (CommRingCat.of ℂ) ⟶ X}
    {V : Sort*} [Fintype K] {M : K → LineBundle X ι} {θ : ι → V → ℂ} {w : K → V}
    (h : ∀ l : K, (M l).IsHomogeneousCoords t fun k : ι ↦ θ k (w l)) :
    (LineBundle.pi M).IsHomogeneousCoords t fun μ : K → ι ↦ ∏ l : K, θ (μ l) (w l) := by
  simp_all [IsHomogeneousCoords, landsIn_iInf, Finset.prod_ne_zero_iff, Finset.prod_mul_distrib]

open HasRingHomProperty MorphismProperty Hom in
omit [IsReduced S] in
/-- A flat proper commutative group scheme A over a locally noetherian S is smooth if every point of
S specialises to the image of a point over an algebraically closed field along which the fibre of A
is reduced. -/
lemma smooth_of_allSpecializeTo_isReduced {A : Over S} [AddObj A] [Flat A.hom] [IsProper A.hom]
    (h_reduced : AllSpecializeTo S fun t ↦ AlgebraicGeometry.IsReduced (Limits.pullback A.hom t)) :
    Smooth A.hom := by
  -- The smooth locus is open, so it suffices that every y specialises to a point x in it.
  let π : A.left ⟶ S := A.hom
  refine smoothLocus_eq_top_iff.mp (top_unique fun y _ ↦ ?_)
  obtain ⟨k, _, _, t, h_spec : π y ⤳ t (closedPoint k), h_red⟩ : ∃ (k : Type) (_ : Field k)
    (_ : IsAlgClosed k) (t : Spec (CommRingCat.of k) ⟶ S), π y ⤳ t (closedPoint k) ∧
    AlgebraicGeometry.IsReduced (Limits.pullback A.hom t) := h_reduced (π y)
  obtain ⟨x, hyx, hx⟩ : ∃ x : A.left, y ⤳ x ∧ π x = t (closedPoint k) :=
    π.isClosedMap.specializingMap h_spec
  refine hyx.mem_open π.smoothLocus.is_open' ?_
  -- The fibre along t is a reduced group over an algebraically closed field: its smooth locus is
  -- dense, hence non-empty, and translations spread smoothness to the whole group.
  have h_geom : Smooth (pullback.snd π t) := by
    have h_dense : Dense ((pullback.snd π t).smoothLocus : Set ↥(Limits.pullback π t)) :=
      (pullback.snd π t).dense_smoothLocus_of_perfectField
    -- The fibre is non-empty: it contains a point over `x`.
    have h_nonempty : Nonempty (pullback.snd π t).smoothLocus :=
      (h_dense.nonempty_iff.mpr (Pullback.exists_preimage_pullback x _ hx).nonempty).to_subtype
    refine (pullbackAddObj t).property_of_isOpenImmersion _ (Opens.ι _) h_nonempty ?_
    simp [π, ← smoothLocus_eq_top_iff, ← preimage_smoothLocus_eq]
  obtain ⟨U, hU, htU⟩ : ∃ V : S.Opens, IsAffineOpen V ∧ LandsIn t V := exists_isAffineOpen_landsIn t
  have hxU : π x ∈ U := by
    rw [hx]
    exact landsIn_iff_mem.mp htU
  obtain ⟨W, hW, hxW, hWU⟩ : ∃ W : A.left.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ π ⁻¹ᵁ U :=
    exists_isAffineOpen_mem_and_subset (π.mem_preimage.mpr hxU)
  -- Smoothness descends from k to the residue field of the image of t.
  have h_fibre : Smooth ((hW.fromSpec ≫ π).fiberToSpecResidueField (t (closedPoint k))) := by
    -- `id (closedPoint k)`: in this form the surjectivity instance below is found.
    refine of_isPullback_of_descendsAlong (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (isPullback_fiberToSpecResidueField_of_isPullback
        (.paste_vert (.of_hasPullback ..) (.of_hasPullback _ t)) (id (closedPoint k))).flip ?_ ?_
    · and_intros <;> infer_instance
    · exact of_isPullback (.of_hasPullback ..) (comp_mem _ _ _ inferInstance h_geom)
  -- Fibre criterion: Γ(U) → Γ(W) is flat, finitely presented, and has a smooth fibre through x.
  let : Algebra Γ(S, U) Γ(A.left, W) := (π.appLE U W hWU).hom'.toAlgebra
  have : Module.Flat Γ(S, U) Γ(A.left, W) := π.flat_appLE hU hW hWU
  have : Algebra.FinitePresentation Γ(S, U) Γ(A.left, W) := π.finitePresentation_appLE hU hW hWU
  let 𝔮 : Ideal Γ(A.left, W) := (hW.primeIdealOf ⟨x, hxW⟩).asIdeal
  let 𝔭 : Ideal Γ(S, U) := 𝔮.under Γ(S, U)
  suffices Algebra.FormallySmooth 𝔭.ResidueField (𝔭.Fiber Γ(A.left, W)) from
    (formallySmooth_stalkMap_iff U hU W hW hWU hxW).mpr (.of_formallySmooth_fiber 𝔭 𝔮)
  -- Restate the fibre through Spec Γ(W) → Spec Γ(U), at the prime under the prime of x.
  have h_point :
      hU.fromSpec (Spec.map (π.appLE U W hWU) (hW.primeIdealOf ⟨x, hxW⟩)) = t (closedPoint k) := by
    -- `erw`: `primeIdealOf` is a point of the prime spectrum, which is the carrier of
    -- `Spec Γ(A.left, W)` only after unfolding.
    erw [← Hom.comp_apply, hU.SpecMap_appLE_fromSpec _ hW, Hom.comp_apply, hW.fromSpec_primeIdealOf,
      hx]
  rw [← h_point, ← hU.SpecMap_appLE_fromSpec π hW hWU] at h_fibre
  -- The ring-theoretic fibre at that prime is isomorphic to it, so it is smooth.
  have h_alg_smooth : Algebra.Smooth 𝔭.ResidueField (𝔭.Fiber Γ(A.left, W)) :=
    RingHom.smooth_algebraMap.mp (Spec_iff.mp (of_isPullback
      (.paste_horiz (.of_horiz_isIso ⟨(fiberToSpecResidueFieldIso ..).inv.w⟩)
        (isPullback_fiberToSpecResidueField_of_isPullback (.of_horiz_isIso_mono ⟨id_comp _⟩)
          (Spec.map (π.appLE U W hWU) _))) h_fibre))
  exact h_alg_smooth.formallySmooth

/-- Group and module laws by density. Let `V` be a finite-dimensional complex space, `O` a
commutative ring and `S` reduced and locally noetherian with complex points `η i`, the finite
subfamily `η ∘ j` being dense. Let `A` be flat and proper over `S` with a reduced geometric fibre at
a specialisation of every point, and let maps `e i : V → A(η i)` be such that all points `e i z`
separate `A` and, for each `i`, the `e i v` separate the fibre of `A` over `η i`. If the addition,
the zero and the action `F i` of `O` on `V` extend to morphisms `m`, `o` and `f c` of `A`, then `A`
is an abelian scheme with an `O`-module structure, each `e i` is additive, and
`c • e i z = e i (F i c z)`. -/
lemma exists_isAbelianScheme (j : ι → κ) (hη : IsDenseFamily fun i : ι ↦ η (j i)) {O : Type}
    [CommRing O] {A : Over S} {e : ∀ i : κ, V → (Over.mk (η i) ⟶ A)}
    (he_sep : ∀ i : κ, IsSeparatingFamily fun v : V ↦ (lift (e i v) (𝟙 (Over.mk (η i)))).left)
    (h_sep : IsSeparatingFamily fun s : κ × V ↦ (e s.1 s.2).left) [Flat A.hom] [IsProper A.hom]
    (h_reduced : AllSpecializeTo S fun t ↦ IsReduced (pullback A.hom t))
    {f : O → (A ⟶ A)} {F : κ → O →+* V →L[ℂ] V}
    (hf : ∀ (d : O) (i : κ) (z : V), e i z ≫ f d = e i (F i d z))
    (m : A ⊗ A ⟶ A) (o : 𝟙_ (Over S) ⟶ A)
    (hm : ∀ (i : κ) (y z : V), e i (y + z) = lift (e i y) (e i z) ≫ m)
    (ho : ∀ i : κ, toUnit (Over.mk (η i)) ≫ o = e i 0) :
    ∃ (_ : IsAbelianScheme A) (_ : ModuleObj O A) (ε : ∀ i : κ, V →+ (Over.mk (η i) ⟶ A)),
      (e = fun (i : κ) (z : V) ↦ ε i z) ∧ ∀ (c : O) (i : κ) (z : V), c • e i z = e i (F i c z) := by
  -- Every axiom is an equality of morphisms out of A, A ⊗ A or A ⊗ A ⊗ A. The points e, their
  -- pairs and their triples separate these schemes, so each axiom reduces to the same law in V.
  -- `IsSeparatingFamily` is the conjunction of reducedness and density.
  have h_red : IsReduced A.left := And.left h_sep
  have h_pairs : IsSeparatingFamily fun z : (κ × V) × V ↦
      (lift (e z.1.1 z.2) (e z.1.1 z.1.2)).left :=
    h_sep.prod (y := fun s : κ × V ↦ e s.1 s.2) (e := fun s : κ × V ↦ e s.1) hη h_red
      fun s : κ × V ↦ (he_sep s.1).right
  have h_flat : Flat (A ⊗ A).hom := Flat.comp (pullback.fst ..) _
  have h_triples : IsSeparatingFamily fun z : ((κ × V) × V) × V ↦
      (lift (e z.1.1.1 z.2) (lift (e z.1.1.1 z.1.2) (e z.1.1.1 z.1.1.2))).left :=
    h_pairs.prod (y := fun s : (κ × V) × V ↦ lift (e s.1.1 s.2) (e s.1.1 s.1.2))
      (e := fun s : (κ × V) × V ↦ e s.1.1) hη h_red fun s : (κ × V) × V ↦ (he_sep s.1.1).right
  have h_left : (λ_ A).inv = lift (toUnit A) (𝟙 A) := by aesop
  have h_right : (ρ_ A).inv = lift (𝟙 A) (toUnit A) := by aesop
  let _ : AddGrpObj A :=
    { zero := o
      add := m
      neg := f (-1)
      zero_add := (λ_ A).inv_comp_eq_id.1 (h_sep.hom_ext (by simp [← hm, ho, ← assoc, h_left]))
      add_zero := (ρ_ A).inv_comp_eq_id.1 (h_sep.hom_ext (by simp [← hm, ho, ← assoc, h_right]))
      add_assoc :=
        (α_ A A A).inv_comp_eq.1 (h_triples.hom_ext (by simp [← hm, ← assoc, add_assoc]))
      left_neg := h_sep.hom_ext (by simp [← hm, ho, hf, ← assoc])
      right_neg := h_sep.hom_ext (by simp [← hm, ho, hf, ← assoc]) }
  let _ : AddObj A :=
    { add_comm := h_pairs.hom_ext (by simp +zetaDelta [← hm, ← assoc, AddMonObj.add, add_comm]) }
  have h_add (T : Over S) (x y : T ⟶ A) : x + y = lift x y ≫ m := rfl
  -- The endomorphisms f c are additive and depend on c as a ring action.
  have hf_hom (c : O) : IsAdditive (f c) :=
    isAdditive_of_universal (h_pairs.hom_ext (by simp [h_add, ← hm, hf, ← assoc]))
  have hf_add (c d : O) : f (c + d) = f c + f d :=
    h_sep.hom_ext (by simp [h_add, ← hm, hf, ← assoc])
  have hf_mul (c d : O) : f (c * d) = f d ≫ f c := h_sep.hom_ext (by simp [hf, ← assoc])
  have hf_one : f 1 = 𝟙 A := h_sep.hom_ext (by simp [hf])
  let module (T : Over S) : Module O (T ⟶ A) :=
    letI : SMul O (T ⟶ A) := ⟨fun c x ↦ x ≫ f c⟩
    Module.ofMinimalAxioms (fun c x y ↦ add_comp x y (f c))
      (fun c d x ↦ (x ≫= hf_add c d).trans (comp_add ..)) (fun c d x ↦ x ≫= hf_mul c d)
      fun x ↦ x ≫= hf_one
  let moduleObj : ModuleObj O A := { comp_smul _ _ _ := (assoc ..).symm }
  -- Multiplication by N ≠ 0 is f N. It sends e i (N⁻¹ • z) to e i z, so its closed image is dense.
  have h_onto (N : ℕ) (hN : N ≠ 0) : Surjective (N • 𝟙 A).left := by
    rw [← N.cast_smul_eq_nsmul O (𝟙 A)]
    have h_dense : IsDenseFamily fun s : κ × V ↦ (e s.1 s.2).left := And.right h_sep
    refine h_dense.surjective _ (fun z : κ × V ↦ (e z.1 ((N⁻¹ : ℂ) • z.2)).left) fun z ↦ ?_
    have h_comp_left :
        (e z.1 ((N⁻¹ : ℂ) • z.2) ≫ f N).left = (e z.1 (F z.1 N ((N⁻¹ : ℂ) • z.2))).left :=
      congrArg CommaMorphism.left (hf N z.1 ((N⁻¹ : ℂ) • z.2))
    refine h_comp_left.trans ?_
    simp [← N.cast_smul_eq_nsmul ℂ, hN]
  exact ⟨{ toSmooth := smooth_of_allSpecializeTo_isReduced h_reduced, nsmul_surjective := h_onto },
    moduleObj, fun i ↦ .mk' (e i) (hm i), rfl, hf⟩

section LevelCoordinates

variable {E : Type} [Field E] [CMBase E] {D : PEL E}

/-- The index `a` of the subgroup `D.dualTorsion` of level torsion does not vanish at the point `t`
of `S`: `c` gives a line bundle on `S` with charts indexed by `D.dualTorsion` for each level torsion
point, and for all `l k : D.dualTorsion` with `l + k = a` the point `t` lies in chart `k` of the
bundle `c l`. -/
def Variety.ThetaNull.IsNonvanishingIndex {S : Scheme}
    (c : D.levelTorsion → LineBundle S D.dualTorsion) (t : S) (a : D.dualTorsion) : Prop :=
  ∀ l k : D.dualTorsion, l + k = a → t ∈ (c ⟨l, D.dualTorsion_le_levelTorsion l.property⟩).opens k

/-- The fibre of the theta family `X` at the complex point `t` is modelled on the theta torus `x`:
it has a torus model (a uniformisation by `V` along `t` with theta coordinates) for the period map
of `x`, whose theta coordinates are the theta functions of `x`. -/
def ThetaFamily.IsModelledOn {S : Scheme} {τ : S ⟶ Spec (CommRingCat.of (𝓞 E))}
    (X : ThetaFamily D S τ) (t : Spec (CommRingCat.of ℂ) ⟶ S) {g : GL D.Index (𝔸f E)}
    {ℓ : Matrix D.Index D.Index ℂ} (x : ThetaTorus D g ℓ V) : Prop :=
  ∃ m : TorusModel (X := X) t x.toPeriodMap, m.θ = fun z k ↦ x.thetaCoord k z

section Torus

variable {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ} (x : ThetaTorus D g ℓ V)

/-- Let `t` be a complex point of `S` at which, for each level torsion point `ω`, the theta values
of `x` at the lift of `ω` are homogeneous coordinates for the line bundle `c ω`. Then at `t` the
bundles `c ω` cut out the set of all theta vectors of `x`: in every choice of charts through `t`,
the rank conditions `thetaRanks` on the transition values define that set (`IsCutOutAt`). -/
lemma ThetaTori.ThetaTorus.isCutOutAt_range_thetaCoord {S : Scheme}
    {t : Spec (CommRingCat.of ℂ) ⟶ S} {c : D.levelTorsion → LineBundle S D.dualTorsion}
    (hx : ∀ ω : D.levelTorsion,
      (c ω).IsHomogeneousCoords t fun k : D.dualTorsion ↦ x.thetaCoord k (x.torsionLift ω)) :
    IsCutOutAt D.paddedNorm D.exponentBound (thetaRanks D.dualTorsion D.paddedNorm) c t
      (Set.range fun (z : V) (k : D.dualTorsion) ↦ x.thetaCoord k z) := by
  -- For the trivial valuation on ℂ every theta vector is its own reduction.
  have h_le (z : ℂ) : (1 : Valuation ℂ NNReal) z ≤ 1 := Valuation.one_apply_le_one z
  have h_aff (z : V) :
      IsIntegralCoords (fun k : D.dualTorsion ↦ x.thetaCoord k z)
        fun k : D.dualTorsion ↦ ⟨x.thetaCoord k z, h_le _⟩ :=
    -- Scale by `1`; a theta value at `z` that is nonzero has valuation `1`.
    ⟨1, by simpa [funext_iff] using x.thetaCoord_vector_ne_zero z⟩
  exact x.isCutOutAt_reduction (φ := algebraMap ..) (fun z ↦ ⟨⟨z, h_le z⟩, rfl⟩)
    x.hasGoodReduction_one h_aff
    (fun ω : D.levelTorsion ↦ h_aff (x.torsionLift ω)) hx

/-- Translation by the lift to `V` of `l ∈ D.dualTorsion` shifts the index `k` of a theta function
of `x` by `l`, up to an exponential factor, the multiplier of `x` and the value at `k` of the
bicharacter (the additive character of `D.dualTorsion` attached to the lift of `l`). -/
lemma ThetaTori.ThetaTorus.thetaCoord_add_torsionLift (l k : D.dualTorsion) (z : V) :
    x.thetaCoord k (z + x.torsionLift l) =
      (x.automorphyForm (x.torsionLift l) z + x.automorphyForm (x.torsionLift l) (x.torsionLift l) /
        2).exp *
        (x.multiplier (x.torsionLift l) * x.bicharacter
          (torsionLift_mem_latticeOver x.toPeriodMap l) k *
          x.thetaCoord (l + k) z) := by
  -- This is the Heisenberg law for the period point of the representative of `l`, at `z`.
  have h_lift : x.periodPoint (ratLift g (l : AdelicTorsion E D.Index)) = x.torsionLift l := rfl
  simpa [thetaShift_apply, ← eq_inv_mul_iff_mul_eq₀, h_lift, ← Complex.exp_neg] using
    congrFun (x.thetaShift_thetaCoord (frameTorsionClass_ratLift (l : AdelicTorsion E D.Index)) k) z

/-- For `s` in `D.dualTorsion` outside the Lagrangian subgroup, the square of the bicharacter of `s`
(an additive character of `D.dualTorsion`) sums to zero over the Lagrangian, as it is a non-trivial
character there. -/
lemma ThetaTori.ThetaTorus.sum_bicharacter_sq_eq_zero
    [Fintype (D.lagrangian.addSubgroupOf D.dualTorsion)] {s : D.dualTorsion}
    (hs : s ∉ D.lagrangian.addSubgroupOf D.dualTorsion) :
    ∑ l : D.lagrangian.addSubgroupOf D.dualTorsion,
      x.bicharacter (torsionLift_mem_latticeOver x.toPeriodMap s) l ^ 2 =
      0 := by
  -- The square, restricted to the Lagrangian, is a non-trivial additive character there.
  let ψ : AddChar (D.lagrangian.addSubgroupOf D.dualTorsion) ℂ :=
    (x.bicharacter (torsionLift_mem_latticeOver x.toPeriodMap s) ^ 2).compAddMonoidHom
      (D.lagrangian.addSubgroupOf D.dualTorsion).subtype
  have h_nontrivial : ψ ≠ 0 := fun h_trivial ↦
    hs (x.mem_lagrangian_of_bicharacter_sq s (DFunLike.congr_fun h_trivial))
  change ∑ l : D.lagrangian.addSubgroupOf D.dualTorsion, ψ l = 0
  exact ψ.sum_eq_zero_iff_ne_zero.mpr h_nontrivial

/-- Let `b` be an integer. There is a nonzero `Y : V` on which `𝓞 E` acts through `ρ`, that is,
through the embedding `Φ v₀`, such that the map `w ↦ x.intAction (star β - b) w - ρ (β - b) • w`
takes its values in the line through `Y`: it is `w ↦ ξ w • Y` for a linear form `ξ`. -/
lemma ThetaTori.ThetaTorus.exists_eigenline (b : ℤ) {ρ : 𝓞 E →+* ℂ}
    (hρ : ∀ d : 𝓞 E, ρ d = Φ v₀ d.val) :
    ∃ Y : V, Y ≠ 0 ∧ (∀ d : 𝓞 E, x.intAction d Y = ρ d • Y) ∧
      ∃ ξ : V →ₗ[ℂ] ℂ, ∀ w : V, x.intAction (star D.β - b) w - ρ (D.β - b) • w = ξ w • Y := by
  -- Coordinates `ε` in which `d : 𝓞 E` acts diagonally: by `Φ v₀ d` on the first axis, by its
  -- conjugate on the second, and by `Φ w d` at each other place `w`.
  obtain ⟨ε, hε⟩ := x.exists_std_equiv
  have h_std (d : 𝓞 E) (z : V) : ε (x.intAction d z) =
      ((Φ v₀ d.val * (ε z).fst.fst, star (Φ v₀ d.val) • (ε z).fst.snd),
        fun w ↦ Φ w.1 d.val • (ε z).snd w) := by
    -- `using!`: the last component comes out as `Pi.map` of the diagonal maps, which is the
    -- stated function only after unfolding.
    simpa using! LinearMap.congr_fun (hε d) (ε z)
  -- The line is the first coordinate axis; on the other coordinates `star β` acts by `Φ v₀ β`.
  refine ⟨ε.symm ((1, 0), 0), ?_, fun d ↦ ?_,
    Φ v₀ (star D.β.val - D.β) • .fst .. ∘ₗ .fst .. ∘ₗ ε.toLinearMap, fun w ↦ ?_⟩
  · simp [← ε.injective.eq_iff]
  · simp [hρ, ← ε.injective.eq_iff, h_std, map_smul, funext_iff]
  · simp +contextual [hρ, ← ε.injective.eq_iff, D.emb_beta_eq_of_ne, h_std, Prod.ext_iff, sub_mul,
      map_smul, funext_iff]

/-- Let `N` embed `A` in projective space over `S`, and let `e : V →+ A(t)` be an additive map to
the points of `A` over the complex point `t` whose coordinates for `N` are the theta vectors of `x`.
Then `e` vanishes on the period lattice of `x`. -/
lemma ThetaTori.ThetaTorus.map_eq_zero_of_mem_periodLattice {S : Scheme}
    {t : Spec (CommRingCat.of ℂ) ⟶ S} {A : Over S} [AddObj A] {N : LineBundle A.left D.dualTorsion}
    (hN : N.IsProjEmbedding A.hom) {e : V →+ (Over.mk t ⟶ A)}
    (he_coords : ∀ z : V, N.IsHomogeneousCoords (e z).left fun k : D.dualTorsion ↦ x.thetaCoord k z)
    {l : V} (hl : l ∈ x.periodLattice) : e l = 0 := by
  -- The coordinates at `0 + l` are those at `0` times the factor of automorphy at the period `l`,
  -- which is nonzero; so they are also coordinates of `e 0`.
  have h_zero : N.IsHomogeneousCoords (e 0).left fun k : D.dualTorsion ↦
    x.thetaCoord k (0 + l) := by
    rw [funext fun k ↦ (x.thetaCoord_mem_thetaSpace k).2 l hl 0]
    exact (he_coords 0).smul (by simp [x.isAppellHumbert_periodLattice.ne_zero hl])
  -- Both points lie over `t` and have the same coordinates, so they are equal.
  have h_left : (e (0 + l)).left = (e 0).left :=
    hN.eq_of_isHomogeneousCoords (by simp) (he_coords (0 + l)) h_zero (N.exists_landsIn _)
  simpa using OverMorphism.ext h_left

end Torus

/-- The padding tuple of `a` and `d` (two pairs `(1, 0)`, the pairs `(d, 1)` and `(1, - star d)`,
and the pairs `(a l, 0)`) is a Riemann tuple for `D` when
`star d * d + 3 + ∑ l, star (a l) * a l = D.paddedNorm`. -/
lemma isRiemannTuple_paddingTuple {a : Fin (D.paddedNorm - 3) → 𝓞 E} {d : 𝓞 E}
    (ha : star d * d + 3 + ∑ l : Fin (D.paddedNorm - 3), star (a l) * a l = D.paddedNorm) :
    IsRiemannTuple (paddingTuple a d) D := by
  -- Both sums run over two pairs `(1, 0)`, the pairs `(d, 1)` and `(1, - star d)`, and the
  -- pairs `(a l, 0)`: the first is `D.paddedNorm` by `ha`, and in the second `star d - star d`
  -- cancels.
  simp [IsRiemannTuple, ← ha, paddingTuple]
  ring

lemma isRiemannTuple_paddingTuple_one_zero :
    IsRiemannTuple (paddingTuple (1 : Fin (D.paddedNorm - 3) → 𝓞 E) 0) D :=
  isRiemannTuple_paddingTuple (by simp [D.three_le_paddedNorm])

/-- Let `A` over `S` be a commutative group scheme with an action of `𝓞 E`, and `c` a class in
`Pic A.left` satisfying Riemann's relation: for all `d` and `a : Fin (D.paddedNorm - 3) → 𝓞 E` with
`d̄ d + 3 + ∑ ā_l a_l = D.paddedNorm`, and all `T`-points `y`, `z`, the pull-backs satisfy
`c(d y + z) + c(y - d̄ z) + ∑ c(a_l y) + c(0) = c(z) + c(-d̄ z) + c(y) + (D.paddedNorm - 3) c(y)`.
Then `c` satisfies the class laws `D.HasClassLaws`: (a) the parallelogram law;
(b) `⟨β x, y⟩ = ⟨x, (1 - β) y⟩` for the pairing `Pic.pairing`, where `β` is the integer of `D` with
`star β = 1 - β`; and (c) the pull-back of `c` along `y` is `⟨β y, y⟩` plus its pull-back along
`0`. -/
lemma PEL.hasClassLaws_of_riemann_relation {S : Scheme} {A : Over S} [AddObj A]
    [ModuleObj (𝓞 E) A] {c : Pic A.left}
    (h_riemann : ∀ (a : Fin (D.paddedNorm - 3) → 𝓞 E) (d : 𝓞 E),
      star d * d + 3 + ∑ l : Fin (D.paddedNorm - 3),
        star (a l) * a l = D.paddedNorm → ∀ (T : Over S) (y z : T ⟶ A),
        c.atPoint (d • y + z) + c.atPoint (y - star d • z) +
          ∑ l : Fin (D.paddedNorm - 3), c.atPoint (a l • y) +
            c.atPoint (0 : T ⟶ A) =
          c.atPoint z + c.atPoint (-(star d • z)) + c.atPoint y + (D.paddedNorm - 3) • c.atPoint
            y) :
    D.HasClassLaws c := by
  -- `a` and `b` are paddings of `1` and `β`.
  obtain ⟨a, -, ha⟩ := D.hasPadding_one
  obtain ⟨b, -, hb⟩ := D.hasPadding_beta
  -- Subtract the relation at `(y, 0)` for a `d'` of the same norm: the padding terms cancel.
  have h_diff {a : Fin (D.paddedNorm - 3) → 𝓞 E} {d' : 𝓞 E}
      (ha : star d' * d' + 3 + ∑ l : Fin (D.paddedNorm - 3), star (a l) * a l = D.paddedNorm)
        (d : 𝓞 E)
      (hd : star d * d = star d' * d') {T : Over S} (y z : T ⟶ A) :
      c.atPoint (d • y + z) + c.atPoint (y - star d • z) + 2 • c.atPoint (0 : T ⟶ A) =
        c.atPoint (d' • y) + c.atPoint y + c.atPoint z + c.atPoint (-(star d • z)) := by
    have h_at_zero : c.atPoint (d' • y) + c.atPoint y +
          ∑ l : Fin (D.paddedNorm - 3), c.atPoint (a l • y) + c.atPoint (0 : T ⟶ A) =
        c.atPoint (0 : T ⟶ A) + c.atPoint (0 : T ⟶ A) + c.atPoint y + (D.paddedNorm - 3) • c.atPoint
          y := by
      simpa only [add_zero, smul_zero, sub_zero, neg_zero] using h_riemann a d' ha T y 0
    linear_combination (norm := abel) h_riemann a d (by rw [hd, ha]) T y z - h_at_zero
  refine ⟨fun T y z ↦ ?_, fun T y z ↦ ⟨?_, ?_⟩⟩
  · -- The parallelogram law is the case `d = -1`, `d' = 1` at the point `(z, y)`.
    have h_par : c.atPoint (y - z) + c.atPoint (y + z) + 2 • c.atPoint (0 : T ⟶ A) =
        c.atPoint z + c.atPoint z + c.atPoint y + c.atPoint y := by
      simpa [neg_add_eq_sub, add_comm z y] using h_diff ha (-1) (by simp) z y
    linear_combination (norm := abel) h_par
  · -- Take `d = β` at `(y, z)` and `d = 1` at `(y, z - β • z)`. As `star β = 1 - β`, both
    -- relations contain the point `y - (z - β • z)`.
    have h_β : c.atPoint (D.β • y + z) + c.atPoint (y - (z - D.β • z)) +
          2 • c.atPoint (0 : T ⟶ A) =
        c.atPoint (D.β • y) + c.atPoint y + c.atPoint z + c.atPoint (-(z - D.β • z)) := by
      simpa [D.star_beta, sub_smul] using h_diff hb D.β rfl y z
    have h_one : c.atPoint (y + (z - D.β • z)) + c.atPoint (y - (z - D.β • z)) +
          2 • c.atPoint (0 : T ⟶ A) =
        c.atPoint y + c.atPoint y + c.atPoint (z - D.β • z) + c.atPoint (-(z - D.β • z)) := by
      simpa using h_diff ha 1 rfl y (z - D.β • z)
    simp only [Pic.pairing, sub_smul, one_smul]
    linear_combination (norm := abel) h_β - h_one
  · -- Take `d = -star β` at `(z, z)`: as `star β = 1 - β`, `-star β • z + z = β • z`.
    have h_ev : c.atPoint (D.β • z) + c.atPoint (z + D.β • z) + 2 • c.atPoint (0 : T ⟶ A) =
        c.atPoint (D.β • z) + c.atPoint z + c.atPoint z + c.atPoint (D.β • z) := by
      simpa [D.star_beta, sub_smul, add_comm z] using
        h_diff hb (-star D.β) (by simp [mul_comm]) z z
    rw [Pic.pairing, add_comm (D.β • z) z]
    linear_combination (norm := abel) -h_ev

variable {S : Scheme} {η : κ → (Spec (CommRingCat.of ℂ) ⟶ S)} {R : CommRingCat}
  {g : κ → GL D.Index (𝔸f E)} {ℓ : κ → Matrix D.Index D.Index ℂ}
  {x : ∀ k : κ, ThetaTorus D (g k) (ℓ k) V} {c : D.levelTorsion → LineBundle S D.dualTorsion}

/-- Suppose `c` attaches to each class `ω` in `D.levelTorsion` a linear system on `S` with charts
indexed by `D.dualTorsion`, whose homogeneous coordinates at each `η i` are the theta coordinates of
`x i` at the torsion lift of `ω`, and that for each point `t` and each `s : D.dualTorsion` some `a`
makes `a`, `-a` and `s - a` nonvanishing indices at `t` (`IsNonvanishingIndex c t a`: `t` lies in
the chart `k` of `c l` whenever `l + k = a`). Then the bicharacters of the theta tori are regular
functions near each point. A point `t` of `S` with values in a local ring lands in an open `W` with
regular functions `r l m`, whose value at each `η i` in `W` is the bicharacter of `x i` at the
torsion lift of `l`, evaluated at `m`. -/
lemma Variety.exists_isRegularOn_bicharacter
    (hc : ∀ ω : D.levelTorsion, (c ω).IsLinearSystem)
    (hx : ∀ (i : κ) (ω : D.levelTorsion),
      (c ω).IsHomogeneousCoords (η i) fun k : D.dualTorsion ↦
        (x i).thetaCoord k ((x i).torsionLift ω))
    (h_index : ∀ (t : S) (s : D.dualTorsion), ∃ a : D.dualTorsion,
      IsNonvanishingIndex c t a ∧ IsNonvanishingIndex c t (-a) ∧ IsNonvanishingIndex c t (s - a))
    {B : Type} [CommRing B] [IsLocalRing B] (t : Spec (CommRingCat.of B) ⟶ S) :
    ∃ (W : S.Opens) (r : D.dualTorsion → D.dualTorsion → PointFn S), LandsIn t W ∧
      (∀ l m : D.dualTorsion, IsRegularOn (r l m) W) ∧
      ∀ (l m : D.dualTorsion) (i : κ), LandsIn (η i) W →
        r l m (CommRingCat.of ℂ) (η i) =
          (x i).bicharacter (torsionLift_mem_latticeOver (x i).toPeriodMap l) m := by
  -- `t` factors through the open set `W` where the coordinates chosen by `o` are units.
  choose o _ho ho_neg ho_sub using h_index (t (closedPoint B))
  let W : S.Opens :=
    ⨅ (l : D.dualTorsion) (m : D.dualTorsion),
      ((c ⟨l, D.dualTorsion_le_levelTorsion l.property⟩).mul (c 0)).opens (-o m - l, m - o m)
  have hW : LandsIn t W := (landsIn_iInf _).2 fun l ↦ (landsIn_iInf _).2 fun m ↦
    landsIn_iff_mem.2 ⟨ho_neg m l _ (by simp), ho_sub m 0 _ (by simp)⟩
  -- Write `X k l` for the coordinate `k` of `c l` and `o` for `o m`. The function is
  -- `X (m - o - l) l * X (-o) 0 / (X (-o - l) l * X (m - o) 0)`: by `thetaCoord_add_torsionLift`
  -- at `z = 0` the theta constants cancel.
  have h_cocycle (l m : D.dualTorsion) : ∃ r : PointFn S, IsRegularOn r W ∧ ∀ i : κ,
    LandsIn (η i) W →
      r (CommRingCat.of ℂ) (η i) =
        (x i).bicharacter (torsionLift_mem_latticeOver (x i).toPeriodMap l) m := by
    -- The product bundle of `c l` and `c 0`, and the chart of it that contains `W`.
    let M : LineBundle S (D.dualTorsion × D.dualTorsion) :=
      (c ⟨l, D.dualTorsion_le_levelTorsion l.property⟩).mul (c 0)
    have hW_le : W ≤ M.opens (-o m - l, m - o m) := (iInf_le _ l).trans (iInf_le _ m)
    have hM : M.IsLinearSystem := (hc _).mul (hc 0)
    refine ⟨M.transition (-o m - l, m - o m) (m - o m - l, -o m),
      (hM.isRegularOn_transition _ _).mono hW_le, fun i hi ↦ ?_⟩
    -- At `z = 0`, the shift by the lift of `l` turns the index `k` into `l + k`.
    have h_shift (k : D.dualTorsion) : (x i).thetaCoord k ((x i).torsionLift l) =
        ((x i).automorphyForm ((x i).torsionLift l) 0 +
            (x i).automorphyForm ((x i).torsionLift l) ((x i).torsionLift l) / 2).exp *
          ((x i).multiplier ((x i).torsionLift l) *
            (x i).bicharacter (torsionLift_mem_latticeOver (x i).toPeriodMap l) k *
            (x i).thetaCoord (l + k) 0) := by
      simpa only [zero_add] using (x i).thetaCoord_add_torsionLift l k 0
    -- By `hx` the transition is a ratio of theta constants; `h_shift` leaves the bicharacter.
    have hi_chart : LandsIn (η i) (M.opens (-o m - l, m - o m)) := hi.mono hW_le
    revert hi_chart
    simp +contextual [M, hx .., sub_eq_add_neg, field, h_shift, AddChar.map_add_eq_mul]
  choose r hr hr_val using h_cocycle
  exact ⟨W, r, hW, hr, hr_val⟩

variable {V κ : Type} [FinComplexSpace V] {E : Type} [Field E] [CMBase E] {D : PEL E} {S : Scheme}
  {η : κ → (Spec (CommRingCat.of ℂ) ⟶ S)} {R : CommRingCat} {g : κ → GL D.Index (𝔸f E)}
  {ℓ : κ → Matrix D.Index D.Index ℂ} {x : ∀ k : κ, ThetaTorus D (g k) (ℓ k) V}
  {c : D.levelTorsion → LineBundle S D.dualTorsion}

/-- Riemann's relation has regular coefficients near every point `t` of `S`. Let `c` have
nonvanishing indices, let `#D.dualTorsion` be a unit in `R`, and let `p`, `q` be Riemann tuples (`q`
starting with `(1, 0), (1, 0)`). Then there are indices `μ' s` and a function `r` regular near `t`
with the following property at each `η i` near `t`. The theta product of `x i` (the product of theta
coordinates `θ_{μ l}(a_l z + b_l y)`) for the pairs `doubledCoeffs p q` (the `(0, b)` of `q`, then
`p`) is `r` times the sum over `s` of those for `doubledCoeffs q p` at `μ' s`. -/
lemma Variety.exists_isRegularOn_riemann_coefficient
    (hc : ∀ ω : D.levelTorsion, (c ω).IsLinearSystem)
    (hx : ∀ (i : κ) (ω : D.levelTorsion),
      (c ω).IsHomogeneousCoords (η i) fun k : D.dualTorsion ↦
        (x i).thetaCoord k ((x i).torsionLift ω))
    (h_index : ∀ (t : S) (s : D.dualTorsion), ∃ a : D.dualTorsion,
      IsNonvanishingIndex c t a ∧ IsNonvanishingIndex c t (-a) ∧ IsNonvanishingIndex c t (s - a))
    {K : Type} [Fintype K] {p q : Bool ⊕ K → 𝓞 E × 𝓞 E} (π : S ⟶ Spec R)
    (hT : IsUnit (Nat.card D.dualTorsion : R)) (hp : IsRiemannTuple p D) (hq : IsRiemannTuple q D)
    (hq_inl : ∀ l : Bool, q (Sum.inl l) = (1, 0)) (μ : (Bool ⊕ K) ⊕ Bool ⊕ K → D.dualTorsion)
      (t : S) :
    ∃ U : S.Opens, t ∈ U ∧ ∃ (μ' : D.dualTorsion → (Bool ⊕ K) ⊕ Bool ⊕ K → D.dualTorsion)
      (r : PointFn S),
      IsRegularOn r U ∧ ∀ (i : κ) (y z : V), LandsIn (η i) U →
        r (CommRingCat.of ℂ) (η i) * ∑ s : D.dualTorsion,
          (x i).thetaProduct (doubledCoeffs q p) (μ' s) y z =
          (x i).thetaProduct (doubledCoeffs p q) μ y z := by
  -- The first two factors are theta constants. Replace their indices by `k - o` and `o`, where
  -- `k` makes the index sums in `riemann_relation` agree and these constants are units near `t`.
  let k : D.dualTorsion := ∑ l : Bool ⊕ K, star (p l).1 • μ (.inr l) -
    ∑ l : K, star (q (.inr l)).1 • μ (.inl (.inr l))
  obtain ⟨o, ho, -, ho_sub⟩ := h_index t k
  let ν : Bool ⊕ K → D.dualTorsion := Sum.elim (fun b ↦ cond b (k - o) o) (μ ∘ .inl ∘ .inr)
  let μ' (s : D.dualTorsion) : (Bool ⊕ K) ⊕ Bool ⊕ K → D.dualTorsion :=
    Sum.elim (fun l ↦ μ (.inr l) - (p l).1 • s) fun l ↦ ν l + (q l).1 • s
  -- The coefficient `r` is the ratio of the old to the new constants, a transition of
  -- `c 0 ⊗ c 0`, times the coefficient `τ` of `riemann_relation`.
  let τ : Γ(S, ⊤) :=
    ↑(hT.map (toSpecΓ R ≫ π.appTop).hom).unit⁻¹ * ↑(D.rTorsion.relIndex D.dualTorsion).sqrt
  let M : LineBundle S (D.dualTorsion × D.dualTorsion) := (c 0).mul (c 0)
  let r : PointFn S :=
    M.transition (o, k - o) (μ (.inl (.inl true)), μ (.inl (.inl false))) * ofSection τ
  have hr : IsRegularOn r (M.opens (o, k - o) ⊓ ⊤) :=
    (((hc 0).mul (hc 0)).isRegularOn_transition _ _).mul (isRegularOn_ofSection τ)
  have ht_mem : t ∈ M.opens (o, k - o) ⊓ ⊤ := ⟨⟨ho 0 _ (by simp), ho_sub 0 _ (by simp)⟩, ⟨⟩⟩
  refine ⟨_, ht_mem, μ', r, hr, fun i y z hi ↦ ?_⟩
  have h_unit : (x i).thetaCoord o 0 ≠ 0 ∧ (x i).thetaCoord (k - o) 0 ≠ 0 := by
    simpa [M, hx ..] using hi
  have h_riemann := (x i).riemann_relation (w := y) hp rfl hq (μ := μ ∘ .inr) (μ' := ν)
    (by simp [ν, k, hq_inl]) z
  simp [ν, hq_inl, mul_assoc, thetaProduct] at h_riemann
  simp [r, M, ofSection_eq, hx .., h_unit, τ, ν, μ', hq_inl, mul_assoc, ← h_riemann,
    mul_left_comm ((x i).thetaCoord o 0)⁻¹, thetaProduct, doubledCoeffs]

/-- Maps of a projective scheme extend along Riemann's relation: if for each pair `(a, b)` of
`doubledCoeffs q p` the map `(z, y) ↦ a z + b y` of the tori extends to `ψ l : A ⊗ A ⟶ A`, then the
maps for `doubledCoeffs p q` extend to morphisms `G l`, and the pull-backs of `N` along the `G l`
and along the `ψ l` have products of the same class. -/
lemma Variety.exists_maps_of_riemann_relation
    (hc : ∀ ω : D.levelTorsion, (c ω).IsLinearSystem)
    (hx : ∀ (i : κ) (ω : D.levelTorsion),
      (c ω).IsHomogeneousCoords (η i) fun k : D.dualTorsion ↦
        (x i).thetaCoord k ((x i).torsionLift ω))
    (h_index : ∀ (t : S) (s : D.dualTorsion), ∃ a : D.dualTorsion,
      IsNonvanishingIndex c t a ∧ IsNonvanishingIndex c t (-a) ∧ IsNonvanishingIndex c t (s - a))
    {K : Type} [Fintype K] {p q : Bool ⊕ K → 𝓞 E × 𝓞 E} (π : S ⟶ Spec R)
    (hT : IsUnit (Nat.card D.dualTorsion : R)) (hp : IsRiemannTuple p D) (hq : IsRiemannTuple q D)
    (hp_inl : ∀ l : Bool, p (Sum.inl l) = (1, 0)) (hq_inl : ∀ l : Bool, q (Sum.inl l) = (1, 0))
    {A : Over S} {N : LineBundle A.left D.dualTorsion} (hN : N.IsProjEmbedding A.hom)
    {e : ∀ i : κ, V → (Over.mk (η i) ⟶ A)}
    (he_coords : ∀ (i : κ) (z : V),
      N.IsHomogeneousCoords (e i z).left fun k : D.dualTorsion ↦ (x i).thetaCoord k z)
    (he_pairs : IsSeparatingFamily fun s : (κ × V) × V ↦
      (lift (e s.1.1 s.2) (e s.1.1 s.1.2)).left)
    (ψ : (Bool ⊕ K) ⊕ Bool ⊕ K → (A ⊗ A ⟶ A))
    (hψ : ∀ (l : (Bool ⊕ K) ⊕ Bool ⊕ K) (i : κ) (y z : V), lift (e i z) (e i y) ≫ ψ l =
      e i ((x i).intAction (doubledCoeffs q p l).1 z + (x i).intAction (doubledCoeffs q p l).2 y)) :
    ∃ G : (Bool ⊕ K) ⊕ Bool ⊕ K → (A ⊗ A ⟶ A),
      (∀ (l : (Bool ⊕ K) ⊕ Bool ⊕ K) (i : κ) (y z : V), lift (e i z) (e i y) ≫ G l =
        e i ((x i).intAction (doubledCoeffs p q l).1 z +
          (x i).intAction (doubledCoeffs p q l).2 y)) ∧
      (pi fun l : (Bool ⊕ K) ⊕ Bool ⊕ K ↦ N.pull (G l).left).picClass =
        (pi fun l : (Bool ⊕ K) ⊕ Bool ⊕ K ↦ N.pull (ψ l).left).picClass := by
  have h_proper : IsProper A.hom := hN.isProper
  let comb (i : κ) (a : 𝓞 E × 𝓞 E) (z y : V) : V := (x i).intAction a.1 z + (x i).intAction a.2 y
  have hψ_coords (s : (κ × V) × V) (l : (Bool ⊕ K) ⊕ Bool ⊕ K) :
      (N.pull (ψ l).left).IsHomogeneousCoords (lift (e s.1.1 s.2) (e s.1.1 s.1.2)).left
        fun k : D.dualTorsion ↦ (x s.1.1).thetaCoord k
          (comb s.1.1 (doubledCoeffs q p l) s.2 s.1.2) := by
    rw [IsHomogeneousCoords.pull_iff, ← comp_left, hψ]
    exact he_coords s.1.1 _
  -- Each side is locally a regular combination of the other, so the side of `G` gives a linear
  -- system `M` as well.
  let w (a b : Bool ⊕ K → 𝓞 E × 𝓞 E) (s : (κ × V) × V) (μ : (Bool ⊕ K) ⊕ Bool ⊕ K → D.dualTorsion) :
    ℂ :=
    (x s.1.1).thetaProduct (doubledCoeffs a b) μ s.1.2 s.2
  have h_local {a b : Bool ⊕ K → 𝓞 E × 𝓞 E} (ha : IsRiemannTuple a D) (hb : IsRiemannTuple b D)
      (hb_inl : ∀ l, b (Sum.inl l) = (1, 0)) : IsLocalCombination D.dualTorsion
        (fun s : (κ × V) × V ↦ (lift (e s.1.1 s.2) (e s.1.1 s.1.2)).left) (w a b) (w b a) := by
    intro μ t
    obtain ⟨U, hU, μ', r, hr, h_sum⟩ :=
      exists_isRegularOn_riemann_coefficient hc hx h_index π hT ha hb hb_inl μ ((A ⊗ A).hom t)
    refine ⟨_, hU, μ', _, hr.pull (A ⊗ A).hom, fun s hs ↦ ?_⟩
    have h_base : (lift (e s.1.1 s.2) (e s.1.1 s.1.2)).left ≫ (A ⊗ A).hom = η s.1.1 := Over.w _
    rw [landsIn_preimage, h_base] at hs
    -- `↓`: `Over.w` must rewrite before `simp` unfolds the point `lift`.
    simpa [w, ↓Over.w] using h_sum s.1.1 s.1.2 s.2 hs
  obtain ⟨M, hM, hM_coords, hM_class⟩ :
      ∃ M : LineBundle (A ⊗ A).left ((Bool ⊕ K) ⊕ Bool ⊕ K → D.dualTorsion), IsLinearSystem M ∧
      (∀ s : (κ × V) × V,
        M.IsHomogeneousCoords (lift (e s.1.1 s.2) (e s.1.1 s.1.2)).left (w p q s)) ∧
      M.picClass = (pi fun l ↦ N.pull (ψ l).left).picClass :=
    exists_isLinearSystem he_pairs (.pi fun l ↦ hN.isLinearSystem.pull _)
      (fun s ↦ .pi (hψ_coords s)) (h_local hp hq hq_inl) (h_local hq hp hp_inl)
  -- `M` defines a map `G` into a power of `A`, which is embedded by the Segre product of `N`.
  obtain ⟨G, hG, hG_pull⟩ := he_pairs.exists_map_of_coords
    (p := fun s ↦ Pi.lift fun l ↦ e s.1.1 (comb s.1.1 (doubledCoeffs p q l) s.2 s.1.2))
    hM (isProjEmbedding_pi (Pi.π _) (fun _ ↦ hN) (Pi.hom_ext _ _)) hM_coords
    fun s ↦ .pi fun l ↦ by simpa [← comp_left, IsHomogeneousCoords.pull_iff] using he_coords _ _
  refine ⟨fun l ↦ G ≫ Pi.π _ l, fun l i y z ↦ ?_, ?_⟩
  · rw [← assoc, hG ((i, y), z), Pi.lift_comp_π]
  · rw [← hM_class, ← hG_pull]
    simp [← pull_comp, pull_pi]

/-- The first two pairs of a padding tuple are `(1, 0)`. -/
lemma paddingTuple_inl (a : Fin (D.paddedNorm - 3) → 𝓞 E) (d : 𝓞 E) (l : Bool) :
    paddingTuple a d (Sum.inl l) = (1, 0) := by
  simp [paddingTuple]
/-- The addition of `V` and the action of `𝓞 E` on the tori `x i` extend to `A`. Assume the linear
systems `c ω` have the theta values of `x i` at the torsion lifts as coordinates at `η i`, that
nonvanishing indices exist at every point of `S`, and that `#D.dualTorsion` is a unit in `R`. Let
`A` over `S` be embedded by `N`, and let `e i z` be points of `A` over `η i` whose homogeneous
coordinates are the theta functions of `x i` at `z` and whose pairs separate `A ⊗ A`. Let the zero
extend to a section `o` of `A`. Then there are a morphism `add : A ⊗ A ⟶ A` with `e i (y + z)` equal
to `add` applied to `(e i y, e i z)`, and for each `d : 𝓞 E` an endomorphism `f` of `A` with
`e i z ≫ f = e i ((x i).intAction d z)`, where `intAction d` is the action of `d` on the torus. -/
lemma Variety.exists_add_and_intAction
    (hc : ∀ ω : D.levelTorsion, (c ω).IsLinearSystem)
    (hx : ∀ (i : κ) (ω : D.levelTorsion),
      (c ω).IsHomogeneousCoords (η i) fun k : D.dualTorsion ↦
        (x i).thetaCoord k ((x i).torsionLift ω))
    (h_index : ∀ (t : S) (s : D.dualTorsion), ∃ a : D.dualTorsion,
      IsNonvanishingIndex c t a ∧ IsNonvanishingIndex c t (-a) ∧ IsNonvanishingIndex c t (s - a))
    (π : S ⟶ Spec R) (hT : IsUnit (Nat.card D.dualTorsion : R)) {A : Over S}
      {N : LineBundle A.left D.dualTorsion}
    (hN : N.IsProjEmbedding A.hom) {e : ∀ i : κ, V → (Over.mk (η i) ⟶ A)}
    (he_coords : ∀ (i : κ) (z : V),
      N.IsHomogeneousCoords (e i z).left fun k : D.dualTorsion ↦ (x i).thetaCoord k z)
    (he_pairs : IsSeparatingFamily fun s : (κ × V) × V ↦
      (lift (e s.1.1 s.2) (e s.1.1 s.1.2)).left)
    {o : 𝟙_ (Over S) ⟶ A} (ho : ∀ i : κ, toUnit (Over.mk (η i)) ≫ o = e i 0) :
    (∃ add : A ⊗ A ⟶ A, ∀ (i : κ) (y z : V), e i (y + z) = lift (e i y) (e i z) ≫ add) ∧
      ∀ d : 𝓞 E, ∃ f : A ⟶ A, ∀ (i : κ) (z : V), e i z ≫ f = e i ((x i).intAction d z) := by
  classical
  -- `a` is a padding of `1`, and the `a l` span `𝓞 E`.
  obtain ⟨a, ha_span, ha⟩ : HasPadding E D.paddedNorm 1 := D.hasPadding_one
  have h_tuple : IsRiemannTuple (paddingTuple a (-1)) D :=
    isRiemannTuple_paddingTuple (by simp [← ha])
  -- For `d = -1` only the projections and zero are needed as `ψ`.
  let ψ (q : 𝓞 E × 𝓞 E) : A ⊗ A ⟶ A :=
    if q.1 = 1 then fst A A else if q.2 = 1 then snd A A else toUnit _ ≫ o
  let b := doubledCoeffs (paddingTuple (1 : Fin (D.paddedNorm - 3) → 𝓞 E) 0) (paddingTuple a (-1))
  have hψ : ∀ l i y z, lift (e i z) (e i y) ≫ ψ (b l) =
      e i ((x i).intAction (b l).1 z + (x i).intAction (b l).2 y) := by
    simp [b, ψ, ho, doubledCoeffs, paddingTuple]
  obtain ⟨G, hG, -⟩ := exists_maps_of_riemann_relation hc hx h_index π hT h_tuple
    isRiemannTuple_paddingTuple_one_zero (paddingTuple_inl a _) (paddingTuple_inl 1 0) hN
    he_coords he_pairs (fun l ↦ ψ (b l)) hψ
  -- The pairs `(1, 1)`, `(-1, 1)`, `(a l, 0)` give addition, subtraction and the action of `a l`.
  refine ⟨⟨G (.inr (.inr (.inl false))), by simp [hG, doubledCoeffs, paddingTuple]⟩, fun d ↦ ?_⟩
  have h_sub (i : κ) (y z : V) :
      lift (e i z) (e i y) ≫ G (.inr (.inr (.inl true))) = e i (y - z) := by
    simp [hG, sub_eq_neg_add, doubledCoeffs, paddingTuple]
  have h_act (l : Fin (D.paddedNorm - 3)) (i : κ) (z : V) :
      e i z ≫ lift (𝟙 A) (𝟙 A) ≫ G (.inr (.inr (.inr l))) = e i ((x i).intAction (a l) z) := by
    simp [hG, ← assoc, doubledCoeffs, paddingTuple]
  -- The `d` whose action extends to `A` contain `1` and are closed under subtraction, so they
  -- form a subgroup that contains the `a l`.
  let P : Set (𝓞 E) := {d | ∃ f : A ⟶ A, ∀ i z, e i z ≫ f = e i ((x i).intAction d z)}
  have hP_sub : ∀ d ∈ P, ∀ d' ∈ P, d + -d' ∈ P := by
    rintro d ⟨f, hf⟩ d' ⟨f', hf'⟩
    refine ⟨lift f' f ≫ G (.inr (.inr (.inl true))), fun i z ↦ ?_⟩
    simp [hf, hf', h_sub, ← assoc, ← sub_eq_add_neg]
  let O : AddSubgroup (𝓞 E) := .ofSub P ⟨1, 𝟙 A, by simp⟩ hP_sub
  have h_le : Submodule.span ℤ (Set.range a) ≤ O.toIntSubmodule :=
    Submodule.span_le.2 (Set.range_subset_iff.2 fun l ↦ ⟨_, h_act l⟩)
  exact ha_span.ge.trans h_le Submodule.mem_top

/-- Let the `c ω` be linear systems on `S` with the theta constants of `x i` at `ω` as coordinates
of `η i` and the index condition `h_index`, and let #`D.dualTorsion` be a unit in `R`. Let `A` over
`S` be a commutative group scheme with an action of `𝓞 E`, embedded by `N`. Let `e i` be additive
maps from `V` to the points of `A` over `η i` that respect the action (`he_smul`), whose homogeneous
coordinates are the theta functions of `x i` and whose pairs separate `A ⊗ A`. Then the class of `N`
satisfies `D.HasClassLaws`: the parallelogram law and the two pairing laws for `β`. -/
lemma Variety.hasClassLaws_picClass
    (hc : ∀ ω : D.levelTorsion, (c ω).IsLinearSystem)
    (hx : ∀ (i : κ) (ω : D.levelTorsion),
      (c ω).IsHomogeneousCoords (η i) fun k : D.dualTorsion ↦
        (x i).thetaCoord k ((x i).torsionLift ω))
    (h_index : ∀ (t : S) (s : D.dualTorsion), ∃ a : D.dualTorsion,
      IsNonvanishingIndex c t a ∧ IsNonvanishingIndex c t (-a) ∧ IsNonvanishingIndex c t (s - a))
    (π : S ⟶ Spec R) (hT : IsUnit (Nat.card D.dualTorsion : R)) {A : Over S} [AddObj A]
    [ModuleObj (𝓞 E) A] {N : LineBundle A.left D.dualTorsion} (hN : N.IsProjEmbedding A.hom)
    {e : ∀ i : κ, V →+ (Over.mk (η i) ⟶ A)}
    (he_coords : ∀ (i : κ) (z : V),
      N.IsHomogeneousCoords (e i z).left fun k : D.dualTorsion ↦ (x i).thetaCoord k z)
    (he_pairs : IsSeparatingFamily fun s : (κ × V) × V ↦
      (lift (e s.1.1 s.2) (e s.1.1 s.1.2)).left)
    (he_smul : ∀ (d : 𝓞 E) (i : κ) (z : V), d • e i z = e i ((x i).intAction d z)) :
    D.HasClassLaws N.picClass := by
  have h_proper : IsProper A.hom := hN.isProper
  refine D.hasClassLaws_of_riemann_relation fun a d ha T y z ↦ ?_
  -- With the group law every map `(z, y) ↦ q.1 z + q.2 y` exists, and the maps `G` of the
  -- extension step are of this form.
  let ψ (q : 𝓞 E × 𝓞 E) : A ⊗ A ⟶ A := q.1 • fst A A + q.2 • snd A A
  have hψ (q : 𝓞 E × 𝓞 E) (i : κ) (y z : V) : lift (e i z) (e i y) ≫ ψ q =
      e i ((x i).intAction q.1 z + (x i).intAction q.2 y) := by
    simp [ψ, he_smul, comp_add]
  obtain ⟨G, hG, hG_class⟩ := exists_maps_of_riemann_relation hc hx h_index π hT
    (isRiemannTuple_paddingTuple ha) isRiemannTuple_paddingTuple_one_zero (paddingTuple_inl a d)
    (paddingTuple_inl 1 0) hN (e := fun i z ↦ e i z) he_coords he_pairs
    (fun l ↦ ψ (doubledCoeffs (paddingTuple 1 0) (paddingTuple a d) l)) fun l ↦ hψ _
  have hGψ (l) : G l = ψ (doubledCoeffs (paddingTuple a d) (paddingTuple 1 0) l) :=
    he_pairs.hom_ext (by simp [hG, hψ])
  -- Pull the identity of classes back along the point `(y, z)` of `A ⊗ A`.
  let cl (u : T ⟶ A) : Pic T.left := N.picClass.atPoint u
  have h_sum : ∑ l, cl (lift y z ≫ ψ (doubledCoeffs (paddingTuple a d) (paddingTuple 1 0) l)) =
      ∑ l, cl (lift y z ≫ ψ (doubledCoeffs (paddingTuple 1 0) (paddingTuple a d) l)) := by
    simpa [-lift_left, ← pull_comp, cl, Pic.atPoint, hGψ] using
      congrArg (Pic.pull (lift y z).left) hG_class
  -- Term by term this is the required relation, with the same extra terms on both sides.
  simp [cl, ψ, doubledCoeffs, paddingTuple, comp_add, ← sub_eq_add_neg] at h_sum
  linear_combination (norm := abel) h_sum

/-- The theta law on base changes to local rings. Assume the following: the linear systems `c ω` on
`S` have, at the separating complex points `η i`, the theta coordinates of `x i` at lifts of `ω`;
they satisfy `h_index`; and `#D.dualTorsion` is a unit in `R`. Also `N` embeds the `𝓞 E`-group `A`
projectively with theta coordinates at the separating points `e i z`, and `σ` lifts the level
torsion. Then for a base change `T` of `A` along `t : Spec B ⟶ S`, `B` local, the pull-backs of `N`
and `σ` on `D.dualTorsion` form a theta structure (`IsThetaStructure`) for the Lagrangian, with some
characters `C s`. -/
lemma Variety.exists_isThetaStructure
    (hc : ∀ ω : D.levelTorsion, (c ω).IsLinearSystem)
    (hx : ∀ (i : κ) (ω : D.levelTorsion),
      (c ω).IsHomogeneousCoords (η i) fun k : D.dualTorsion ↦
        (x i).thetaCoord k ((x i).torsionLift ω))
    (h_index : ∀ (t : S) (s : D.dualTorsion), ∃ a : D.dualTorsion,
      IsNonvanishingIndex c t a ∧ IsNonvanishingIndex c t (-a) ∧ IsNonvanishingIndex c t (s - a))
    (π : S ⟶ Spec R) (hT : IsUnit (Nat.card D.dualTorsion : R))
    (hη_sep : IsSeparatingFamily fun i : κ ↦ (toUnit (Over.mk (η i))).left)
    {A : Over S} [AddObj A] [ModuleObj (𝓞 E) A] {N : LineBundle A.left D.dualTorsion}
    (hN : N.IsProjEmbedding A.hom) {e : ∀ i : κ, V →+ (Over.mk (η i) ⟶ A)}
    (he_coords : ∀ (i : κ) (z : V),
      N.IsHomogeneousCoords (e i z).left fun k : D.dualTorsion ↦ (x i).thetaCoord k z)
    (he_sep : IsSeparatingFamily fun s : κ × V ↦ (e s.1 s.2).left)
    {σ : D.levelTorsion →ₗ[𝓞 E] (𝟙_ (Over S) ⟶ A)} (hσ : ∀ (l : D.levelTorsion) (i : κ),
      toUnit (Over.mk (η i)) ≫ σ l = e i ((x i).torsionLift l))
    {B : Type} [CommRing B] [IsLocalRing B] (t : Spec (CommRingCat.of B) ⟶ S)
    {T : Over (Spec (CommRingCat.of B))} [AddObj T] [ModuleObj (𝓞 E) T]
    {q : (Over.map t).obj T ⟶ A} (hq : IsGroupBaseChange t (B := T) q) :
    ∃ C : D.dualTorsion → AddChar D.dualTorsion B,
      IsThetaStructure (D.lagrangian.addSubgroupOf D.dualTorsion)
      (.comp (hq.pullSection ∘ₗ σ) (AddSubgroup.inclusion D.dualTorsion_le_levelTorsion))
      (hN.isLinearSystem.pull q.left) C := by
  -- The bicharacters of the `x i` are the values of regular functions `r s m` near `t`.
  obtain ⟨W, r, hW, hr, hr_val⟩ := exists_isRegularOn_bicharacter hc hx h_index t
  -- Two functions regular on `W` that agree at the dense points `η i` agree at `t`.
  have h_ext {r₁ r₂ : PointFn S} (h₁ : IsRegularOn r₁ W) (h₂ : IsRegularOn r₂ W)
      (h : ∀ i, LandsIn (η i) W → r₁ (.of ℂ) (η i) = r₂ (.of ℂ) (η i)) :
      r₁ (.of B) t = r₂ (.of B) t :=
    hη_sep.pointFn_ext h₁ h₂ h _ t hW
  -- The value of `r s m` at `t` is again a character in `m`.
  have hC_zero (s : D.dualTorsion) : r s 0 (.of B) t = (1 : PointFn S) (.of B) t :=
    h_ext (hr s 0) (by simp [IsRegularOn]) (by simp +contextual [hr_val])
  have hC_add (s m m' : D.dualTorsion) : r s (m + m') (.of B) t = (r s m * r s m') (.of B) t :=
    h_ext (hr s (m + m')) (by simp +contextual [IsRegularOn, hr _ _ _])
      (by simp +contextual [hr_val, AddChar.map_add_eq_mul])
  let C (s : D.dualTorsion) : AddChar D.dualTorsion B :=
    .mk (fun m ↦ r s m (.of B) t) (hC_zero s) (hC_add s)
  -- The five conditions: the identity `C s (-m) = C m s`, the theta law, equal coordinates on the
  -- Lagrangian, the order of `D.dualTorsion` is a unit, and the vanishing sums off the Lagrangian.
  refine ⟨C, fun s m ↦ ?_, fun ε s ↦ ?_, fun s hs ↦ ?_, ?_, fun s hs ↦ ?_⟩
  · exact h_ext (hr s _) (hr m s) (by simp +contextual [hr_val, bicharacter_neg_eq_swap])
  · refine exists_isSectionLift_coordSection _ _ fun l m _ y hl hm ↦
      ⟨⟨(ε : ℤ) • l - s, ?_⟩, fun k ↦ ?_⟩
    · simp [N.transition_self, landsIn_preimage.1 hl, ↓H0_smul, smul_smul, AddChar.val_isUnit,
        IsUnit.map, -AddChar.coe_mk, coordSection]
    -- The map `y ↦ ε y + σ s` of `T` is the base change of `(ε • 𝟙 A) ≫ tr`.
    let s' : D.levelTorsion := ⟨s, D.dualTorsion_le_levelTorsion s.property⟩
    let tr : A ⟶ A := translation (σ s')
    have h_comm : ((ε : ℤ) • 𝟙 T).left ≫ (translation (hq.pullSection (σ s'))).left ≫ q.left =
        q.left ≫ ((ε : ℤ) • 𝟙 A).left ≫ tr.left := by
      simpa [tr, ← hq.translation_comp, Int.cast_smul_eq_zsmul] using
        hq.smul_id_comp (ε : ℤ) =≫ tr.left
    have h_reg (m : D.dualTorsion) : (PointFn.pull A.hom (r s m) *
        N.transition l ((ε : ℤ) • (s + m))).IsRegularOn (A.hom ⁻¹ᵁ W ⊓ N.opens l) :=
      ((hr s m).pull A.hom).mul (hN.isLinearSystem.isRegularOn_transition l _)
    -- The sign `ε` acts on theta functions up to a constant `ρ i`.
    choose ρ h_neg using fun i ↦ (x i).exists_thetaCoord_sign_smul ε
    -- The law on `A`: at theta points it is `thetaCoord_add_torsionLift` and `h_neg`.
    have h_law : (PointFn.pull A.hom (r s k) * N.transition l ((ε : ℤ) • (s + k))) _ (y ≫ q.left) =
        (PointFn.pull A.hom (r s m) * N.transition l ((ε : ℤ) • (s + m)) *
          PointFn.pull (((ε : ℤ) • 𝟙 A) ≫ tr).left (N.transition m k)) _ (y ≫ q.left) := by
      refine he_sep.pointFn_ext ((h_reg k).mono inf_le_left) ((h_reg m).mul
        ((hN.isLinearSystem.isRegularOn_transition m k).pull (((ε : ℤ) • 𝟙 A) ≫ tr).left)) ?_ _ _ ?_
      · simp +contextual [hr_val, he_coords .., thetaCoord_add_torsionLift, h_neg, ← comp_left,
          field, tr, s', hσ, ← map_zsmul, ← map_add, comp_add, AddGrpObj.comp_zsmul]
      · simpa [tr, ← h_comm, LandsIn.comp, hW] using! ⟨hl, hm⟩
    -- `using!`: the coordinate sections of the pull-back of `N` are its transitions only up to
    -- unfolding `coordSection`.
    simpa [↓H0_smul, ← hr _ _ _ _ hW, C, tr, ← h_comm] using! h_law
  · -- On the Lagrangian the two sections have the same transitions: checked at the points `e i z`.
    exact H0_ext fun _ _ B' u hu ↦ he_sep.pointFn_ext
      (hN.isLinearSystem.isRegularOn_transition _ _) (hN.isLinearSystem.isRegularOn_transition _ _)
      (by simp +contextual [he_coords .., thetaCoord_eq_of_mem_lagrangian _ s hs]) B' _ hu
  · simpa using hT.map (preimage (t ≫ π)).hom
  · -- For `s` outside the Lagrangian the sum is zero at each `η i`.
    -- `using!`: the sum of the functions `r s l ^ 2` agrees with the sum of their values only up to
    -- unfolding.
    simpa using! h_ext (r₁ := ∑ l : D.lagrangian.addSubgroupOf D.dualTorsion, r s l ^ 2) (r₂ := 0)
      (by simp +contextual [IsRegularOn, hr _ _ _]) (by simp [IsRegularOn])
      fun i hi ↦ by simpa [hr_val _ _ _ hi] using! (x i).sum_bicharacter_sq_eq_zero hs

/-- Sections of `A` that restrict at each `η i` to `e i` of the lift of the level point are the
function of an `𝓞 E`-linear map `ς`, when the `e i` respect the action of `𝓞 E` and vanish on the
period lattices. -/
lemma Variety.exists_linearMap_coe_eq_of_comp_eq_torsionLift {E : Type} [Field E] [CMBase E]
    {D : PEL E} {S : Scheme} {η : κ → (Spec (CommRingCat.of ℂ) ⟶ S)}
    {g : κ → GL D.Index (𝔸f E)} {ℓ : κ → Matrix D.Index D.Index ℂ}
    {x : ∀ k : κ, ThetaTorus D (g k) (ℓ k) V}
    (hη_sep : IsSeparatingFamily fun i : κ ↦ (toUnit (Over.mk (η i))).left)
    {A : Over S} [AddObj A] [ModuleObj (𝓞 E) A] [IsSeparated A.hom]
    {e : ∀ i : κ, V →+ (Over.mk (η i) ⟶ A)}
    (he_smul : ∀ (d : 𝓞 E) (i : κ) (z : V), d • e i z = e i ((x i).intAction d z))
    (he_lattice : ∀ (i : κ) (l : V), l ∈ (x i).periodLattice → e i l = 0)
    {σ : D.levelTorsion → (𝟙_ (Over S) ⟶ A)} (hσ : ∀ (l : D.levelTorsion) (i : κ),
      toUnit (Over.mk (η i)) ≫ σ l = e i ((x i).torsionLift l)) :
    ∃ ς : D.levelTorsion →ₗ[𝓞 E] (𝟙_ (Over S) ⟶ A), ⇑ς = σ := by
  -- At each `η i` both sides are `e i` of lifts that differ by an element of the period lattice.
  have hσ_add (l m : D.levelTorsion) : σ (l + m) = σ l + σ m := by
    refine hη_sep.hom_ext fun i ↦ sub_eq_zero.1 ?_
    simp [hσ, PeriodMap.torsionLift, ← map_add, ← map_sub, comp_add]
    exact he_lattice i _ ⟨_, by simp, rfl⟩
  have hσ_smul (d : 𝓞 E) (l : D.levelTorsion) : σ (d • l) = d • σ l := by
    refine hη_sep.hom_ext fun i ↦ sub_eq_zero.1 ?_
    simp [hσ, he_smul, PeriodMap.torsionLift, intAction, ← toRealVectors_smul, ← map_sub]
    exact he_lattice i _ ⟨_, by simp, rfl⟩
  exact ⟨⟨⟨σ, hσ_add⟩, hσ_smul⟩, rfl⟩

/-- The points of `A` over a point `η` of `S`, seen as points of the fibre of `A` over `η`; the map
is `𝓞 E`-linear. -/
noncomputable def Variety.fibrePointMap {E : Type} [Field E] [CMBase E] {S : Scheme}
    (A : Over S) [AddObj A] [ModuleObj (𝓞 E) A] (η : Spec (CommRingCat.of ℂ) ⟶ S) :
    (Over.mk η ⟶ A) →ₗ[𝓞 E] (𝟙_ (Over (Spec (CommRingCat.of ℂ))) ⟶ (Over.pullback η).obj A) :=
  ((isGroupBaseChange_counit (O := 𝓞 E) (A := A) η).pointEquiv (T := 𝟙_ _)).symm.toLinearMap

/-- The point of the fibre given by `fibrePointMap A η u` is the pair of `u` and the point `η`. -/
lemma Variety.fibrePointMap_left {E : Type} [Field E] [CMBase E] {S : Scheme}
    {η : Spec (CommRingCat.of ℂ) ⟶ S} (A : Over S) [AddObj A] [ModuleObj (𝓞 E) A]
    (u : Over.mk η ⟶ A) :
    (fibrePointMap (E := E) A η u).left = (lift u (𝟙 (Over.mk η))).left :=
  -- `using!`: `fibrePointMap` is the pull-back lift only after unfolding `pointEquiv`.
  pullback.hom_ext (by simpa [pullback.lift_fst] using!
      (isGroupBaseChange_counit (O := 𝓞 E) (A := A) η).isPullback.lift_fst ..)
    (by simpa [pullback.lift_snd] using (fibrePointMap (E := E) A η u).w)

/-- The torus `x` uniformises the fibre of `A` over the complex point `η`: the fibre has a
uniformisation `u` with exponential map `e` followed by `fibrePointMap A η`, lattice the period
lattice of `x`, and the theta functions of `x` as theta coordinates of the pull-back of `N`; and
its relative dimension `d` is `abelianDim E D.Index`. -/
lemma Variety.exists_uniformisation_pullback_of_isSeparatingFamily {E : Type} [Field E] [CMBase E]
    {D : PEL E} {S : Scheme} {η : Spec (CommRingCat.of ℂ) ⟶ S} {g : GL D.Index (𝔸f E)}
    {ℓ : Matrix D.Index D.Index ℂ} (x : ThetaTorus D g ℓ V)
    {A : Over S} [IsAbelianScheme A] [ModuleObj (𝓞 E) A] {N : LineBundle A.left D.dualTorsion}
    (hN : N.IsProjEmbedding A.hom) (h_par : N.picClass.ParallelogramLaw) {e : V →+ (Over.mk η ⟶ A)}
    (he_coords : ∀ z : V, N.IsHomogeneousCoords (e z).left fun k : D.dualTorsion ↦ x.thetaCoord k z)
    (he_fibre : IsSeparatingFamily fun z : V ↦ (lift (e z) (𝟙 (Over.mk η))).left)
    (he_lattice : ∀ l : V, l ∈ x.periodLattice → e l = 0)
    (d : ℕ) (h_smooth : SmoothOfRelativeDimension d ((Over.pullback η).obj A).hom) :
    ∃ u : Uniformisation ((Over.pullback η).obj A) V,
      HasThetaCoords u.lattice (atGeneric u.expMap) (N.pull ((mapPullbackAdj η).counit.app A).left)
        x.automorphyForm x.multiplier (flip x.thetaCoord) ∧
      u.expMap = .comp (fibrePointMap (E := E) A η) e ∧ u.lattice = x.periodLattice ∧
      d = abelianDim E D.Index := by
  have h_fibre := isGroupBaseChange_counit (O := 𝓞 E) (A := A) η
  refine x.exists_uniformisation_of_isSeparatingFamily d h_smooth
    (hN.of_isPullback h_fibre.isPullback) ?_ _ ?_
    ?_ ?_
  · -- the pull-back of `N` to the fibre satisfies the parallelogram law
    simp [Pic.ParallelogramLaw, ↓h_fibre.atPoint_picClass_pull, h_par _]
  · -- the points of `e` separate the fibre
    simpa [fibrePointMap_left] using he_fibre
  · -- the theta functions of `x` are homogeneous coordinates along `e`
    simp [fibrePointMap_left, he_coords, IsHomogeneousCoords.pull_iff]
  · -- `e` kills the period lattice
    simp +contextual [he_lattice]

end LevelCoordinates

omit [IsLocallyNoetherian S] in
/-- The signature condition for `A`: at every point `s` of `S` with values in a local ring there are
coordinates of `A` at `0` in which `𝓞 E` acts on the Lie algebra by matrices `m` with the signature
given by `β` and `b` (`HasSignature`). `Φ v₀` is the embedding of `E` into `ℂ` at the base place
`v₀`. -/
lemma Variety.exists_isLieChart_hasSignature (j : ι → κ) (hη : IsDenseFamily fun i : ι ↦ η (j i))
    {E : Type} [Field E] [CMBase E] {D : PEL E} {R : CommRingCat} {π : S ⟶ Spec R} {φ : 𝓞 E →+* R}
    (hη_base : ∀ (i : κ) (d : 𝓞 E), (preimage (η i ≫ π ≫ specMap φ)).hom d = Φ v₀ d.val)
    {g : κ → GL D.Index (𝔸f E)} {ℓ : κ → Matrix D.Index D.Index ℂ}
    {x : ∀ k : κ, ThetaTorus D (g k) (ℓ k) V} (hβ : IsUnit (φ (star D.β - D.β)))
    {A : Over S} [AddObj A] [ModuleObj (𝓞 E) A]
    (h_dim : SmoothOfRelativeDimension (abelianDim E D.Index) A.hom)
    {e : ∀ i : κ, V →+ (Over.mk (η i) ⟶ A)}
    (he_smul : ∀ (d : 𝓞 E) (i : κ) (z : V), d • e i z = e i ((x i).intAction d z))
    {u : ∀ i : κ, Uniformisation ((Over.pullback (η i)).obj A) V}
    (hu_e : ∀ i : κ, (u i).expMap = .comp (fibrePointMap (E := E) A (η i)) (e i))
    (b : ℤ) {B : CommRingCat} (s : Spec B ⟶ S) [IsLocalRing B] :
    ∃ (U : A.left.Opens) (z : Fin (abelianDim E D.Index) → Γ(A.left, U))
      (m : 𝓞 E → Matrix (Fin (abelianDim E D.Index)) (Fin (abelianDim E D.Index)) B),
      IsLieChart A (ι := Fin (abelianDim E D.Index)) s U z m ∧
      HasSignature (preimage (s ≫ π ≫ specMap φ)).hom (star D.β - b) (D.β - b) m := by
  -- Work over the stalk at the closed point of `s`; there `HasSignature` is checked at the dense
  -- points `η (j i)`, where it becomes a statement on the action on `V` (`hasSignature_iff`).
  rw [← Spec_stalkClosedPointTo_fromSpecStalk s]
  simp only [assoc, preimage_comp, preimage_map, CommRingCat.hom_comp]
  obtain ⟨U, z, m, h_jac⟩ :=
    exists_isLieChart (O := 𝓞 E) h_dim (S.fromSpecStalk (s (closedPoint _)))
  refine ⟨U, z, _, h_jac rfl, .of_points (stalk_eq_zero_of_dense hη) ?_ _ (.map _ ?_)⟩
  · rintro ⟨i, ψ, hψ⟩
    exact ((u _).hasSignature_iff (F := (x (j i)).intAction) (by simp [hu_e, ← he_smul])
      (h_jac hψ) (isGroupBaseChange_counit (O := 𝓞 E) (A := A) (η (j i)))
      (x (j i)).isPeriodMap.finrank_eq_abelianDim).2
      ((x (j i)).exists_eigenline b fun d ↦ by simpa [← hψ] using hη_base (j i) d)
  · simpa [← assoc] using hβ.map (preimage (S.fromSpecStalk (s (closedPoint _)) ≫ π)).hom

unseal ThetaObject.groupScheme ThetaObject.toFamily in
/-- A theta family from dense complex points: if `S` is embedded by the linear systems `c ω` whose
coordinates at the complex points `η i` are the theta functions of the theta tori `x i`, then `S`
is, under the further hypotheses of the statement, the base of a theta family whose object at each
`η i` is modelled on `x i`. Here `S` is reduced and locally noetherian, `V` is a finite-dimensional
complex space, and `Φ v₀` is the embedding of `E` into `ℂ` at the base place `v₀`. -/
theorem Variety.exists_thetaFamily_of_points (j : ι → κ) (hη : IsDenseFamily fun i : ι ↦ η (j i))
    {E : Type} [Field E] [CMBase E] {D : PEL E} {R : CommRingCat} {π : S ⟶ Spec R}
    {φ : 𝓞 E →+* R} (hφ : Mono (specMap φ))
    (hη_base : ∀ (i : κ) (d : 𝓞 E), (preimage (η i ≫ π ≫ specMap φ)).hom d = Φ v₀ d.val)
    {g : κ → GL D.Index (𝔸f E)} {ℓ : κ → Matrix D.Index D.Index ℂ}
    {c : D.levelTorsion → LineBundle S D.dualTorsion} {x : ∀ k : κ, ThetaTorus D (g k) (ℓ k) V}
    (hc : ∀ ω : D.levelTorsion, (c ω).IsLinearSystem) [Fintype D.levelTorsion]
    (hπ : (LineBundle.pi c).IsProjEmbedding π)
    (hx : ∀ (i : κ) (ω : D.levelTorsion),
      (c ω).IsHomogeneousCoords (η i) fun k : D.dualTorsion ↦
        (x i).thetaCoord k ((x i).torsionLift ω))
    (hβ : IsUnit (φ (star D.β - D.β))) (hT : IsUnit (Nat.card D.dualTorsion : R))
    (h_closed : AllSpecializeTo S fun {k : Type} [Field k] (t : Spec (CommRingCat.of k) ⟶ S) ↦
      ∃ Z : Set (D.dualTorsion → k), IsCutOutAt D.paddedNorm D.exponentBound
        (thetaRanks D.dualTorsion D.paddedNorm) c t Z)
    (h_index : ∀ (t : S) (s : D.dualTorsion), ∃ a : D.dualTorsion,
      IsNonvanishingIndex c t a ∧ IsNonvanishingIndex c t (-a) ∧ IsNonvanishingIndex c t (s - a)) :
    ∃ X : ThetaFamily D S (π ≫ specMap φ), ∀ i : κ, X.IsModelledOn (η i) (x i) := by
  -- `A` is the closure of the theta points over `S`. Riemann's relation extends the maps
  -- `(z, y) ↦ a z + b y` from the theta points to `A ⊗ A`; this makes `A` an abelian scheme with
  -- an action of `𝓞 E` and gives the class identities. The other fields of `ThetaFamily` are
  -- mostly identities of regular functions, checked at the dense complex points.
  obtain ⟨A, N, e, h_closure⟩ : ∃ (A : Over S) (N : LineBundle A.left D.dualTorsion)
      (e : ∀ i, V → (Over.mk (η i) ⟶ A)), IsFlatClosure (fun i z k ↦ (x i).thetaCoord k z) N e :=
    exists_isFlatClosure j hη hc (Nat.le_of_lt D.three_le_paddedNorm) D.isCutDegree
      (fun i ↦ (x i).thetaCoord_vector_ne_zero)
      (fun i ↦ (x i).isCutOutAt_range_thetaCoord (hx i)) h_closed
  obtain ⟨hN, h_flat, he_coords, he_fibre, h_reduced, he_sep⟩ := h_closure
  replace he_fibre (i : κ) :
      IsSeparatingFamily fun z : V ↦ (lift (e i z) (𝟙 (Over.mk (η i)))).left := he_fibre i
  have h_proper : IsProper A.hom := hN.isProper
  have hη_sep : IsSeparatingFamily fun i : κ ↦ (toUnit (Over.mk (η i))).left :=
    ⟨(inferInstance : IsReduced S), hη.of_comp⟩
  have he_pairs :
      IsSeparatingFamily fun s : (κ × V) × V ↦ (lift (e s.1.1 s.2) (e s.1.1 s.1.2)).left :=
    he_sep.prod (y := fun s : κ × V ↦ e s.1 s.2) (e := fun s ↦ e s.1) hη he_sep.1
      fun s ↦ (he_fibre s.1).right
  -- The linear systems `c l` are the coordinates of sections `σ l` of `A`.
  have h_section (l : D.levelTorsion) : ∃ σ : 𝟙_ (Over S) ⟶ A,
      (∀ i : κ, toUnit (Over.mk (η i)) ≫ σ = e i ((x i).torsionLift l)) ∧ N.pull σ.left = c l :=
    hη_sep.exists_map_of_coords (hc l) hN (fun i ↦ hx i l) fun i ↦ he_coords i _
  choose σ hσ hσ_pull using h_section
  -- The group law and the action of `𝓞 E`; from here on the `e i` are homomorphisms.
  have h_zero (i : κ) : toUnit (Over.mk (η i)) ≫ σ 0 = e i 0 := by simp [hσ]
  obtain ⟨⟨add, h_add⟩, h_act⟩ :=
    exists_add_and_intAction hc hx h_index π hT hN he_coords he_pairs h_zero
  choose f hf using h_act
  obtain ⟨_, _, e, rfl, he_smul⟩ :=
    exists_isAbelianScheme j hη he_fibre he_sep h_reduced hf add (σ 0) h_add h_zero
  -- The `rfl` above replaced `e` by a family of additive maps; put the facts back in plain form.
  beta_reduce at he_coords he_fibre he_sep he_pairs hσ he_smul
  have h_class : D.HasClassLaws N.picClass :=
    hasClassLaws_picClass hc hx h_index π hT hN he_coords he_pairs he_smul
  have he_lattice (i : κ) (l : V) (hl : l ∈ (x i).periodLattice) : e i l = 0 :=
    (x i).map_eq_zero_of_mem_periodLattice hN (he_coords i) hl
  -- `σ` is linear: the lifts `(x i).torsionLift l` are linear in `l` modulo the lattice.
  obtain ⟨ς, rfl⟩ := exists_linearMap_coe_eq_of_comp_eq_torsionLift hη_sep he_smul he_lattice hσ
  -- `e i` uniformises the fibre over `η i`, and this forces the dimension.
  have h_unif (i : κ) := exists_uniformisation_pullback_of_isSeparatingFamily (x i) hN h_class.1
    (he_coords i)
    (he_fibre i) (he_lattice i)
  have h_dim : SmoothOfRelativeDimension (abelianDim E D.Index) A.hom := by
    refine smoothOfRelativeDimension_of_fibres he_sep.2 fun s d h_smooth ↦ ?_
    obtain ⟨-, -, -, -, hd⟩ := h_unif s.1 d h_smooth
    exact hd
  -- The fibre over `η i` is the base change of `A` along `η i`, so it has the same dimension.
  choose u hu_theta hu_e hu_L _ using fun i : κ ↦
    h_unif i _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).1
      (isGroupBaseChange_counit (O := 𝓞 E) (A := A) (η i)).isPullback h_dim)
  refine ⟨{ total := A, lineBundle := N, embeds := hN, levelPoints := ς, class_laws := h_class
            relative_dim := h_dim
            theta_law t T _ _ q hq :=
              exists_isThetaStructure hc hx h_index π hT hη_sep hN he_coords he_sep hσ t hq
            signature b _ s _ :=
              exists_isLieChart_hasSignature j hη hη_base hβ h_dim he_smul hu_e b s
            eq_of_level_coords_eq t t' h_base h_coord := ?ext }, fun i ↦ ?model⟩
  case ext =>
    -- The lists agree, so do the pull-backs of the product of the `c l`.
    have h_pi : pi (fun l : D.levelTorsion ↦ N.pull (t ≫ (ς l).left)) =
        pi (fun l : D.levelTorsion ↦ N.pull (t' ≫ (ς l).left)) := congrArg pi (funext h_coord)
    exact hπ.ext (by simpa [← hσ_pull, pull_pi] using h_pi) (hφ.right_cancellation _ _ h_base)
  case model =>
    refine ⟨⟨hη_base i, u i, _, _, hu_theta i, fun d w ↦ ?_, fun l ↦ ?_, hu_L i⟩, rfl⟩
    -- `using!`: the exponential map `u i` matches `fibrePointMap A (η i)` only up to unfolding.
    · simpa [hu_e, he_smul, intAction] using!
        (fibrePointMap (E := E) A (η i)).map_smul d (e i ((x i).realEquiv w))
    · simpa [hu_e] using! congr(fibrePointMap (E := E) A (η i) $(hσ l i))

end New
