import Lib.Cohomology.Etale.Basic
import Lib.General.Geometry.DenseComplexPoints
import Lib.Shimura.AbelianScheme.Basic

/-!
# Geometric points, specialisation, separating products and integral abelian varieties

Let `k` be an algebraically closed field. For schemes and morphisms locally of finite type, points
with values in `k` detect nonempty locally closed sets and images of morphisms, and this is used to
spread properties over commutative group schemes.
Smooth morphisms are shown to be geometrically reduced, and abelian schemes over `k` are shown to be
integral. The file also records that flat morphisms are injective on stalks. Finally it gives
criteria for families of complex points to be separating over a stalk of the base and on a product
of flat schemes.

## Main definitions and results

* `New.exists_section_mem`, `New.exists_point_mem`: a nonempty locally closed set in a scheme
  locally of finite type over `k` contains a `k`-point.
* `New.IsDenseFamily.of_fibres`: if the complex points `η i` are dense in `S` and `A` is smooth over
  `S`, a family containing every complex point of `A` over the `η i` is dense in `A`.
* `New.AddObj.property_of_isOpenImmersion`: take a commutative group scheme (`New.AddObj`) locally
  of finite type over `k`. A property induced by a property of ring maps spreads from a nonempty
  open part to the whole scheme, by translation.
* `New.AddObj.smoothOfRelativeDimension_of_fibres`: the relative dimension of an abelian scheme can
  be read off the fibres through a dense family of points.
* `New.isSeparatingFamily_stalk`: for `A` and `S` reduced and dense points of `A` with finitely many
  images in `S`, the lifts of those that factor through a stalk of `S` separate the base change of
  `A` to that stalk.
* `New.IsSeparatingFamily.prod`: separating points of `B`, paired with dense points of the fibres of
  `A` over their images in `S`, separate `A ×_S B`, for `A`, `B` flat and locally of finite type,
  `A` reduced, and `S` reduced, locally noetherian, with finitely many dense complex points.

Notions from other files:
* `New.IsDenseFamily`: the images of a family of complex points are dense.
* `New.IsSeparatingFamily`: the family is dense and the scheme is reduced.
* `New.IsAbelianScheme`: a smooth proper commutative group scheme on which multiplication by every
  `m ≠ 0` is surjective.
* `New.translation`: translation x ↦ x + z by a section z of a commutative group scheme.

## Relation to the literature

Known; see `Lib.Shimura.AbelianScheme.IsogenyFlatness` for sources.
-/

/-! ## Points over algebraically closed fields -/

section GeometricPoints

open CategoryTheory AlgebraicGeometry MonoidalCategory Scheme Over Limits.pullback Pullback Set

namespace New

/-- A nonempty locally closed subset of a scheme `X` locally of finite type over an algebraically
closed field `k` contains the image of a `k`-point, that is, of a section `x : Spec k ⟶ X` of the
structure morphism `s`. -/
lemma exists_section_mem {k : Type*} {X : Scheme} [Field k] [IsAlgClosed k]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] {S : Set X} (hS : IsLocallyClosed S)
    (hS_ne : S.Nonempty) :
    ∃ x : Spec (.of k) ⟶ X, x ≫ s = 𝟙 (Spec (.of k)) ∧ x (default : Spec (.of k)) ∈ S := by
  -- `X` is a Jacobson space, so `S` contains a closed point; over `k` a closed point is a
  -- `k`-point.
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace s
  obtain ⟨x, hxS, hx : IsClosed {x}⟩ := nonempty_inter_closedPoints hS_ne hS
  exact ⟨pointOfClosedPoint s x hx, pointOfClosedPoint_comp s x hx,
    by simpa [pointOfClosedPoint] using hxS⟩

/-- Let `X` be a scheme over `Spec k`, locally of finite type, with `k` an algebraically closed
field. A nonempty locally closed subset `S` of `X` contains the image of a `k`-point, that is, of a
morphism over `Spec k` from the unit object `𝟙_` (`Spec k` over itself) to `X`. This is
`New.exists_section_mem` in the category of schemes over `Spec k`. -/
lemma exists_point_mem {k : Type*} [Field k] [IsAlgClosed k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] {S : Set X.left} (hS : IsLocallyClosed S) (hS_ne : S.Nonempty) :
    ∃ x : 𝟙_ (Over (Spec (.of k))) ⟶ X, x.left (default : Spec (.of k)) ∈ S := by
  obtain ⟨x, hx_section, hx_mem⟩ := exists_section_mem X.hom hS hS_ne
  exact ⟨homMk x hx_section, hx_mem⟩

/-- Let f : X → S be locally of finite type, k algebraically closed and t a k-point of S. If the
image of t lies in the image of f, then there is a k-point y of X over t, that is, y ≫ f = t. -/
lemma exists_point_over {k : Type*} {X : Scheme} [Field k] [IsAlgClosed k] {S : Scheme}
    (f : X ⟶ S) [LocallyOfFiniteType f] {t : Spec (.of k) ⟶ S}
    (ht : t (IsLocalRing.closedPoint k) ∈ range f) : ∃ y : Spec (.of k) ⟶ X, y ≫ f = t := by
  -- The fibre of `f` over `t` is nonempty and locally of finite type over `k`, so it has a
  -- `k`-point.
  obtain ⟨q, -⟩ : IsLocalRing.closedPoint k ∈ range (snd f t) := by rwa [range_snd]
  obtain ⟨x, hx, -⟩ := exists_section_mem (snd f t) isOpen_univ.isLocallyClosed ⟨q, mem_univ q⟩
  exact ⟨x ≫ fst f t, by rw [Category.assoc, condition, reassoc_of% hx]⟩

/-- Let `f : A ⟶ S` be smooth and `η i` complex points with dense images in `S`
(`New.IsDenseFamily`). If every complex point of `A` over some `η i` is one of the points `ξ z`,
then the `ξ z` have dense images in `A`. -/
lemma IsDenseFamily.of_fibres {A S : Scheme} {κ Z : Type} {η : κ → (Spec (.of ℂ) ⟶ S)}
    (hη : IsDenseFamily η) (f : A ⟶ S) [s : Smooth f] {ξ : Z → (Spec (.of ℂ) ⟶ A)}
    (h_all : ∀ (i : κ) (y : Spec (.of ℂ) ⟶ A), y ≫ f = η i → ∃ z : Z, ξ z = y) :
    IsDenseFamily ξ := by
  -- As `f` is open, the points of `A` over the `η i` are dense; so it suffices to see that each
  -- of them lies in the closure of the `ξ z`.
  refine (hη.preimage f.isOpenMap).induction (fun x ⟨i, hx⟩ ↦ mem_closure_iff.2 fun U hU hxU ↦ ?_)
    isClosed_closure
  -- An open neighbourhood `U` of `x` contains a complex point over `η i`, which is some `ξ z`.
  let V : A.Opens := ⟨U, hU⟩
  obtain ⟨y, hy⟩ : ∃ y : Spec (.of ℂ) ⟶ V, y ≫ V.ι ≫ f = η i :=
    exists_point_over (V.ι ≫ f) ⟨⟨x, hxU⟩, hx.symm⟩
  obtain ⟨z, hz⟩ := h_all i (y ≫ V.ι) hy
  exact ⟨(y ≫ V.ι) (IsLocalRing.closedPoint ℂ), (y _).2, z, by simp only [hz]⟩

/-- Let `X` be a commutative group scheme (`grp`, a `New.AddObj` structure) locally of finite type
over an algebraically closed field `k`, with structure morphism `s`, and let `P` be a property of
morphisms of schemes induced by a property `Q` of ring maps. If a nonempty open subscheme
`i : Y ⟶ X` has `P` over `k`, so does `X`. -/
lemma AddObj.property_of_isOpenImmersion {k : Type} {X : Scheme} [Field k] [IsAlgClosed k]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] {P : MorphismProperty Scheme}
    {Q : {R S : Type} → [CommRing R] → [CommRing S] → (R →+* S) → Prop} [HasRingHomProperty P Q]
    (grp : AddObj (Over.mk s)) {Y : Scheme} (i : Y ⟶ X) [IsOpenImmersion i] (hY : Nonempty Y)
    (hP : P (i ≫ s)) : P s := by
  -- The translates of `i` (for the group structure `grp`) cover `X`, each has `P` over `k`, and
  -- `P` is local on the source.
  let Pt : Type := 𝟙_ (Over (Spec (.of k))) ⟶ Over.mk s
  let c : Spec (.of k) := default
  have : LocallyOfFiniteType (Over.mk s).hom := inferInstanceAs (LocallyOfFiniteType s)
  obtain ⟨y, a, ha⟩ : ∃ y : Pt, y.left c ∈ range i :=
    exists_point_mem (Over.mk s) i.isLocallyClosed_range (range_nonempty i)
  let t (z : Pt) : Y ⟶ X := i ≫ (translation z).left
  let U : X.Opens := ⨆ z : Pt, (t z).opensRange
  have h_cover (x : X) : ∃ (z : Pt) (b : Y), t z b = x := by
    suffices x ∈ U by simpa [U]
    -- Otherwise the closed complement of `U` has a `k`-point `z`; but translation by `z - y`
    -- carries `y`, which lies in the image of `i`, to `z`.
    by_contra hx
    obtain ⟨z, hz⟩ : ∃ z : Pt, z.left c ∈ (U : Set X)ᶜ :=
      exists_point_mem (Over.mk s) U.isOpen.isClosed_compl.isLocallyClosed ⟨x, hx⟩
    refine hz (TopologicalSpace.Opens.mem_iSup.2 ⟨z - y, a, ?_⟩)
    have h_yz : y ≫ translation (z - y) = z := by simp [Pt, comp_add]
    show (translation (z - y)).left (i a) = z.left c
    rw [ha, ← Hom.comp_apply, ← comp_left, h_yz]
  refine IsZariskiLocalAtSource.of_openCover (.mkOfCovers _ _ t h_cover) fun z ↦ ?_
  -- Translations are morphisms over `k`.
  show P ((i ≫ (translation z).left) ≫ (Over.mk s).hom)
  rwa [Category.assoc, (translation z).w]

/-- A standard smooth ring map is standard smooth of some relative dimension. -/
lemma exists_isStandardSmoothOfRelativeDimension {R T : Type} [CommRing R] [CommRing T]
    {φ : R →+* T} (hφ : φ.IsStandardSmooth) : ∃ n : ℕ, φ.IsStandardSmoothOfRelativeDimension n := by
  algebraize [φ]
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hφ
  exact ⟨P.dimension, ι, σ, hσ, hι, P, rfl⟩

/-- Let `f : X ⟶ S` map the affine open `V` into the affine open `U`. If the ring map
`Γ(S, U) ⟶ Γ(X, V)` is standard smooth of relative dimension `n`, then `Spec Γ(X, V) ⟶ S` is smooth
of relative dimension `n`. -/
lemma smoothOfRelativeDimension_fromSpec_comp {X S : Scheme} {f : X ⟶ S} {U : S.Opens}
    {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) {n : ℕ}
    (hn : (f.appLE U V hVU).hom.IsStandardSmoothOfRelativeDimension n) :
    SmoothOfRelativeDimension n (hV.fromSpec ≫ f) := by
  rw [← hU.SpecMap_appLE_fromSpec f hV hVU]
  have : SmoothOfRelativeDimension n (Spec.map (f.appLE U V hVU)) := HasRingHomProperty.Spec_iff.2
    (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hn)
  -- The open immersion `hU.fromSpec` has relative dimension `0`.
  exact smoothOfRelativeDimension_comp n 0 (Spec.map (f.appLE U V hVU)) hU.fromSpec

/-- Let `A` be an abelian scheme over `S` (`New.IsAbelianScheme`) with complex points `y i` over
`η i` whose images are dense in `A`. If `g` is the only possible relative dimension of each fibre
over `η i`, then `A` is smooth of relative dimension `g` over `S`. -/
lemma AddObj.smoothOfRelativeDimension_of_fibres {S : Scheme} {κ : Type} {g : ℕ} {A : Over S}
    [IsAbelianScheme A] {η : κ → (Spec (.of ℂ) ⟶ S)} {y : ∀ i : κ, Over.mk (η i) ⟶ A}
    (hy : IsDenseFamily fun i : κ ↦ (y i).left)
    (h_dim : ∀ (i : κ) (n : ℕ), SmoothOfRelativeDimension n (snd A.hom (η i)) → n = g) :
    SmoothOfRelativeDimension g A.hom := by
  -- Around each `x` there is an affine chart `V`, standard smooth of some relative dimension `n`.
  -- It contains some `y i`, so it gives a nonempty open part of the fibre over `η i` that has
  -- dimension `n`; by `property_of_isOpenImmersion` the whole fibre has dimension `n`, and `n = g`
  -- by `h_dim`.
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨U, hU, V, hV, hxV, hVU, h_std⟩ := Smooth.exists_isStandardSmooth A.hom x
  obtain ⟨n, hn⟩ := exists_isStandardSmoothOfRelativeDimension h_std
  let c : Spec (.of ℂ) := IsLocalRing.closedPoint ℂ
  obtain ⟨i, hi⟩ : ∃ i : κ, (y i).left c ∈ V := hy.exists_mem_open V.isOpen ⟨x, hxV⟩
  suffices h_fibre : SmoothOfRelativeDimension n (snd A.hom (η i)) by
    obtain rfl : n = g := h_dim i n h_fibre
    exact ⟨U, hU, V, hV, hxV, hVU, hn⟩
  -- Let `j` be the inclusion of the open part of the fibre that lies over `V`.
  let π : Limits.pullback A.hom (η i) ⟶ A.left := fst A.hom (η i)
  let j : Limits.pullback hV.fromSpec π ⟶ Limits.pullback A.hom (η i) := snd hV.fromSpec π
  -- It contains the point `p` of the fibre given by `y i`.
  let p : Spec (.of ℂ) ⟶ Limits.pullback A.hom (η i) := lift (y i).left (𝟙 _) (y i).w
  obtain ⟨p', -⟩ : p c ∈ range j := by
    rwa [range_snd, mem_preimage, ← Hom.comp_apply, show p ≫ π = (y i).left from lift_fst _ _ _,
      hV.range_fromSpec]
  -- `pullbackAddObj` is the group structure on the fibre.
  refine (pullbackAddObj (η i)).property_of_isOpenImmersion (snd A.hom (η i)) j ⟨p'⟩ ?_
  -- This open part of the fibre is the base change of the chart along `η i`.
  have h_square : IsPullback _ (j ≫ snd A.hom (η i)) (hV.fromSpec ≫ A.hom) (η i) :=
    (IsPullback.of_hasPullback hV.fromSpec π).paste_vert (IsPullback.of_hasPullback A.hom (η i))
  exact (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback h_square
    (smoothOfRelativeDimension_fromSpec_comp hU hV hVU hn)

end New

end GeometricPoints

/-!
## Geometric reducedness of smooth morphisms and integral abelian varieties

Two instances. A smooth morphism of schemes is geometrically reduced (locally it is étale over a
polynomial ring, `New.Variety.isReduced_of_algebra_etale`). An abelian scheme over an algebraically
closed field is integral. Here `New.IsAbelianScheme` asks a commutative group scheme to be smooth,
proper and divisible (multiplication by each `m ≠ 0` is onto); divisibility takes the place of the
usual connectedness of the fibres, and the second instance recovers it.
-/

section AbelianIntegral

open CategoryTheory AlgebraicGeometry Algebra MorphismProperty TensorProduct Set LocallyOfFiniteType

namespace New.Variety

/-- An étale algebra over an integral domain is reduced. -/
lemma isReduced_of_algebra_etale (A B : Type*) [CommRing A] [CommRing B] [IsDomain A]
    [Algebra A B] [Algebra.Etale A B] : IsReduced B := by
  -- `B` is flat over `A`, so it embeds in `K ⊗[A] B`, which is unramified over the field `K`.
  let K : Type _ := FractionRing A
  have : IsReduced (K ⊗[A] B) := FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective _ (includeRight_injective (IsFractionRing.injective A K))

/-- The form of `New.Variety.isReduced_of_algebra_etale` in which étaleness of `B` over the domain
`A` is an explicit hypothesis, from which the algebra structure is inferred. -/
lemma isReduced_of_etale {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] {alg : Algebra A B}
    (h_etale : Algebra.Etale A B) : IsReduced B :=
  isReduced_of_algebra_etale A B

/-- A smooth morphism of schemes is geometrically reduced. -/
instance {X Y : Scheme.{0}} (s : X ⟶ Y) [hs : Smooth s] : GeometricallyReduced s := by
  -- The base change `t` to a field is smooth, so locally it is étale over a polynomial ring over
  -- the field, which is a domain; reducedness passes to the stalks.
  refine ⟨fun K _ y Z _ t h_pullback ↦ ?_⟩
  have : AlgebraicGeometry.Smooth t := of_isPullback h_pullback hs
  suffices ∀ x : Z, _root_.IsReduced (Z.presheaf.stalk x) from isReduced_of_isReduced_stalk Z
  intro x
  obtain ⟨U, -, V, hV, hx, hVU, h_smooth⟩ := Smooth.exists_isStandardSmooth t x
  have : Nonempty U := ⟨⟨t x, hVU hx⟩⟩
  obtain ⟨n, g, -, h_etale : g.Etale⟩ := h_smooth.exists_etale_mvPolynomial
  have h_red : _root_.IsReduced Γ(Z, V) := isReduced_of_etale h_etale
  -- The stalk at `x` is a localization of `Γ(Z, V)`.
  let : Algebra Γ(Z, V) (Z.presheaf.stalk x) := Z.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
  have := hV.isLocalization_stalk ⟨x, hx⟩
  exact isReduced_localizationPreserves (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ h_red

/-- An abelian scheme (`New.IsAbelianScheme`: smooth, proper and divisible) over an algebraically
closed field is integral. -/
instance {k : Type} [Field k] [IsAlgClosed k] (A : Over (Spec ⟨k⟩)) [hA : IsAbelianScheme A] :
    AlgebraicGeometry.IsIntegral A.left := by
  -- The `k`-points act by translation on the finite set of irreducible components, so `n • x` fixes
  -- every component, where `n = G.index` is the index of the kernel. As multiplication by `n` is
  -- onto, the component of the origin is everything.
  have : IsReduced A.left := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian A.hom
  have : IsNoetherian A.left :=
    { isLocallyNoetherian A.hom, compactSpace_of_universallyClosed A.hom with }
  have := (finite_irreducibleComponents_of_isNoetherian (X := A.left)).to_subtype
  -- Translation by a `k`-point is a homeomorphism, so it acts on the irreducible components.
  let P : Type := MonoidalCategoryStruct.tensorUnit (Over (Spec ⟨k⟩)) ⟶ A
  let act : AddAction P (irreducibleComponents A.left) :=
    { vadd g C := ⟨(translation g).left ⁻¹' C, preimage_mem_irreducibleComponents C.prop
        (translation g).left.isOpenEmbedding (by simp [C.prop.1.nonempty])⟩
      zero_vadd := by simp [HVAdd.hVAdd, preimage]
      add_vadd := by simp [P, HVAdd.hVAdd, preimage, ← Scheme.Hom.comp_apply, ← Over.comp_left,
        add_assoc, comp_add] }
  let G : AddSubgroup P := (AddAction.toPermHom P (irreducibleComponents A.left)).ker
  let pt : Spec ⟨k⟩ := default
  let C : irreducibleComponents A.left :=
    ⟨irreducibleComponent ((0 : P).left pt), irreducibleComponent_mem_irreducibleComponents _⟩
  have h_univ : C.val = univ := by
    by_contra h_ne
    -- Otherwise some `k`-point `x` has `n • x` outside `C`.
    have h_onto : Surjective (G.index • 𝟙 A).left := hA.nsmul_surjective _ G.index_ne_zero_of_finite
    obtain ⟨x, hx⟩ : ∃ x : P, x.left pt ∈ (G.index • 𝟙 A).left ⁻¹' C.valᶜ := exists_point_mem A
      (isClosed_irreducibleComponent.isOpen_compl.preimage (by fun_prop)).isLocallyClosed
      ((nonempty_compl.mpr h_ne).preimage h_onto.surj)
    -- But `n • x` is the translate of the origin by `n • x`, which preserves `C`.
    have h_ker : AddAction.toPermHom P _ (G.index • x) = 0 := G.nsmul_index_mem x
    have h_fix : (translation (G.index • x)).left ⁻¹' C.val = C.val :=
      congrArg Subtype.val (DFunLike.congr_fun (congrArg Additive.toMul h_ker) C)
    have h_mem : ((0 : P) ≫ translation (G.index • x)).left pt ∈ C.val :=
      h_fix.symm.subset mem_irreducibleComponent
    have h_transl : (0 : P) ≫ translation (G.index • x) = x ≫ (G.index • 𝟙 A) := by
      simp [comp_add, comp_nsmul]
    exact hx (by rwa [h_transl] at h_mem)
  have : IrreducibleSpace A.left :=
    (irreducibleSpace_def _).mpr (h_univ.subst isIrreducible_irreducibleComponent)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end New.Variety

end AbelianIntegral

/-!
## Specialisation to geometric points and flat morphisms on stalks

`New.Variety.AllSpecializeTo S Q` says that every point of `S` specialises to a geometric point with
the property `Q`.
-/

section Specialisation

open AlgebraicGeometry Scheme RingHom.FaithfullyFlat Flat

/-- Every point of `S` specialises to the image of the closed point under some `t : Spec k ⟶ S` with
`k` algebraically closed and `Q t`. -/
def New.Variety.AllSpecializeTo (S : Scheme)
    (Q : ∀ {k : Type} [Field k], (Spec ⟨k⟩ ⟶ S) → Prop) : Prop :=
  ∀ s : S, ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (t : Spec ⟨k⟩ ⟶ S),
    s ⤳ t (IsLocalRing.closedPoint k) ∧ Q t

/-- For a point `s` of a scheme `Z`, the morphism from the spectrum of the stalk at `s` to `Z` is
flat. -/
instance {Z : Scheme} (s : Z) : Flat (fromSpecStalk Z s) := by
  -- The stalk is a localization of the ring of an affine open `U` around `s`, and `U ⊆ Z` is open.
  obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
  let : Algebra Γ(Z, U) (Z.presheaf.stalk s) := Z.presheaf.algebra_section_stalk (⟨s, hs⟩ : U)
  have := hU.isLocalization_stalk ⟨s, hs⟩
  have : Flat (Spec.map (Z.presheaf.germ U s hs)) :=
    SpecMap_iff.mpr (IsLocalization.flat _ (hU.primeIdealOf ⟨s, hs⟩).asIdeal.primeCompl)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hs, IsAffineOpen.fromSpecStalk]
  infer_instance

/-- A flat morphism of schemes is injective on stalks. -/
lemma New.stalkMap_injective_of_flat {X Y : Scheme} (q : X ⟶ Y) [Flat q] (x : X) :
    Function.Injective (q.stalkMap x) := by
  -- The map of stalks is flat and local, hence faithfully flat, hence injective.
  have h_flat : (q.stalkMap x).hom.Flat := Flat.stalkMap q x
  algebraize [(q.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (q x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (q.stalkMap x).hom)
  exact RingHom.FaithfullyFlat.injective Module.FaithfullyFlat.of_flat_of_isLocalHom

end Specialisation

/-!
## Separating families of points over a stalk and on products of flat schemes

A family of complex points of a scheme is separating (`New.IsSeparatingFamily`) if the scheme is
reduced and the points are dense (`New.IsDenseFamily`); regular functions are then determined by
their values there.
-/

namespace New

open CategoryTheory AlgebraicGeometry Limits pullback Set Scheme Spec Pullback Over PointFn Filter

/-- The points of a finite set `C` that lie near `s` specialise to `s`. -/
lemma eventually_specializes_of_finite {T : Type*} [TopologicalSpace T] {C : Set T}
    (hC : C.Finite) (s : T) : ∀ᶠ t in nhds s, t ∈ C → t ⤳ s := by
  suffices h : ∀ᶠ t in nhds s, ∀ c ∈ C, t = c → c ⤳ s from h.mono fun t ht htC ↦ ht t htC rfl
  refine hC.eventually_all.2 fun c _ ↦ eventually_imp_distrib_right.2 fun h_freq ↦ ?_
  exact specializes_iff_mem_closure.2 h_freq.mem_closure

/-- Let `S` and `A` be reduced, `z : A ⟶ S`, `s` a point of `S`, and `x w` complex points of `A`
with dense images and with finitely many composites `x w ≫ z`. Consider the pairs of an index `w`
and a map `ψ` from the stalk `𝒪_{S,s}` to `ℂ` such that `x w ≫ z` factors through `Spec 𝒪_{S,s}`
via `Spec.map ψ`. The points `(x w, Spec.map ψ)` of `A ×_S Spec 𝒪_{S,s}` form a separating family:
this scheme is reduced and the images of these points are dense. -/
lemma isSeparatingFamily_stalk {S : Scheme} [IsReduced S] {W : Type} {A : Scheme} {z : A ⟶ S}
    {x : W → (Spec (.of ℂ) ⟶ A)} [IsReduced A] (h_dense : IsDenseFamily x)
    (h_finite : (range fun w : W ↦ x w ≫ z).Finite) (s : S) :
    IsSeparatingFamily
      (Z := Σ' (w : W) (ψ : S.presheaf.stalk s ⟶ .of ℂ), Spec.map ψ ≫ S.fromSpecStalk s = x w ≫ z)
      fun ⟨w, ψ, h_factor⟩ ↦ (pullback.lift (x w) (Spec.map ψ) h_factor.symm :
        Spec (.of ℂ) ⟶ pullback z (S.fromSpecStalk s)) := by
  let P : Scheme := pullback z (S.fromSpecStalk s)
  let π : P ⟶ A := fst z (S.fromSpecStalk s)
  refine ⟨?_, π.isEmbedding.dense_iff.2 fun y ↦ ?_⟩
  · -- The stalk maps of `π` are bijective, and the stalks of `A` are reduced.
    suffices ∀ y : P, _root_.IsReduced (P.presheaf.stalk y) from isReduced_of_isReduced_stalk P
    intro y
    let e : A.presheaf.stalk (π y) ≃+* P.presheaf.stalk y := .ofBijective (π.stalkMap y).hom
      ⟨stalkMap_injective_of_flat π y, π.stalkMap_surjective y⟩
    exact isReduced_of_injective e.symm e.symm.injective
  -- Of the finitely many images in `S`, only those that specialise to `s` lie near `s`, and so
  -- near `z (π y)`, which specialises to `s`.
  let c : Spec (.of ℂ) := IsLocalRing.closedPoint ℂ
  let C : Set S := range fun w : W ↦ (x w ≫ z) c
  have hC : C.Finite := (h_finite.image fun p ↦ p c).subset (by simp [C, ← range_comp'])
  have h_spec : z (π y) ⤳ s := by
    simpa [range_fromSpecStalk] using (range_fst z (S.fromSpecStalk s)).subset (mem_range_self y)
  have h_near : ∀ᶠ a in nhds (π y), z a ∈ C → z a ⤳ s := (z.continuous.tendsto (π y)).eventually
    ((eventually_specializes_of_finite hC s).filter_mono (specializes_iff_nhds.1 h_spec))
  -- So the `x w` whose image specialises to `s` accumulate at `π y`, and these lift.
  refine (((mem_closure_iff_frequently.1 (h_dense (π y))).and_eventually h_near).mono
    ?_).mem_closure
  rintro _ ⟨⟨w, rfl⟩, hw⟩
  have hw_spec : (x w ≫ z) c ⤳ s := hw ⟨w, rfl⟩
  let ψ : S.presheaf.stalk s ⟶ .of ℂ :=
    S.presheaf.stalkSpecializes hw_spec ≫ stalkClosedPointTo (x w ≫ z)
  have hψ : Spec.map ψ ≫ S.fromSpecStalk s = x w ≫ z := by
    rw [Spec.map_comp, Category.assoc, SpecMap_stalkSpecializes_fromSpecStalk]
    exact Spec_stalkClosedPointTo_fromSpecStalk _
  exact ⟨pullback.lift (x w) (Spec.map ψ) hψ.symm c, ⟨⟨w, ψ, hψ⟩, rfl⟩,
    by rw [← Hom.comp_apply, pullback.lift_fst]⟩

/-- Let `S` be reduced with finitely many complex points `ξ i` whose images are dense. An element
`a` of the stalk at `x` is zero if `ψ a = 0` for every map `ψ` from the stalk to `ℂ` such that
some `ξ i` factors through the spectrum of the stalk via `Spec.map ψ`. -/
lemma stalk_eq_zero_of_forall_factor {S : Scheme} [IsReduced S] {J : Type} [Finite J]
    {ξ : J → (Spec (.of ℂ) ⟶ S)} (hξ : IsDenseFamily ξ) {x : S} (a : S.presheaf.stalk x)
    (h_vanish : ∀ (i : J) (ψ : S.presheaf.stalk x ⟶ .of ℂ),
      Spec.map ψ ≫ S.fromSpecStalk x = ξ i → ψ a = 0) :
    a = 0 := by
  -- View `a` as a regular function `f` on the ring-valued points (`PointFn`) of
  -- `S ×_S Spec 𝒪_{S,x}`, where the lifts of the `ξ i` separate. It agrees at these lifts with the
  -- function of the zero section, hence also at the tautological point `inv q`, where it is `a`.
  let q : pullback (𝟙 S) (S.fromSpecStalk x) ⟶ Spec (S.presheaf.stalk x) := snd _ _
  let f : PointFn (pullback (𝟙 S) (S.fromSpecStalk x)) := fun _ y ↦ preimage (y ≫ q) a
  have hf : IsRegularOn f ⊤ := by simp [f, IsRegularOn]
  have h_eq : f _ (inv q) = ofSection (U := ⊤) 0 _ (inv q) := by
    refine (isSeparatingFamily_stalk (z := 𝟙 S) hξ (toFinite _) x).pointFn_ext hf
      (isRegularOn_ofSection 0) (fun ⟨i, ψ, hψ⟩ _ ↦ ?_) _ (inv q) landsIn_top
    -- At the lift given by `ψ` the function `f` takes the value `ψ a`.
    simpa [f, q, pullback.lift_snd] using h_vanish i ψ hψ
  simpa [f] using h_eq

/-- The form of `New.stalk_eq_zero_of_forall_factor` in which the index `i`, the map `ψ` from the
stalk to `ℂ` and the factorisation of `ξ i` via `Spec.map ψ` are bundled into one triple `p` (so
that `p.snd.fst` is `ψ`): for `S` reduced with finitely many dense complex points `ξ i`, an element
`a` of the stalk at `x` is zero if `ψ a = 0` for every such triple. -/
lemma stalk_eq_zero_of_dense {S : Scheme} [IsReduced S] {J : Type} [Finite J]
    {ξ : J → (Spec (.of ℂ) ⟶ S)} (hξ : IsDenseFamily ξ) {x : S} (a : S.presheaf.stalk x)
    (h_vanish : ∀ p : Σ' (i : J) (ψ : S.presheaf.stalk x ⟶ .of ℂ),
      Spec.map ψ ≫ S.fromSpecStalk x = ξ i, p.snd.fst a = 0) : a = 0 :=
  stalk_eq_zero_of_forall_factor hξ a fun i ψ hψ ↦ h_vanish ⟨i, ψ, hψ⟩

open MonoidalCategory IsSchemeTheoreticallyDominant LocallyOfFiniteType CartesianMonoidalCategory

/-- Let X be reduced, locally noetherian, flat and locally of finite type over a reduced locally
noetherian scheme S with finitely many complex points whose images are dense. Then the smooth
locus of X over S is dense in X. -/
lemma dense_smoothLocus_of_isDenseFamily {S : Scheme} [IsReduced S] [IsLocallyNoetherian S]
    {J : Type} [Finite J] {ξ : J → (Spec (.of ℂ) ⟶ S)} (hξ : IsDenseFamily ξ) {X : Scheme}
    (f : X ⟶ S) [LocallyOfFiniteType f] [Flat f] [IsReduced X] [IsLocallyNoetherian X] :
    Dense (f.smoothLocus : Set X) := by
  -- At a generic point `a` of `X` the stalks of `X` and `S` are fields. The second maps to `ℂ`,
  -- so it has characteristic zero and is perfect, and the extension is formally smooth.
  refine (dense_iff_closure_eq.2 genericPoints.closure).mono fun a ha ↦ ?_
  have hX : IsField (X.presheaf.stalk a) :=
    isField_stalk_of_closure_mem_irreducibleComponents _ a ha
  have hS : IsField (S.presheaf.stalk (f a)) :=
    IsLocalHom.isField (stalkMap_injective_of_flat f a) hX
  -- As `1 ≠ 0` in the stalk, some `ξ i` factors through it.
  obtain ⟨ψ⟩ : Nonempty (S.presheaf.stalk (f a) ⟶ .of ℂ) := by_contra fun h_empty ↦
    one_ne_zero (stalk_eq_zero_of_forall_factor hξ 1 fun _ ψ _ ↦ (h_empty ⟨ψ⟩).elim)
  let : Field (X.presheaf.stalk a) := hX.toField
  let : Field (S.presheaf.stalk (f a)) := hS.toField
  have : CharZero (S.presheaf.stalk (f a)) := ψ.hom.charZero
  have h_ft : (f.stalkMap a).hom.EssFiniteType := LocallyOfFiniteType.stalkMap f a
  algebraize [(f.stalkMap a).hom]
  exact Algebra.FormallySmooth.of_perfectField

/-- Let S be reduced and locally noetherian, with a finite family of complex points whose images are
dense. Let A and B be flat and locally of finite type over S, with A reduced. Let η_w be complex
points of S, and let y_w be complex points of B over η_w that separate B, meaning B is reduced and
the images of the y_w are dense. Suppose that for each w the complex points e_w(v) of A over η_w
have dense image in the fibre A ×_S Spec ℂ over η_w. Then the complex points (e_w(v), y_w) separate
A ×_S B: it is reduced and their images are dense (`New.IsSeparatingFamily`). -/
lemma IsSeparatingFamily.prod {S : Scheme} [IsReduced S] {A B : Over S} {V W J : Type} [Finite J]
    {ξ : J → (Spec (.of ℂ) ⟶ S)} {η : W → (Spec (.of ℂ) ⟶ S)} [LocallyOfFiniteType A.hom]
    [LocallyOfFiniteType B.hom] [IsLocallyNoetherian S] [Flat A.hom] [Flat B.hom]
    {y : ∀ w : W, Over.mk (η w) ⟶ B} {e : ∀ w : W, V → (Over.mk (η w) ⟶ A)}
    (hy : IsSeparatingFamily fun w : W ↦ (y w).left) (hξ : IsDenseFamily ξ)
    (h_red : IsReduced A.left)
    (he : ∀ w : W, IsDenseFamily fun v : V ↦
      (pullback.lift (e w v).left (𝟙 (Spec (.of ℂ))) (e w v).w :
        Spec (.of ℂ) ⟶ pullback A.hom (η w))) :
    IsSeparatingFamily fun ((w, v) : W × V) ↦
      ((CartesianMonoidalCategory.lift (e w v) (y w)).left : Spec (.of ℂ) ⟶ (A ⊗ B).left) := by
  obtain ⟨hB_red : IsReduced B.left, hB_dense⟩ := hy
  have : IsLocallyNoetherian A.left := isLocallyNoetherian A.hom
  have : IsLocallyNoetherian B.left := isLocallyNoetherian B.hom
  -- The smooth locus of `A` over `S`, with inclusion `j`, is dense.
  let j : A.hom.smoothLocus.toScheme ⟶ A.left := A.hom.smoothLocus.ι
  have : Smooth (j ≫ A.hom) := by
    simp [j, ← Hom.smoothLocus_eq_top_iff, ← j.preimage_smoothLocus_eq]
  have : IsDominant j := ⟨(dense_smoothLocus_of_isDenseFamily hξ A.hom).denseRange_val⟩
  have : IsSchemeTheoreticallyDominant j := of_isDominant j
  -- Hence `A ×_S B` is reduced: the flat base change `j'` of `j` is scheme-theoretically dominant,
  -- and its source is smooth over the reduced `B`.
  let j' : pullback (j ≫ A.hom) B.hom ⟶ pullback A.hom B.hom :=
    (pullbackRightPullbackFstIso A.hom B.hom j).inv ≫ snd j (fst A.hom B.hom)
  refine ⟨isReduced j', .of_closure ?_⟩
  -- The points of `A ⊗ B` over some `y w` are dense, as `A` is universally open over `S`. Such a
  -- point comes from the fibre of `A` at `η w`, where the `e w v` are dense.
  refine (hB_dense.preimage (pullback.snd A.hom B.hom).isOpenMap).mono ?_
  rintro t ⟨w, hw⟩
  have ht : pullback.snd A.hom B.hom t ∈ range (y w).left := ⟨_, hw⟩
  obtain ⟨u, rfl⟩ : t ∈ range (A ◁ y w).left := by simpa [range_map, whiskerLeft_left] using ht
  refine map_mem_closure (by fun_prop) (he w u) (forall_mem_range.2 fun v ↦ ⟨(w, v), ?_⟩)
  -- The map `A ◁ y w` from the fibre sends `(e w v, 𝟙)` to `(e w v, y w)`.
  have h_lift : lift (e w v) (𝟙 _) ≫ A ◁ y w = lift (e w v) (y w) := by simp
  exact congrArg (fun m : Over.mk (η w) ⟶ A ⊗ B ↦ m.left (IsLocalRing.closedPoint ℂ)) h_lift.symm

end New
