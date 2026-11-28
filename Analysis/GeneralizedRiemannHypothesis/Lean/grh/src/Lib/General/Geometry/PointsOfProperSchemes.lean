import Lib.Cohomology.ProperBaseChange.PlaceSpace
import Lib.General.Geometry.EtaleCharts
import Lib.Shimura.AbelianScheme.Basic

/-!
# Functors of points of proper schemes: closed loci, atlases and descent of relations

Schemes over `Spec R` are studied through their functors of points. The functor of points of a
proper scheme is proper and separated. On comparable rings (`New.Variety.IsComparableRing`), its
points all come from one affine scheme. If the scheme is smooth of relative dimension `d` after base
change to `k`, it also has an étale atlas.

## Main definitions and results

* `New.Variety.exists_ideal_le_ker_iff_factors`: for a closed immersion `i : Z ⟶ X` and a point `a`
  of `X` with values in `S`, one ideal `I` of `S` describes the ring maps `γ : S →+* B` along which
  `a` lands in `Z`, namely those that kill `I`. It is finitely generated if `i` is of finite
  presentation.
* `New.Variety.exists_locallyOfFiniteType_forall_factors`: a proper scheme `X` over `Spec R`
  receives a morphism `Spec T ⟶ X` from one affine scheme, locally of finite type, through which
  every point with values in a comparable ring (`New.Variety.IsComparableRing`) factors.
* `New.Variety.isProperOver_pointsToBase`: the functor of points of `X` over `R` satisfies
  `New.Variety.IsProperOver`.
* `New.Variety.isSeparatedFunctor_algPointsOf`: for an `R`-algebra `k` and a proper scheme `W` over
  `Spec R`, the points of `W` with values in `k`-algebras form a separated functor
  (`New.Variety.IsSeparatedFunctor`).
* `New.Variety.hasAtlas_algPointsOf`: if moreover `W` is smooth of relative dimension `d` after base
  change to `k`, the functor has an atlas of dimension `d`.
* `New.Variety.isAffinelyCovered_algPointsOf`: on rings satisfying `New.Variety.IsComparableRing`,
  one affine scheme surjects onto the points of a proper `W`.
* `New.Variety.exists_hom_of_rel` builds a homomorphism A → B of commutative group objects over S
  from a homomorphism f : W → B and a relation between T-points of W and of A. The relation is
  stable under pull-back and subtraction, compatible with f, and defined on an fpqc cover of A.

Notions from other files:
* `New.Variety.IsComparableRing`, applied to the identity map of a ring: for any a, b in the ring
  there is an idempotent e with a ∣ e * b and b ∣ (1 - e) * a.
* `New.Variety.pointsToBase`: For a morphism s: X → Spec R, the map from the functor of points of X
  to the functor A ↦ Hom(R, A) that sends x ∈ X(A) to the ring map R → A of s∘x.
* `New.Variety.HasAtlas`: X is separated and has finitely many charts, each with exactly d étale
  coordinates, that contain every field-valued point.
* `New.Variety.IsOpenSubfunctor`: V is an open subfunctor of X: each x ∈ X(A) has an ideal I of A
  such that, for φ: A → B, φ(x) ∈ V(B) iff φ(I)B = B.
* `New.IsAdditive`: The morphism f : A → B of commutative group objects is a homomorphism: composing
  with f is additive on U-points for every U.

## Relation to the literature

Known; see `Lib.Cohomology.Etale.FilteredLimits` and `Lib.PadicComparison.HodgeTate.PeriodMap` for
sources.
-/

/-! ## Morphisms of spectra over a base and algebra maps -/

section SpecOver

open CategoryTheory AlgebraicGeometry CommRingCat Over OverMorphism

namespace New.specOver

variable {R C D E : Type} [CommRing R] [CommRing C] [CommRing D] [CommRing E] [Algebra R C]
  [Algebra R D] [Algebra R E] (φ : C →ₐ[R] D) (ψ : D →ₐ[R] E)

/-- For an R-algebra homomorphism φ: C→D, the induced morphism Spec D → Spec C of schemes over
Spec R. -/
noncomputable def map : specOver R D ⟶ specOver R C :=
  homMk (Spec.map (ofHom φ)) (by simp [← Spec.map_comp, ← ofHom_comp])

@[reassoc]
lemma map_comp : map ψ ≫ map φ = map (ψ.comp φ) := ext (Spec.map_comp ..).symm

@[simp]
lemma map_id : map (AlgHom.id R C) = 𝟙 (specOver R C) := ext (Spec.map_id _)

/-- Every morphism `Spec D ⟶ Spec C` over `Spec R` is induced by exactly one `R`-algebra map
`C → D`. -/
lemma map_bijective : (map : (C →ₐ[R] D) → (specOver R D ⟶ specOver R C)).Bijective := by
  -- `Spec` is fully faithful on the opposite category of `R`-algebras.
  let toOp : (C →ₐ[R] D) ≃ (Opposite.op (CommAlgCat.of R D) ⟶ Opposite.op (CommAlgCat.of R C)) :=
    { toFun φ := (CommAlgCat.ofHom φ).op, invFun f := f.unop.hom }
  exact (toOp.trans (algSpec.fullyFaithful (R := .of R)).homEquiv).bijective

end New.specOver

end SpecOver

/-! ## The ideal cutting out the locus of a closed subscheme -/

section FactorisationIdeal

open CategoryTheory AlgebraicGeometry Ideal.Quotient Limits.pullback CommRingCat Spec RingHom

namespace New.Variety

/-- A ring map `γ : S →+* B` kills the ideal `I` if and only if `Spec γ` factors through
`Spec (S ⧸ I) ⟶ Spec S`. -/
lemma le_ker_iff_factors {S B : Type} [CommRing S] [CommRing B] {I : Ideal S} {γ : S →+* B} :
    I ≤ ker γ ↔ ∃ l : Spec (of B) ⟶ Spec (of (S ⧸ I)),
      l ≫ specMap (Ideal.Quotient.mk I) = specMap γ := by
  refine ⟨fun hI ↦ ⟨specMap (lift I γ hI), (map_comp ..).symm⟩, ?_⟩
  rintro ⟨l, hl⟩ x hx
  -- On rings, `γ` factors through `S ⧸ I`, where `x` is zero.
  have h_factor : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ preimage l = CommRingCat.ofHom γ :=
    map_inj.1 (by simpa using hl)
  simpa [eq_zero_iff_mem.2 hx] using (ConcreteCategory.congr_hom h_factor x).symm

/-- For a closed immersion i: Z → X and a: Spec S → X, there is an ideal I of S, finitely
generated if i is of finite presentation, such that a∘Spec γ factors through Z exactly when
γ: S → B kills I. -/
lemma exists_ideal_le_ker_iff_factors {S : Type} [CommRing S] {X Z : Scheme} (i : Z ⟶ X)
    [IsClosedImmersion i] (a : Spec (of S) ⟶ X) :
    ∃ I : Ideal S,
      -- (a) finite generation
      (LocallyOfFinitePresentation i → I.FG) ∧
      -- (b) the ring maps along which `a` lands in `Z` are those that kill `I`
      ∀ ⦃B : Type⦄ [CommRing B] (γ : S →+* B),
        I ≤ ker γ ↔ ∃ l : Spec (of B) ⟶ Z, l ≫ i = Spec.map (ofHom γ) ≫ a := by
  -- The pull-back of `i` along `a` is a closed subscheme of `Spec S`, so it is `Spec (S ⧸ I)`.
  obtain ⟨I, e, he⟩ : ∃ (I : Ideal S) (e : Limits.pullback i a ≅ Spec (of (S ⧸ I))),
      snd i a = e.hom ≫ Spec.map (ofHom (mk I)) :=
    (IsClosedImmersion.Spec_iff (f := snd i a)).1 inferInstance
  refine ⟨I, fun _ ↦ ?_, fun B _ γ ↦ le_ker_iff_factors.trans ⟨?_, ?_⟩⟩
  · -- `S ⧸ I` is of finite presentation over `S`, so the kernel `I` is finitely generated.
    have h_scheme : LocallyOfFinitePresentation (map (ofHom (mk I))) := by
      rw [← e.inv_comp_eq.2 he]
      infer_instance
    have : Algebra.FinitePresentation S (S ⧸ I) := HasRingHomProperty.Spec_iff.1 h_scheme
    simpa using Algebra.FinitePresentation.ker_fG_of_surjective (mkₐ S I) mk_surjective
  · -- A map to `Spec (S ⧸ I)` composes with the first projection of the pull-back.
    rintro ⟨l, hl⟩
    exact ⟨l ≫ e.inv ≫ fst i a, by grind [condition]⟩
  · -- A map to `Z` that lifts `Spec γ ≫ a` gives a map to the pull-back, which is `Spec (S ⧸ I)`.
    rintro ⟨l, hl⟩
    exact ⟨lift l _ hl ≫ e.hom, by grind [lift_snd]⟩

end New.Variety

end FactorisationIdeal

/-! ## Properness of the functor of points of a proper scheme -/

section ProperSchemes

open CategoryTheory Limits AlgebraicGeometry CommRingCat Scheme Spec terminal Ideal TopologicalSpace
  PrimeSpectrum Set Cofan.IsColimit IsOpenImmersion Fintype prod

variable {X : Scheme} {R : CommRingCat} (s : X ⟶ Spec R)

/-- If X is proper over Spec R, there is a morphism a: Spec T → X, locally of finite type, through
which every morphism Spec O → X factors, for all rings O whose identity map satisfies
`New.Variety.IsComparableRing`: any two elements are comparable for divisibility after a partition
by an idempotent. -/
lemma New.Variety.exists_locallyOfFiniteType_forall_factors [IsProper s] :
    ∃ (T : CommRingCat) (a : Spec T ⟶ X),
      LocallyOfFiniteType a ∧
      ∀ O : CommRingCat,
        IsComparableRing (id : O → O) →
          ∀ z : Spec O ⟶ X, ∃ u : T ⟶ O, Spec.map u ≫ a = z := by
  -- Take the disjoint union of a finite affine open cover `𝒰` of `X`. Partition `Spec O` into
  -- finitely many clopen pieces, each sent by the `O`-valued point `z` into one member of `𝒰`.
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
  have : LocallyOfFiniteType (Sigma.desc 𝒰.f) :=
    HasRingHomProperty.instIsZariskiLocalAtSource.sigmaDesc inferInstance
  refine ⟨_, inv (toSpecΓ _) ≫ Sigma.desc 𝒰.f, locallyOfFiniteType_comp ..,
    fun O h_comparable z ↦ ?_⟩
  -- Around each prime `x` there is such a clopen piece: take a maximal ideal `m ⊇ x`, a basic open
  -- `D(g) ∋ m` sent into one member, and an idempotent `e ∉ m` divisible by `g` (this is where
  -- `h_comparable` is used). The clopen set `D(e)` contains `x` and lies in `D(g)`.
  have h_local (x : Spec O) :
      ∃ (C : Clopens (Spec O)) (i : 𝒰.I₀), x ∈ C ∧ ∀ y ∈ C, z y ∈ range (𝒰.f i) := by
    obtain ⟨m, hm, hxm⟩ := exists_le_maximal x.asIdeal x.isPrime.ne_top
    obtain ⟨j, hj⟩ : ∃ j : 𝒰.I₀, z ⟨m, hm.isPrime⟩ ∈ range (𝒰.f j) := ⟨_, 𝒰.covers _⟩
    obtain ⟨_, ⟨g, rfl⟩, hg, hg_sub⟩ := isTopologicalBasis_basic_opens.isOpen_iff.1
      (z ⁻¹ᵁ Hom.opensRange (𝒰.f j)).isOpen ⟨m, hm.isPrime⟩ hj
    obtain ⟨e, hem, he, hge⟩ := exists_dvd_idempotent_of_notMem h_comparable hm hg
    refine ⟨isIdempotentElemEquivClopens ⟨e, he⟩, j, fun hex ↦ hem (hxm hex), fun y hy ↦ ?_⟩
    exact hg_sub fun hgy ↦ hy (mem_of_dvd _ hge hgy)
  choose C i mem_C hC using h_local
  -- Finitely many pieces cover; shrink them to be disjoint, so that `Spec O` is their coproduct.
  obtain ⟨t, ht⟩ := finite_cover_nhds fun x ↦ (C x).isOpen.mem_nhds (mem_C x)
  obtain ⟨D, hD_le, hD_sup, hD_disj⟩ := exists_disjointed_le fun x : t ↦ C x
  have hD_cover : ⨆ x : t, Scheme.Hom.opensRange (Opens.ι (D x).toOpens) = ⊤ := by
    simp_all [Clopens.ext_iff, iUnion_subtype]
  obtain ⟨c⟩ : Nonempty (IsColimit (Cofan.mk (Spec O) fun x ↦ Opens.ι (D x).toOpens)) :=
    nonempty_isColimit_cofanMk_of _ hD_cover (hD_disj.mono (by simp [← Opens.coe_disjoint]))
  -- Lift `z` on each piece and glue along the coproduct `c`; equality is checked piece by piece.
  let piece (x : t) : Opens.toScheme (D x).toOpens ⟶ 𝒰.X (i x) :=
    lift (𝒰.f (i x)) (Opens.ι _ ≫ z) (range_subset_iff.2 fun y ↦ hC x y.1 (hD_le x y.2))
  let glued : Spec O ⟶ ∐ 𝒰.X := desc c fun x ↦ piece x ≫ Sigma.ι 𝒰.X (i x)
  have h_glued : glued ≫ Sigma.desc 𝒰.f = z := by
    refine hom_ext c _ _ fun x ↦ ?_
    -- On `D x` the glued map is `piece x`, and this lifts `z` to the member `i x` of the cover.
    have h_piece : Cofan.inj (Cofan.mk (Spec O) fun x ↦ Opens.ι (D x).toOpens) x ≫ glued =
        piece x ≫ Sigma.ι 𝒰.X (i x) := by
      simp [glued, -cofan_mk_inj]
    rw [reassoc_of% h_piece]
    simp [piece]
  exact ⟨preimage (glued ≫ toSpecΓ _), by simpa using h_glued⟩

/-- If `s : X ⟶ Spec R` is a proper morphism of schemes, then the functor of points `A ↦ X(A)` with
its structure map `pointsToBase s` is proper over `R` (`New.Variety.IsProperOver`). The locus where
two points agree is cut out by an ideal. There are a ring `T` and a point `a ∈ X(T)` such that each
point of `X` in an algebraically closed field `K` that maps `R` into a valuation ring `O` of `K` is
the image of `a` under some `T → O ⊆ K`. -/
lemma New.Variety.isProperOver_pointsToBase [IsProper s] : IsProperOver (pointsToBase s) := by
  have : X.IsSeparated := by
    rw [X.isSeparated_iff, ← comp_from s]
    infer_instance
  refine ⟨fun C ⟨x⟩ ⟨y⟩ ↦ ?_, ?_⟩
  · -- Two points agree exactly where the pair factors through the closed diagonal, and
    -- `exists_ideal_le_ker_iff_factors` cuts that locus out by an ideal `I`.
    obtain ⟨I, -, hI⟩ := exists_ideal_le_ker_iff_factors (diag X) (lift x y)
    refine ⟨I, fun B f ↦ ULift.up_inj.trans ?_⟩
    simp [hI, prod.hom_ext_iff]
  · -- A geometric point `z` whose ring map on `R` lands in the valuation ring `O` extends to
    -- an `O`-point by the valuative criterion, and `O`-points factor through the atlas `a`,
    -- as a valuation ring is a comparable ring.
    obtain ⟨T, a, -, ha⟩ := exists_locallyOfFiniteType_forall_factors s
    refine ⟨T, ⟨a⟩, fun {K} _ _ O z hz ↦ ?_⟩
    -- A proper morphism is universally closed, so valuative squares have liftings.
    have h_val : ValuativeCriterion.Existence s :=
      (UniversallyClosed.eq_valuativeCriterion.le X (Spec R) s inferInstance).left
    -- The ring map `ρ : R ⟶ K` under `z` factors through `ρ₀ : R → O`, which gives a square.
    let ρ₀ : R →+* O := (baseRingMap (pointsToBase s) z).hom.codRestrict O hz
    have hρ : Spec.map (baseRingMap (pointsToBase s) z) = z.down ≫ s := map_preimage _
    have h_comm : z.down ≫ s = Spec.map (ofHom (algebraMap O K)) ≫ Spec.map (ofHom ρ₀) := by
      rw [← hρ, ← Spec.map_comp]
      rfl
    let sq : ValuativeCommSq s :=
      { R := O, K := K, i₁ := z.down, i₂ := Spec.map (ofHom ρ₀), commSq := ⟨h_comm⟩ }
    obtain ⟨l, hl⟩ : ∃ l : Spec (of O) ⟶ X, Spec.map (ofHom O.subtype) ≫ l = z.down := by
      obtain ⟨⟨lifting⟩⟩ := h_val sq
      exact ⟨lifting.l, lifting.fac_left⟩
    obtain ⟨u, hu⟩ := ha (of O) isTest_of_preValuationRing.isComparableRing l
    refine ⟨u, congrArg ULift.up ?_⟩
    change Spec.map (u ≫ ofHom O.subtype) ≫ a = z.down
    rw [Spec.map_comp, Category.assoc, hu, hl]

end ProperSchemes

/-!
## Separatedness, affine covers and étale atlases for points

The passage from schemes to functors of points: for a scheme `W` over `Spec R` and an `R`-algebra
`k`, `New.Variety.algPointsOf k R W` sends a `k`-algebra `A` to `W(A)`.

* `New.Variety.isOpenSubfunctor_of_landsIn`: the points that land in an open subset form an open
  subfunctor.
-/

section ProperAtlas

open CategoryTheory AlgebraicGeometry Limits PrimeSpectrum Spec pullback Over Category RingHom
  CommAlgCat HasRingHomProperty ULift

namespace New.Variety

variable {k : Type} [CommRing k] {R : CommRingCat} [Algebra R k] {W : Over (Spec R)}

/-- Every open subset `V` of `Spec A` has an ideal `I` of `A` such that, for a ring map
`φ : A → B`, the morphism `Spec φ` lands in `V` iff `φ(I)` generates the unit ideal of `B`. -/
lemma exists_ideal_preimage_eq_top_iff {A : Type} [CommRing A] (V : (Spec (.of A)).Opens) :
    ∃ I : Ideal A, ∀ (B : Type) [CommRing B] (φ : A →+* B),
      specMap φ ⁻¹ᵁ V = ⊤ ↔ I.map φ = ⊤ := by
  -- The complement of `V` is the zero locus of an ideal `I`.
  let V' : Set (PrimeSpectrum A) := V.carrier
  obtain ⟨I, hI⟩ : ∃ I : Ideal A, V'ᶜ = zeroLocus I :=
    (isClosed_iff_zeroLocus_ideal _).1 V.isOpen.isClosed_compl
  refine ⟨I, fun B _ φ ↦ ?_⟩
  calc specMap φ ⁻¹ᵁ V = ⊤
    _ ↔ comap φ ⁻¹' V' = Set.univ := TopologicalSpace.Opens.ext_iff
    _ ↔ comap φ ⁻¹' zeroLocus I = ∅ := by rw [← hI, Set.preimage_compl, Set.compl_empty_iff]
    _ ↔ zeroLocus (I.map φ : Set B) = ∅ := by
      rw [preimage_comap_zeroLocus, Ideal.map, zeroLocus_span]
    _ ↔ I.map φ = ⊤ := zeroLocus_empty_iff_eq_top

/-- Let `t` send points of `W` naturally to points of a scheme `Z` (`ht`). If a subfunctor `U` of
the points of `W` consists of the points whose image lands in an open subset `V` of `Z`, then `U`
is an open subfunctor. -/
lemma isOpenSubfunctor_of_landsIn {Z : Scheme}
    (t : ∀ {A : CommAlg k}, PointsIn (R := R) W A → (Spec ⟨A⟩ ⟶ Z))
    (ht : ∀ (A B : CommAlg k) (φ : A ⟶ B) (x : PointsIn W A),
      t (PointsIn.map φ x) = specMap φ.hom ≫ t x)
    {V : Z.Opens} (U : Subfunctor (algPointsOf k R W))
    (hU : ∀ (A : CommAlg k) (x : PointsIn W A), x ∈ U A ↔ LandsIn (t x) V) :
    IsOpenSubfunctor U := by
  intro A x
  obtain ⟨I, hI⟩ := exists_ideal_preimage_eq_top_iff (t x ⁻¹ᵁ V)
  refine ⟨I, fun B φ ↦ ?_⟩
  calc PointsIn.map φ x ∈ U B
    _ ↔ LandsIn (specMap (φ.hom : A →+* B) ≫ t x) V := by rw [hU, ht]
    _ ↔ specMap (φ.hom : A →+* B) ⁻¹ᵁ t x ⁻¹ᵁ V = ⊤ := eq_top_iff.symm
    _ ↔ I.map (φ.hom : A →+* B) = ⊤ := hI B φ.hom
    _ ↔ I.map φ.hom = ⊤ := by rw [Ideal.map_coe]

/-- A point of `W` with values in a `k`-algebra `A` lies over the composite
`Spec A ⟶ Spec k ⟶ Spec R`, so it is also a point of the base change of `W` to `k`. -/
lemma left_comp_hom {A : CommAlg k} (x : PointsIn W A) :
    x.down.left ≫ W.hom = specMap (algebraMap k A) ≫ specMap (algebraMap R k) :=
  x.down.w.trans (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _))

lemma PointsIn.eq_of_left_eq {A : CommAlg k} {x y : PointsIn W A}
    (h_left : x.down.left = y.down.left) : x = y :=
  ULift.down_injective (OverMorphism.ext h_left)

/-- The image of a point `x` under `φ : A → B` has underlying morphism `Spec φ ≫ x`. -/
lemma PointsIn.map_left {A B : CommAlg k} (φ : A ⟶ B) (x : PointsIn W A) :
    (x.map φ).down.left = specMap φ.hom ≫ x.down.left := rfl

/-- A ring map `u : A → B` of `k`-algebras whose spectrum commutes with the structure maps to
`Spec k` induces the same morphism of spectra as some map of `k`-algebras `A → B`. -/
lemma exists_hom_specMap_eq {A B : CommAlg k} (u : CommRingCat.of A ⟶ CommRingCat.of B)
    (hu : Spec.map u ≫ specMap (algebraMap k A) = specMap (algebraMap k B)) :
    ∃ φ : A ⟶ B, specMap (φ.hom : A →+* B) = Spec.map u := by
  exact ⟨ofHom ⟨u.hom, ConcreteCategory.congr_hom (map_inj.1 ((Spec.map_comp ..).trans hu))⟩, rfl⟩

/-- If `W` is proper over `Spec R`, its functor of points on `k`-algebras is separated: the locus
where two points of `W` with values in `A` agree is cut out by an ideal of `A`. -/
instance isSeparatedFunctor_algPointsOf [IsProper W.hom] :
    IsSeparatedFunctor (algPointsOf k R W) := by
  refine ⟨fun A ⟨x⟩ y ↦ ?_⟩
  -- the ideal that cuts out the coincidence of the underlying morphisms of schemes
  obtain ⟨I, hI⟩ := (isProperOver_pointsToBase W.hom).diagonal_closed _ ⟨x.left⟩ ⟨y.down.left⟩
  refine ⟨I, fun B φ ↦ Iff.trans ⟨fun h_eq ↦ ?_, fun h_eq ↦ ?_⟩
    (hI (.of B) (CommRingCat.ofHom (φ.hom : A →+* B)))⟩
  · exact congrArg (fun p : PointsIn W B ↦ up p.down.left) h_eq
  · exact PointsIn.eq_of_left_eq (congrArg down h_eq)

section SmoothAtlas

/-- Let `f : Y ⟶ Spec k` be smooth of relative dimension `d`. Each point `z` of `Y` lies in the
image of an open immersion `Spec A ⟶ Y` over `k`, where the `k`-algebra `A` is étale over the
polynomial ring in `d` variables. -/
lemma exists_etale_coordinates_of_smooth (d : ℕ) {Y : Scheme} (f : Y ⟶ Spec (.of k))
    [hf : SmoothOfRelativeDimension d f] (z : Y) :
    ∃ (A : CommAlg k) (j : Spec (.of A) ⟶ Y) (_ : IsOpenImmersion j) (coord : Fin d → A),
      z ∈ j.opensRange ∧
      j ≫ f = specMap (algebraMap k A) ∧
      (MvPolynomial.aeval (R := k) coord).toRingHom.Etale := by
  -- Affine opens `z ∈ V ⊆ Y` over `U ⊆ Spec k` with `Γ(U) → Γ(V)` standard smooth.
  obtain ⟨U, hU, V, hV, hz, hVU, h_smooth⟩ := hf.exists_isStandardSmoothOfRelativeDimension z
  obtain ⟨ρ, hρ⟩ : ∃ ρ : .of k ⟶ Γ(Spec (.of k), U), Spec.map ρ = hU.fromSpec := map_surjective _
  let σ : .of k ⟶ Γ(Y, V) := ρ ≫ f.appLE U V hVU
  let : Algebra k Γ(Y, V) := σ.hom.toAlgebra
  -- `Γ(U)` is étale over `k`, so `Γ(V)` is standard smooth over `k` and has étale coordinates.
  have hρ_etale : Etale (Spec.map ρ) := by rw [hρ]; infer_instance
  have hσ_smooth : σ.hom.IsStandardSmoothOfRelativeDimension d := by
    simpa [σ] using h_smooth.comp
      (etale_iff_isStandardSmoothOfRelativeDimension_zero.1 (Spec_iff.1 hρ_etale))
  obtain ⟨g, hg⟩ : ∃ g : MvPolynomial (Fin d) k →ₐ[k] Γ(Y, V), g.Etale :=
    hσ_smooth.toAlgebra.exists_etale_mvPolynomial
  have h_struct : hV.fromSpec ≫ f = Spec.map σ := by
    rw [Spec.map_comp, hρ, hU.SpecMap_appLE_fromSpec f hV hVU]
  refine ⟨.of k Γ(Y, V), hV.fromSpec, inferInstance, fun i ↦ g (MvPolynomial.X i),
    by rwa [hV.opensRange_fromSpec], h_struct, ?_⟩
  rwa [MvPolynomial.aeval_unique g] at hg

/-- Suppose the base change `Wₖ` of `W` to `k` is smooth of relative dimension `d`, and `t` sends
each point `x` of `W` with values in a `k`-algebra `A` (`PointsIn`) to the corresponding `A`-point
of `Wₖ`, naturally in `A` and compatibly with the two projections. Then each `z` in `Wₖ` has an open
neighbourhood `V` and an `EtaleChart` of `algPointsOf k R W`. Such a chart is a `k`-algebra `S` with
`d` étale coordinates together with a point `y` of `W` in `S` that embeds `Spec S` as an open
subfunctor. Its `locus` (the points `φ(y)` for `φ : S → A`) consists exactly of the `x` with `t x`
landing in `V` (`LandsIn`). -/
lemma exists_etaleChart_of_smooth (d : ℕ)
    [hW : SmoothOfRelativeDimension d (snd W.hom (specMap (algebraMap R k)))]
    (t : ∀ {A : CommAlg k}, PointsIn (R := R) W A →
      (Spec (.of A) ⟶ Limits.pullback W.hom (specMap (algebraMap R k))))
    (t_fst : ∀ {A : CommAlg k} (x : PointsIn W A),
      t x ≫ fst W.hom (specMap (algebraMap R k)) = x.down.left)
    (t_snd : ∀ {A : CommAlg k} (x : PointsIn W A),
      t x ≫ snd W.hom (specMap (algebraMap R k)) = specMap (algebraMap k A))
    (t_map : ∀ (A B : CommAlg k) (φ : A ⟶ B) (x : PointsIn W A),
      t (x.map φ) = specMap φ.hom ≫ t x)
    (z : (Limits.pullback W.hom (specMap (algebraMap R k)) : Scheme)) :
    ∃ V : (Limits.pullback W.hom (specMap (algebraMap R k))).Opens, z ∈ V ∧
      ∃ a : EtaleChart d (algPointsOf k R W),
        ∀ (A : CommAlg k) (x : PointsIn W A), x ∈ a.locus.obj A ↔ LandsIn (t x) V := by
  let b : Spec (.of k) ⟶ Spec R := specMap (algebraMap R k)
  obtain ⟨B, j, _, coord, hz, hj, h_etale⟩ :
      ∃ (B : CommAlg k) (j : Spec (.of B) ⟶ Limits.pullback W.hom b) (_ : IsOpenImmersion j)
        (coord : Fin d → B), z ∈ j.opensRange ∧ j ≫ snd W.hom b = specMap (algebraMap k B) ∧
          (MvPolynomial.aeval (R := k) coord).toRingHom.Etale :=
    exists_etale_coordinates_of_smooth d (snd W.hom b) z
  -- The point `y` of the chart is the open immersion `j : Spec B ⟶ Wₖ`, read in `W`.
  have h_w : (j ≫ fst W.hom b) ≫ W.hom = specMap (algebraMap k B) ≫ b := by
    rw [assoc, condition, reassoc_of% hj]
  let y : PointsIn (R := R) W B := ⟨homMk (j ≫ fst W.hom b) (h_w.trans (Spec.map_comp ..).symm)⟩
  have hy : t y = j := hom_ext (t_fst y) ((t_snd y).trans hj.symm)
  have t_inj {A : CommAlg k} {x x' : PointsIn W A} (h_eq : t x = t x') : x = x' :=
    PointsIn.eq_of_left_eq (by rw [← t_fst, h_eq, t_fst])
  -- A point is the image of `y` under an algebra map iff it factors through `j`.
  have h_range (A : CommAlg k) (x : PointsIn W A) :
      x ∈ (Subfunctor.range (pointMap y)).obj A ↔ LandsIn (t x) j.opensRange := by
    rw [landsIn_opensRange]
    constructor
    · rintro ⟨⟨φ⟩, hφ : y.map φ = x⟩
      exact ⟨CommRingCat.ofHom (φ.hom : B →+* A), by rw [← hφ, t_map, hy]⟩
    · rintro ⟨u, hu⟩
      obtain ⟨φ, hφ⟩ : ∃ φ : B ⟶ A, specMap (φ.hom : B →+* A) = Spec.map u :=
        exists_hom_specMap_eq u (by rw [← hj, reassoc_of% hu, t_snd])
      exact ⟨⟨φ⟩, t_inj (x := y.map φ) (by rw [t_map, hy, hφ, hu])⟩
  have h_inj (A : CommAlg k) : Function.Injective fun φ : B ⟶ A ↦ y.map φ := by
    intro φ ψ (h_eq : y.map φ = y.map ψ)
    have h_spec : specMap (φ.hom : B →+* A) ≫ j = specMap (ψ.hom : B →+* A) ≫ j := by
      rw [← hy, ← t_map, ← t_map, h_eq]
    simpa [cancel_mono, map_inj, ConcreteCategory.hom_ext_iff] using h_spec
  let chart : EtaleChart d (algPointsOf k R W) :=
    { coordRing := B, point := y, coordinate := coord, etale := h_etale, injective := h_inj
      isOpenSubfunctor := isOpenSubfunctor_of_landsIn t t_map _ h_range }
  exact ⟨j.opensRange, hz, chart, h_range⟩

/-- If `W` is proper over `Spec R` and its base change to `k` is smooth of relative dimension `d`,
the functor of points of `W` on `k`-algebras has an atlas of dimension `d`: it is separated, and
finitely many charts with `d` étale coordinates contain all its field-valued points. -/
lemma hasAtlas_algPointsOf (d : ℕ) [IsProper W.hom]
    [hW : SmoothOfRelativeDimension d (snd W.hom (specMap (algebraMap R k)))] :
    HasAtlas d (algPointsOf k R W) := by
  -- A point `x` of `W` with values in a `k`-algebra is a point `t x` of the base change `Wₖ`. Each
  -- point of `Wₖ` has a standard smooth affine neighbourhood, which is a chart; `Wₖ` is compact.
  let b : Spec (.of k) ⟶ Spec R := specMap (algebraMap R k)
  let t {A : CommAlg k} (x : PointsIn W A) : Spec (.of A) ⟶ Limits.pullback W.hom b :=
    lift x.down.left (specMap (algebraMap k A)) (left_comp_hom x)
  have t_fst {A : CommAlg k} (x : PointsIn W A) : t x ≫ fst W.hom b = x.down.left := lift_fst ..
  have t_snd {A : CommAlg k} (x : PointsIn W A) :
      t x ≫ snd W.hom b = specMap (algebraMap k A) := lift_snd ..
  have t_map (A B : CommAlg k) (φ : A ⟶ B) (x : PointsIn W A) :
      t (x.map φ) = specMap φ.hom ≫ t x := by
    apply pullback.hom_ext
    · rw [assoc, t_fst, t_fst, PointsIn.map_left]
    · -- `φ` commutes with the structure maps from `k`.
      rw [assoc, t_snd, t_snd, ← φ.hom.comp_algebraMap]
      exact Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)
  -- An open neighbourhood `V z` of each `z`, and a chart `a z` for the points that land in it.
  choose V hV a ha using exists_etaleChart_of_smooth d t t_fst t_snd t_map
  obtain ⟨T, hT⟩ := finite_cover_nhds fun z ↦ (V z).isOpen.mem_nhds (hV z)
  refine ⟨T.card, fun i ↦ a (T.equivFin.symm i), fun K hK x ↦ ?_⟩
  -- A point with values in a field lies in an open set as soon as its closed point does.
  let : Field K := hK.toField
  obtain ⟨z, hzT, hz⟩ : ∃ z ∈ T, t x (IsLocalRing.closedPoint K) ∈ V z := by
    simpa using Set.eq_univ_iff_forall.1 hT (t x (IsLocalRing.closedPoint K))
  have h_mem : x ∈ (a z).locus.obj K := by rwa [ha, landsIn_iff_mem]
  exact ⟨T.equivFin ⟨z, hzT⟩, by simpa using h_mem⟩

end SmoothAtlas

/-- Let `ι` be a functor to `k`-algebras whose values are comparable rings
(`New.Variety.IsComparableRing`). If `W` is proper over `Spec R`, its functor of points is
separated, and one point with values in a `k`-algebra `B` gives, along the maps `B → ι c`, all the
points of `W` with values in each `ι c` (`New.Variety.IsAffinelyCovered`). -/
lemma isAffinelyCovered_algPointsOf {C : Type 1} [Category C] {ι : C ⥤ CommAlg k}
    (h_comparable : ∀ c : C, IsComparableRing (id : ι c → ι c)) (W : Over (Spec R))
    [IsProper W.hom] : IsAffinelyCovered ι (algPointsOf k R W) := by
  -- Take the affine scheme `Spec T` of `exists_locallyOfFiniteType_forall_factors` for the base
  -- change of `W` to `k`: every point with values in a comparable ring factors through `t`.
  let b : Spec (.of k) ⟶ Spec R := specMap (algebraMap R k)
  obtain ⟨T, t, -, h_lift⟩ := exists_locallyOfFiniteType_forall_factors (snd W.hom b)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : CommRingCat.of k ⟶ T, Spec.map ρ = t ≫ snd W.hom b := map_surjective _
  let : Algebra k T := ρ.hom.toAlgebra
  -- `t` followed by the first projection is a `T`-point of `W` over `Spec R`.
  have h_w : (t ≫ fst W.hom b) ≫ W.hom = Spec.map (CommRingCat.ofHom (algebraMap R k) ≫ ρ) := by
    rw [Spec.map_comp, hρ, assoc, assoc, condition]
  let y : PointsIn (R := R) W (.of k T) := ⟨homMk (t ≫ fst W.hom b) h_w⟩
  refine ⟨isSeparatedFunctor_algPointsOf, .of k T, y, fun c (x : PointsIn W (ι c)) ↦ ?_⟩
  -- A point `x` gives a point `x'` of the base change, which factors through `t` along some `u`.
  obtain ⟨x', hx'_fst, hx'_snd⟩ : ∃ x' : Spec (.of (ι c)) ⟶ Limits.pullback W.hom b,
      x' ≫ fst W.hom b = x.down.left ∧ x' ≫ snd W.hom b = specMap (algebraMap k (ι c)) :=
    exists_lift _ _ _ _ (left_comp_hom x)
  obtain ⟨u, hu⟩ : ∃ u : T ⟶ .of (ι c), Spec.map u ≫ t = x' := h_lift _ (h_comparable c) x'
  -- Second projection: `u` is a map of `k`-algebras.
  have h_snd : Spec.map u ≫ Spec.map ρ = specMap (algebraMap k (ι c)) := by
    rw [hρ, reassoc_of% hu, hx'_snd]
  obtain ⟨φ, hφ⟩ := exists_hom_specMap_eq (A := .of k T) u h_snd
  -- First projection: it sends `y` to `x`.
  have h_fst : specMap (φ.hom : T →+* ι c) ≫ t ≫ fst W.hom b = x.down.left := by
    rw [hφ, reassoc_of% hu, hx'_fst]
  exact ⟨⟨φ⟩, PointsIn.eq_of_left_eq (x := y.map φ) h_fst⟩

end New.Variety

end ProperAtlas

/-!
## Homomorphisms from relations total on an fpqc cover

`New.Variety.exists_hom_of_rel` uses that representable functors are sheaves for the fpqc topology.
-/

section RelationDescent

open CategoryTheory GrothendieckTopology Sheaf Precoverage CartesianMonoidalCategory AddGrpObj

/-- fpqc descent: let f : W → B be a homomorphism of commutative group objects over S and R a
relation between T-points of W and of A. Suppose R is stable under pull-back and under subtraction,
and x ≫ f = 0 whenever x is related to 0. If every member of an fpqc cover P of A is related to
some point of W, then there is a homomorphism F : A → B with y ≫ F = x ≫ f whenever x is related
to y. -/
lemma New.Variety.exists_hom_of_rel {S : AlgebraicGeometry.Scheme} {A B W : Over S} [AddObj A]
    [AddObj B] [AddObj W] (f : W ⟶ B) [IsAdditive f] (R : ∀ {T : Over S}, (T ⟶ W) → (T ⟶ A) → Prop)
    (h_nat : ∀ {T' T : Over S} {x : T ⟶ W} {y : T ⟶ A} (a : T' ⟶ T),
      R x y → R (T := T') (a ≫ x) (a ≫ y))
    (h_sub : ∀ {T : Over S} {x : T ⟶ W} {y : T ⟶ A} {x' : T ⟶ W} {y' : T ⟶ A},
      R x y → R x' y' → R (x - x') (y - y'))
    (h_ker : ∀ {T : Over S} (x : T ⟶ W), R x 0 → x ≫ f = 0) (P : Presieve A.left)
    (hP : P ∈ AlgebraicGeometry.Scheme.fpqcPrecoverage A.left)
    (h_total : ∀ (Z : AlgebraicGeometry.Scheme) (g : Z ⟶ A.left),
      @P Z g → ∃ x : Over.mk (g ≫ A.hom) ⟶ W, R x ((Over.mk (g ≫ A.hom)).homMk g)) :
    ∃ F : A ⟶ B, IsAdditive F ∧
      ∀ (T : Over S) (x : T ⟶ W) (y : T ⟶ A), R x y → y ≫ F = x ≫ f := by
  -- The points of `A` related to some point of `W` form a sieve `D`. It contains the fpqc cover, so
  -- it covers for the canonical topology, for which `B` is a sheaf: the values of `f` glue to `F`.
  let D : Sieve A :=
    { arrows _ y := ∃ x, R x y, downward_closed := fun ⟨x, hx⟩ a ↦ ⟨a ≫ x, h_nat a hx⟩ }
  have hD_fpqc : Sieve.overEquiv A D ∈ AlgebraicGeometry.Scheme.fpqcTopology A.left :=
    mem_toGrothendieck_iff_of_isStableUnderComposition.2
      ⟨P, hP, fun Z g hg ↦ ⟨_, _, 𝟙 _, h_total Z g hg, rfl⟩⟩
  have hD : D ∈ canonicalTopology (Over S) A := le_canonical _ _ ((mem_over_iff _ D).2 hD_fpqc)
  -- Two points related to the same `y` differ by a point related to `0`.
  have same_value {T : Over S} (x x' : T ⟶ W) (y : T ⟶ A) (hx : R x y) (hx' : R x' y) :
      x ≫ f = x' ≫ f := by
    have h_zero : R (x - x') 0 := by simpa using h_sub hx hx'
    rw [← sub_eq_zero, ← sub_comp, h_ker _ h_zero]
  -- The values `hy.choose ≫ f` form a compatible family on `D`.
  let values : Presieve.FamilyOfElements (yoneda.obj B) D.arrows := fun _ _ hy ↦ hy.choose ≫ f
  have h_compatible : values.Compatible := fun T₁ T₂ U a₁ a₂ y₁ y₂ hy₁ hy₂ h_eq ↦ by
    have h_rel : R (a₂ ≫ hy₂.choose) (a₁ ≫ y₁) := by
      simpa only [h_eq] using h_nat a₂ hy₂.choose_spec
    simpa [values, ← Category.assoc] using same_value _ _ _ (h_nat a₁ hy₁.choose_spec) h_rel
  obtain ⟨F, hF⟩ :
      ∃ F : A ⟶ B, ∀ (T : Over S) (y : T ⟶ A) (hy : ∃ x, R x y), y ≫ F = hy.choose ≫ f :=
    (isSheaf_yoneda_obj B D hD values h_compatible).exists
  have hF_spec (T : Over S) (x : T ⟶ W) (y : T ⟶ A) (hxy : R x y) : y ≫ F = x ≫ f := by
    have hy : ∃ x, R x y := ⟨x, hxy⟩
    exact (hF T y hy).trans (same_value _ x y hy.choose_spec hxy)
  refine ⟨F, isAdditive_of_universal ?_, hF_spec⟩
  -- Additivity on the projections `p`, `q` is local on `A × A`: test it on the points at which
  -- `p + q` is related to some `x` and `q` to some `x'`; there `p` is related to `x - x'`.
  have h_cover : D.pullback (fst A A + snd A A) ⊓ D.pullback (snd A A) ∈
      canonicalTopology (Over S) _ :=
    intersection_covering _ (pullback_stable _ _ hD) (pullback_stable _ _ hD)
  refine ((isSheaf_yoneda_obj B).isSeparated _ h_cover).ext fun T a ⟨⟨x, hx⟩, x', hx'⟩ ↦ ?_
  have h_diff : R (x - x') (a ≫ fst A A) := by simpa [comp_add] using h_sub hx hx'
  calc a ≫ (fst A A + snd A A) ≫ F
    _ = x ≫ f := by rw [← Category.assoc, hF_spec T x _ hx]
    _ = (x - x') ≫ f + x' ≫ f := by simp [sub_comp]
    _ = a ≫ (fst A A ≫ F + snd A A ≫ F) := by
      simp [← hF_spec T _ _ h_diff, ← hF_spec T _ _ hx', comp_add]

end RelationDescent
