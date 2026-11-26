import Lib.Cohomology.Etale.DenseSubfunctors

/-!
# Continuity of cohomology along filtered limits, via test rings and relatively affine maps

The cohomology of a set-valued functor `Y` on rings is Hⁿ(Y) = Extⁿ(ℤ[Y], F). Here ℤ[Y] is the free
abelian group functor, and h_A = Hom(A, −) is the functor represented by `A`. The question is when
Hⁿ turns a cofiltered limit of functors into a filtered colimit of groups. Cohomology is computed on
test rings, with coefficients the locally constant functions to an abelian group Λ. Test rings have
no higher cohomology, and their cohomology commutes with filtered colimits. Relatively affine maps
are maps whose pull-backs to representable functors are representable.

## Main definitions and results

* `New.Variety.ContinuousUpTo`: for a cone `c` over a cofiltered diagram `D` of set-valued functors,
  the maps colim_j Hⁿ(D j) → Hⁿ(c.pt) satisfy the first `r` conditions of
  `New.Variety.BijectiveUpTo`.
* `New.Variety.ContinuousUpTo.of_cech`: the property descends along covers, by
  `New.Variety.cech_descent_step`.
* `New.Variety.continuousUpTo_locConstCoeff`: the cohomology of test rings, with locally constant
  coefficients, commutes with filtered colimits.
* `New.Variety.Envelope.exists_natTrans_isTest_and_factors`: a functorial map θ : A → E(A) to a test
  ring through which, for A in a given family, every map to a test ring factors.
* `New.Variety.IsCohomContinuous`: continuity over X, for coefficients Λ. On a filtered inverse
  system of functors affine over X, the cohomology of the limit is the colimit of the cohomologies.
  `New.Variety.IsCohomContinuous.of_isRelAffine` passes it to functors affine over X.
* `New.Variety.IsCohomContinuous.of_hasCohomDenseImage`: continuity holds over Y if a representable
  functor h_T maps to Y by a map that is affine and has dense image.

Notions from other files:
* `New.Variety.IsTest`: A is a test ring: reduced, absolutely integrally closed, and any a, b admit
  an idempotent e with a ∣ eb and b ∣ (1 − e)a. `New.Variety.TestRing` is their category.
* `New.Variety.IsCover`: p: E → Y is a cover for F: the inclusion of the image of p in Y induces
  bijections on Ext^n(Z[−],F) for all n.
* `New.Variety.locConstCoeff`: For an abelian group Λ, the coefficient functor on test rings sending
  A to the group of locally constant functions Spec A → Λ.
* `New.Variety.BijectiveUpTo`: for maps f_n : A_n → B_n, the first r of the conditions f₀
  injective, f₀ surjective, f₁ injective, f₁ surjective, and so on.

## Relation to the literature

Known result: Descent of torsion étale cohomology along v-covers, with excision, transfer and
limits. Here cohomology is defined as Ext of presheaves on test rings. The local rings of a test
ring are valuation rings of algebraically closed fields. Descent, excision, transfer and limits are
proved from this definition, while equality with étale cohomology is neither proved nor used.
Source: Scholze, Berkovich Motives, arXiv 2412.03382 (2024), Thm 4.1 and Lemmas 4.7, 4.8 (descent
and limits from finitary functors on test rings); Bhatt, Mathew, The arc-topology, Duke Math. J. 170
(2021), Prop 5.2, Thm 5.4; Stacks project, Tag 09YQ; Scholze, Étale cohomology of diamonds,
7.15-7.16.

See also `Lib.Cohomology.ProperBaseChange.Theorem`.
-/

noncomputable section

namespace New.Variety

/-!
## The colimit condition for cohomology along cofiltered systems

* `New.Variety.IsFilteredColimit`: a cocone of abelian groups is a filtered colimit, stated on
  elements; by `New.Variety.isFilteredColimit_iff_bijective` this holds exactly when the map from
  the colimit to the vertex is bijective.
* `New.Variety.ContinuousUpTo` and `New.Variety.ContinuousUpTo.of_cech`: continuity of
  cohomology up to a level, and its descent along covers.
-/

section FilteredColimits

open CategoryTheory Limits Function Functor AddCommGrpCat MorphismProperty colimit Arrow
  LongExactSeq H Comparison

variable {C : Type 1} [Category C] {F : AbFunctor C}
  {J : Type} [SmallCategory.{0} J] [IsFiltered J] {D : Jᵒᵖ ⥤ C ⥤ Type 1} {T : Type*} [Category* T]

/-- A cocone of abelian groups is a filtered colimit elementwise: an element mapping to 0 in the
vertex dies at a later stage, and every element of the vertex comes from some stage. -/
def IsFilteredColimit {X : J ⥤ Ab} (c : Cocone X) : Prop :=
  (∀ (j : J) (x : X.obj j), c.ι j x = 0 → ∃ i : J, ∃ f : j ⟶ i, X.map f x = 0) ∧
  ∀ y : c.pt, ∃ (j : J) (x : X.obj j), c.ι j x = y

-- Built by hand rather than from Mathlib's `extFunctor`, with which the kernel check of
-- `ContinuousUpTo.of_cech` is much heavier.
/-- The contravariant functor sending Φ: T → (functors from C to abelian groups) to the
contravariant functor t ↦ Ext^n(Φ(t),F) from T to abelian groups. For Φ = `freeAb` its value
`(cohomologyFunctor F n).obj ⟨freeAb⟩` is Y ↦ Hⁿ(Y) = Ext^n(ℤ[Y],F). -/
abbrev cohomologyFunctor (F : AbFunctor C) (n : ℕ) : (T ⥤ AbFunctor C)ᵒᵖ ⥤ Tᵒᵖ ⥤ AddCommGrpCat :=
  opHom T (AbFunctor C) ⋙ (whiskeringRight (Tᵒᵖ) ((AbFunctor C)ᵒᵖ) AddCommGrpCat).obj
    { obj N := .of (H N.unop F n)
      map α := ofHom (map F α.unop n)
      map_id := by aesop
      map_comp _ _ := ext (map_comp _ _) }

/-- Continuity of cohomology up to a level. For a cone `c` over a cofiltered system `D j` of
set-valued functors, `ContinuousUpTo F c : ℕ → Prop` is a predicate on the level `r`:
`ContinuousUpTo F c r` says that the canonical maps colim_j Extⁿ(ℤ[D j], F) → Extⁿ(ℤ[c.pt], F)
satisfy the first `r` of the conditions of `New.Variety.BijectiveUpTo` (injective in degree 0,
surjective in degree 0, injective in degree 1, …). -/
def ContinuousUpTo (F : AbFunctor C) (c : Cone D) : ℕ → Prop :=
  BijectiveUpTo fun n : ℕ ↦
    desc _ (((cohomologyFunctor F n).obj ⟨freeAb⟩).mapCocone (coconeRightOpOfCone c))

attribute [local instance] preservesSmallestFilteredColimits_of_preservesFilteredColimits

/-- A cocone `c` of abelian groups over a filtered diagram `X` is a filtered colimit in the sense of
`New.Variety.IsFilteredColimit` if and only if the canonical map from the colimit of `X` to the
vertex of `c` is bijective. -/
lemma isFilteredColimit_iff_bijective {X : J ⥤ Ab.{2}} {c : Cocone X} :
    IsFilteredColimit c ↔ Bijective (desc X c) := by
  -- Every element of a filtered colimit comes from some stage, and an element of a stage dies in
  -- the colimit exactly when it dies at a later stage.
  have h_surj : Surjective fun a : Σ j : J, X j ↦ ι X a.fst a.snd :=
    Concrete.from_union_surjective_of_isColimit _ (isColimit X)
  have h_zero (j : J) (x : X j) : ι X j x = 0 ↔ ∃ (i : J) (f : j ⟶ i), X.map f x = 0 := by
    simpa using (isColimit X).eq_iff' x 0
  simp only [IsFilteredColimit, Bijective, injective_iff_map_eq_zero]
  refine and_congr ?_ ?_
  · -- injectivity, tested on the representatives `ι X j x`
    simp [h_surj.forall, Sigma.forall, h_zero]
  · -- surjectivity: both sides say that every element of `c.pt` comes from some stage
    simp [Surjective, h_surj.exists, Sigma.exists]

/-- Cover lemma for continuity. Let `a` be a cone over a cofiltered system `A` of maps `E j ⟶ Y j`
of set-valued functors, each a cover for the coefficients `F` (`hp`), whose vertex `E ⟶ Y` is a
cover too (`hq`). If `New.Variety.ContinuousUpTo` holds at level `r` for the sources `E j`
(`leftFunc`) and at level `r - 1` for each of their fibre powers over the `Y j` (`cechFunctor m`),
then it holds at level `r` for the targets `Y j` (`rightFunc`). For a cone over a system `X j`,
level `r` means that the maps colim_j Extⁿ(ℤ[X j], F) → Extⁿ(ℤ[vertex], F) meet the first `r`
conditions: injective in degree 0, surjective in degree 0, injective in degree 1, and so on. -/
lemma ContinuousUpTo.of_cech {A : Jᵒᵖ ⥤ Arrow (C ⥤ Type 1)} (a : Cone A)
    (hp : ∀ j : Jᵒᵖ, IsCover F (A j).hom) (hq : IsCover F a.pt.hom) {r : ℕ}
    (h_src : ContinuousUpTo F (leftFunc.mapCone a) r)
    (h_cech : ∀ m : ℕ, ContinuousUpTo F ((cechFunctor m).mapCone a) (r - 1)) :
    ContinuousUpTo F (rightFunc.mapCone a) r := by
  -- A functor N from arrows of sets to groups, read on a map p : E ⟶ Y pointwise, gives a
  -- functor N(p) on C; `(k n).obj ⟨N⟩` is p ↦ Extⁿ(N(p), F). With p_j the maps of the system and
  -- p the vertex, both N ↦ colim_j Extⁿ(N(p_j), F) and N ↦ Extⁿ(N(p), F) are δ-functors, so
  -- `cech_descent_step` applies to the canonical map `η` between them, for the universal arrow
  -- `leftToRight` (which read on p is p itself).
  let k (n : ℕ) : (Arrow (Type 1) ⥤ Ab.{1})ᵒᵖ ⥤ (Arrow (C ⥤ Type 1))ᵒᵖ ⥤ Ab.{2} :=
    (toArrowFunctor ⋙ whiskeringLeft C (Arrow (Type 1)) Ab.{1}).flip.op ⋙ cohomologyFunctor F n
  -- `G X` is the colimit of `X` over the system, and `η` maps it to the value at the vertex
  let G : ((Arrow (C ⥤ Type 1))ᵒᵖ ⥤ Ab.{2}) ⥤ Ab.{2} :=
    (whiskeringLeft J (Arrow (C ⥤ Type 1))ᵒᵖ Ab.{2}).obj A.rightOp ⋙ colim
  let η : G ⟶ (evaluation (Arrow (C ⥤ Type 1))ᵒᵖ Ab.{2}).obj ⟨a.pt⟩ :=
    { app X := desc _ (X.mapCocone (coconeRightOpOfCone a))
      naturality := by simp [G, colimit.hom_ext_iff] }
  -- filtered colimits of groups are exact
  have G_exact {X Y W : (Arrow (C ⥤ Type 1))ᵒᵖ ⥤ Ab.{2}} {f : X ⟶ Y} {g : Y ⟶ W}
      (hfg : ∀ t : (Arrow (C ⥤ Type 1))ᵒᵖ, Exact (f.app t) (g.app t)) :
      Exact (G.map f) (G.map g) := by
    obtain ⟨h_comp, h_exact⟩ := exact_of_app hfg
    exact exact_of_shortComplex_exact (h_exact.map G)
  -- the maps `φ N n` : colim_j Extⁿ(N(p_j), F) → Extⁿ(N(p), F) respect long exact sequences, so
  -- the four lemma gives the hypothesis of `cech_descent_step`
  let φ (N : Arrow (Type 1) ⥤ Ab.{1}) (n : ℕ) :
      G.obj ((k n).obj ⟨N⟩) → ((k n).obj ⟨N⟩).obj ⟨a.pt⟩ :=
    ⇑(η.app ((k n).obj ⟨N⟩))
  have step {S : ShortComplex (Arrow (Type 1) ⥤ Ab.{1})} {r : ℕ} (hS : S.ShortExact) :
      BijectiveUpTo (φ S.X₂) r → BijectiveUpTo (φ S.X₁) (r - 1) → BijectiveUpTo (φ S.X₃) r := by
    -- the long exact sequence of S read on the map t
    let L (t : Arrow (C ⥤ Type 1)) : LongExactSeq :=
      contravariant
        (hS.map_of_exact ((whiskeringLeft C (Arrow (Type 1)) Ab.{1}).obj (toArrowFunctor.obj t))) F
    -- Its connecting maps are natural in t: a map of arrows gives a morphism of long exact
    -- sequences (`pull_hom_contravariant`, for the identity comparison), which commutes with δ.
    -- The source and target of `ofHom` are given explicitly: inferred, they make the kernel check
    -- much heavier.
    let δ (n : ℕ) : (k n).obj ⟨S.X₁⟩ ⟶ (k (n + 1)).obj ⟨S.X₃⟩ :=
      { app t := ofHom (X := (L t.unop).C n) (Y := (L t.unop).A (n + 1)) ((L t.unop).δ n)
        naturality _ _ f := by
          have h_ladder :=
            pull_hom_contravariant (hS.map_of_exact _) (hS.map_of_exact _) (.id F)
              (S.mapNatTrans
                ((whiskeringLeft C (Arrow (Type 1)) Ab.{1}).map (toArrowFunctor.map f.unop)))
          ext x
          -- the square of the ladder at the connecting maps; `id_pull` reads `pull` for the
          -- identity comparison as `H.map`
          have h_square := h_ladder.comm_delta n x
          rw [id_pull, id_pull] at h_square
          exact h_square.symm }
    -- the colimit of the sequences `L (A.obj j)` is again a long exact sequence
    let colimL : LongExactSeq :=
      { A n := G.obj ((k n).obj ⟨S.X₃⟩)
        B n := G.obj ((k n).obj ⟨S.X₂⟩)
        C n := G.obj ((k n).obj ⟨S.X₁⟩)
        f n := (G.map ((k n).map S.g.op)).hom
        g n := (G.map ((k n).map S.f.op)).hom
        δ n := (G.map (δ n)).hom
        -- a filtered colimit of monomorphisms is a monomorphism
        injective_f := (AddCommGrpCat.mono_iff_injective _).mp <| (monomorphisms _).colimMap _
          fun j ↦ ConcreteCategory.mono_of_injective _ (L _).injective_f
        exact_f_g n := G_exact fun t ↦ (L t.unop).exact_f_g n
        exact_g_delta n := G_exact fun t ↦ (L t.unop).exact_g_delta n
        exact_delta_f n := G_exact fun t ↦ (L t.unop).exact_delta_f n }
    -- four lemma: `η` gives a morphism from it to the sequence at the vertex, by naturality
    apply Hom.four_lemma (L := colimL) (L' := L a.pt)
    exact
      { comm_f n x := η.naturality_apply ((k n).map S.g.op) x
        comm_g n x := η.naturality_apply ((k n).map S.f.op) x
        comm_delta n x := η.naturality_apply (δ n) x }
  -- Čech descent: `step`, level `r` for ℤ[E] and level `r - 1` for the fibre powers give level
  -- `r` for ℤ[image], that is, the claim for the images of the covers
  have h_image : BijectiveUpTo (φ ((Subfunctor.range leftToRight).toFunctor ⋙ free)) r :=
    cech_descent_step _ (f := φ) ⟨step⟩ h_src h_cech
  -- the inclusion of the image is bijective on cohomology, at each j (`hp`), hence in the
  -- colimit, and at the vertex (`hq`)
  let incl (n : ℕ) : (k n).obj ⟨rightFunc ⋙ free⟩ ⟶
      (k n).obj ⟨(Subfunctor.range leftToRight).toFunctor ⋙ free⟩ :=
    (k n).map (whiskerRight (Subfunctor.range leftToRight).ι free).op
  have h_colim (n : ℕ) : Bijective (G.map (incl n)) :=
    (ConcreteCategory.isIso_iff_bijective _).mp <| (isomorphisms _).colimMap _
      fun j ↦ (ConcreteCategory.isIso_iff_bijective _).mpr (hp _ n)
  exact (BijectiveUpTo.congr h_colim hq fun n x ↦ (η.naturality_apply (incl n) x).symm).mpr h_image

end FilteredColimits

/-!
## Acyclicity of test rings and filtered colimits of test rings

* `New.Variety.isFilteredColimit_locConstSpec`: locally constant functions on the spectrum commute
  with filtered colimits of rings.
* `New.Variety.IsAcyclicOver.of_bijective`: `q : T ⟶ testIncl ⋙ reprBy B` is acyclic over `B` if `B`
  is a test ring and `q` is bijective on points.
* `New.Variety.IsTest.filtered_colimit`: a filtered colimit of test rings is a test ring.
-/

section AcyclicTests

open CategoryTheory Limits colimit Concrete Function Abelian.Ext LocallyConstant PrimeSpectrum
  Comparison ULift IsFiltered

variable {Λ : Ab} {J : Type _}
  {B B' : CommRingCat} {T T' : TestRing ⥤ Type 1} (q : T ⟶ testIncl ⋙ reprBy B)
  {q' : T' ⟶ testIncl ⋙ reprBy B'} [SmallCategory J] [IsFiltered J] {L : J ⥤ CommRingCat}

/-- Locally constant `Λ`-valued functions on the prime spectrum commute with filtered colimits of
rings: if the cocone `c` of rings over `L` is a colimit on elements (every element of `c.pt` comes
from some stage, `h_surj`; an element killed in `c.pt` is killed at a later stage, `h_zero`), then
a function vanishing on the spectrum of `c.pt` vanishes at a later stage, and every function on it
comes from some stage. -/
lemma isFilteredColimit_locConstSpec {c : Cocone L}
    (h_surj : ∀ y : c.pt, ∃ (j : J) (x : L.obj j), c.ι j x = y)
    (h_zero : ∀ (j : J) (x : L.obj j), c.ι j x = 0 → ∃ (i : J) (f : j ⟶ i), L.map f x = 0) :
    IsFilteredColimit ((locConstSpec Λ).mapCocone c) := by
  refine ⟨fun j x hx ↦ ?_, fun y ↦ ?_⟩
  · -- the zero set of `x` is that of an idempotent `e`, whose image in `c.pt` lies in every prime
    obtain ⟨e, he, h_locus⟩ :
        ∃ e : L.obj j, IsIdempotentElem e ∧ {p | x.toFun p = 0} = zeroLocus {e} :=
      isClopen_iff_zeroLocus.mp ((LocallyConstant.isLocallyConstant x).isClopen_fiber 0)
    have h_nil : IsNilpotent (c.ι.app j e) := by
      refine nilpotent_iff_mem_prime.mpr fun P hP ↦ ?_
      -- `x` vanishes at the image of `P` in the spectrum of `L.obj j`
      have h_val : x.toFun (comap (c.ι.app j).hom ⟨P, hP⟩) = 0 :=
        congrArg (fun g : LocallyConstant (PrimeSpectrum c.pt) Λ ↦ g ⟨P, hP⟩) hx
      exact h_locus.le h_val rfl
    -- so `e` vanishes in `c.pt`, hence at a later stage `i`, and `x` vanishes there
    obtain ⟨i, f, hf⟩ := h_zero j e ((he.map _).eq_zero_of_isNilpotent h_nil)
    exact ⟨i, f, ext fun p ↦ h_locus.ge (by simp [mem_zeroLocus, hf])⟩
  · -- it suffices to lift the function that is `a` on the locus of an idempotent and `0` elsewhere
    obtain ⟨z, hz⟩ : y ∈ (desc (C := Ab) _ ((locConstSpec Λ).mapCocone c)).hom.range := by
      refine locallyConstant_mem_of_indicator (fun a e he ↦ ?_) y
      obtain ⟨j, e, rfl⟩ := h_surj e
      -- a representative of the idempotent becomes idempotent at a later stage
      obtain ⟨i, f, hf⟩ := h_zero j (e * e - e) (by simp [he.eq])
      have h_idem : IsIdempotentElem (L.map f e) := by rwa [map_sub, map_mul, sub_eq_zero] at hf
      -- the indicator of `L.map f e` at stage `i` maps to the indicator of the image of `e`
      let ind : LocallyConstant (PrimeSpectrum (L.obj i)) Λ :=
        indicator (LocallyConstant.const _ a) (isClopen_iff.mpr ⟨L.map f e, h_idem, rfl⟩)
      simpa only [← c.w f] using ⟨_, ι_desc_apply ((locConstSpec Λ).mapCocone c) i ind⟩
    obtain ⟨j, x, rfl⟩ := colimit_exists_rep _ z
    exact ⟨j, x, by simpa using hz⟩

/-- For q: T → h_B on test rings, the map from locally constant functions Spec B → Λ to
Hⁿ(T, Λ): pull-back along q for n = 0, zero for n > 0. -/
noncomputable def locConstClass : ∀ n : ℕ, locConstSpec Λ B →+ H (freeAb T) (locConstCoeff Λ) n
  | 0 => (AddMonoidHom.mk' (mk₀ (X := freeAb T) (Y := locConstCoeff Λ)) mk₀_add).comp
      ((homOfValue ⟨testIncl, 𝟙 (testIncl ⋙ liftCoeff (locConstSpec Λ))⟩ q).comp
        (AddMonoidHom.mk' up (by tauto)))
  | _ => 0

/-- Property of q: T → h_B on tests: pull-back of locally constant functions Spec B → Λ is a
bijection onto H⁰(T, Λ), and Hⁿ(T, Λ) = 0 for n > 0 (there `locConstClass` is zero and onto). -/
def IsAcyclicOver (Λ : Ab) : Prop :=
  Function.Injective (locConstClass (Λ := Λ) q 0) ∧ ∀ n : ℕ, Surjective (locConstClass (Λ := Λ) q n)

variable {q}

/-- Naturality of `New.Variety.locConstClass`. Let `q : T ⟶ h_B`, `q' : T' ⟶ h_B'` and `e : T' ⟶ T`.
If `f` on `Spec B` and `f'` on `Spec B'` have the same pull-back at every point `x` of `T'` (along
`q (e x)` and `q' x`), then `e` pulls the class of `f` back to the class of `f'`. -/
lemma map_locConstClass {e : T' ⟶ T} {f : (locConstSpec Λ).obj B} {f' : (locConstSpec Λ).obj B'}
    (h_eq : ∀ (c : TestRing) (x : T'.obj c),
      (locConstSpec Λ).map (q c (e c x)).down f = (locConstSpec Λ).map (q' c x).down f') :
    ∀ n : ℕ,
      H.map (locConstCoeff Λ) (freeAb.map e) n (locConstClass q n f) = locConstClass q' n f' := by
  rintro (_ | n)
  · -- in degree `0` both sides are classes of morphisms; compare these on generators, by `h_eq`
    refine (mk₀_comp_mk₀ ..).trans (congrArg _ (freeAb.hom_ext fun c x ↦ ?_))
    -- `erw`: both sides are `ULift.up` of the sides of `h_eq c x` only after `homOfValue` and
    -- `freeAb.map` are unfolded on generators, which no rewriting lemma states
    erw [up_inj]
    tauto
  · exact map_zero _

/-- On the spectrum of a domain, the locally constant `Λ`-valued functions are the constants. -/
lemma bijective_const_of_isDomain {Λ : Type*} [IsDomain B] :
    Bijective fun a : Λ ↦ ULift.up.{1} (LocallyConstant.const (PrimeSpectrum B) a) := by
  refine ⟨fun a b hab ↦ ?_, fun ⟨x⟩ ↦ ?_⟩
  · -- evaluate both constants at the generic point `⊥`
    simpa using congrArg (fun y : ULift (LocallyConstant (PrimeSpectrum B) Λ) ↦ y.down ⊥) hab
  · -- the spectrum of a domain is connected, so `x` is constant with value `x ⊥`
    exact ⟨x ⊥, congrArg ULift.up (x.eq_const ⊥).symm⟩

/-- If `T` over the domain `B` and `T'` over the domain `B'` both satisfy
`New.Variety.IsAcyclicOver`, then every map `u : T' ⟶ T` induces bijections on cohomology: both have
`H⁰ = Λ` and no higher groups. No compatibility of `u` with the maps to `h_B` and `h_B'` is
needed. -/
lemma IsAcyclicOver.isCohomEquiv (hB : IsDomain B) (hB' : IsDomain B') (u : T' ⟶ T)
    (hT : IsAcyclicOver q Λ) (hT' : IsAcyclicOver q' Λ) :
    IsCohomEquiv (locConstCoeff Λ) (freeAb.map u) := by
  obtain ⟨h_inj, h_onto⟩ : Function.Injective (locConstClass (Λ := Λ) q 0) ∧
      ∀ n : ℕ, Surjective (locConstClass (Λ := Λ) q n) := hT
  obtain ⟨h_inj', h_onto'⟩ : Function.Injective (locConstClass (Λ := Λ) q' 0) ∧
      ∀ n : ℕ, Surjective (locConstClass (Λ := Λ) q' n) := hT'
  rintro (_ | n)
  · -- the spectra are connected, so the constants give all of `H⁰` on both sides
    have h_const : Bijective fun x : Λ ↦ locConstClass q 0 (.const _ x) :=
      .comp ⟨h_inj, h_onto 0⟩ (down_bijective.comp bijective_const_of_isDomain)
    have h_const' : Bijective fun x : Λ ↦ locConstClass q' 0 (.const _ x) :=
      .comp ⟨h_inj', h_onto' 0⟩ (down_bijective.comp bijective_const_of_isDomain)
    have h_sq (x : Λ) :
        H.map (locConstCoeff Λ) (freeAb.map u) 0 (locConstClass q 0 (.const _ x)) =
          locConstClass q' 0 (.const _ x) := by
      -- constants pull back to constants along any ring map
      have h_pull (c : TestRing) (y : T'.obj c) :
          (locConstSpec Λ).map (q c (u c y)).down (.const _ x) =
            (locConstSpec Λ).map (q' c y).down (.const _ x) := by
        tauto
      exact map_locConstClass h_pull 0
    exact (bijective_iff_of_comm_sq (f := id) h_sq h_const h_const').mp bijective_id
  · -- in positive degree `locConstClass` is zero and onto, so both groups vanish
    have h_triv (x : H (freeAb T) (locConstCoeff Λ) (n + 1)) : x = 0 := by
      obtain ⟨f, rfl⟩ := h_onto (n + 1) x
      simp [locConstClass]
    have h_triv' (y : H (freeAb T') (locConstCoeff Λ) (n + 1)) : y = 0 := by
      obtain ⟨f, rfl⟩ := h_onto' (n + 1) y
      simp [locConstClass]
    exact ⟨fun x₁ x₂ _ ↦ (h_triv x₁).trans (h_triv x₂).symm,
      fun y ↦ ⟨0, (map_zero _).trans (h_triv' y).symm⟩⟩

/-- A filtered colimit of test rings, taken in commutative rings, is a test ring: absolutely
integrally closed, comparable for divisibility after splitting by an idempotent, and reduced. -/
lemma IsTest.filtered_colimit (hL : ∀ j : J, IsTest (L.obj j)) : IsTest ↑(colimit L) := by
  classical
  -- every element `x` of the colimit has a representative `y x` at a stage `j x`
  choose j y hy using colimit_exists_rep L
  -- the elements of a finite set `s` have representatives `z s x` at one common stage
  have h_common (s : Finset ↑(colimit L)) (x : ↑(colimit L)) (hx : x ∈ s) :
      ∃ w : L.obj (sup (s.image j) ∅), ι L (sup (s.image j) ∅) w = x :=
    ⟨_, (w_apply L (toSup (s.image j) ∅ (Finset.mem_image_of_mem j hx)) (y x)).trans (hy x)⟩
  choose! z hz using h_common
  refine ⟨⟨fun P ↦ ?_⟩, fun f g ↦ ?_, ⟨fun x ⟨n, hn⟩ ↦ ?_⟩⟩
  · -- the coefficients of `P` lift to one stage, where the lift has a root
    exact (hL _).exists_root_of_coeffs_subset_range fun x hx ↦ ⟨z P.coeffs x, hz P.coeffs x hx⟩
  · -- compare representatives of `f` and `g` at one stage, and map the idempotent to the colimit
    obtain ⟨e, he_idem, h_f_dvd, h_g_dvd⟩ := (hL _).isComparableRing (z {f, g} f) (z {f, g} g)
    refine ⟨ι L _ e, he_idem.map (ι L _).hom, ?_, ?_⟩
    · simpa [hz {f, g}] using map_dvd (ι L _).hom h_f_dvd
    · simpa [hz {f, g}] using map_dvd (ι L _).hom h_g_dvd
  · -- a representative of `x ^ n` vanishes at a later stage `i`, which is reduced
    have h_pow : ι L (j x) (y x ^ n) = ι L (j x) 0 := by rw [map_pow, hy x, hn, map_zero]
    obtain ⟨i, f, h_fg⟩ := ((isColimit L).eq_iff' (y x ^ n) 0).mp h_pow
    have h_zero : L.map f (y x) = 0 :=
      (hL i).isReduced.eq_zero _ ⟨n, by rw [← map_pow, h_fg, map_zero]⟩
    rw [← hy x, ← w_apply L f (y x), h_zero, map_zero]

/-- If B is a test ring and q : T → h_B is bijective on points in every test ring, then H⁰(T, Λ)
is, via q, the group of locally constant functions Spec B → Λ, and Hⁿ(T, Λ) = 0 for n > 0. -/
lemma IsAcyclicOver.of_bijective (hB : IsTest B) (hq : ∀ {C : TestRing}, Bijective (q C)) :
    IsAcyclicOver q Λ := by
  -- On test rings `h_B` is represented by `B` itself, so the comparison with `H(h_B)` is bijective.
  let cmp := of testIncl (𝟙 (testIncl ⋙ liftCoeff (locConstSpec Λ)))
  have h_repr : cmp.IsBijective (freeAbMap (𝟙 (testIncl ⋙ reprBy B))) :=
    isBijective_of_repr _ (pointMap_id_bijective_of_fullyFaithful testIncl ⟨B, hB⟩) bijective_id
  -- precompose with `q`, which is bijective on points
  have h_cmp : cmp.IsBijective (freeAbMap q) :=
    h_repr.precomp_of_bijective q (Category.comp_id _) fun C ↦ hq (C := C)
  -- For a representable functor this says: sections over `B` give `H⁰`, and higher groups vanish.
  obtain ⟨h_sec, h_van⟩ := isBijective_reprBy_iff.mp h_cmp
  have h_zero : Bijective (locConstClass (Λ := Λ) q 0) :=
    (mk₀_bijective ..).comp (h_sec.comp up_bijective)
  refine ⟨h_zero.injective, fun n ↦ ?_⟩
  cases n with
  | zero => exact h_zero.surjective
  | succ n => exact fun x ↦ ⟨0, (h_van n).elim _ x⟩ -- the target group is trivial

/-- The functor restricting a set-valued functor on commutative rings to the full subcategory of
test rings, by precomposition with the inclusion. -/
abbrev onTests : (CommRingCat ⥤ Type 1) ⥤ TestRing ⥤ Type 1 := restrictAlong (D := Type 1) testIncl

/-- Let `L` be a filtered diagram of test rings A_j, and A its colimit as a ring (a test ring by
`New.Variety.IsTest.filtered_colimit`). Then the Λ-cohomology Hⁿ(h_A) on test rings is the colimit
of the Hⁿ(h_{A_j}), for every n: `New.Variety.ContinuousUpTo` holds at every level `r` for the
cone of the functors h_{A_j} restricted to test rings. -/
lemma continuousUpTo_locConstCoeff (hL : ∀ j : J, IsTest (L j)) :
    ∀ r : ℕ, ContinuousUpTo (locConstCoeff Λ)
      ((reprFunctor ⋙ onTests).mapCone (colimit.cocone L).op) r := by
  -- All `L.obj j` and their colimit are test rings, so `locConstClass` identifies `H⁰` with the
  -- locally constant functions, naturally in the ring, and the higher groups vanish.
  have class_nat {A B : CommRingCat} (φ : A ⟶ B) (x : (locConstSpec Λ).obj A) :
      H.map (locConstCoeff Λ) (freeAb.map (mapOnTests (reprMap φ))) 0 (locConstClass (𝟙 _) 0 x) =
        locConstClass (𝟙 _) 0 ((locConstSpec Λ).map φ x) :=
    map_locConstClass (q := 𝟙 _) (q' := 𝟙 _) (by tauto) 0
  have h_acyclic {A : CommRingCat} (hA : IsTest A) : IsAcyclicOver (𝟙 (testIncl ⋙ reprBy A)) Λ :=
    .of_bijective hA bijective_id
  have h_acyclic_colim := h_acyclic (IsTest.filtered_colimit hL)
  refine allBijective_iff_forall_bijectiveUpTo.mp fun n ↦ isFilteredColimit_iff_bijective.mp ?_
  rcases n with _ | n
  · -- Transport the claim along `locConstClass` to the continuity of locally constant functions.
    have h_locConst : IsFilteredColimit ((locConstSpec Λ).mapCocone (colimit.cocone L)) :=
      isFilteredColimit_locConstSpec (colimit_exists_rep L) fun i x ↦ by
        simpa using ((isColimit L).eq_iff' x 0).mp
    -- `+instances` lets simp rewrite inside instance arguments.
    simpa +instances [IsFilteredColimit, ((h_acyclic (hL _)).right _).forall,
      ((h_acyclic (hL _)).right _).exists, (h_acyclic_colim.right _).forall,
      h_acyclic_colim.left.eq_iff, map_eq_zero_iff _ h_acyclic_colim.left,
      map_eq_zero_iff _ (h_acyclic (hL _)).left, class_nat] using h_locConst
  · -- In positive degree `locConstClass` is zero and onto, so every group vanishes.
    have h_later (j : J) : ∃ i : J, Nonempty (j ⟶ i) := ⟨j, ⟨𝟙 j⟩⟩
    simp +instances [IsFilteredColimit, ((h_acyclic (hL _)).right _).forall,
      ((h_acyclic (hL _)).right _).exists, (h_acyclic_colim.right _).forall, locConstClass.eq_2,
      nonempty, h_later]

end AcyclicTests

end New.Variety

/-!
## A functorial test-ring envelope

There are too many test rings to take the product of all of them, so the maps from a given ring to
test rings are cut down to a small family.

* `New.Variety.Envelope.IsSolution`, `New.Variety.Envelope.IsSolutionClosed`: a list of equations,
  and the injective ring maps whose image holds a solution of each solvable equation with
  coefficients in the image.
* `New.Variety.Envelope.exists_isSolutionClosed`: every map B → V factors through such a subring of
  V, which is a quotient of one polynomial ring over B (its variables
  `New.Variety.Envelope.SolutionName` name solutions).
* `New.Variety.Envelope.IsSolutionClosed.isTest`: such a subring of a test ring is a test ring.
-/

section TestEnvelope

open CategoryTheory CommRingCat MvPolynomial Ideal.Quotient

variable (B : Type _) {W V J : Type} [CommRing B] [CommRing W] [CommRing V] (g : W →+* V)

namespace New.Variety.Envelope

/-- x solves equation number o with coefficients a.
* o = 0: x is idempotent, a₀ ∣ xa₁ and a₁ ∣ (1 − x)a₀.
* o = 1: a₀ⁿ ∣ a_{n+1} − x for all n.
* o = n + 2: Σ_{k<n} a_k x^k = 0. -/
def IsSolution (a : ℕ → V) (x : V) : ℕ → Prop
  | 0 => IsIdempotentElem x ∧ a 0 ∣ x * a 1 ∧ a 1 ∣ (1 - x) * a 0
  | 1 => ∀ n : ℕ, a 0 ^ n ∣ a (n + 1) - x
  | n + 2 => ∑ k ∈ Finset.range n, a k * x ^ k = 0

/-- Formal names for solutions over B: a term is an equation number o with a sequence of
coefficients, each a polynomial over B in finitely many earlier terms. -/
inductive SolutionName
  /-- Builds a solution name from an equation number `o` and, for each `k`, a polynomial `P k` over
  `B` in `n k` variables together with the `n k` solution names `t k` substituted into it. -/
  | op (o : ℕ) (n : ℕ → ℕ) (P : ∀ k : ℕ, MvPolynomial (Fin (n k)) B)
      (t : ∀ k : ℕ, Fin (n k) → SolutionName)

/-- g: W → V is injective, and every equation `New.Variety.Envelope.IsSolution` with coefficients in
g(W) that has a solution in V has one in g(W). -/
def IsSolutionClosed : Prop :=
  (⇑g).Injective ∧
  ∀ (o : ℕ) (a : ℕ → W), (∃ x : V, IsSolution (g ∘ a) x o) → ∃ x : W, IsSolution (g ∘ a) (g x) o

variable {B g}

/-- Every ring map φ : B → V extends to a ring map g from the polynomial ring over B in the names
`New.Variety.Envelope.SolutionName`, such that the induced injection of the quotient by ker g into V
satisfies the closure condition `New.Variety.Envelope.IsSolutionClosed`. -/
lemma exists_isSolutionClosed (φ : B →+* V) :
    ∃ g : MvPolynomial (SolutionName B) B →+* V, g.comp C = φ ∧ IsSolutionClosed g.kerLift := by
  -- Send the variable named `op o n P t` to a chosen solution of equation `o` with coefficients the
  -- polynomials `P k` evaluated at the values of the names `t k`.
  let val : SolutionName B → V :=
    SolutionName.rec fun o _ P _ v ↦ Classical.epsilon fun x ↦ IsSolution
    (fun k ↦ (P k).eval₂ φ (v k)) x o
  refine ⟨eval₂Hom φ val, by simp, RingHom.kerLift_injective _, fun o ↦ ?_⟩
  -- lift the coefficients to polynomials `a k`; each is a polynomial `P k` in finitely many names
  refine mk_surjective.comp_left.forall.2 fun a h_sol ↦ ?_
  choose n t _ P hP using fun k ↦ (a k).exists_fin_rename
  use mk _ (X (.op o n P t))
  simpa [val, hP, eval₂_rename, Function.comp_def] using! Classical.epsilon_spec h_sol

/-- If g : W → V is solution-closed (`New.Variety.Envelope.IsSolutionClosed`), then g x divides
g y in V exactly when x divides y in W. -/
lemma IsSolutionClosed.map_dvd_iff (h : IsSolutionClosed g) {x y : W} : g x ∣ g y ↔ x ∣ y := by
  obtain ⟨hg_inj, hg_closed⟩ := h
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, map_dvd g⟩
  -- equation `4` for the coefficients `-y, x` is the linear equation `-y + x * z = 0` in `z`
  obtain ⟨z, hz⟩ := hg_closed 4 (fun k ↦ [-y].getD k x)
    ⟨c, by simp [IsSolution, Finset.sum_range_succ, hc]⟩
  have h_eq : g (-y + x * z) = g 0 := by simpa [IsSolution, Finset.sum_range_succ] using hz
  exact ⟨z, neg_add_eq_zero.mp (hg_inj h_eq)⟩

/-- If `g : W →+* V` is solution-closed (`IsSolutionClosed`: `g` is injective, and every equation of
the kind `IsSolution` with coefficients in `g(W)` that has a solution in `V` already has one in
`g(W)`), and `V` is a test ring (`IsTest`: reduced, absolutely integrally closed, and any `a, b`
admit an idempotent `e` with `a ∣ e b` and `b ∣ (1 − e) a`), then `W` is a test ring. The reason is
that roots of monic polynomials, the idempotents that compare two elements, and reducedness all pull
back along `g`. -/
lemma IsSolutionClosed.isTest (h : IsSolutionClosed g) (hV : IsTest V) : IsTest W := by
  have h_dvd_iff {a b : W} : g a ∣ g b ↔ a ∣ b := h.map_dvd_iff
  obtain ⟨hg_inj, hg_closed⟩ := h
  have hV_reduced : IsReduced V := hV.isReduced
  refine { toIsAbsIntegrallyClosed := ⟨fun P h_monic h_deg ↦ ?_⟩, isComparableRing := fun x y ↦ ?_,
           isReduced := isReduced_of_injective g hg_inj }
  · -- `P(x) = 0` is equation number `n + 2` for the `n = P.natDegree + 1` coefficients of `P`
    obtain ⟨x, hx⟩ := hV.toIsAbsIntegrallyClosed.exists_eval₂_eq_zero g h_monic h_deg
    have h_sol : ∃ x : V, IsSolution (g ∘ P.coeff) x (P.natDegree + 3) :=
      ⟨x, show ∑ k ∈ Finset.range (P.natDegree + 1), (g ∘ P.coeff) k * x ^ k = 0 by
        simpa [P.eval₂_eq_sum_range] using hx⟩
    obtain ⟨x, hx⟩ := hg_closed (P.natDegree + 3) P.coeff h_sol
    change ∑ k ∈ Finset.range (P.natDegree + 1), (g ∘ P.coeff) k * g x ^ k = 0 at hx
    have h_sum : g (∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * x ^ k) = g 0 := by
      simpa using hx
    exact ⟨x, (P.eval_eq_sum_range x).trans (hg_inj h_sum)⟩
  · -- equation `0` for the coefficients `x, y`; divisibility descends along `g`
    have h_sol : ∃ e : V, IsSolution (g ∘ fun k ↦ [x].getD k y) e 0 :=
      hV.isComparableRing (g x) (g y)
    obtain ⟨e, he_sol⟩ := hg_closed 0 (fun k ↦ [x].getD k y) h_sol
    change IsIdempotentElem (g e) ∧ g x ∣ g e * g y ∧ g y ∣ (1 - g e) * g x at he_sol
    obtain ⟨he_idem, h_dvd_x, h_dvd_y⟩ := he_sol
    refine ⟨e, ?_, ?_, ?_⟩
    · exact hg_inj ((map_mul g e e).trans he_idem.eq)
    · rwa [← h_dvd_iff, map_mul]
    · rwa [← h_dvd_iff, map_mul, map_sub, map_one]

/-- For any family of commutative rings R o there are an endofunctor E of commutative rings and a
natural map θ : A → E(A) such that (a) every E(A) is a test ring, and (b) every ring map φ from
some R o to a test ring factors through θ at R o (the source of φ is written as the identity functor
applied to R o, which is R o). -/
lemma exists_natTrans_isTest_and_factors (R : J → CommRingCat) :
    ∃ E : CommRingCat ⥤ CommRingCat, ∃ θ : 𝟭 CommRingCat ⟶ E,
      -- (a)
      (∀ A : CommRingCat, IsTest (E A)) ∧
      -- (b)
      ∀ (o : J) (A : TestRing) (φ : (𝟭 CommRingCat).obj (R o) ⟶ A.obj),
        ∃ ψ : E (R o) ⟶ A.obj, θ (R o) ≫ ψ = φ := by
  -- `E S` is the product, over all maps from `S` to the test rings of a fixed small family, of
  -- these rings. The family consists of the quotients of `MvPolynomial (SolutionName (R o)) (R o)`
  -- that are test rings; by `exists_isSolutionClosed` every map from `R o` to a test ring factors
  -- through one of them.
  let Fam : Type := {q : Σ o : J, Ideal (MvPolynomial (SolutionName (R o)) (R o)) //
    IsTest (MvPolynomial (SolutionName (R q.fst)) (R q.fst) ⧸ q.snd)}
  let Q (q : Fam) : Type := MvPolynomial (SolutionName (R q.val.fst)) (R q.val.fst) ⧸ q.val.snd
  -- the maps from `S` to the rings of the family, and the projection to the factor of one of them
  let Idx (S : CommRingCat) : Type := Σ q : Fam, S ⟶ of (Q q)
  let proj {S : CommRingCat} (x : Idx S) : ((y : Idx S) → Q y.fst) →+* Q x.fst :=
    Pi.evalRingHom (fun y : Idx S ↦ Q y.fst) x
  let E : CommRingCat ⥤ CommRingCat :=
    { obj S := of ((x : Idx S) → Q x.fst)
      map f := ofHom (.pi fun x ↦ proj ⟨x.fst, f ≫ x.snd⟩) }
  let θ : 𝟭 CommRingCat ⟶ E := { app S := ofHom (.pi fun x : Idx S ↦ x.snd.hom) }
  refine ⟨E, θ, fun S ↦ .pi fun x : Idx S ↦ x.fst.property, fun o A φ ↦ ?_⟩
  obtain ⟨g, hg_comp, hg_closed⟩ := exists_isSolutionClosed φ.hom
  -- the quotient by the kernel of `g` is a test ring of the family; project to it, embed in `A`
  let q : Fam := ⟨⟨o, RingHom.ker g⟩, hg_closed.isTest A.property⟩
  exact ⟨ofHom (g.kerLift.comp (proj ⟨q, ofHom (algebraMap (R o) (Q q))⟩)), hom_ext hg_comp⟩

end New.Variety.Envelope

end TestEnvelope

/-!
## Relatively affine maps, zero loci and unit loci

Relative representability for functors from rings to sets (`New.Variety.PointFunctor`):
`New.Variety.IsRelAffine p` says that the pull-back of `p` along each point `reprBy A ⟶ Y` is
representable. This is the analogue of an affine morphism.

* It is stable under pull-back and composition (`New.Variety.IsRelAffine.baseChange`,
  `New.Variety.IsRelAffine.comp`).
* `New.Variety.unitPoints_le_range_reprMap`: for a localisation `L` of `R` at `M`, the unit locus of
  `M` lies in the image of `reprBy L`.
* `New.Variety.isRelAffine_zeroPoints`: the inclusion of a zero locus is relatively representable.
-/

namespace New.Variety

open CategoryTheory CommRingCat IsLocalization Ideal Quotient

variable {X Y W V : PointFunctor} {p : X ⟶ Y} {u : W ⟶ Y} {q : V ⟶ W} {v : V ⟶ X} {R : CommRingCat}
  (s : X ⟶ reprBy R) (I : Set R)

/-- The property of a map X → Y of set-valued functors on rings that its pull-back along every
point h_A → Y is representable, of the form h_B → h_A. -/
abbrev IsRelAffine : MorphismProperty PointFunctor := reprFunctor.relativelyRepresentable

/-- Relative representability is stable under pull-back: if `p : X ⟶ Y` is relatively
representable and the square of `v : V ⟶ X`, `q : V ⟶ W`, `p` and `u : W ⟶ Y` is a pull-back,
then `q` is relatively representable. -/
lemma IsRelAffine.baseChange (hp : IsRelAffine p) (h_sq : IsPullback v q p u) :
    IsRelAffine (X := V) (Y := W) q :=
  IsRelAffine.of_isPullback h_sq hp

lemma IsRelAffine.comp {v : W ⟶ X} (hv : IsRelAffine (X := W) (Y := X) v) (hp : IsRelAffine p) :
    IsRelAffine (v ≫ p) :=
  IsRelAffine.comp_mem v p hv hp

/-- Let `L` be a localisation of `R` at `M`. Every ring map out of `R` that sends each element of
`M` to a unit factors through `R → L`. In other words, the unit locus of `M` in `reprBy R` lies in
the image of `reprBy L`. -/
lemma unitPoints_le_range_reprMap (L : Type) [CommRing L] [Algebra R L] (M : Submonoid R)
    [IsLocalization (R := R) M L] :
    unitPoints (𝟙 (reprBy (of R))) M ≤ .range (reprMap (ofHom (algebraMap R L))) := by
  intro B f hf
  have h_unit (a : M) : IsUnit (f.down.hom a) := hf a a.prop
  exact ⟨⟨ofHom (IsLocalization.lift h_unit)⟩, congrArg ULift.up (hom_ext (lift_comp h_unit))⟩

/-- Let `U` be a subfunctor of `Y`. Suppose that for each point `y ∈ Y(R)` there are subsets `A`,
`N` of `R` such that `f : R ⟶ B` carries `y` into `U` exactly when it kills `A` and inverts
`N`. Then the inclusion of `U` is relatively representable. -/
lemma isRelAffine_ι_of_forall_map_mem_iff {U : Subfunctor Y}
    (h : ∀ {R : CommRingCat} (y : Y.obj R), ∃ A N : Set R, ∀ (B : CommRingCat) (f : R ⟶ B),
      Y.map f y ∈ U B ↔ (∀ a ∈ A, f a = 0) ∧ ∀ a ∈ N, IsUnit (f a)) :
    IsRelAffine (Subfunctor.ι U) := by
  -- Over a point `y` of `Y R`, the pull-back of `U` is represented by the ring `Q` obtained from
  -- `R` by inverting `N` and then dividing by the ideal generated by `A`.
  rintro ⟨R⟩
  refine (Equiv.forall_congr_left uliftCoyonedaEquiv).mpr fun y ↦ ?_
  obtain ⟨A, N, hAN⟩ := h y
  let L : Type := Localization (Submonoid.closure N)
  let Q : Type := L ⧸ span (algebraMap R L '' A)
  -- the map `R → Q` kills `A` and inverts `N`, so it carries `y` into `U`
  have h_mem : Y.map (ofHom (algebraMap R Q)) y ∈ U.obj (of Q) :=
    (hAN (of Q) (ofHom (algebraMap R Q))).mpr
      ⟨fun a ha ↦ eq_zero_iff_mem.mpr (subset_span ⟨a, ha, rfl⟩),
        fun a ha ↦ isUnit_comp _ _ ⟨a, Submonoid.subset_closure ha⟩⟩
  refine ⟨⟨of Q⟩, (ofHom (algebraMap R Q)).op, pointMap ⟨_, h_mem⟩,
    isPullback_iff.mpr ⟨fun _ _ ↦ (Y.map_comp_apply ..).symm, ?_⟩⟩
  -- a map `f : R ⟶ B` that carries `y` into `U` factors uniquely through `Q`
  rintro B ⟨f⟩ ⟨_, hf_mem⟩ ⟨⟩
  obtain ⟨hfA, hfN⟩ := (hAN B f).mp hf_mem
  -- `f` inverts `N`, so it factors as `l` through `L`; and `l` kills the image of `A`
  have h_units : Submonoid.closure N ≤ (IsUnit.submonoid B).comap (Hom.hom f) :=
    Submonoid.closure_le.mpr hfN
  -- matching on the equation replaces `f` by the composite of `R → L` and `l`
  obtain ⟨⟨l⟩, ⟨⟩⟩ := unitPoints_le_range_reprMap L (Submonoid.closure N) B h_units
  have h_ker : span (algebraMap R L '' A) ≤ RingHom.ker l.hom :=
    span_le.mpr (Set.forall_mem_image.mpr fun a ha ↦ by simpa using hfA a ha)
  refine ⟨⟨ofHom (lift _ l.hom h_ker)⟩, ⟨rfl, SetCoe.ext (Y.map_comp_apply ..).symm⟩, ?_⟩
  -- uniqueness: `R → L` and `L → Q` are both epimorphisms of rings
  rintro ⟨g⟩ ⟨hg, -⟩
  have h_on_L : (Hom.hom g).comp (Ideal.Quotient.mk _) =
      (Ideal.Quotient.lift _ (Hom.hom l) h_ker).comp (Ideal.Quotient.mk _) :=
    IsLocalization.ringHom_ext (Submonoid.closure N)
      (congrArg (fun x ↦ CommRingCat.Hom.hom x.down) hg)
  exact congrArg ULift.up (hom_ext (Ideal.Quotient.ringHom_ext h_on_L))

/-- For `s : X ⟶ h_R` and a subset `I` of `R`, the inclusion of the zero locus
`New.Variety.zeroPoints s I` (the points whose ring map `R → B` kills `I`) is relatively
representable. -/
lemma isRelAffine_zeroPoints : IsRelAffine (zeroPoints s I).ι := by
  refine isRelAffine_ι_of_forall_map_mem_iff fun y ↦ ⟨baseRingMap s y '' I, ∅, fun B f ↦ ?_⟩
  -- a point lies in the zero locus when its ring map kills `I`; nothing needs to be inverted
  simp [zeroPoints]

end New.Variety

/-!
## Continuity of cohomology from an affine atlas

* `New.Variety.IsCohomContinuous.isFilteredColimit_antitoneFamily`,
  `New.Variety.IsCohomContinuous.isFilteredColimit_adjoin`: the two forms used later, for a
  decreasing family of subfunctors and for base change to the finitely generated subalgebras of an
  algebra.
-/

section ContinuityAtlas

open CategoryTheory Limits IsLimit colimit Functor essImage Over Comma Subfunctor Subalgebra Algebra
  CostructuredArrow.CreatesConnected Types FilteredColimit Preorder

namespace New.Variety

variable {X Y W : PointFunctor} (s : X ⟶ Y)

/-- Pull-back on cohomology (`New.Variety.TestCohomology.map`) is contravariantly functorial:
pulling back along `u ≫ s` is pulling back along `s`, then along `u`. Here x lies in Hⁿ(Y,
Λ) = Extⁿ(ℤ[Y restricted along the inclusion `testIncl` of test rings], `locConstCoeff Λ`). -/
lemma TestCohomology.map_comp (u : W ⟶ X) (s : X ⟶ Y) {Λ : Ab} {n : ℕ}
    (x : H (freeAb.obj (testIncl ⋙ Y)) (locConstCoeff Λ) n) :
    map Λ (u ≫ s) n x = map Λ u n (map Λ s n x) := by
  simp [H.map]

/-- Two points of a base change X ×_{h_R} h_A with values in B are equal if they have the same
point of X and the same ring map A → B. -/
lemma baseChangeOf.ext {A R : CommRingCat} {s : X ⟶ reprBy R} {φ : R ⟶ A} {B : CommRingCat}
    {x y : baseChangeOf s φ B} (h_pt : x.val.fst = y.val.fst)
    (h_hom : ∀ a : A, x.val.snd.down.hom a = y.val.snd.down.hom a) :
    x = y := by
  exact Subtype.ext
    (Prod.ext h_pt (ULift.down_injective (CommRingCat.hom_ext (RingHom.ext h_hom))))

set_option backward.isDefEq.respectTransparency false

/-- For s: X → Y, the base change functor from functors over Y to functors over X, sending E → Y
to X ×_Y E → X. -/
def pullbackOver : Over Y ⥤ Over X where
  obj Z := Over.mk (fibreProd.fst s Z.hom)
  map f :=
    homMk
      { app B := ↾fun x ↦ ⟨(x.1.1, f.left.app B x.1.2), congr(($f.w) B _) ▸ x.2⟩
        naturality := by aesop_cat (add simp fibreProd) }

instance : (pullbackOver s).IsRightAdjoint where
  exists_leftAdjoint :=
    ⟨_,
      ⟨(mapPullbackAdj s).ofNatIsoRight
        (NatIso.ofComponents (fun _ ↦ isoMk isPullback_fibreProd.isoPullback)
          fun f ↦ OverMorphism.ext (by cat_disch)).symm⟩⟩

/-! ### Continuity and its first consequences -/

/-- Continuity over X: for every filtered inverse system of functors relatively representable
(affine) over X, the cohomology on test rings with locally constant Λ-valued coefficients of the
limit is the colimit of the cohomologies. -/
def IsCohomContinuous (Λ : Ab) (X : PointFunctor) : Prop :=
  ∀ ⦃J : Type⦄ [SmallCategory J] [IsFiltered J] ⦃D : Jᵒᵖ ⥤ Over X⦄ ⦃c : Cone D⦄,
    IsLimit ((Over.forget X).mapCone c) →
    (∀ j : Jᵒᵖ, IsRelAffine (D j).hom) →
    ∀ r : ℕ, ContinuousUpTo (locConstCoeff Λ) ((Over.forget X ⋙ onTests).mapCone c) r

variable {Λ : Ab} {R : CommRingCat} {S : CommRingCat} (s : X ⟶ reprBy R) {T : CommRingCat}
  {α : Type*} [Preorder α] {V : α → Subfunctor Y} (hV : Antitone V)

/-- If q: X → Y is relatively representable (affine) and Λ-cohomology is continuous over Y, that is,
turns filtered limits of functors affine over Y into colimits (`New.Variety.IsCohomContinuous`),
then it is continuous over X. -/
lemma IsCohomContinuous.of_isRelAffine {q : X ⟶ Y} (h : IsRelAffine q)
    (hY : IsCohomContinuous Λ Y) :
    IsCohomContinuous Λ X := by
  intro J hJ_cat hJ_filtered D c hc hD
  -- the same system, seen over `Y` through `q`, is affine over `Y`
  exact hY (c := (map q).mapCone c) hc fun j ↦ (hD j).comp h

/-- For a decreasing family V of subfunctors of Y, the direct system a ↦ H^n(V_a, Λ) with
restriction maps, computed on test rings with locally constant Λ-valued coefficients. -/
noncomputable abbrev TestCohomology.antitoneFamily (Λ : Ab) (n : ℕ) : α ⥤ AddCommGrpCat :=
  CategoryTheory.Functor.mk (fun a ↦ Opposite.op (V a).toFunctor)
    (fun g ↦ (homOfLe (hV g.le)).op) ⋙ onTests.op ⋙ cohomologyFunctor (locConstCoeff Λ) n ⟨freeAb⟩

/-- Let V be a decreasing family of subfunctors of Y, indexed by a preorder, whose inclusions are
relatively representable, and let cohomology be continuous over Y. If D is a filtered diagram of
indices with a cocone m such that V at the vertex of m contains the intersection of the V(D j),
then Hⁿ(V(m.pt), Λ) is the colimit of the Hⁿ(V(D j), Λ). -/
lemma IsCohomContinuous.isFilteredColimit_antitoneFamily (hV : Antitone V) {J : Type}
    [SmallCategory J] [IsFiltered J] {D : J ⥤ α} (h : IsCohomContinuous Λ Y)
    (h_rep : ∀ j : α, IsRelAffine (V j).ι) {m : Cocone D}
    (h_inter : ∀ {A : CommRingCat} {x : Y.obj A}, (∀ j : J, x ∈ V (D j) A) → x ∈ V m.pt A) {n : ℕ} :
    IsFilteredColimit ((TestCohomology.antitoneFamily hV Λ n).mapCocone m) := by
  -- `V m.pt` is the intersection of the `V (D.obj j)`, so it is the limit of this inverse system
  -- of relatively representable functors over `Y`; apply continuity over `Y`.
  let F : αᵒᵖ ⥤ Subfunctor Y := .mk (fun a ↦ V a.unop) fun g ↦ (hV (leOfHom g.unop)).hom
  let c : Cone (D.op ⋙ F) := F.mapCone m.op
  have h_glb : IsGLB (Set.range (D.op ⋙ F).obj) c.pt := ⟨conePt_mem_lowerBounds _ c,
    fun U hU A x hx ↦ h_inter fun j ↦ hU (Set.mem_range_self (Opposite.op j)) A hx⟩
  -- pass from subfunctors of `Y` to objects over `Y`, then forget the map to `Y`
  let G : Subfunctor Y ⥤ Over Y := (equivalenceMonoOver Y).functor ⋙ MonoOver.forget Y
  have h_lim : IsLimit ((Over.forget Y).mapCone (G.mapCone c)) :=
    isLimitOfPreserves _ (isLimitOfPreserves G (isLimitOfIsGLB _ c h_glb))
  exact isFilteredColimit_iff_bijective.mpr
    (allBijective_iff_forall_bijectiveUpTo.mpr (h h_lim fun j ↦ h_rep (D.obj j.unop)) n)

/-- For s: X → h_R, the contravariant functor sending an R-algebra S to the functor X ×_{h_R}
h_S, forgetting its projection to X. -/
def baseChangeFunctor : (Under R)ᵒᵖ ⥤ PointFunctor :=
  ((opEquivOpUnder R).inverse ⋙ Over.post uliftCoyoneda ⋙ pullbackOver s) ⋙ Over.forget X

/-- For X over h_R and a homomorphism f: S → T of R-algebras, the induced map of base changes
X_T → X_S. -/
abbrev baseChangeTransition {a : R ⟶ S} {b : R ⟶ T} (f : S ⟶ T) (h : a ≫ f = b) :
    baseChangeOf s b ⟶ baseChangeOf s a :=
  (baseChangeFunctor s).map (Under.homMk f h : Under.mk a ⟶ Under.mk b).op

/-- Let s : X → h_R, let Λ-cohomology be continuous over X (`New.Variety.IsCohomContinuous`), let a
: R → S be a ring map and T an S-algebra. Then in each degree the cohomology of the base change X_T
is the colimit of the cohomologies of the X_{T'}, where T' runs over the S-subalgebras of T
generated by finite subsets. -/
lemma IsCohomContinuous.isFilteredColimit_adjoin (h : IsCohomContinuous Λ X) (T : Type) [CommRing T]
    [Algebra S T] (a : R ⟶ S) (n : ℕ) :
    IsFilteredColimit
      (((baseChangeFunctor s ⋙ onTests).rightOp ⋙ cohomologyFunctor (locConstCoeff Λ) n
        ⟨freeAb⟩).mapCocone
        ((Under.map a).mapCocone
          -- the system of the subalgebras generated by finite sets, with the inclusions
          (J := Finset T)
          (F :=
            CategoryTheory.Functor.mk (fun t : Finset T ↦ S.mkUnder (adjoin S (A := T) t)) fun g ↦
              (Subalgebra.inclusion (adjoin_mono g.le)).toUnder)
          -- the cocone of the inclusions in `T`
          ⟨_, NatTrans.mk fun _ ↦ (val _).toUnder⟩)) := by
  -- the base changes of `X` form a system that is affine over `X`, and base change preserves
  -- limits: `h` applies once `T` is the colimit of the subalgebras, which is checked on sets
  refine isFilteredColimit_iff_bijective.mpr (allBijective_iff_forall_bijectiveUpTo.mpr (h
    (isLimitOfPreserves _ (isLimitOfPreserves
      ((opEquivOpUnder R).inverse ⋙ Over.post uliftCoyoneda ⋙ pullbackOver s) (IsColimit.op ?_)))
    fun _ ↦ .baseChange (.map uliftCoyoneda _) isPullback_fibreProd) n)
  refine
    ((reflectsColimit_of_reflectsIsomorphisms _
      (Under.forget R ⋙ forget CommRingCat)).reflects ?_).some
  -- `x` lies in the subalgebra generated by `{x}`, and the maps to `T` are injective
  exact isColimitOf' _ _ (fun x ↦ ⟨{x}, ⟨x, by simp⟩, rfl⟩)
    fun i x y h_eq ↦ ⟨i, 𝟙 _, Subtype.ext h_eq⟩

/-- The `(m + 1)`-fold fibre power, as a functor on maps of sets, is corepresented by the map from
`m + 1` points to one point; in particular it preserves limits. -/
lemma isCorepresentable_cech (m : ℕ) :
    (cech (D := Arrow (Type 1)) Arrow.leftToRight m).IsCorepresentable :=
  -- a map from this arrow to `f` is a tuple of `m + 1` points of the source with the same image
  ⟨Types.isTerminalPUnit.from (ULift (Fin (m + 1))),
    ⟨{ homEquiv {f} :=
         { toFun g := (cech (D := Arrow (Type 1)) Arrow.leftToRight m).map g ⟨.up, fun _ _ ↦ rfl⟩
           invFun e := ⟨↾fun i ↦ e.val i.down, ↾fun _ ↦ f.hom (e.val 0), congr(↾fun _ ↦
             $(e.prop _ 0))⟩
           left_inv g := Arrow.hom_ext _ _ rfl congr(↾fun _ ↦ $(g.w) _) } }⟩⟩

/-- Let `q : h_T → Y` be relatively affine: its pull-back along every point h_A → Y is
representable. Suppose the image of `q` on test rings is cohomologically dense in `Y` for the
coefficient functor of locally constant functions Spec A → Λ (`HasCohomDenseImage`). Then, for every
filtered inverse system of functors affine over `Y`, the Λ-cohomology of the limit is the colimit of
the cohomologies (`New.Variety.IsCohomContinuous`). -/
lemma IsCohomContinuous.of_hasCohomDenseImage {T : CommRingCat} {q : reprBy T ⟶ Y}
    (hq_rep : IsRelAffine (X := reprBy T) (Y := Y) q)
    (hq : HasCohomDenseImage Λ q) :
    IsCohomContinuous Λ Y := by
  -- Induction on the level, for all systems `D` at once. Cover each `D j` by an affine map `p j`
  -- from the functor of a test ring. By `ContinuousUpTo.of_cech`, level `n + 1` for `D` follows
  -- from level `n + 1` for the sources and level `n` for the fibre powers of the covers.
  intro J hJ_cat hJ_filtered D c hc hD n
  have := IsFiltered.isConnected J
  induction n generalizing D with
  | zero => simp [ContinuousUpTo, BijectiveUpTo]
  | succ n ih =>
    -- the pull-back of `D j` along `q` is affine over the ring `T`, so represented by a ring `B j`
    obtain ⟨B, e⟩ : Σ B : J ⥤ CommRingCat,
        .op B ⋙ uliftCoyoneda ≅ D ⋙ pullbackOver q ⋙ forget (reprBy T) :=
      ⟨.unop _, liftFunctorCompIso _ uliftCoyoneda fun j ↦
        ⟨_, ⟨((hD j).isPullback q).isoIsPullback _ _ isPullback_fibreProd⟩⟩⟩
    -- the rings `B j` and `colimit B`, indexed by `some j` and `none`
    let R' : Option J → CommRingCat := (·.elim (colimit B) B.obj)
    -- test envelopes `θ : A → E A`: each `E A` is a test ring (`h_test`), and every map to a test
    -- ring from some `B j` or from `colimit B` factors through `θ` (`h_univ`)
    obtain ⟨E, θ, h_test, h_univ⟩ := Envelope.exists_natTrans_isTest_and_factors R'
    -- the cover `p j` is `h_{E (B j)} → h_{B j} ≅ h_T ×_Y D j → D j`; `ε` is the last projection
    let ε : pullbackOver q ⋙ forget (reprBy T) ⟶ forget Y := { app D := fibreProd.snd q D.hom }
    let p : (B ⋙ E).op ⋙ uliftCoyoneda ⟶ D ⋙ forget Y :=
      whiskerRight (NatTrans.op (B.whiskerLeft θ)) _ ≫ e.hom ≫ D.whiskerLeft ε
    have hp (j : Jᵒᵖ) : IsRelAffine (p.app j) := .comp (.map uliftCoyoneda _)
      (.comp (.of_isIso ..) (hq_rep.baseChange isPullback_fibreProd.flip))
    -- if one of these rings represents the pull-back of `D'`, its envelope has dense image in `D'`:
    -- on tests the image holds the preimage of the image of `q`
    have h_dense {D' : Over Y} (o : Option J)
        (e' : reprBy (R' o) ≅ (pullbackOver q ⋙ forget (reprBy T)).obj D') :
        HasCohomDenseImage Λ (reprMap (θ.app (R' o)) ≫ e'.hom ≫ ε.app D') := by
      refine hq.of_preimage_le (mapOnTests D'.hom) fun A y h_y ↦ ?_
      -- `y` over a point `x` of `h_T` gives the point `(x, y)` of the pull-back, which comes from
      -- a map `R' o → A`, and that map factors through `θ`
      obtain ⟨x, hx⟩ := h_y
      obtain ⟨z, hz⟩ := (e'.app _).toEquiv.surjective.comp (ULift.map_surjective.mpr (h_univ o A))
        ⟨(x, y), hx⟩
      exact ⟨z, congrArg (fun w ↦ w.val.snd) hz⟩
    -- the limit of the maps `p j`; its source is represented by the colimit of the test rings
    -- `E (B j)`, for which `continuousUpTo_locConstCoeff` gives continuity at every level
    let a : Cone (toArrowFunctor.obj (.mk p)) :=
      coneOfPreserves (toArrowFunctor.obj (.mk p)) (reprFunctor.mapCone (cocone (B ⋙ E)).op) hc
    refine .of_cech (onTests.mapArrow.mapCone a)
      (fun j ↦ (h_dense j.unop (e.app j)).isCohomEquiv) ?_
      (continuousUpTo_locConstCoeff (fun j ↦ h_test (B.obj j)) _) fun m ↦ ?_
    · -- the limit map is a cover: `colimit B` represents the pull-back of the vertex `c.pt`, and
      -- the map from its envelope factors through `a.pt.hom`
      let e' : reprBy (colimit B) ≅ ((pullbackOver q ⋙ Over.forget (reprBy T)).mapCone c).pt :=
        (isLimitOfPreserves uliftCoyoneda (isColimit B).op).conePointsIsoOfNatIso
          (isLimitOfPreserves (pullbackOver q ⋙ Over.forget (reprBy T))
            (isLimitOfReflects (Over.forget Y) hc)) e
      have h_fac :
          reprMap (θ.app (colimit B)) ≫ e'.hom ≫ ε.app c.pt = reprMap (post B E) ≫ a.pt.hom := by
        refine hc.hom_ext fun j ↦ ?_
        -- compare the projections to `D j`: both sides come down to `e` and `ε` at `j` after a map
        -- of rings `B j → E (colimit B)`, and the two ring maps agree by naturality of `θ`
        simp only [e', Category.assoc]
        have h_nat : ε.app c.pt ≫ ((Over.forget Y).mapCone c).π.app j =
            ((pullbackOver q ⋙ Over.forget (reprBy T)).mapCone c).π.app j ≫ ε.app (D.obj j) :=
          (ε.naturality (c.π.app j)).symm
        rw [h_nat, IsLimit.conePointsIsoOfNatIso_hom_comp_assoc]
        simp only [Functor.mapCone_π_app, Over.forget_map]
        -- `erw`: `reprMap` and the maps of `a` match these lemmas only after unfolding definitions
        erw [fac, ← map_comp_assoc, ← op_comp, θ.naturality, ← ι_post]
        rfl
      have h_dense_colim :
          HasCohomDenseImage Λ (reprMap (θ.app (colimit B)) ≫ e'.hom ≫ ε.app c.pt) :=
        h_dense none e'
      refine (h_dense_colim.mono ?_).isCohomEquiv
      rw [h_fac, mapOnTests, whiskerLeft_comp]
      apply range_comp_le
    · -- the induction hypothesis applies to the system of the fibre powers of the `p j`, over `Y`
      let toY : toArrowFunctor.obj (.mk p) ⋙ cechFunctor m ⟶ (const _).obj Y :=
        { app j := cech.proj (p.app j) m 0 } ≫ p ≫ { app j := (D.obj j).hom }
      refine ih (D := Over.lift _ toY) (c := raiseCone ((cechFunctor m).mapCone a)) ?_ fun j ↦ ?_
      · -- fibre powers commute with limits, pointwise
        have := isCorepresentable_cech m
        refine evaluationJointlyReflectsLimits _ fun A ↦ ?_
        let v : (CommRingCat ⥤ Type 1) ⥤ Type 1 := (evaluation _ (Type 1)).obj A
        exact isLimitOfPreserves (cech ..) (fstSndJointlyReflectLimit (c := v.mapArrow.mapCone a)
          (isLimitOfPreserves (uliftCoyoneda ⋙ v) (isColimit _).op) (isLimitOfPreserves v hc))
      · -- the projections of the fibre powers are affine, by induction on `m`
        have h_pr (k : ℕ) : IsRelAffine (cech.proj (p.app j) k 0) := by
          induction k with
          | zero => exact .of_isIso ..
          | succ k hk => exact (hk.comp (hp j)).baseChange isPullback_cech.flip
        exact (h_pr m).comp ((hp j).comp (hD j))

end New.Variety

end ContinuityAtlas

end
