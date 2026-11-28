import Lib.Cohomology.Etale.BijectiveComparisons

/-!
# Dense subfunctors, Mayer–Vietoris and partitions along idempotents

This file studies the cohomology Hⁿ(Y) = Extⁿ(ℤ[Y], F) of a set-valued functor Y on a category C
with coefficients in a functor F : C → Ab, where ℤ[Y] = `New.Variety.freeAb` Y. A map is an
equivalence for F (`New.Variety.IsCohomEquiv`) if it induces bijections on all Extⁿ(-, F). A
subfunctor U of Y is dense (`New.Variety.IsCohomDense`) if, over every point h_A → Y with h_A =
Hom(A,−), the inclusion of the preimage of U is an equivalence. The Mayer–Vietoris sequence, the
calculus of dense subfunctors and closed classes of functors are used to cut functors into pieces.
When ι attaches commutative rings to objects and `New.Variety.HasPartitions ι F` holds, partitions
along idempotents are dense. Locally constant coefficients on test rings satisfy
`New.Variety.HasPartitions`.

## Main definitions and results

* `New.Variety.mayer_vietoris_shortExact`: 0 → ℤ[U ∩ V] → ℤ[U] ⊕ ℤ[V] → ℤ[U ∪ V] → 0 is short exact.
* `New.Variety.IsCohomDense.isCohomEquiv`: the inclusion of a dense subfunctor is an equivalence.
* `New.Variety.IsClosedClass.freeAb_iSup`: if a closed class contains ℤ[V] for all V in a set of
  subfunctors closed under intersection, it contains ℤ[-] of their finite unions (Mayer–Vietoris).
* `New.Variety.HasPartitions.isCohomDense_partition`: for an idempotent `e`, the maps that kill `e`
  or `1 - e` are dense.
* `New.Variety.HasPartitions.hasZariskiDescent`: Zariski descent for rings `κ` that receive an
  injective map from `ι`, when any two elements of `κ` are comparable for divisibility after a cut
  along an idempotent of `ι`.
* `New.Variety.IsCohomDense.isCohomEquiv_of_fromPreimage`: a map is an equivalence if it is one over
  a dense subfunctor.

Notions from other files:
* `New.Variety.freeAb`: The functor sending a set-valued functor Y to ℤ[Y], whose value at A is the
  free abelian group on Y(A).
* `New.Variety.IsClosedClass`: a class of functors C → Ab that contains every zero functor and, for
  a short exact sequence whose first term lies in it, contains the middle term exactly when it
  contains the last.
* `New.Variety.HasPartitions`: Each idempotent e ≠ 1 of ι(A) has a `New.Variety.IsQuotientByElem`
  A → B, and ι(A) ≅ ι(B₁) × ι(B₂) via maps A → B₁, B₂ implies F(A) ≅ F(B₁) × F(B₂).

## Relation to the literature

Known; see `Lib.Cohomology.Etale.FilteredLimits` for sources.
-/

/-! ## Mayer–Vietoris sequence and the calculus of dense subfunctors -/

namespace New.Variety

open CategoryTheory Limits Subfunctor IsCohomEquiv Comparison Types biprod ShortComplex IsPushout

variable {C : Type _} [Category C] {F} {Y E : C ⥤ Type 1} {U V : Subfunctor Y} {g : E ⟶ Y}

lemma mono_of_app_injective (h : ∀ A : C, Function.Injective (g A)) : Mono g := by
  simpa [g.mono_iff_mono_app, mono_iff_injective] using h

/-- Mayer–Vietoris: for subfunctors U, V of Y, the sequence 0 → ℤ[U∩V] → ℤ[U] ⊕ ℤ[V] → ℤ[U∪V] →
0, with maps x ↦ (x,−x) and (x,y) ↦ x+y, is short exact. -/
lemma mayer_vietoris_shortExact :
    ∃ w : biprod.lift (freeAb.map ((U ⊓ V).homOfLe inf_le_left))
          (-freeAb.map (homOfLe inf_le_right)) ≫
        biprod.desc (freeAb.map (homOfLe le_sup_left)) (freeAb.map (homOfLe le_sup_right)) = 0,
      ShortExact
        ⟨biprod.lift (freeAb.map ((U ⊓ V).homOfLe inf_le_left))
            (-freeAb.map (homOfLe inf_le_right)),
          biprod.desc (freeAb.map (homOfLe le_sup_left)) (freeAb.map (homOfLe le_sup_right)),
          w⟩ := by
  -- The square of `U ⊓ V`, `U`, `V`, `U ⊔ V` is a pushout at each object, and stays one after
  -- passing to free abelian groups.
  have h_push :
      IsPushout (freeAb.map ((U ⊓ V).homOfLe inf_le_left)) (freeAb.map (homOfLe inf_le_right))
        (freeAb.map (homOfLe le_sup_left)) (freeAb.map (homOfLe le_sup_right)) :=
    of_forall_isPushout_app fun _ ↦ (isPushout_of_bicartSq ⟨rfl, rfl⟩).map AddCommGrpCat.free
  refine ⟨h_push.shortComplex.zero, .mk' h_push.exact_shortComplex ?_ (epi_shortComplex_g h_push)⟩
  -- the first map is a monomorphism, because its first component is
  have h_mono : Mono (freeAb.map ((U ⊓ V).homOfLe inf_le_left)) := by
    -- free abelian groups preserve injections; the instance is found once `freeAb` is unfolded
    delta freeAb
    infer_instance
  exact mono_of_mono_fac (biprod.lift_fst _ _)

/-- A monomorphism g : E → Y with image U is an equivalence for F exactly when the inclusion
U → Y is one. -/
lemma isCohomEquiv_iff_range [hg : Mono g] (h : range g = U) :
    IsCohomEquiv F (freeAb.map g) ↔ IsCohomEquiv F (freeAb.map U.ι) := by
  -- `g` is the isomorphism `toRange g` onto its range followed by the inclusion of the range
  subst h
  rw [show freeAb.map g = freeAb.map (toRange g) ≫ freeAb.map (range g).ι by
    rw [← Functor.map_comp, toRange_ι]]
  exact comp_iff (of_isIso (freeAb.map (toRange g)))

namespace IsCohomDense

/-! ### Dense subfunctors -/

/-- If the subfunctor U of Y is dense for F, then the inclusion U → Y is an equivalence: it
induces bijections H^n(Y,F) → H^n(U,F) for all n. -/
lemma isCohomEquiv (h : IsCohomDense F U) : IsCohomEquiv F (freeAb.map U.ι) := by
  -- It suffices to test on the fibres over the points `y` (`isBijective_of_fibres`); such a fibre
  -- injects into the representable h_A with image the preimage of `U`.
  refine (isBijective_of_fibres (𝟙 _) .of_id_snd fun A y ↦ IsCohomEquiv.bij ?_).eqv
  -- written in the form of the goal that `isBijective_of_fibres` leaves, so that `exact` matches it
  have h_range : range (fibreProd.snd U.ι
        ((Comparison.id F).functor.whiskerLeft (pointMap (NatTrans.app (𝟙 Y) A y)))) =
      U.preimage (pointMap y) := by
    aesop (add simp [toFunctor, fibreProd, fibreProd.snd])
  -- the projection is a monomorphism as a pullback of `U.ι`
  exact (isCohomEquiv_iff_range (hg := isPullback_fibreProd.mono_fst_of_mono) h_range).mpr (h A y)

/-- The preimage of a dense subfunctor `U` of `Y` under `p : E ⟶ Y` is dense in `E`. -/
lemma preimage (h : IsCohomDense F U) (p : E ⟶ Y) : IsCohomDense (Y := E) F (U.preimage p) := by
  -- over a point `y` of `E`, this is the density of `U` over the point `p y` of `Y`
  intro A y
  have h_point := h A (p.app A y)
  rwa [← pointMap_comp] at h_point

/-- A subfunctor U that is all of Y is dense for F. The hypothesis is stated as `⊤ ≤ U`. -/
lemma of_top_le (h : ⊤ ≤ U) : IsCohomDense F U := by
  obtain rfl : U = ⊤ := top_unique h
  exact fun _ _ ↦ of_isIso (freeAb.map (ι ⊤))

/-- Let U, V be subfunctors of Y. If V is dense in Y for F (`h`) and U ∩ V, the preimage of U in V,
is dense in V (`k`), then U is dense in Y. -/
lemma trans (h : IsCohomDense F V) (k : IsCohomDense F (U.preimage V.ι)) : IsCohomDense F U := by
  -- Over a point `y`, compare the preimages `U_y` and `V_y` in h_A through `U_y ⊓ V_y`.
  intro A y
  let U_y : Subfunctor (reprBy A) := U.preimage (pointMap y)
  let V_y : Subfunctor (reprBy A) := V.preimage (pointMap y)
  -- `U_y ⊓ V_y ⊆ V_y` is an equivalence by `k`, and `V_y ⊆ h_A` is one by `h`.
  have h_inf : IsCohomEquiv F (freeAb.map (U_y ⊓ V_y).ι) := by
    have h_comp : IsCohomEquiv F
        (freeAb.map ((U.preimage V.ι).preimage (V.fromPreimage (pointMap y))).ι ≫
          freeAb.map V_y.ι) :=
      (k.preimage (fromPreimage V (pointMap y))).isCohomEquiv.comp_iff.mpr (h A y)
    -- the composite of the two inclusions is injective with image `U_y ⊓ V_y`
    rwa [← freeAb.map_comp, isCohomEquiv_iff_range (U := U_y ⊓ V_y) (by aesop (add simp toFunctor))]
      at h_comp
  -- `U_y ⊓ V_y ⊆ U_y` is an equivalence by `h`, so `U_y ⊆ h_A` is one by cancellation.
  refine (h.preimage (U_y.ι ≫ pointMap y)).isCohomEquiv.comp_iff.mp ?_
  -- again the composite of the two inclusions has image `U_y ⊓ V_y`
  rwa [← freeAb.map_comp, isCohomEquiv_iff_range (U := U_y ⊓ V_y) (by aesop (add simp toFunctor))]

/-- A subfunctor that contains a dense subfunctor is dense. -/
lemma mono (h : IsCohomDense F U) (hU : U ≤ V) : IsCohomDense F V := by
  -- the preimage of `V` in the dense subfunctor `U` is all of `U`
  exact h.trans (of_top_le fun A x _ ↦ hU A x.prop)

/-- A subfunctor W of E that contains the preimage under p : E → Y of a dense subfunctor is
dense. -/
lemma of_preimage_le (h : IsCohomDense F U) (p : E ⟶ Y) {W : Subfunctor E}
    (hW : U.preimage p ≤ W) : IsCohomDense F W :=
  (h.preimage p).mono hW

lemma inf (h : IsCohomDense F U) (hV : IsCohomDense F V) : IsCohomDense F (U ⊓ V) := by
  -- in `U`, the preimage of `U ⊓ V` contains the preimage of `V`, which is dense
  exact h.trans (hV.of_preimage_le U.ι fun A x hx ↦ ⟨x.prop, hx⟩)

end IsCohomDense

end New.Variety

/-!
## Closed classes of functors

Properties of closed classes of functors C → Ab (`New.Variety.IsClosedClass`), used to prove a
property of ℤ[Y] for many set-valued functors Y by cutting them up.
-/

section ClosedClasses

open CategoryTheory ShortComplex Subfunctor Splitting Equiv

namespace New.Variety

variable {C : Type 1}
  {D : Type _} [Category C] [Category D]
  {P : AbFunctor C → Prop} {E Y : C ⥤ Type 1}

/-- Let P be a closed class and `g : E ⟶ Y` a map of set-valued functors that is bijective at every
object. If ℤ[E] lies in P, then so does ℤ[Y]. -/
lemma IsClosedClass.freeAb_of_bijective (hP : IsClosedClass P) (g : E ⟶ Y)
    (h : AllBijective fun A : C ↦ g.app A) (h_E : P (freeAb E)) :
    P (freeAb Y) :=
  (hP.iff_of_isIso (freeAb.map (isoOfAppBijective g h).hom)).mp h_E

/-- Let P satisfy `New.Variety.IsClosedClass` and S be a set of subfunctors of Y closed under
intersection (`hS`), with ℤ[V] in P for all V in S (`hPS`). Then ℤ[⋃ U_i] is in P for every finite
family U_i in S. -/
lemma IsClosedClass.freeAb_iSup (hP : IsClosedClass P) (S : Set (Subfunctor Y))
    (hPS : ∀ V ∈ S, P (freeAb V.toFunctor)) (hS : ∀ V ∈ S, ∀ W ∈ S, V ⊓ W ∈ S) {ι : Type}
    [Finite ι] {U : ι → Subfunctor Y} (hU : ∀ i : ι, U i ∈ S) :
    P (freeAb (iSup U).toFunctor) := by
  obtain ⟨h_zero, h_ses⟩ : (∀ N : AbFunctor C, 𝟙 N = 0 → P N) ∧
      ∀ S : ShortComplex (AbFunctor C), ShortExact S → P S.X₁ → (P S.X₂ ↔ P S.X₃) := hP
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih => simpa only [iSup_comp e] using ih fun i ↦ hU (e i)
  | h_empty =>
    -- the empty union has no points, so its free abelian functor is zero
    exact h_zero _ (freeAb.hom_ext nofun)
  | h_option ih =>
    -- Write the union as V ∪ W with V the union of the `U (some i)` and W = `U none`.
    -- By induction `P` holds for ℤ[V] and for ℤ[V ∩ W], as V ∩ W is the union of the Uᵢ ∩ W.
    have h_union : P (freeAb.obj (⨆ i, U (some i)).toFunctor) := ih fun i ↦ hU (some i)
    have h_inter : P (freeAb.obj ((⨆ i, U (some i)) ⊓ U none).toFunctor) := by
      simpa only [iSup_min] using ih fun i ↦ hS _ (hU (some i)) _ (hU none)
    -- the split sequence ℤ[V] → ℤ[V] ⊕ ℤ[W] → ℤ[W] gives `P` for the direct sum
    have h_sum : P (freeAb.obj (⨆ i, U (some i)).toFunctor ⊞ freeAb.obj (U none).toFunctor) :=
      (h_ses _ (ofHasBinaryBiproduct _ _).shortExact h_union).mpr (hPS (U none) (hU none))
    -- Mayer–Vietoris: ℤ[V ∩ W] → ℤ[V] ⊕ ℤ[W] → ℤ[V ∪ W] is short exact
    obtain ⟨h_mv_comp, h_mv⟩ := mayer_vietoris_shortExact (U := ⨆ i, U (some i)) (V := U none)
    rw [iSup_option, sup_comm]
    exact (h_ses _ h_mv h_inter).mp h_sum

/-- If P is a closed class of functors C → Ab and Φ is an exact functor from functors D → Ab to
functors C → Ab, then the class of all N with Φ(N) in P is closed. -/
lemma IsClosedClass.comap (h : IsClosedClass P) (Φ : AbFunctor D ⥤ AbFunctor C) [IsExactFunctor Φ] :
    IsClosedClass fun N : D ⥤ Ab ↦ P (Φ N) := by
  -- `Φ` sends zero functors to zero functors and short exact sequences to short exact sequences
  obtain ⟨h_zero, h_ses⟩ : (∀ N : AbFunctor C, 𝟙 N = 0 → P N) ∧
      ∀ S : ShortComplex (AbFunctor C), ShortExact S → P S.X₁ → (P S.X₂ ↔ P S.X₃) := h
  refine ⟨fun N hN ↦ h_zero (Φ N) ?_, fun S hS ↦ h_ses (S.map Φ) (hS.map_of_exact Φ)⟩
  rw [← Φ.map_id, hN, Φ.map_zero]

end New.Variety

end ClosedClasses

namespace New.Variety

/-!
## Relations among pull-backs from the relation locus

For finitely many maps `f i : W ⟶ Y` of set-valued functors and integers `c i`,
`New.Variety.relationLocus c f` is the subfunctor of the points `x` of `W` at which the formal sum
`∑ c i [f i x]` vanishes. If its inclusion into `W` is an equivalence for `F`, the same relation
holds among the pull-backs along the `f i` on cohomology.
-/

section Relations

open CategoryTheory Preadditive Subfunctor

variable {C : Type _} [Category C] {Y W : C ⥤ Type 1} {F} {n : ℕ} {ι : Type _} [Fintype ι]
  (c : ι → ℤ) (f : ι → (W ⟶ Y))

/-- For finitely many f_i: W → Y and integers c_i, the subfunctor of W of the points x ∈ W(A) with ∑
c_i [f_i(x)] = 0 in ℤ[Y(A)], expressed by `New.Variety.Cancels`. -/
def relationLocus : Subfunctor W :=
  Subfunctor.mk (fun A ↦ {x : W.obj A | Cancels c fun i ↦ f i A x}) fun _ _ hx ↦
    hx.mono fun _ ↦ by simp_all

/-- On the relation locus, the sum `∑ c i • ℤ[f i]` vanishes. -/
lemma relationLocus_sum_eq_zero :
    freeAb.map (relationLocus c f).ι ≫ ∑ i : ι, c i • freeAb.map (f i) = 0 :=
  -- On a generator `x` of the locus the sum vanishes by the defining condition of `x`.
  freeAb.hom_ext fun _ x ↦ sum_app_apply.trans x.prop

private lemma H.mapHom_apply {M N : AbFunctor C} (α : M ⟶ N) : H.mapHom F M N n α = H.map F α n :=
  rfl

/-- For finitely many f_i: W → Y and integers c_i, if the inclusion into W of the locus where ∑
c_i [f_i(w)] = 0 is an equivalence for F, then ∑ c_i f_i^* x = 0 for every x in H^n(Y,F). -/
lemma H.sum_map_eq_zero_of_relationLocus {C : Type 1} [Category C] {Y W : C ⥤ Type 1}
    {F : AbFunctor C} {n : ℕ} {ι : Type _} [Fintype ι] (c : ι → ℤ) (f : ι → (W ⟶ Y))
    (h : IsCohomEquiv F (freeAb.map (relationLocus c f).ι)) (x : H (freeAb.obj Y) F n) :
    ∑ i : ι, c i • map F (freeAb.map (f i)) n x = 0 := by
  -- Pull-back along the locus is injective, and pull-back is additive in the morphism.
  apply (h n).injective
  have h_zero : mapHom F (freeAb.obj (relationLocus c f).toFunctor) (freeAb.obj Y) n
      (freeAb.map (relationLocus c f).ι ≫ ∑ i : ι, c i • freeAb.map (f i)) x = 0 := by
    rw [relationLocus_sum_eq_zero, map_zero, AddMonoidHom.zero_apply]
  -- `mapHom` is additive in the morphism, and applied to a morphism it is the pull-back along it
  have h_sum : ∑ i : ι, c i • mapHom F (freeAb.obj (relationLocus c f).toFunctor) (freeAb.obj Y) n
      (freeAb.map (relationLocus c f).ι ≫ freeAb.map (f i)) x = 0 := by
    simpa [comp_sum] using h_zero
  simpa [H.mapHom_apply, ← map_comp] using h_sum

end Relations

/-!
## Partitions along idempotents and Zariski descent

Here `ι` attaches a commutative ring to each object of `C`, and `New.Variety.HasPartitions ι F` says
that objects can be cut along idempotents and that `F` respects products of two rings.
-/

section Partitions

open CategoryTheory Function Comparison Ideal IsCohomDense RingHom Limits H

-- `hF` is not used below; the lemmas that need it take it as an argument. The variable fixes the
-- type elaborated for `elemKillingMaps`.
variable {C : Type 1} [Category C]
  {Y : C ⥤ Type 1} {ι : C ⥤ CommRingCat} {F : AbFunctor C} {A : C} (hF : HasPartitions ι F)
  (e : ι A)

/-- If `β : F ⟶ G` is bijective at every object `A` at which `Y` has a point (the hypothesis
`Y A → …` reads: if the set Y(A) is nonempty), it is bijective on the cohomology of `Y`: `H.push` is
the map Hⁿ(Y,F) → Hⁿ(Y,G) induced by β. -/
lemma H.push_bijective_of_points {G : AbFunctor C} (β : F ⟶ G)
    (hβ_bij : ∀ A : C, Y A → Bijective (β A)) (n : ℕ) :
    Bijective (push (freeAb Y) β n) := by
  rw [← pull_id_eq_push β, ← freeAb.map_id Y]
  -- over a point `y ∈ Y(A)` the pair `(y, 𝟙 A)` is universal
  refine HasUniversalPoints.isBijective (fun A y ↦ ⟨A, y, 𝟙 A, by simp,
    -- a pair `(z, f)` over `y` comes from `(y, 𝟙 A)` by `f`, and by no other map
    fun D z f hz ↦ ⟨f, ⟨hz.symm, Category.id_comp f⟩, fun g ⟨_, h_comp⟩ ↦ by simpa using h_comp⟩,
    -- on coefficients the map is `β A`
    by simpa using hβ_bij A y⟩) n

/-- Let U be a subfunctor of Hom(A,−) and z: A → L a member of U. If every member of U factors
uniquely through z, then z represents U: the map Hom(L,D) → U(D) is bijective for every D. -/
lemma pointMap_bijective_of_existsUnique {L : C} (U : Subfunctor (reprBy A)) (z : U.toFunctor L)
    (h_unique : ∀ (D : C) (y : A ⟶ D), .up y ∈ U D → ∃! a : L ⟶ D, z.val.down ≫ a = y) :
    AllBijective fun D : C ↦ pointMap z D := by
  refine fun D ↦ (bijective_iff_existsUnique _).mpr fun y ↦ ?_
  -- equality in `U.toFunctor D` is equality of the underlying maps
  exact (Equiv.ulift.existsUnique_congr fun _ ↦ Subtype.ext_iff.trans ULift.ext_iff).mpr
    (h_unique D _ y.property)

/-- Let `f : E → B` satisfy `New.Variety.IsComparableRing`: any `a`, `b` in `B` have an idempotent
`e` of `E` with `a ∣ f e * b` and `b ∣ (1 - f e) * a`. Then an element `g` outside a maximal ideal
`m` divides some `f e` outside `m` with `e` idempotent. -/
lemma exists_dvd_idempotent_of_notMem {E B : Type*} [Mul E] [CommRing B] {f : E → B}
    (h_compare : IsComparableRing f) {m : Ideal B} {g : B} (hm : IsMaximal m) (hg : g ∉ m) :
    ∃ e : E, f e ∉ m ∧ IsIdempotentElem e ∧ g ∣ f e := by
  -- Write `b * g + d = 1` with `d ∈ m`, and compare `g` with `d`.
  obtain ⟨b, d, hd, h_one⟩ := hm.exists_inv hg
  obtain ⟨e, he, ⟨a, ha⟩, h_dvd⟩ := h_compare g d
  refine ⟨e, fun hfe ↦ hg ?_, he, a + b * f e, ?_⟩
  · -- `g = (1 - f e) * g + f e * g`; the first term is a multiple of `d ∈ m`, and `f e ∈ m`
    -- would put the second in `m`.
    have h_split : g = (1 - f e) * g + f e * g := by ring
    rw [h_split]
    exact add_mem (mem_of_dvd _ h_dvd hd) (mul_mem_right g _ hfe)
  · -- `f e = f e * (b * g + d)` and `f e * d = g * a`.
    linear_combination ha - f e * h_one

/-- For a functor `ι` from `C` to commutative rings and `e` in `ι A`, the subfunctor of `reprBy A`
(the maps out of `A`) of the maps `f : A ⟶ B` with `ι.map f e = 0`. -/
abbrev elemKillingMaps : Subfunctor (reprBy A) where
  obj _ := {f | ι.map f.down e = 0}
  map := by
    delta reprBy reprFunctor
    simp_all

/-- The preimage of the maps that kill `e` or `1 - e` under the point `k : A ⟶ B` is the subfunctor
of the maps out of `B` that kill `ι k e` or `1 - ι k e`. -/
lemma preimage_pointMap_elemKillingMaps_sup {B : C} (k : A ⟶ B) :
    (elemKillingMaps e ⊔ elemKillingMaps (1 - e)).preimage (pointMap (⟨k⟩ : (reprBy A).obj B)) =
      elemKillingMaps (ι.map k e) ⊔ elemKillingMaps (1 - ι.map k e) := by
  ext D f
  -- the point `k` sends `f` to `k ≫ f`
  have h_point :
      ((pointMap (⟨k⟩ : (reprBy A).obj B)).app D f : (reprBy A).obj D).down = k ≫ f.down := rfl
  simp [h_point]

/-- Let F satisfy `New.Variety.HasPartitions` for the rings ι(A). If ι(B) is the zero ring whenever
Y(B) is non-empty, then H^n(Y,F) = 0 for all n. -/
lemma HasPartitions.eq_zero_of_zero_ring (hF : HasPartitions ι F)
    (h_zero_ring : ∀ B : C, Y B → (0 : ι B) = 1) (n : ℕ) (x : H (freeAb Y) F n) :
    x = 0 := by
  -- If the ring of `B` is zero, the diagonal of `F.obj B` is bijective, so `F.obj B` is trivial.
  have h_triv (B : C) (y : Y.obj B) : Subsingleton (F.obj B) := by
    constructor
    simpa [h_zero_ring B y, bijective_iff_existsUnique, ExistsUnique,
      subsingleton_of_zero_eq_one] using hF.bijective_prod (𝟙 B) (𝟙 B)
  -- Hence the zero map of `F` is bijective where `Y` has points, and so is injective on `H`.
  have h_zero_bij (B : C) (y : Y.obj B) : Bijective ((0 : F ⟶ F) B) :=
    have := h_triv B y
    bijective_of_subsingleton _
  exact (H.push_bijective_of_points 0 h_zero_bij n).injective (by simp [H.push])

/-- Let `e` be an idempotent of the ring `ι A`, let `π : A ⟶ B` kill `e` and `ρ : A ⟶ E` kill
`1 - e`, both onto on rings, with kernels in the ideals `(e)` and `(1 - e)`. Then
`x ↦ (ι π x, ι ρ x)` is bijective: the ring of `A` is the product of the rings of `B` and `E`. -/
lemma bijective_map_prod_map_of_idempotent {B E : C} {π : A ⟶ B} {ρ : A ⟶ E}
    (he : IsIdempotentElem e) (π_kill : ι.map π e = 0) (π_surj : Surjective (ι.map π))
    (π_ker : RingHom.ker (ι.map π).hom ≤ Ideal.span {e}) (ρ_kill : ι.map ρ (1 - e) = 0)
    (ρ_surj : Surjective (ι.map ρ)) (ρ_ker : RingHom.ker (ι.map ρ).hom ≤ Ideal.span {1 - e}) :
    Bijective fun x : ι.obj A ↦ (ι.map π x, ι.map ρ x) := by
  constructor
  · -- an element of both kernels is a multiple of both `e` and `1 - e`, hence `0`
    refine (injective_iff_map_eq_zero ((ι.map π).hom.prod (ι.map ρ).hom)).mpr fun x hx ↦ ?_
    have hx_π : ι.map π x = 0 := congrArg Prod.fst hx
    have hx_ρ : ι.map ρ x = 0 := congrArg Prod.snd hx
    obtain ⟨a, ha⟩ : ∃ a : ι.obj A, a * e = x := mem_span_singleton'.mp (π_ker hx_π)
    obtain ⟨b, hb⟩ : ∃ b : ι.obj A, b * (1 - e) = x := mem_span_singleton'.mp (ρ_ker hx_ρ)
    -- `x = e * x + (1 - e) * x`, and `e * (1 - e) = 0`
    linear_combination (-(a + b)) * he.eq - e * hb - (1 - e) * ha
  · -- `x + e * (y - x)` goes to `x` under `π`, which kills `e`, and to `y` under `ρ`, which kills
    -- `1 - e`
    refine (π_surj.prodMap ρ_surj).forall.mpr fun (x, y) ↦ ⟨x + e * (y - x), ?_⟩
    grind

/-- Let F satisfy `New.Variety.HasPartitions` for the rings ι(A). For an idempotent e of ι(A), the
maps out of A that kill e or kill 1 − e form a dense subfunctor of `reprBy A` for F. -/
lemma HasPartitions.isCohomDense_partition (hF : HasPartitions ι F) (e : ι A)
    (he : IsIdempotentElem e) :
    IsCohomDense F (elemKillingMaps e ⊔ elemKillingMaps (1 - e)) := by
  -- The preimage under a point `k` is the same subfunctor for the idempotent `ι.map k e`.
  suffices h_isCohomEquiv_of_idempotent : ∀ (A : C) (e : ι.obj A), IsIdempotentElem e →
      IsCohomEquiv F (freeAb.map (elemKillingMaps e ⊔ elemKillingMaps (1 - e)).ι) by
    rintro B ⟨k⟩
    rw [preimage_pointMap_elemKillingMaps_sup e k]
    exact h_isCohomEquiv_of_idempotent B _ (he.map (ι.map k).hom)
  intro A e he
  by_cases h_trivial : e = 1 ∨ e = 0
  · -- for `e = 1` or `e = 0` every map kills `e` or `1 - e`
    exact isCohomEquiv (of_top_le (by aesop))
  obtain ⟨he_ne_one, he_ne_zero⟩ := not_or.mp h_trivial
  -- The two pieces are represented by the cuts `π` and `ρ`: they give projective functors, and a
  -- section on a piece is determined by its value at the cut. Here `π` kills `e` (`π_kill`),
  -- every map that kills `e` factors uniquely through `π` (`π_univ`), `ι π` is onto (`π_surj`)
  -- and its kernel lies in `(e)` (`π_ker`); likewise `ρ` for `1 - e`.
  obtain ⟨B, π, π_kill, π_univ, π_surj, π_ker⟩ := hF.exists_quotient _ _ he he_ne_one
  obtain ⟨E, ρ, ρ_kill, ρ_univ, ρ_surj, ρ_ker⟩ :=
    hF.exists_quotient _ _ he.one_sub fun h_eq ↦ he_ne_zero (sub_eq_self.mp h_eq)
  obtain ⟨hπ_proj, hπ_rep⟩ : Projective (freeAb (elemKillingMaps e).toFunctor) ∧
      Bijective fun s : freeAb (elemKillingMaps e).toFunctor ⟶ F ↦
        s B (FreeAbelianGroup.of ⟨⟨π⟩, π_kill⟩) :=
    projective_and_eval_bijective F _
      (pointMap_bijective_of_existsUnique (elemKillingMaps e) ⟨_, π_kill⟩ π_univ)
  obtain ⟨hρ_proj, hρ_rep⟩ : Projective (freeAb (elemKillingMaps (1 - e)).toFunctor) ∧
      Bijective fun s : freeAb (elemKillingMaps (1 - e)).toFunctor ⟶ F ↦
        s E (FreeAbelianGroup.of ⟨⟨ρ⟩, ρ_kill⟩) :=
    projective_and_eval_bijective F _
      (pointMap_bijective_of_existsUnique (elemKillingMaps (1 - e)) ⟨_, ρ_kill⟩ ρ_univ)
  -- The ring of `A` is the product of the rings of `B` and `E`.
  have h_ring : Bijective fun x : ι.obj A ↦ (ι.map π x, ι.map ρ x) :=
    bijective_map_prod_map_of_idempotent e he π_kill π_surj π_ker ρ_kill ρ_surj ρ_ker
  -- Mayer–Vietoris: `0 → freeAb[U ∩ V] → freeAb[U] ⊕ freeAb[V] → freeAb[U ∪ V] → 0` for the two
  -- pieces `U`, `V`.
  obtain ⟨h_mv_comp, h_mv⟩ :=
    mayer_vietoris_shortExact (U := elemKillingMaps e) (V := elemKillingMaps (1 - e))
  -- Degree zero: test a section on the union by its values at `π` and `ρ`.
  let ev (w : freeAb.obj (elemKillingMaps e ⊔ elemKillingMaps (1 - e)).toFunctor ⟶ F) :
      F.obj B × F.obj E :=
    (w.app B (.of ⟨_, .inl π_kill⟩), w.app E (.of ⟨_, .inr ρ_kill⟩))
  have ev_inj : Injective ev := by
    intro w w' h_eq
    obtain ⟨h_π, h_ρ⟩ := Prod.ext_iff.mp h_eq
    -- the sum of the two pieces maps onto the union, and a section on a piece is read at its cut
    refine h_mv.epi_g.left_cancellation _ _
      (Limits.biprod.hom_ext' _ _ (hπ_rep.injective ?_) (hρ_rep.injective ?_))
    -- `aesop` reads `freeAb.map` of the inclusion on a generator and uses `h_π`, `h_ρ`
    · aesop
    · aesop
  -- `isBijective_reprBy_iff`: it suffices that `F A` be the sections on the union, and that the
  -- union have no cohomology in positive degrees.
  refine IsBijective.eqv
    (isBijective_reprBy_iff.mpr ⟨.of_comp_left (f := ev) ?_ ev_inj, fun n ↦ ?_⟩)
  · -- a section read at `π` and at `ρ` gives the two components of `F.map π` and `F.map ρ`
    have h_ev : ev ∘ (Comparison.id F).homOfValue (elemKillingMaps e ⊔ elemKillingMaps (1 - e)).ι =
        fun x ↦ (F.map π x, F.map ρ x) :=
      funext fun x ↦ Prod.ext (homOfValue_app ..) (homOfValue_app ..)
    rw [h_ev]
    exact hF.bijective_prod π ρ h_ring
  · -- Higher degrees: on the intersection `1 = e + (1 - e)` is killed, so it has no cohomology, and
    -- the union has the cohomology of the projective sum of the two pieces.
    have h_inter_zero : ∀ D : C,
        (elemKillingMaps e ⊓ elemKillingMaps (1 - e)).toFunctor.obj D → (0 : ι D) = 1 := by
      simp +contextual
    exact (isCohomEquiv_quotient_of_acyclic h_mv (hF.eq_zero_of_zero_ring h_inter_zero)
      _).injective.subsingleton

/-- Zariski descent. Let `F` satisfy `New.Variety.HasPartitions` for the rings `ι`: idempotents of
ι(A) cut A into two pieces, and F of A is the product of F over the pieces. Let `η : ι ⟶ κ` be a map
of ring-valued functors such that (a) each `η.app A` is injective (has trivial kernel) and (b) any
`a`, `b` in `κ.obj A` have an idempotent `e` of `ι.obj A` with `a ∣ η e * b` and
`b ∣ (1 - η e) * a`. Then every subfunctor that is Zariski-locally everything for the rings `κ` (for
each point y ∈ Y(A) and maximal ideal m of κ(A), some g ∉ m such that every map A → B inverting g
sends y into U) is dense for `F` (`New.Variety.HasZariskiDescent`): pulled back to any point, its
inclusion is an equivalence for `F`. -/
lemma HasPartitions.hasZariskiDescent (hF : HasPartitions ι F) {κ : C ⥤ CommRingCat} (η : ι ⟶ κ)
    (hη_inj : ∀ (A : C) (x : ι.obj A), η A x = 0 → x = 0)
    (h_compare : ∀ A : C, IsComparableRing (η A)) :
    HasZariskiDescent κ F := by
  intro Y U hU A y
  let U_y : Subfunctor (reprBy A) := U.preimage (pointMap y)
  -- The `a` in the ring `κ.obj A` such that `U_y` together with the maps that kill `a` is dense
  -- form an ideal, since density passes to intersections and larger subfunctors.
  have h_zero_top : ⊤ ≤ elemKillingMaps (0 : κ.obj A) ⊔ U_y := by aesop
  let I : Ideal (κ.obj A) :=
    .ofLinearComb {a | IsCohomDense F (elemKillingMaps a ⊔ U_y)} ⟨0, of_top_le h_zero_top⟩
      fun a₁ ha₁ a₂ ha₂ c₁ c₂ ↦ (ha₁.inf ha₂).mono fun _ _ ↦ by simp +contextual [or_imp]
  -- No maximal ideal `m` contains `I`: take `g ∉ m` whose inversion puts `y` into `U`, and an
  -- idempotent `e` whose image lies outside `m` and is divisible by `g`; that image is in `I`.
  have hI : I = ⊤ := by
    refine ne_top_iff_exists_maximal.not_right.mpr fun ⟨m, hm, hIm⟩ ↦ ?_
    obtain ⟨g, hg, hgU⟩ : ∃ g ∉ m, ∀ (B : C) (f : A ⟶ B), IsUnit (κ.map f g) → Y.map f y ∈ U B :=
      hU A y m hm
    obtain ⟨e, he_notMem, he, hg_dvd⟩ := exists_dvd_idempotent_of_notMem (h_compare A) hm hg
    refine he_notMem (hIm ((hF.isCohomDense_partition e he).mono ?_))
    rintro B f (hf | hf)
    · -- `f` kills `e` in `ι`, so it kills `η e` in `κ`
      exact .inl (by simpa using congrArg (η.app B) hf : κ.map f.down (η A e) = 0)
    · -- If `f` kills `1 - e` then it sends `e` to `1`, so it inverts `g`.
      refine .inr (hgU B f.down (isUnit_of_dvd_unit (map_dvd _ hg_dvd) ?_))
      simp [← η.naturality_apply, ← (sub_mem_ker_iff _).mp hf]
  -- So `elemKillingMaps 1 ⊔ U_y` is dense, and it remains to see that `U_y` is dense in it.
  have h_one : IsCohomDense F (elemKillingMaps 1 ⊔ U_y) := (eq_top_iff_one I).mp hI
  refine isCohomEquiv (h_one.trans ?_)
  rintro B ⟨f, hf | hf⟩
  · -- If `f` kills `1`, all rings under `B` are zero and both cohomology groups vanish.
    have h_zero (D : C) (x : (reprBy B).obj D) : (0 : ι.obj D) = 1 :=
      -- `f ≫ x` kills `1` in `κ`, so `η` kills `1`
      (hη_inj D 1 (by simpa using (elemKillingMaps 1).map x.down hf)).symm
    simp [IsCohomEquiv, hF.eq_zero_of_zero_ring h_zero,
      hF.eq_zero_of_zero_ring fun D x ↦ h_zero D ((Subfunctor.ι _).app D x),
      bijective_iff_existsUnique, ExistsUnique]
  · -- If `f` lies in `U_y`, the preimage of `U_y` in `reprBy B` is everything.
    exact isCohomEquiv (of_top_le fun _ g _ ↦ Subfunctor.map _ g.down hf)

end Partitions

/-! ## Pull-back along composites and equivalences over dense subfunctors -/

section DenseRestriction

open CategoryTheory

variable {C : Type 1} [Category C] {F : AbFunctor C} {Y : C ⥤ Type 1} {n : ℕ} {X K : C ⥤ Type 1}
  {W : Subfunctor Y}

/-- Pull-back along `v` and then along `u` is pull-back along `u ≫ v`. -/
lemma H.map_map (u : X ⟶ Y) (v : Y ⟶ K) (x : H (freeAb.obj K) F n) :
    map F (freeAb.map u) n (map F (freeAb.map v) n x) = map F (freeAb.map (u ≫ v)) n x := by
  simp [map]

/-- Let `W` be dense in `Y`. If `u : X ⟶ Y` restricts to an equivalence from the preimage of `W`
to `W`, then `u` is an equivalence. -/
lemma IsCohomDense.isCohomEquiv_of_fromPreimage {u : X ⟶ Y} (hd : IsCohomDense F W)
    (h : IsCohomEquiv F (freeAb.map (W.fromPreimage u))) :
    IsCohomEquiv F (freeAb.map u) := by
  -- in the square from `W.preimage u` to `Y`, the way through `W` is an equivalence by `h` and
  -- `hd`, and `W.preimage u → X` is one because density passes to preimages
  have h_via_W : IsCohomEquiv F (freeAb.map (W.fromPreimage u) ≫ freeAb.map W.ι) :=
    h.comp_iff.mpr hd.isCohomEquiv
  have h_square : IsCohomEquiv F (freeAb.map (W.preimage u).ι ≫ freeAb.map u) := by
    rwa [← Functor.map_comp, ← W.fromPreimage_ι, Functor.map_comp]
  exact (hd.preimage u).isCohomEquiv.comp_iff.mp h_square

end DenseRestriction

end New.Variety

/-!
## Locally constant coefficients on test rings

`New.Variety.hasPartitions_locConstCoeff`: test rings (`New.Variety.IsTest`) can be cut along
idempotents, and the coefficient `New.Variety.locConstCoeff Λ` of locally constant functions
`Spec A → Λ` turns a product of two rings into a product of groups.
-/

section LocConstPartitions

open PrimeSpectrum ULift CommRingCat Ideal Quotient

namespace New.Variety

/-- In a test ring (a ring satisfying `IsTest`; the proof uses only that such a ring is reduced) the
ideal generated by an idempotent is radical. -/
lemma IsTest.isRadical_span_idempotent {A : Type*} [CommRing A] (h : IsTest A) {e : A}
    (he : IsIdempotentElem e) :
    (span {e}).IsRadical := by
  -- `(e)` is the annihilator of `1 - e`. If `x ^ n * (1 - e) = 0` then `x * (1 - e)` is nilpotent,
  -- hence zero in the reduced ring `A`.
  rw [← he.ker_toSpanSingleton_one_sub_eq_span]
  intro x ⟨n, hn⟩
  refine h.isReduced.eq_zero _ ⟨n + 1, ?_⟩
  have hn_zero : x ^ n * (1 - e) = 0 := by simpa using hn
  calc (LinearMap.toSpanSingleton A A (1 - e)) x ^ (n + 1)
      = x ^ (n + 1) * (1 - e) ^ (n + 1) := by
        rw [LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_pow]
    _ = x * (x ^ n * (1 - e)) * (1 - e) ^ n := by ring
    _ = 0 := by rw [hn_zero, mul_zero, zero_mul]

/-- Here `testIncl` is the inclusion of the full category of test rings (commutative rings
satisfying `IsTest`) into commutative rings. Test rings can be cut along idempotents, and locally
constant functions on the spectrum of a product of two test rings are pairs of such functions. -/
lemma hasPartitions_locConstCoeff {Λ : Ab} : HasPartitions testIncl (locConstCoeff Λ) := by
  refine ⟨fun A e he _ ↦ ?_, fun {A B₁ B₂} π₁ π₂ h_bij ↦ ?_⟩
  · -- cut along `e` by the quotient `A ⧸ (e)`, a test ring because `(e)` is radical; it kills `e`,
    -- is universal (shown below), is onto and has kernel `(e)`
    refine ⟨⟨_, A.property.quotient (A.property.isRadical_span_idempotent he)⟩,
      ⟨ofHom (mk (span {e}))⟩, mk_singleton_self _, fun B f hf ↦ ?_, exists_rep, by simp⟩
    -- `f` kills `e`, hence the ideal `(e)`, so it factors through the quotient
    exact ⟨⟨ofHom (lift _ f.hom.hom (by simp_all [mem_span_singleton']))⟩, by aesop⟩
  · -- the spectrum of `A ≃ B₁ × B₂` is the disjoint union of the two spectra
    let spec_sum : PrimeSpectrum A.obj ≃ₜ PrimeSpectrum B₁.obj ⊕ PrimeSpectrum B₂.obj :=
      (homeomorphOfRingEquiv (.ofBijective (RingHom.prod ..) h_bij)).trans primeSpectrumProdHomeo
    -- a locally constant function on a disjoint union is a pair of such functions
    let restrict (S T : Type) [TopologicalSpace S] [TopologicalSpace T] :
        LocallyConstant (S ⊕ T) Λ ≃ ULift (LocallyConstant S Λ) × ULift (LocallyConstant T Λ) :=
      { toFun x := (up (x.comap (.mk .inl)), up (x.comap (.mk .inr)))
        invFun := fun (⟨x⟩, ⟨y⟩) ↦
          ⟨Sum.elim x y, fun s ↦ isOpen_sum_iff.mpr ⟨x.isLocallyConstant s, y.isLocallyConstant s⟩⟩
        left_inv := by cat_disch }
    -- the composite bijection is the pair of pull-backs along `π₁` and `π₂`: a prime of `B₁` or
    -- `B₂` is sent to its preimage in `A`
    refine Eq.subst ?_
      (Equiv.ulift.trans ((LocallyConstant.congrLeft spec_sum).trans (restrict ..))).bijective
    ext x
    all_goals
      refine congrArg x.down ?_
      ext
      -- `erw`: `primeSpectrumProdHomeo.symm` is `primeSpectrumProd.symm` only after unfolding
      erw [mem_prod]
      simp

end New.Variety

end LocConstPartitions
