import Lib.General.Geometry.ProjectiveSpace

/-!
# Dense families of complex points: reduced closures, separation of maps, and arcs

Identities between functions or morphisms on a reduced scheme can be checked on a dense family of
complex points. `New.IsDenseFamily ξ` says that the points `ξ z : Spec ℂ ⟶ X` have dense image, and
`New.IsSeparatingFamily ξ` says that moreover `X` is reduced. Every family of complex points factors
through its reduced closure, on which it is separating.

## Main definitions and results

* `New.exists_reduced_closure`: any family of complex points of `X` factors through a closed
  subscheme in which it is `New.IsSeparatingFamily`, namely the reduced closure.
* `New.IsSeparatingFamily.pointFn_ext`, `New.IsSeparatingFamily.hom_ext`: regular functions, and
  morphisms over `S` to a scheme separated over `S`, that agree at the points are equal.
* `New.IsSeparatingFamily.exists_map_of_coords`: if a linear system on `X` gives the points `e z`
  the same coordinates as a projective embedding of `G` gives points `p z`, then it comes from a
  morphism `X ⟶ G` that sends `e z` to `p z`.
* `New.exists_valuative_arc_of_isDenseFamily` joins any point of a locally noetherian scheme with
  finitely many dense complex points to one of them by an arc `Spec V → S`, with `V` the ring of a
  valuation of `ℂ` in `ℝ≥0`.

Notions from other files:
* `New.PointFn X`: rules that attach an element of `A` to every ring-valued point `Spec A ⟶ X`.
  It is regular on `U` (`IsRegularOn`) if, at points landing in `U`, it commutes with ring maps.
* `New.LineBundle X ι`: an open cover `U_i` of `X` with transition functions `g_ij`.
* `New.LineBundle.IsHomogeneousCoords`: `v` is a vector of homogeneous coordinates of the point `t`,
  that is, `t` lands in `U_j` exactly when `v_j` is a unit, and then `g_jk(t) = v_k / v_j`.
* `New.LineBundle.IsLinearSystem`: the data of a map to projective space, the model being
  `g_ij = s_j / s_i` on `U_i = {s_i ≠ 0}` for sections `s_i` without common zero.
* `New.LineBundle.IsProjEmbedding`: a linear system on a proper `X ⟶ S` for which points in one
  chart with the same affine coordinates and the same image in `S` are equal.
-/

/-! ## Reduced closures of families of complex points -/

section ReducedClosure

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData IsLocalRing

/-- Let `i : Y ⟶ Z` be a closed immersion and `f : X ⟶ Z` with `X` reduced. If the preimage under
`f` of the image of `i` is dense in `X`, then `f` factors through `i`. -/
lemma New.exists_lift_of_dense_preimage {X Y Z : Scheme} [IsReduced X] (i : Y ⟶ Z)
    [IsClosedImmersion i] (f : X ⟶ Z) (h_dense : Dense (f ⁻¹' Set.range i)) :
    ∃ g : X ⟶ Y, g ≫ i = f := by
  -- The pull-back of the ideal of `i` has closed support containing a dense set, hence full
  -- support, so it is zero as `X` is reduced. Thus `f` kills the ideal of `i`.
  have h_supp : (i.ker.comap f).support = ⊤ := by
    ext x
    simp [i.support_ker, f.continuous.closure_preimage_subset _ (h_dense x)]
  have h_ker : i.ker ≤ f.ker := by simpa using (map_gc f).le_u (support_eq_top_iff.1 h_supp).le
  exact ⟨_, IsClosedImmersion.lift_fac i f h_ker⟩

/-- The images of the complex points `ξ z : Spec ℂ ⟶ X` form a dense subset of `X`. -/
abbrev New.IsDenseFamily {Z : Type} {X : Scheme} (ξ : Z → (Spec (CommRingCat.of ℂ) ⟶ X)) : Prop :=
  DenseRange fun z : Z ↦ ξ z (closedPoint ℂ)

/-- `X` is reduced and the complex points `ξ z` are dense in it, so that regular functions are
determined by their values at these points. -/
def New.IsSeparatingFamily {Z : Type} {X : Scheme} (ξ : Z → (Spec (CommRingCat.of ℂ) ⟶ X)) :
    Prop := AlgebraicGeometry.IsReduced X ∧ IsDenseFamily ξ

/-- Reduced closure: complex points `ξ z : Spec ℂ ⟶ X` factor as `ξ z = i ∘ e z` through a closed
immersion `i : Y ⟶ X`, with `Y` reduced and the points `e z` dense in `Y`
(`IsSeparatingFamily e`). -/
lemma New.exists_reduced_closure {Z : Type} {X : Scheme}
    (ξ : Z → (Spec (CommRingCat.of ℂ) ⟶ X)) :
    ∃ (Y : Scheme) (i : Y ⟶ X) (e : Z → (Spec (CommRingCat.of ℂ) ⟶ Y)),
      IsClosedImmersion i ∧ (∀ z : Z, e z ≫ i = ξ z) ∧ IsSeparatingFamily e := by
  -- Take the reduced closed subscheme on the closure of the points.
  let I : IdealSheafData X := vanishingIdeal (.closure (.range fun z ↦ ξ z (closedPoint ℂ)))
  -- Each point `ξ z` lands in the support, so it factors through the subscheme.
  have h_lift (z : Z) : ∃ g : Spec (CommRingCat.of ℂ) ⟶ I.subscheme, g ≫ I.subschemeι = ξ z :=
    exists_lift_of_dense_preimage I.subschemeι (ξ z)
      (dense_indiscrete ⟨_, ⟨ξ z (closedPoint ℂ), subset_closure ⟨z, rfl⟩⟩, rfl⟩)
  choose e he using h_lift
  -- On each affine chart the ideal is a vanishing ideal, hence radical.
  have (U : I.subschemeCover.cover.I₀) : IsReduced (I.subschemeCover.cover.X U) :=
    (affine_isReduced_iff _).2
      ((Ideal.isRadical_iff_quotient_reduced _).1 (PrimeSpectrum.isRadical_vanishingIdeal _))
  have h_red : IsReduced I.subscheme := IsReduced.of_openCover _ I.subschemeCover.cover
  -- The image of a point of the subscheme lies in the closure of the images of the `e z`.
  have h_dense : IsDenseFamily e := by
    have h_pt (z : Z) (x : Spec (CommRingCat.of ℂ)) : I.subschemeι (e z x) = ξ z x := by
      rw [← he z, Scheme.Hom.comp_apply]
    refine I.subschemeι.isEmbedding.dense_iff.2 fun y ↦ closure_mono ?_ y.property
    exact Set.range_subset_iff.2 fun z ↦ ⟨e z (closedPoint ℂ), ⟨z, rfl⟩, h_pt z _⟩
  exact ⟨I.subscheme, I.subschemeι, e, inferInstance, he, h_red, h_dense⟩

end ReducedClosure

/-! ## Functions and morphisms on reduced schemes determined by dense points -/

namespace New

open CategoryTheory AlgebraicGeometry Limits Set Over LineBundle PointFn

/-- A universally closed morphism `f : Y ⟶ X` is surjective if every point `ξ z` of a dense family
of complex points of `X` lifts to a complex point `y z` of `Y`. -/
lemma IsDenseFamily.surjective {Z : Type} {X Y : Scheme}
    {ξ : Z → (Spec (CommRingCat.of ℂ) ⟶ X)} (hξ : IsDenseFamily ξ) (f : Y ⟶ X) [UniversallyClosed f]
    (y : Z → (Spec (CommRingCat.of ℂ) ⟶ Y)) (h_lift : ∀ z : Z, y z ≫ f = ξ z) :
    Surjective f := by
  -- The range of `f` is closed and contains the dense set of the points `ξ z`.
  have h_mem (z : Z) (x : Spec (CommRingCat.of ℂ)) : ξ z x ∈ range f :=
    ⟨y z x, by rw [← h_lift z, Scheme.Hom.comp_apply]⟩
  exact ⟨fun x ↦ hξ.induction_on x f.isClosedMap.isClosed_range fun z ↦ h_mem z _⟩

namespace IsSeparatingFamily

/-- Let `X` be reduced and the complex points `ξ z` dense. Two functions on ring-valued points that
are regular on an open `U` (compatible with ring maps at points of `U`) and agree at all `ξ z`
landing in `U` agree at every ring-valued point `t` landing in `U`. -/
lemma pointFn_ext {Z : Type} {X : Scheme} {ξ : Z → (Spec (CommRingCat.of ℂ) ⟶ X)}
    (hξ : IsSeparatingFamily ξ) {U : X.Opens} {f g : PointFn X} (hf : IsRegularOn f U)
    (hg : IsRegularOn g U)
    (h_agree : ∀ z : Z, LandsIn (ξ z) U → f (CommRingCat.of ℂ) (ξ z) = g (CommRingCat.of ℂ) (ξ z))
    (A : CommRingCat) (t : Spec A ⟶ X) (ht : LandsIn t U) :
    f A t = g A t := by
  obtain ⟨h_red, h_dense⟩ := hξ
  -- On `U` both `f` and `g` are given by sections of the structure sheaf.
  obtain ⟨s, hs⟩ := hf.exists_ofSection
  obtain ⟨s', hs'⟩ := hg.exists_ofSection
  suffices h_eq : s - s' = 0 by rw [← hs A t ht, ← hs' A t ht, sub_eq_zero.1 h_eq]
  by_contra hs_ne
  -- On a reduced scheme a nonzero section is invertible on a nonempty open set.
  have h_nonempty : (X.basicOpen (s - s') : Set X).Nonempty := by
    simpa [nonempty_iff_ne_empty] using hs_ne
  -- By density some `ξ z` lies in it: there `s - s'` is a unit, but `f` and `g` agree.
  obtain ⟨z, hz⟩ := h_dense.exists_mem_open (X.basicOpen (s - s')).isOpen h_nonempty
  have hz_U : LandsIn (ξ z) U := (landsIn_iff_mem.2 hz).mono (X.basicOpen_le _)
  exact ((landsIn_basicOpen hz_U _).1 (landsIn_iff_mem.2 hz)).ne_zero
    (by simp [hs _ _ hz_U, hs' _ _ hz_U, h_agree z hz_U])

/-- Let `e z` be complex points of the `S`-scheme `X` over the points `η z` of `S`, with `X` reduced
and the `e z` dense. Two morphisms over `S` from `X` to a separated `G` that agree at every `e z`
are equal. -/
lemma hom_ext {Z : Type} {S : Scheme} {η : Z → (Spec (CommRingCat.of ℂ) ⟶ S)} {X G : Over S}
    {e : ∀ z : Z, Over.mk (η z) ⟶ X} (he : IsSeparatingFamily fun z : Z ↦ (e z).left)
    [IsSeparated G.hom] {f g : X ⟶ G} (h_agree : ∀ z : Z, e z ≫ f = e z ≫ g) :
    f = g := by
  obtain ⟨h_red, h_dense⟩ := he
  -- The equalizer `i` of `f` and `g` is a closed subscheme through which every `e z` factors, so it
  -- is surjective onto `X`; a reduced source and a separated target then give `f = g`.
  let i : (equalizer f g).left ⟶ X.left := (equalizer.ι f g).left
  have : Surjective i := h_dense.surjective i (fun z ↦ (equalizer.lift (e z) (h_agree z)).left)
    fun z ↦ by rw [← Over.comp_left, equalizer.lift_ι]
  exact OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom (by simp) i
    (by rw [← Over.comp_left, ← Over.comp_left, equalizer.condition]))

/-- Let `e z`, `p z` be complex points of the `S`-schemes `X`, `G` over the same point `η z`, with
`X` reduced and the `e z` dense. If a linear system `W` on `X` and a projective embedding `M` of
`G`, both with the finite index set `ι`, give `e z` and `p z` the same homogeneous coordinates
`v z`, then some morphism `d : X ⟶ G` over `S` sends each `e z` to `p z` and pulls the charts and
transition functions of `M` back to those of `W`. -/
lemma exists_map_of_coords {Z ι : Type} {S : Scheme} {η : Z → (Spec (CommRingCat.of ℂ) ⟶ S)}
    [Finite ι] {v : Z → ι → ℂ} {X G : Over S} {e : ∀ z : Z, Over.mk (η z) ⟶ X}
    (he : IsSeparatingFamily fun z : Z ↦ (e z).left) {p : ∀ z : Z, Over.mk (η z) ⟶ G}
    {W : LineBundle X.left ι} {M : LineBundle G.left ι}
    (hW : IsLinearSystem W) (hM : IsProjEmbedding M G.hom)
    (he_coords : ∀ z : Z, W.IsHomogeneousCoords (e z).left (v z))
    (hp_coords : ∀ z : Z, M.IsHomogeneousCoords (p z).left (v z)) :
    ∃ d : X ⟶ G, (∀ z : Z, e z ≫ d = p z) ∧ M.pull d.left = W := by
  -- `W` is the pull-back of the hyperplane bundle `H` along a map `f : X ⟶ ℙ × S` over `S`, and
  -- `M` along a closed immersion `j : G ⟶ ℙ × S` over `S`.
  let H : LineBundle (ProjSpace ι ⨯ S) ι := (ProjSpace.hyperplaneBundle ι).pull prod.fst
  obtain ⟨f, hf_over, rfl⟩ : ∃ f : X.left ⟶ ProjSpace ι ⨯ S,
      f ≫ prod.snd = X.hom ∧ H.pull f = W := hW.exists_hom_projSpace X.hom
  obtain ⟨j, hj_closed, hj_over, rfl⟩ : ∃ j : G.left ⟶ ProjSpace ι ⨯ S,
      IsClosedImmersion j ∧ j ≫ prod.snd = G.hom ∧ H.pull j = M := hM.exists_isClosedImmersion
  obtain ⟨h_red, h_dense⟩ := he
  -- Equal homogeneous coordinates give equal points of projective space.
  have h_pt (z : Z) : (p z).left ≫ j = (e z).left ≫ f :=
    isProjEmbedding_projSpace.eq_of_isHomogeneousCoords (by simp [hf_over, hj_over]) (hp_coords z)
      (he_coords z) (LineBundle.exists_landsIn _ _)
  -- So `f` sends a dense set into the image of `j`, and factors through `j`.
  have h_mem (z : Z) (x : (Over.mk (η z)).left) : f ((e z).left x) ∈ range j :=
    ⟨(p z).left x, by rw [← Scheme.Hom.comp_apply, h_pt z, Scheme.Hom.comp_apply]⟩
  have h_dense_pre : Dense (f ⁻¹' range j) :=
    h_dense.mono (range_subset_iff.2 fun z ↦ h_mem z _)
  obtain ⟨d, rfl⟩ := exists_lift_of_dense_preimage j f h_dense_pre
  exact ⟨homMk d (by rw [← hf_over, ← hj_over, Category.assoc]),
    fun z ↦ OverMorphism.ext (by simp [← cancel_mono j, h_pt z]), by simp [pull_comp]⟩

end IsSeparatingFamily

end New

/-! ## Arcs from dense complex points to arbitrary points -/

section ArcExistence

open CategoryTheory AlgebraicGeometry Spec Scheme Set Ideal IsLocalRing MvPolynomial
  IsLocalization.AtPrime CommRingCat ValuativeRel Valuation IsIntegrallyClosed LocalSubring

/-- The extension of a prime ideal of `A` to a polynomial ring over `A` is prime. -/
lemma New.isPrime_map_C_mvPolynomial {A σ : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] :
    (p.map (C : A →+* MvPolynomial σ A)).IsPrime := by
  -- It is the kernel of the map to the polynomial ring over the domain `A ⧸ p`.
  rw [← p.mk_ker, ← ker_map]
  exact RingHom.ker_isPrime _

/-- A prime of a noetherian ring that is minimal over one element extends to a prime of height at
most one in a polynomial ring in finitely many variables. -/
lemma New.height_map_C_le_one {A σ : Type*} [CommRing A] [IsNoetherianRing A] [Finite σ] {x : A}
    {p : Ideal A} (hp : p ∈ (span {x} : Ideal A).minimalPrimes) :
    (p.map (C : A →+* MvPolynomial σ A)).height ≤ 1 := by
  obtain ⟨⟨hp_prime, hxp⟩, hp_min⟩ := hp
  have : Nontrivial A := (Ideal.Quotient.mk p).domain_nontrivial
  -- The extension is minimal over `x`, so Krull's principal ideal theorem applies.
  have h_min : p.map (C : A →+* MvPolynomial σ A) ∈ ((span {x}).map C).minimalPrimes :=
    ⟨⟨isPrime_map_C_mvPolynomial p, map_mono hxp⟩, fun J ⟨hJ_prime, hxJ⟩ hJp ↦
      map_le_of_le_comap (hp_min ⟨hJ_prime.comap C, le_comap_of_map_le hxJ⟩
        ((comap_mono hJp).trans_eq p.comap_map_eq_self_of_faithfullyFlat))⟩
  exact height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ h_min

/-- Let `p` be a prime of a noetherian domain `A` that is minimal over one element. A nonzero prime
`J` of a polynomial ring over `A` that lies in the extension of `p` equals that extension. -/
lemma New.eq_map_C_of_ne_bot_of_le_map_C {A σ : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] {x : A} {p : Ideal A} (hp : p ∈ (span {x} : Ideal A).minimalPrimes)
    {J : Ideal (MvPolynomial σ A)} [J.IsPrime] (hJ_ne : J ≠ ⊥) (hJ_le : J ≤ p.map C) :
    J = p.map C := by
  -- In the finitely many variables of a nonzero `w ∈ J`, the prime `J` cuts out a nonzero prime
  -- `J'` inside the extension of `p`, which has height at most one; so the two are equal.
  obtain ⟨w, hw_mem, hw_ne⟩ := J.ne_bot_iff.1 hJ_ne
  obtain ⟨n, u, hu, w, rfl⟩ := w.exists_fin_rename
  let J' : Ideal (MvPolynomial (Fin n) A) := J.comap (rename u)
  have h_le : J' ≤ p.map C := by
    refine fun a ha ↦ mem_map_C_iff.2 fun m ↦ ?_
    rw [← coeff_rename_mapDomain u hu]
    exact mem_map_C_iff.1 (hJ_le (mem_comap.1 ha)) _
  have h_ne_bot : J' ≠ ⊥ := J'.ne_bot_iff.2 ⟨w, mem_comap.2 hw_mem, ne_zero_of_map hw_ne⟩
  have : p.IsPrime := Ideal.IsMinimalPrime.isPrime hp
  have := isPrime_map_C_mvPolynomial (σ := Fin n) p
  have h_eq : J' = p.map C := J'.eq_of_le_of_height_le h_le
    ((height_map_C_le_one hp).trans (by simpa [Order.one_le_iff_ne_zero] using h_ne_bot))
  refine hJ_le.antisymm (map_le_of_le_comap fun a ha ↦ ?_)
  simpa [J'] using h_eq.ge (mem_map_of_mem C ha)

/-- Let `V` be a valuation subring of a field in which every nonzero prime ideal contains the
maximal ideal. Then the valuation of `V` is archimedean: every value is bounded by a
power of any value above one. -/
lemma New.exists_valuation_le_pow_of_maximalIdeal_le {K : Type*} [Field K] (V : ValuationSubring K)
    (hV : ∀ J : Ideal V, J.IsPrime → J ≠ ⊥ → maximalIdeal V ≤ J) (z : K)
    {y : K} (hy : 1 < V.valuation y) :
    ∃ n : ℕ, V.valuation z ≤ V.valuation y ^ n := by
  -- The element `y⁻¹` lies in the maximal ideal, so a power of it lies in the nonzero ideal `I` of
  -- denominators of `z`.
  let I : Ideal V := (1 : Submodule V K).comap (LinearMap.toSpanSingleton V K z)
  have h_mem_iff (a : V) : a ∈ I ↔ ∃ w : V, (w : K) = a * z := by simp [I, Algebra.smul_def]
  obtain ⟨⟨c, hc⟩, w₀, hw₀⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors V) z
  have hI_ne : I ≠ ⊥ := I.ne_bot_iff.2
    ⟨c, (h_mem_iff c).2 ⟨w₀, by simpa [Algebra.smul_def] using hw₀⟩, nonZeroDivisors.ne_zero hc⟩
  have h_rad : maximalIdeal V ≤ I.radical := by
    rw [radical_eq_sInf]
    exact le_sInf fun J ⟨hIJ, hJ⟩ ↦ hV J hJ (ne_bot_of_le_ne_bot hI_ne hIJ)
  obtain ⟨hy_mem, hy_max⟩ := V.mem_nonunits_iff_exists_mem_maximalIdeal.1
    (show y⁻¹ ∈ V.nonunits by simpa [V.mem_nonunits_iff] using inv_lt_one_of_one_lt₀ hy)
  obtain ⟨n, hn⟩ := mem_radical_iff.1 (h_rad hy_max)
  -- So `w = y⁻¹ ^ n * z` lies in `V`, that is, `y ^ n` divides `z` over `V`.
  obtain ⟨w, hw⟩ : ∃ w : V, (w : K) = y⁻¹ ^ n * z := by simpa using (h_mem_iff _).1 hn
  have hy_ne : y ≠ 0 := V.valuation.pos_iff.1 (zero_lt_one.trans hy)
  have h_dvd : (w : K) * y ^ n = z := by simp [hw, field]
  exact ⟨n, ((V.valuation_le_iff z (y ^ n)).2 ⟨w, h_dvd⟩).trans_eq (map_pow _ y n)⟩

/-- A valuation subring `V` of a field, in which every prime ideal with a nonzero element `c`
contains the maximal ideal, is the ring of a valuation with values in `ℝ≥0`. -/
lemma New.exists_nnreal_valuation {K : Type*} [Field K] (V : ValuationSubring K)
    (hV : ∀ J : Ideal V, J.IsPrime → ∀ c ∈ nonZeroDivisors V, c ∈ J → maximalIdeal V ≤ J) :
    ∃ v : Valuation K NNReal, v.valuationSubring = V := by
  -- The canonical valuation of the valuative relation of `V` is equivalent to that of `V`.
  let : ValuativeRel K := ofValuation V.valuation
  have : V.valuation.Compatible := .ofValuation V.valuation
  have h_equiv : (valuation K).IsEquiv V.valuation := isEquiv _ _
  have h_prime (J : Ideal V) (hJ : J.IsPrime) (hJ_ne : J ≠ ⊥) : maximalIdeal V ≤ J :=
    let ⟨c, hc_mem, hc_ne⟩ := J.ne_bot_iff.1 hJ_ne
    hV J hJ c (mem_nonZeroDivisors_of_ne_zero hc_ne) hc_mem
  have h_arch : MulArchimedean (ValueGroupWithZero K) := by
    refine ⟨valuation_surjective.forall₂.2 fun z y hy ↦ ?_⟩
    obtain ⟨n, hn⟩ :=
      exists_valuation_le_pow_of_maximalIdeal_le V h_prime z (h_equiv.one_lt_iff_one_lt.1 hy)
    exact ⟨n, by rwa [← map_pow, h_equiv.le_iff_le, map_pow]⟩
  -- An archimedean value group has rank at most one, that is, it embeds in `ℝ≥0` by some `g`.
  obtain ⟨g, hg⟩ : IsRankLeOne K := isRankLeOne_iff_mulArchimedean.2 h_arch
  refine ⟨(valuation K).map ⟨g, hg.monotone⟩, ?_⟩
  rw [(isEquiv_iff_valuationSubring _ _).1
    ((isEquiv_map_self_of_strictMono ⟨g, hg.monotone⟩ hg.injective).trans h_equiv),
    V.valuationSubring_valuation]

/-- Blowing up inside a valuation ring. Let `O ⟶ W` be a local map from a noetherian local ring to
a valuation ring. Then `W` has a noetherian `O`-subalgebra `A` with a prime `p` that is minimal
over one element and lies over the maximal ideal of `O`. -/
lemma New.exists_subalgebra_minimalPrimes_span_singleton (O W : Type*) [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] [CommRing W] [IsDomain W] [ValuationRing W] [Algebra O W]
    [IsLocalHom (algebraMap O W)] :
    ∃ (A : Subalgebra O W) (x : A) (p : Ideal A), IsNoetherianRing A ∧
      p ∈ (span {x} : Ideal A).minimalPrimes ∧ maximalIdeal O ≤ p.comap (algebraMap O A) := by
  obtain ⟨r, hr⟩ := (maximalIdeal O).fg_of_isNoetherianRing
  -- Divisibility in `W` is total, so one element `x` of the maximal ideal divides all its
  -- generators; `A` is generated by the quotients `k y = y / x`, so the maximal ideal becomes
  -- principal in `A`.
  have h_total : Std.Total fun a b : W ↦ b ∣ a := ⟨fun a b ↦ ValuationRing.dvd_total b a⟩
  obtain ⟨⟨x, hx_mem⟩, hx⟩ : ∃ x : (maximalIdeal O : Set O),
      ∀ y : r, ∃ c : W, algebraMap O W y = algebraMap O W x * c :=
    (h_total.directed fun y : (maximalIdeal O : Set O) ↦ algebraMap O W y).finite_le
      (inclusion (subset_span.trans hr.le))
  choose k hk using hx
  let A : Subalgebra O W := (aeval (R := O) k).range
  have hx_nonunit : ¬IsUnit (algebraMap O A x) := fun h_unit ↦
    notMem_maximalIdeal.2 (isUnit_of_map_unit (algebraMap O W) x (h_unit.map A.val)) hx_mem
  obtain ⟨p, hp⟩ := nonempty_minimalPrimes (span_singleton_ne_top hx_nonunit)
  have h_dvd (y : r) : algebraMap O A x ∣ algebraMap O A y :=
    ⟨⟨k y, X y, aeval_X k y⟩, Subtype.ext (hk y)⟩
  -- `A` is noetherian as the image of a polynomial ring in finitely many variables over `O`.
  refine ⟨A, algebraMap O A x, p, inferInstance, hp, ?_⟩
  exact hr.ge.trans <| span_le.2 fun y hy ↦
    Ideal.IsMinimalPrime.le hp (mem_span_singleton.2 (h_dvd ⟨y, hy⟩))

/-- Let `e` identify a ring `R` with a subring of a field `K`. Every prime `P` of `R` is the centre
of a valuation subring `U` of `K` that contains `R`. -/
lemma New.exists_valuationSubring_comap_maximalIdeal_eq {R K : Type*} [CommRing R] [Field K]
    {B : Subring K} (e : R ≃+* B) (P : Ideal R) [P.IsPrime] :
    ∃ (U : ValuationSubring K) (f : R →+* U),
      (∀ a : R, (f a : K) = e a) ∧ (maximalIdeal U).comap f = P := by
  -- `U` dominates the localisation `L` of `B` at the image of `P`.
  let L : LocalSubring K := LocalSubring.ofPrime B (P.map e)
  obtain ⟨U, hU, hU_local⟩ := L.exists_le_valuationSubring
  let f : R →+* U := (Subring.inclusion hU).comp ((algebraMap B L.toSubring).comp e.toRingHom)
  -- The maximal ideal of `U` meets `B` in the image of `P`, as `U` dominates `L`.
  refine ⟨U, f, fun _ ↦ rfl, ext fun a ↦ ?_⟩
  calc f a ∈ maximalIdeal U
      ↔ algebraMap B L.toSubring (e a) ∈ maximalIdeal L.toSubring :=
        map_mem_nonunits_iff (Subring.inclusion hU) _
    _ ↔ e a ∈ P.map e := to_map_mem_maximal_iff _ _ (e a)
    _ ↔ a ∈ P := apply_mem_of_equiv_iff

/-- Let `A` be a noetherian subring of a field `K` and `p` a prime of `A` that is minimal over one
element. Then `A` lies in the ring of a valuation `v` of `K` with values in `ℝ≥0`, in such a way
that `p` lies in the maximal ideal. -/
lemma New.exists_nnreal_valuation_le_comap_maximalIdeal {A : Type*} (K : Type*) [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [FaithfulSMul A K] {x : A}
    {p : Ideal A} (hp : p ∈ (span {x} : Ideal A).minimalPrimes) :
    ∃ (v : Valuation K NNReal) (ψ : A →+* v.valuationSubring),
      (∀ a : A, (ψ a : K) = algebraMap A K a) ∧ p ≤ (maximalIdeal v.valuationSubring).comap ψ := by
  -- Adjoin a transcendence basis `t`, take a valuation ring `U` with centre the extension of `p`,
  -- and localise at a prime `q` minimal over `p`. The result `V` has rank at most one.
  have hp_prime : p.IsPrime := Ideal.IsMinimalPrime.isPrime hp
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis A K
  let P : Ideal (MvPolynomial t A) := p.map C
  have hP_prime : P.IsPrime := isPrime_map_C_mvPolynomial p
  let e : MvPolynomial t A ≃+* (Algebra.adjoin A (range (Subtype.val : t → K))).toSubring :=
    ht.1.aevalEquiv.toRingEquiv
  obtain ⟨U, f, hf, h_centre⟩ := exists_valuationSubring_comap_maximalIdeal_eq e P
  obtain ⟨q, ⟨⟨hq_prime, hPq⟩, hq_min⟩, hq_le⟩ :
      ∃ q ∈ (P.map f).minimalPrimes, q ≤ maximalIdeal U :=
    exists_minimalPrimes_le (map_le_of_le_comap h_centre.ge)
  let V : ValuationSubring K := U.ofPrime q
  let g : MvPolynomial t A →+* V := (algebraMap U V).comp f
  have hg (a : MvPolynomial t A) : (g a : K) = e a := hf a
  let : Algebra (MvPolynomial t A) V := g.toAlgebra
  -- Every prime of `V` with a nonzero element contains the maximal ideal `q V`.
  have h_rank (J : Ideal V) (hJ : J.IsPrime) (c : V) (hc : c ∈ nonZeroDivisors V)
      (hcJ : c ∈ J) : maximalIdeal V ≤ J := by
    rw [← map_eq_maximalIdeal q V, map_le_iff_le_comap]
    -- The ideals of the valuation ring `U` are totally ordered, so we may assume `J ∩ U ≤ q`.
    obtain hqJ | hJq : q ≤ J.comap (algebraMap U V) ∨ J.comap (algebraMap U V) ≤ q :=
      (ValuationRing.le_total_ideal U).total _ _
    · exact hqJ
    -- As `K` is algebraic over the polynomial ring, `c` divides a polynomial `w ≠ 0`.
    have hc_alg : IsAlgebraic (MvPolynomial t A) c :=
      (ht.isAlgebraic.isAlgebraic (c : K)).of_ringHom_of_comp_eq _ _ e.surjective
        V.subtype_injective (RingHom.ext fun a ↦ (hg a).symm)
    obtain ⟨w, hw_ne, hcw⟩ : ∃ w : MvPolynomial t A, w ≠ 0 ∧ c ∣ g w :=
      hc_alg.exists_nonzero_dvd hc
    have h_comap : J.comap g = (J.comap (algebraMap U V)).comap f := (comap_comap _ _).symm
    have hJP : J.comap g ≤ P :=
      h_comap.trans_le ((comap_mono (hJq.trans hq_le)).trans_eq h_centre)
    have hJ_eq : J.comap g = P := eq_map_C_of_ne_bot_of_le_map_C hp
      ((J.comap g).ne_bot_iff.2 ⟨w, mem_of_dvd J hcw hcJ, hw_ne⟩) hJP
    -- So `J ∩ U` contains the extension of `p`, and `q` is minimal among such primes.
    have hPJ : P.map f ≤ J.comap (algebraMap U V) :=
      map_le_iff_le_comap.2 (hJ_eq.ge.trans_eq h_comap)
    exact hq_min ⟨hJ.comap _, hPJ⟩ hJq
  obtain ⟨v, hv⟩ := exists_nnreal_valuation V h_rank
  refine ⟨v, ?_⟩
  rw [hv]
  refine ⟨g.comp C, fun a ↦ (hg (C a)).trans (aeval_C _ a), fun a ha ↦ ?_⟩
  exact (under_maximalIdeal V q).ge (hPq (mem_map_of_mem f (mem_map_of_mem C ha)))

/-- Let `S` be a locally noetherian scheme with finitely many complex points `η i` whose images are
dense. For every point `s` of `S` there are an index `i`, a valuation `v` of `ℂ` with values in
`ℝ≥0` and a morphism `a` from the spectrum of its valuation ring `V` to `S` that restricts to `η i`
along `Spec ℂ ⟶ Spec V` (the map `specMap` of the inclusion) and sends the closed point to `s`. -/
lemma New.exists_valuative_arc_of_isDenseFamily {S : Scheme} {ι : Type} [IsLocallyNoetherian S]
    [Finite ι] (η : ι → (Spec (of ℂ) ⟶ S)) (hη : IsDenseFamily η) (s : S) :
    ∃ (i : ι) (v : Valuation ℂ NNReal) (a : Spec (of v.valuationSubring) ⟶ S),
      specMap v.valuationSubring.subtype ≫ a = η i ∧
      a (closedPoint (of v.valuationSubring)) = s := by
  -- Some `η i` specialises to `s`, which gives a map `θ` from the local ring `O` at `s` to `ℂ`.
  -- By blowing up at `s`, find a noetherian subring `A` of `ℂ` containing the image of `O`, with a
  -- prime `p` over `s` minimal over one element; take a real valuation `v` centred above `p`.
  obtain ⟨i, h_spec⟩ : ∃ i : ι, η i (closedPoint ℂ) ⤳ s := by
    simpa [← iUnion_singleton_eq_range, ← specializes_iff_mem_closure] using hη s
  let O : CommRingCat := S.presheaf.stalk s
  let θ : O ⟶ of ℂ := S.presheaf.stalkSpecializes h_spec ≫ stalkClosedPointTo (η i)
  obtain ⟨W, hW, hW_local⟩ : ∃ (W : ValuationSubring ℂ) (hW : ∀ a : O, θ.hom a ∈ W.toSubring),
      IsLocalHom (θ.hom.codRestrict W.toSubring hW) := exists_factor_valuationRing θ.hom
  let : Algebra O W := (θ.hom.codRestrict W hW).toAlgebra
  have : IsLocalHom (algebraMap O W) := hW_local
  obtain ⟨A, x, p, hA, hp, h_max_le⟩ : ∃ (A : Subalgebra O W) (x : A) (p : Ideal A),
      IsNoetherianRing A ∧ p ∈ (span {x} : Ideal A).minimalPrimes ∧
        maximalIdeal O ≤ p.comap (algebraMap O A) :=
    exists_subalgebra_minimalPrimes_span_singleton O W
  obtain ⟨v, ψ, hψ, hp_le⟩ : ∃ (v : Valuation ℂ NNReal) (ψ : A →+* v.valuationSubring),
      (∀ a : A, (ψ a : ℂ) = algebraMap A ℂ a) ∧ p ≤ (maximalIdeal v.valuationSubring).comap ψ :=
    exists_nnreal_valuation_le_comap_maximalIdeal ℂ hp
  -- The arc is `Spec V → Spec O → S`, with `V` the ring of `v`.
  let φ : O →+* v.valuationSubring := ψ.comp (algebraMap O A)
  have hφ : ofHom φ ≫ ofHom v.valuationSubring.subtype = θ :=
    CommRingCat.hom_ext (RingHom.ext fun a ↦ hψ (algebraMap O A a))
  refine ⟨i, v, Spec.map (ofHom φ) ≫ S.fromSpecStalk s, ?_, ?_⟩
  · simp [← map_comp_assoc, hφ, θ, Spec_stalkClosedPointTo_fromSpecStalk _]
  · -- `φ` is local, so the closed point goes to the closed point.
    have h_local : maximalIdeal O ≤ (maximalIdeal v.valuationSubring).comap φ :=
      fun y hy ↦ hp_le (h_max_le hy)
    have h_closed : Spec.map (ofHom φ) (closedPoint (of v.valuationSubring)) = closedPoint O :=
      PrimeSpectrum.ext ((maximalIdeal.isMaximal O).eq_of_le (IsPrime.ne_top') h_local).symm
    exact (congrArg (S.fromSpecStalk s) h_closed).trans fromSpecStalk_closedPoint

end ArcExistence
