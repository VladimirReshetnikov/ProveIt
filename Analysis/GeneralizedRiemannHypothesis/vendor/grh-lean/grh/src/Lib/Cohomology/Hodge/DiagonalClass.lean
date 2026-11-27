import Lib.Cohomology.Hodge.GrothendieckSymbol

/-!
# The Hodge class of the diagonal of a variety with an atlas, with its local description

The class of the diagonal in Hodge cohomology, for a functor of points `X` on `k`-algebras.

* `New.Variety.exists_diagonal_class`: if `k` has characteristic zero and `X` has an atlas of
  dimension `d`, there is a class `δ` of degree `d` on `X × X` relative to the complement of the
  diagonal that is, near the diagonal, the symbol `[df / f]` of the differences of chart
  coordinates. It is glued from such symbols.

`New.Variety.HasAtlas d X`: `X` is separated and its field points lie in finitely many affine charts
`New.Variety.EtaleChart d X` with `d` étale coordinates. `HodgeH (relFreeAb U) q` is Hodge
cohomology relative to the subfunctor `U`. `New.Variety.IsLocalSymbol ξ y P g m` says three things:
`g` cuts out `P` at the point `y`; `y` maps the part of `Spec R` off the preimage of `P` into `U`;
and `ξ` pulls back along `y` to `m • [dg / g]`. Here `[dg / g]` is the pull-back of
`New.Variety.symbolClass` along `g`. `P` is a predicate on points, not the subfunctor that `ξ` is
relative to; that subfunctor is the implicit `U`. For the diagonal class, `P` is the diagonal
`x.1 = x.2`, while `δ` is relative to its complement.

Notions from other files:
* `New.Variety.CutsOutLocus`: The elements `f i` of `R` cut out the locus where the point `x` of
  `X(R)` satisfies `P`: a map `α : R ⟶ C` kills every `f i` exactly when the image of `x` in `X(C)`
  satisfies `P`.
* `New.Variety.IsOpenSubfunctor`: V is an open subfunctor of X: each x ∈ X(A) has an ideal I of A
  such that, for φ: A → B, φ(x) ∈ V(B) iff φ(I)B = B.
* `New.Variety.EtaleChart`: A chart of X: a k-algebra R with finitely many étale coordinates and a
  point y in X(R) that embeds Spec R as an open subfunctor, its `locus`.
* `New.Variety.offDiagonal`: The complement of the diagonal in X × X: pairs of points whose values
  in every field are distinct.
* `New.Variety.relFreeAb`: For a subfunctor U of a set-valued functor V, the functor to abelian
  groups ℤ[V]/ℤ[U].
* `New.Variety.HodgeH`: Hodge cohomology: for a functor N from k-algebras to abelian groups, Ext^q
  from (A, M) ↦ N(A ⊕ M) to (A, M) ↦ ⋀_A M, in functors on pairs.

## Relation to the literature

Known; see `Lib.Cohomology.Hodge.FixedPointFormula` for sources.
-/

namespace New.Variety

open CategoryTheory MonoidalCategory Ideal Set EtaleChart

variable {k : Type} [Field k] {X : CommAlg k ⥤ Type 1} {d : ℕ}

/-- Excision to a chart. Let `c` be a chart of `X` whose image `c.locus` is `W`, and `U` a
subfunctor of `X`. Pull-back along the point of `c`, seen as a point of `W`, is a bijection on Hodge
cohomology relative to `U`: classes on `W` relative to `U` are determined by, and may be prescribed
through, their pull-back to `c.point`. `pointMap` sends `χ : c.coordRing ⟶ B` to the image of
`c.point`; `IsCohomEquiv hodgeCoeff` (on functors whiskered by `HodgeTest.sqZeroExt`) means
bijective in every degree. -/
lemma EtaleChart.isCohomEquiv_relFreeAb_map_pointMap (c : EtaleChart d X) (U : Subfunctor X)
    {W : Subfunctor X} (hc : c.locus = W) :
    IsCohomEquiv hodgeCoeff (HodgeTest.sqZeroExt.whiskerLeft (relFreeAb.map (U := U.preimage W.ι)
      (pointMap (A := c.coordRing) ⟨c.point, hc.le c.coordRing c.point_mem_locus⟩) le_rfl)) := by
  refine hodge_excision (c.comap W.ι ⟨c.point, hc.le c.coordRing c.point_mem_locus⟩
    rfl).isOpenSubfunctor ?_
    rfl
  -- every point of `W` lies in the range of the chart
  subst hc
  rintro K - ⟨_, χ, rfl⟩ h_not_mem
  exact absurd ⟨χ, rfl⟩ h_not_mem

/-- Let `c` be a chart of `X × X` on which the differences of the first `d` and the last `d`
coordinates cut out the diagonal. Then the Hodge cohomology of its image relative to the
complement of the diagonal vanishes in degrees below `d`. -/
lemma EtaleChart.subsingleton_hodgeH_offDiagonal (c : EtaleChart (d + d) (X ⊗ X))
    (h_cut : CutsOutLocus (X ⊗ X) (fun (C : CommAlg k) (p : (X ⊗ X).obj C) ↦ p.fst = p.snd) c.point
      (c.coordinate ∘ Fin.castAdd d - c.coordinate ∘ Fin.natAdd d))
    {m : ℕ} (hm : m < d) :
    Subsingleton (HodgeH (relFreeAb ((offDiagonal X).preimage c.locus.ι)) m) := by
  -- pull-back to the universal point of `c` is injective, and there the cohomology vanishes
  obtain ⟨μ, -, hμ⟩ := c.exists_section_isCohomEquiv
  -- `h_univ`: pull-back along `μ` and restriction to where some difference is a unit is a bijection
  -- on cohomology
  obtain ⟨h_le, h_univ⟩ := hμ h_cut.preimage_fieldLocus_not
  have h_vanish : Subsingleton (H (relFreeAb (someUnitLocus (c := ⟨c.coordRing, Fin (d + d)⟩)
      (c.coordinate ∘ Fin.castAdd d - c.coordinate ∘ Fin.natAdd d))) hodgeCoeff m) :=
    hodge_vanishing_along_diagonal c.etale hm
  -- `h_vanish` enters as the instance that makes the target of this injection subsingleton
  exact (h_univ.comp_iff.mpr (c.isCohomEquiv_relFreeAb_map_pointMap (offDiagonal X) rfl)
    m).injective.subsingleton

/-- On the subfunctor `O` of `X × X`, the class `δ` is the symbol of the differences of the
coordinates of the chart `a`: every point of `O` is a pair of points `φ`, `ψ` of the chart, the
differences `f i = φ (a.coordinate i) - ψ (a.coordinate i)` cut out the diagonal there, and `δ`
pulls back to `[df / f]`. -/
structure IsDiagonalSymbolOn [CharZero k]
    (δ : HodgeH (relFreeAb (offDiagonal X)) d) (a : EtaleChart d X)
    (O : Subfunctor (X ⊗ X)) : Prop where
  /-- The first component of a point of `O` lies in the chart `a`. -/
  fst_mem_locus {B : CommAlg k} {p : (X ⊗ X).obj B} (hp : p ∈ O.obj B) : p.fst ∈ a.locus.obj B
  /-- The second component of a point of `O` lies in the chart `a`. -/
  snd_mem_locus {B : CommAlg k} {p : (X ⊗ X).obj B} (hp : p ∈ O.obj B) : p.snd ∈ a.locus.obj B
  /-- At a point `p` of `O` given by `φ` and `ψ` in the chart, the differences of the coordinates
  cut out the diagonal and `δ` is their symbol. -/
  isLocalSymbol {B : CommAlg k} {p : (X ⊗ X).obj B} (hp : p ∈ O.obj B) {φ ψ : a.coordRing ⟶ B}
    (hφ : X.map φ a.point = p.fst) (hψ : X.map ψ a.point = p.snd) :
    IsLocalSymbol δ p (fun (C : CommAlg k) (q : (X ⊗ X).obj C) ↦ q.fst = q.snd)
      (fun i : Fin d ↦ φ (a.coordinate i) - ψ (a.coordinate i)) 1

/-- A chart `a` of `X` gives a chart `V` of `X × X` near the diagonal. The point of `V` is a pair of
points `φ`, `ψ` of `a`, its coordinates are those of `φ` and `ψ`, their differences cut out the
diagonal, and `V` contains `(z, z)` for every point `z` of `a`. -/
lemma EtaleChart.exists_chart_near_diagonal (a : EtaleChart d X) :
    ∃ (V : EtaleChart (d + d) (X ⊗ X)) (φ ψ : a.coordRing ⟶ V.coordRing),
      V.point = (X.map φ a.point, X.map ψ a.point) ∧
      V.coordinate ∘ Fin.castAdd d = φ ∘ a.coordinate ∧
      V.coordinate ∘ Fin.natAdd d = ψ ∘ a.coordinate ∧
      CutsOutLocus (X ⊗ X) (fun (C : CommAlg k) (p : (X ⊗ X).obj C) ↦ p.fst = p.snd) V.point
        (V.coordinate ∘ Fin.castAdd d - V.coordinate ∘ Fin.natAdd d) ∧
      ∀ (K : CommAlg k), ∀ z ∈ a.locus.obj K, (z, z) ∈ V.locus.obj K := by
  -- `h_eq_iff`: a pair of points of `a` is diagonal iff `e` is a unit at it and the two points
  -- have the same coordinates. Take for `V` the part of `a × a` where `e` is a unit.
  obtain ⟨e, h_eq_iff⟩ := a.exists_eq_iff_coordinate_eq
  let V : EtaleChart (d + d) (X ⊗ X) := (a.prod a).away e
  let l : a.coordRing ⊗ a.coordRing ⟶ V.coordRing := CommAlg.toAway e
  have h_fst : V.coordinate ∘ Fin.castAdd d = (tensorInl ≫ l : a.coordRing ⟶ V.coordRing) ∘
    a.coordinate :=
    funext fun j ↦ congrArg l
      (Fin.append_left (fun i ↦ a.coordinate i ⊗ₜ 1) (fun i ↦ 1 ⊗ₜ a.coordinate i) j)
  have h_snd : V.coordinate ∘ Fin.natAdd d = (tensorInr ≫ l : a.coordRing ⟶ V.coordRing) ∘
    a.coordinate :=
    funext fun j ↦ congrArg l
      (Fin.append_right (fun i ↦ a.coordinate i ⊗ₜ 1) (fun i ↦ 1 ⊗ₜ a.coordinate i) j)
  refine ⟨V, tensorInl ≫ l, tensorInr ≫ l, ?_, h_fst, h_snd, fun C α ↦ ?_, fun K z hz ↦ ?_⟩
  · rw [X.map_comp_apply, X.map_comp_apply]
    -- the point of `V` is the image under `l` of the pair of points of `a × a`
    rfl
  · -- `e` is a unit on `V`, so there equal coordinates mean equal points
    have h_unit : IsUnit ((l ≫ α) e) := (CommAlg.exists_toAway_comp_iff e (l ≫ α)).mp ⟨α, rfl⟩
    have h_diff : V.coordinate ∘ Fin.castAdd d - V.coordinate ∘ Fin.natAdd d =
        fun j ↦ l (a.coordinate j ⊗ₜ 1 - 1 ⊗ₜ a.coordinate j) := by
      rw [h_fst, h_snd]
      exact funext fun j ↦ (map_sub l.hom _ _).symm
    rw [h_diff]
    -- `using!`: the point of `V` is the image of the point of `a × a` under `l` by definition.
    simpa [span_le, -map_sub, range_subset_iff] using! ((h_eq_iff C (l ≫ α)).trans (and_iff_right
      h_unit)).symm
  · -- `e` is a unit at a diagonal pair
    obtain ⟨⟨χ : a.coordRing ⊗ a.coordRing ⟶ K⟩, hχ : (X ⊗ X).map χ (a.prod a).point = (z, z)⟩ :
        (z, z) ∈ (a.prod a).locus.obj K :=
      (range_pointMap_prod a a).ge K ⟨hz, hz⟩
    have h_eq : X.map χ (a.prod a).point.fst = X.map χ (a.prod a).point.snd :=
      (congrArg Prod.fst hχ).trans (congrArg Prod.snd hχ).symm
    have h_unit : IsUnit (χ e) := ((h_eq_iff K χ).mp h_eq).left
    rw [← hχ]
    exact ((a.prod a).mem_locus_away e χ).mpr h_unit

/-- Let `X` be separated (`IsSeparatedFunctor`; here it makes `offDiagonal X` open), and let `V i`
be finitely many étale charts of `X ⊗ X` with `d + d` coordinates, such that every diagonal point
`(z, z)` with values in a field lies in some `V i`. Suppose that on each `V i` the differences of
the first `d` and last `d` coordinates cut out the diagonal. Then there is a class `δ` in degree-`d`
Hodge cohomology of `X ⊗ X` relative to `offDiagonal X` which, for every `i`, is a local symbol
(`IsLocalSymbol`) with multiplicity `1` at the point of `V i` for these coordinate differences. -/
lemma exists_isLocalSymbol_of_charts_near_diagonal [IsSeparatedFunctor X] {r : ℕ}
    (V : Fin r → EtaleChart (d + d) (X ⊗ X))
    (h_cut : ∀ i : Fin r,
      CutsOutLocus (X ⊗ X) (fun (C : CommAlg k) (p : (X ⊗ X).obj C) ↦ p.fst = p.snd)
      (V i).point ((V i).coordinate ∘ Fin.castAdd d - (V i).coordinate ∘ Fin.natAdd d))
    (h_near : ∀ K : CommAlg k, IsField K.carrier →
      ∀ z : X.obj K, ∃ i : Fin r, (z, z) ∈ (V i).locus.obj K) :
    ∃ δ : HodgeH (relFreeAb (offDiagonal X)) d, ∀ i : Fin r,
      IsLocalSymbol δ (V i).point (fun (C : CommAlg k) (p : (X ⊗ X).obj C) ↦ p.fst = p.snd)
        ((V i).coordinate ∘ Fin.castAdd d - (V i).coordinate ∘ Fin.natAdd d) 1 := by
  -- The symbols of the `f i` agree on overlaps and lower cohomology vanishes, so
  -- `relFreeAb.exists_glued_class` glues them to a class on `X ⊗ X`.
  let f (i : Fin r) : Fin d → (V i).coordRing :=
    (V i).coordinate ∘ Fin.castAdd d - (V i).coordinate ∘ Fin.natAdd d
  -- for each `i`, a class `ξ` on `V i` whose value at the point of the chart is the symbol of `f i`
  have h_class (i : Fin r) : ∃ ξ : HodgeH (relFreeAb ((offDiagonal X).preimage (V i).locus.ι)) d,
      IsLocalSymbol ξ ⟨(V i).point, (V i).point_mem_locus⟩
        (fun C (p : (V i).locus.toFunctor.obj C) ↦ p.val.fst = p.val.snd) (f i) 1 := by
    -- by excision, a class on `V i` may be prescribed through its pull-back to the point
    obtain ⟨ξ, hξ⟩ := ((V i).isCohomEquiv_relFreeAb_map_pointMap (offDiagonal X) rfl d).surjective
      ((1 : k) • symbolClass.map (relFreeAb.map _ (h_cut i).preimage_fieldLocus_not.le))
    exact ⟨ξ, h_cut i, le_rfl, hξ⟩
  choose ξ hξ using h_class
  -- hence the same description of `ξ i` at every point of `V i`
  have h_local {i : Fin r} {B : CommAlg k} {p : (X ⊗ X).obj B} {χ : (V i).coordRing ⟶ B}
      (hp : (pointMap (V i).point).app B ⟨χ⟩ = p) :
      IsLocalSymbol (ξ i) ⟨p, ⟨χ⟩, hp⟩
        (fun C (q : (V i).locus.toFunctor.obj C) ↦ q.val.fst = q.val.snd) (χ ∘ f i) 1 := by
    subst hp
    exact (hξ i).map χ
  obtain ⟨δ, hδ⟩ : ∃ δ : HodgeH (relFreeAb (offDiagonal X)) d,
      ∀ i, δ.map (relFreeAb.map (V i).locus.ι le_rfl) = ξ i := by
    refine relFreeAb.exists_glued_class ((offDiagonal X).whisker HodgeTest.sqZeroExt)
      {W | ∃ i, ∃ c : EtaleChart (d + d) (X ⊗ X),
        c.locus.whisker HodgeTest.sqZeroExt = W ∧ c.locus ≤ (V i).locus}
      ?_ ?_ (fun i ↦ (V i).locus.whisker HodgeTest.sqZeroExt) (fun i ↦ ⟨i, V i, rfl, le_rfl⟩) ?_ ξ
      fun i j ↦ ?_
    · -- the charts inside some `V i` are closed under intersection
      rintro _ ⟨i, c, rfl, hc⟩ _ ⟨_, b, rfl, -⟩
      obtain ⟨c', hc'⟩ := c.exists_locus_eq_inf b
      refine ⟨i, c', ?_, hc'.trans_le (inf_le_left.trans hc)⟩
      rw [hc']
      rfl
    · -- such a chart `c`, with the coordinates of `V i`, has differences that cut out the diagonal
      rintro _ ⟨i, c, rfl, hc⟩ m hm
      obtain ⟨⟨χ : (V i).coordRing ⟶ c.coordRing⟩, hχ⟩ := hc c.coordRing c.point_mem_locus
      have h_diff : χ ∘ f i =
          (χ ∘ (V i).coordinate) ∘ Fin.castAdd d - (χ ∘ (V i).coordinate) ∘ Fin.natAdd d :=
        funext fun j ↦ map_sub χ.hom _ _
      obtain ⟨h_cut_c, -, -⟩ := h_local hχ
      rw [h_diff] at h_cut_c
      exact ((V i).restrict hχ c.injective c.isOpenSubfunctor).subsingleton_hodgeH_offDiagonal
        h_cut_c hm
    · -- the `V i` and the complement of the diagonal are open and cover all field points
      refine hasZariskiDescent_hodgeCoeff (isZariskiLocallyTop_of_open_cover fun K hK ⟨z, w⟩ ↦ ?_)
      obtain rfl | h_ne := eq_or_ne z w
      · obtain ⟨i, hi⟩ := h_near K hK z
        exact ⟨(V i).locus, (V i).isOpenSubfunctor, hi, le_sup_of_le_left (le_sSup ⟨i, rfl⟩)⟩
      · exact ⟨offDiagonal X, isOpenSubfunctor_offDiagonal, mem_offDiagonal_of_ne hK h_ne,
        le_sup_right⟩
    · -- the overlap is a chart `c`; both sequences cut out the diagonal at `c.point`, so their
      -- symbols agree there (`EtaleChart.symbolClass_eq_of_cutsOutLocus`)
      obtain ⟨c, hc⟩ := (V i).exists_locus_eq_inf (V j)
      obtain ⟨⟨⟨χ⟩, hχ⟩, ⟨χ'⟩, hχ'⟩ := hc.le c.coordRing c.point_mem_locus
      obtain ⟨h_cut_i, h_le, h_symb⟩ := h_local hχ
      obtain ⟨h_cut_j, h_le', h_symb'⟩ := h_local hχ'
      -- `erw`: the points of `(V i).locus` are a subtype here and values of the subfunctor there.
      erw [c.symbolClass_eq_of_cutsOutLocus h_cut_i h_cut_j, ← h_symb'] at h_symb
      -- a class on the overlap is determined by its value at `c.point`; on each side, restriction
      -- to the overlap followed by that value is the value in `h_symb`
      refine (c.isCohomEquiv_relFreeAb_map_pointMap (offDiagonal X) hc d).injective
        (.trans ?_ (h_symb.trans (.symm ?_)))
      · refine (HodgeH.map_comp _ (relFreeAb.restrict _ (by simp)) (ξ i)).symm.trans ?_
        rw [relFreeAb.map_comp_map]
        rfl
      · refine (HodgeH.map_comp _ (relFreeAb.restrict _ (by simp)) (ξ j)).symm.trans ?_
        rw [relFreeAb.map_comp_map]
        rfl
  -- `δ` restricts to `ξ i` on `V i`, so it has the local description of `ξ i` there
  refine ⟨δ, fun i ↦ ⟨h_cut i, le_rfl, ?_⟩⟩
  obtain ⟨h_cut_i, h_le, h_symb⟩ := hξ i
  rwa [← hδ, ← δ.map_comp _ (relFreeAb.map _ le_rfl), relFreeAb.map_comp_map] at h_symb

/-- The class of the diagonal. If `X` has an atlas of dimension `d`, there is a Hodge class `δ` of
degree `d` on `X × X` relative to the complement of the diagonal, such that every point `z` of
`X` in a field has a chart `a` and an open `O ∋ (z, z)` on which `δ` is the symbol of the
differences of the coordinates of `a`. -/
lemma exists_diagonal_class [CharZero k] (hX : HasAtlas d X) :
    ∃ δ : HodgeH (relFreeAb (offDiagonal X)) d,
      ∀ (K : CommAlg k) (z : X.obj K), IsField K.carrier →
        ∃ (a : EtaleChart d X) (O : Subfunctor (X ⊗ X)),
          IsOpenSubfunctor O ∧
          (z, z) ∈ O.obj K ∧
          IsDiagonalSymbolOn δ a O := by
  -- Each chart `a i` of the atlas gives a chart `V i` of `X × X` near the diagonal. Glue the
  -- symbols of the differences of the coordinates on the `V i`.
  obtain ⟨r, a, h_cover⟩ := hX.exists_finite_charts
  choose V φ₀ ψ₀ h_point h_fst h_snd h_cut h_diag using fun i ↦ (a i).exists_chart_near_diagonal
  have h_near (K : CommAlg k) (hK : IsField K.carrier) (z : X.obj K) :
      ∃ i, (z, z) ∈ (V i).locus.obj K :=
    (h_cover K hK z).imp fun i hz ↦ h_diag i K z hz
  obtain ⟨δ, hδ⟩ := exists_isLocalSymbol_of_charts_near_diagonal V h_cut h_near
  refine ⟨δ, fun K z hK ↦ ?_⟩
  obtain ⟨i, hi⟩ := h_near K hK z
  -- a point `χ` of `V i` is the pair of the points `φ₀ i ≫ χ` and `ψ₀ i ≫ χ` of `a i`
  have h_pair {B : CommAlg k} (χ : (V i).coordRing ⟶ B) : (pointMap (V i).point).app B ⟨χ⟩ =
      (X.map (φ₀ i ≫ χ) (a i).point, X.map (ψ₀ i ≫ χ) (a i).point) := by
    rw [h_point, X.map_comp_apply, X.map_comp_apply]
    rfl
  refine ⟨a i, (V i).locus, (V i).isOpenSubfunctor, hi, ?_, ?_, ?_⟩
  · rintro B _ ⟨⟨χ⟩, rfl⟩
    exact ⟨⟨φ₀ i ≫ χ⟩, (congrArg Prod.fst (h_pair χ)).symm⟩
  · rintro B _ ⟨⟨χ⟩, rfl⟩
    exact ⟨⟨ψ₀ i ≫ χ⟩, (congrArg Prod.snd (h_pair χ)).symm⟩
  · rintro B _ ⟨⟨χ : (V i).coordRing ⟶ B⟩, rfl⟩ φ ψ hφ hψ
    obtain rfl : φ = φ₀ i ≫ χ := (a i).injective B (hφ.trans (congrArg Prod.fst (h_pair χ)))
    obtain rfl : ψ = ψ₀ i ≫ χ := (a i).injective B (hψ.trans (congrArg Prod.snd (h_pair χ)))
    have h_diff : (fun j ↦ (φ₀ i ≫ χ) ((a i).coordinate j) - (ψ₀ i ≫ χ) ((a i).coordinate j)) =
        χ ∘ ((V i).coordinate ∘ Fin.castAdd d - (V i).coordinate ∘ Fin.natAdd d) := by
      rw [h_fst, h_snd]
      exact funext fun j ↦ (map_sub χ.hom _ _).symm
    rw [h_diff]
    exact (hδ i).map χ

end New.Variety
