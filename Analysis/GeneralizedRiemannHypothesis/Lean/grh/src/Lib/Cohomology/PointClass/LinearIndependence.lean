import Lib.Cohomology.PointClass.ProjectiveNonvanishing

/-!
# The Hodge–Tate map keeps classes of points on a projective variety linearly independent

Let `k` be an algebraically closed field with a map to `Q̄_p`, and let `Y` be a projectively
embedded scheme whose points over `k`-algebras (`New.Variety.algPointsOf`; `PointsIn Y A` is the set
of points of `Y` with values in a `k`-algebra `A`, and `structureMap` is the map `k ⟶ A`) are
covered by charts with `d` étale coordinates (`New.Variety.HasAtlas`). The Hodge–Tate map
`New.Variety.hodgeTateMap d` sends the distinct classes of `k`-points of `Y` to linearly independent
elements.

* `New.Variety.linearIndepOn_hodgeTateMap_pointClass`: the main result.
* `New.Variety.exists_map_separating_class`: for a `k`-point `z₀` and finitely many other points, a
  map `j` to `Y` whose pull-back kills the classes that differ from that of `z₀` and keeps the
  Hodge–Tate image of the class of `z₀` non-zero.

The map `j` is an open part of the graph of a linear projection of the component of `z₀` to
projective space, chosen by Noether normalisation (`New.Variety.exists_generic_chart`,
`New.Variety.exists_etale_projection`). Over a suitable `k`-point `Q` of projective space the
projection is étale and its fibre consists of points with the class of `z₀`. Pull-back along the
projection is injective and the Hodge–Tate image of the class of `Q` is non-zero, so the Hodge–Tate
image of the class of `z₀` is non-zero too.

Notions from other files:
* `New.Variety.pointClass d z`: the class of the `k`-point `z` in the Hodge cohomology of degree
  `d`.
* `New.Variety.IsCoordsWithUnit L x v`: `v` is a vector of homogeneous coordinates of the point `x`
  for the embedding `L`, and some entry of `v` is a unit.
* `New.Variety.CutsOutLocus.IsHomogeneousSolution k g v`: every homogeneous polynomial over `k` that
  vanishes at `g` vanishes at `v`, that is, `v` lies on the cone cut out at `g`.
* `New.Variety.CutsOutLocus.IsNoetherNormalization Λ g`: the values `evalForms Λ g` of the linear
  forms `Λ j` satisfy no non-zero homogeneous relation, and the cone of `g` is integral over them.
* `New.Variety.EtaleChart d X`: a `k`-algebra `c.coordRing` with `d` étale coordinates and a point
  `c.point` of `X` with values in `c.coordRing`, whose images `c.locus` (the points
  `X.map φ c.point`) make its spectrum an open subfunctor of `X`.

## Relation to the literature

Known result: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles.
This file proves only that the Hodge–Tate images of the distinct point classes are linearly
independent, without duality or a trace map. Non-vanishing on projective space is imported
(`New.Variety.projSpace.hodgeTateMap_pointClass_ne_zero`) and carried to a smooth projective variety
by transfer along a finite linear projection. Source: Faltings, p-adic Hodge theory, JAMS 1 (1988)
(compatibility with traces and cycle classes); for transfer, Suslin–Voevodsky, Singular homology of
abstract algebraic varieties, Invent. Math. 123 (1996), §§4–6.
-/

open CategoryTheory Function CommAlgCat New.Variety CutsOutLocus IsCoordsWithUnit projSpace
  MvPolynomial Finset RingHom Fin CommAlg IsLocalization Away Field Submodule Algebra Ideal
  EtaleChart CartesianMonoidalCategory MonoidalCategory

attribute [local instance] FractionRing.liftAlgebra FormallyEtale.of_isSeparable

/-- The chart `c` with coordinates `w`, embedded in a field by `κ`, is a generic point of the
component of the `k`-point `z` (coordinates `v`), with a Noether normalisation `Λ` of `κ ∘ w`. -/
structure New.Variety.IsGenericChart {k : Type} [Field k] {R : CommRingCat} [Algebra R k]
    {Y : Over (AlgebraicGeometry.Spec R)} {d : ℕ} {ι : Type} [Finite ι] (L : LineBundle Y.left ι)
    (z : PointsIn Y (of k k)) (c : EtaleChart d (algPointsOf k R Y)) {F : Type} [Field F]
    [Algebra k F] (κ : c.coordRing ⟶ of k F) (w : ι → c.coordRing) {n : ℕ}
    (Λ : Fin (n + 1) → homogeneousSubmodule ι k 1) (v : ι → k) : Prop where
  /-- `κ` is injective. -/
  injective : Function.Injective κ
  /-- `w` are homogeneous coordinates of the point of the chart, with a unit entry. -/
  isCoordsWithUnit_point : IsCoordsWithUnit L c.point w
  /-- The form `Λ 0` takes the value `1` at `w`. -/
  evalForms_zero : evalForms Λ w 0 = 1
  /-- `Λ` is a Noether normalisation of the image of `w` in the field. -/
  isNoetherNormalization : IsNoetherNormalization Λ (κ ∘ w)
  /-- `v` are homogeneous coordinates of `z`, with a unit entry. -/
  isCoordsWithUnit_z : IsCoordsWithUnit L z v
  /-- `z` lies on the cone of the generic point. -/
  isHomogeneousSolution : IsHomogeneousSolution k (κ ∘ w) v

/-- Let `k` be a field of characteristic zero and an `R`-algebra, and let `Y` be a scheme over
`Spec R` with an atlas of dimension `d` on its points (`HasAtlas`), projectively embedded by the
line bundle `L` with sections indexed by the finite type `ι` (`IsProjEmbedding`, which includes
that `Y → Spec R` is proper). For every `k`-point `z` of `Y` there are an étale chart `c`, a field
extension `F` of `k` with a map `κ : c.coordRing ⟶ F`, coordinates `w : ι → c.coordRing`, linear
forms `Λ 0`, …, `Λ n` over `k` in the variables `ι` and coordinates `v : ι → k` of `z` with
`IsGenericChart L z c κ w Λ v`: the map `κ` is a generic point of a component of `Y` containing
`z`, and `Λ` is a Noether normalisation of `κ ∘ w`. -/
lemma New.Variety.exists_generic_chart {k : Type} [Field k] [CharZero k] {R : CommRingCat}
    [Algebra R.carrier k] {Y : Over (AlgebraicGeometry.Spec R)} {d : ℕ}
    [HasAtlas d (algPointsOf k R Y)] {ι : Type} [Finite ι] (L : LineBundle Y.left ι)
    [Fact (L.IsProjEmbedding Y.hom)] (z : PointsIn Y (of k k)) :
    ∃ (c : EtaleChart d (algPointsOf k R Y)) (F : Type) (_ : Field F) (_ : Algebra k F)
      (κ : c.coordRing ⟶ of k F) (w : ι → c.coordRing) (n : ℕ)
        (Λ : Fin (n + 1) → homogeneousSubmodule ι k 1)
      (v : ι → k), IsGenericChart L z c κ w Λ v := by
  obtain ⟨a, ζ, w₀, rfl, hw₀⟩ := exists_chart_coords (d := d) L z (toIsField _)
  -- `a.coordRing` is reduced and noetherian: a minimal prime `q` below `ζ` is the annihilator of
  -- some `γ`.
  have h_reduced : IsReduced a.coordRing := isReduced_of_etale a.etale
  have h_noetherian : IsNoetherianRing a.coordRing := FiniteType.isNoetherianRing k a.coordRing
  have h_ker_prime : (ker ζ.hom').IsPrime := ker_isPrime ζ.hom'
  obtain ⟨q, hq, hζ⟩ : ∃ q ∈ (colon (⊥ : Ideal a.coordRing) {1}).minimalPrimes, q ≤ ker ζ.hom' :=
    exists_minimalPrimes_le fun x hx ↦ by simp_all
  have h_q_prime : q.IsPrime := Ideal.IsMinimalPrime.isPrime hq
  obtain ⟨γ, hγ⟩ := Submodule.exists_eq_colon_of_mem_minimalPrimes hq
  obtain ⟨ψ, hψ⟩ : ∃ ψ : a.coordRing →ₐ[k] q.ResidueField, q = ker ψ :=
    ⟨algHom .., q.ker_algebraMap_residueField.symm⟩
  have hψ_iff (x : a.coordRing) : ψ x = 0 ↔ x * γ = 0 := by simpa [hψ] using Ideal.ext_iff.mp hγ x
  rw [hψ] at hζ
  have ⟨_, i, hi⟩ := hw₀
  have h_ψw_ne : (fun i : ι ↦ ψ (w₀ i)) ≠ 0 := ne_iff.mpr ⟨i, (hi.map ψ).ne_zero⟩
  obtain ⟨n, Λ, hΛ_ne, hΛ⟩ := exists_isNoetherNormalization (k := k) h_ψw_ne
  -- Invert `β`, the product of `γ` and the value of `Λ 0`. Neither factor is in `q` (`γ * γ ≠ 0`),
  -- so `ψ` factors through a map `κ`, which is injective since inverting `γ` kills `q`.
  let β : a.coordRing := γ * evalForms Λ w₀ 0
  have hψγ : ψ γ ≠ 0 := by simpa [hψ_iff, ← sq] using hψ_iff 1
  have h_unit_β : IsUnit (ψ β) := by simp [β, comp_aeval_apply, hΛ_ne, hψγ]
  obtain ⟨κ, hκψ⟩ : ∃ κ : of k (Localization.Away β) ⟶ of k q.ResidueField,
      toAway β ≫ κ = ofHom ψ := (exists_toAway_comp_iff β (ofHom ψ)).mpr h_unit_β
  cases hκψ
  have h_unit_γ : IsUnit (algebraMap a.coordRing (Localization.Away β) γ) :=
    isUnit_of_dvd β ⟨_, rfl⟩
  have hκ : Function.Injective κ :=
    injective_of_map_algebraMap_zero (M := .powers β) _ κ.hom'.toRingHom fun r hr ↦
      h_unit_γ.mul_right_cancel (by rw [← map_mul, (hψ_iff r).mp hr, map_zero, zero_mul])
  -- The value of `Λ 0` is now a unit `u`; divide the coordinates by it.
  let u : (Localization.Away β)ˣ := (isUnit_of_dvd β (Dvd.intro_left γ rfl)).unit
  let w : ι → Localization.Away β := u⁻¹ • toAway β ∘ w₀
  have hw : IsCoordsWithUnit L (a.away β).point w := hw₀.map_unit_smul (toAway β) u⁻¹
  have hw₁ : evalForms Λ w 0 = 1 := by
    simp only [w, Units.smul_def]
    rw [evalForms_smul, evalForms_map]
    exact u.inv_mul
  -- In the residue field the old and the new coordinates differ by a unit `t`.
  obtain ⟨t, ht⟩ : ∃ t : (of k q.ResidueField)ˣ, t • κ ∘ w = κ ∘ toAway β ∘ w₀ :=
    (hw.comp κ).exists_unit_smul_eq ((hw₀.comp _).comp κ)
  have hΛw : IsNoetherNormalization Λ (κ ∘ w) := by
    rw [← inv_smul_smul t (κ ∘ w), ht]
    exact hΛ t⁻¹
  have h_cone : IsHomogeneousSolution k (κ ∘ w) (κ ∘ toAway β ∘ w₀) := by
    rw [← ht]
    exact IsHomogeneousSolution.smul (AlgHom.id k _) _ .refl
  exact ⟨a.away β, q.ResidueField, inferInstance, inferInstance, κ, w, n, Λ, ζ ∘ w₀, hκ, hw, hw₁,
    hΛw, hw₀.comp ζ, .of_ker _ _ hζ h_cone⟩

/-- If `Λ` is a Noether normalisation of the image of `w` in a field and `Λ 0` is `1` at `w`, then
the values of `Λ 1`, …, `Λ n` at `w` are algebraically independent. -/
lemma New.Variety.injective_aeval_of_isNoetherNormalization {k A F ι : Type} [Field k] [CommRing A]
    [Algebra k A] [Field F] [Algebra k F] (κ : A →ₐ[k] F) {w : ι → A} {n : ℕ}
    {Λ : Fin (n + 1) → homogeneousSubmodule ι k 1} (hw₁ : evalForms Λ w 0 = 1)
    (hΛ : IsNoetherNormalization Λ (κ ∘ w)) :
    Function.Injective (aeval (R := k) (evalForms Λ w ∘ succ)) := by
  refine algebraicIndependent_iff.mpr fun P hP ↦ ?_
  obtain ⟨h_indep, -⟩ := hΛ
  -- Homogenise the relation `P` to a form `G`, which agrees with `P` wherever `X 0` is `1`.
  obtain ⟨G, hG, h_eval⟩ : ∃ G : MvPolynomial (Fin (n + 1)) k,
      G.IsHomogeneous (rename succ P).totalDegree ∧
      ∀ {B : Type} [CommRing B] [Algebra k B] (φ : MvPolynomial (Fin (n + 1)) k →ₐ[k] B),
        φ (X 0) = 1 → φ G = φ (rename succ P) :=
    exists_homogenization (isHomogeneous_X k 0) (P.rename succ) le_rfl
  have hGw : aeval (evalForms Λ (κ ∘ w)) G = 0 := by
    rw [evalForms_map, Function.comp_def, ← comp_aeval_apply]
    simp [aeval_rename, h_eval, hw₁, hP]
  -- By `hΛ` the form `G` is zero; setting `X 0 = 1` in it gives back `P`.
  simpa [h_eval, comp_def, bind₁_rename] using
    h_indep.map (aeval (cons (1 : MvPolynomial (Fin n) k) X)) hG hGw

/-- The fibre of a linear projection over a general point lies in a given open set. Let `L` embed
`Y` (over `Spec R`) in projective space, and let the field point `η` of `Y` have `L`-coordinates
`κ ∘ w`, where `κ` embeds `A` in a field. Let `Λ 0` be `1` at `w`, and let every non-zero element of
`A` be a root of a polynomial over `k[X₁, …, Xₙ]` (`Xᵢ` acting as `Λ i` at `w`) with non-zero
constant term. If an open `V` contains `η`, then for some `q`, every field point `x` of `Y` lies in
`V` when its `L`-coordinates `v` lie on the cone of `κ ∘ w` (homogeneous polynomials vanishing at
`κ ∘ w` vanish at `v`) and satisfy `Λ v = [1 : q]`. -/
lemma New.Variety.exists_fibre_mem_of_isOpenSubfunctor {k : Type} [Field k] [CharZero k]
    {R : CommRingCat} [Algebra R.carrier k] {Y : Over (AlgebraicGeometry.Spec R)} {ι : Type}
    [Finite ι] {L : LineBundle Y.left ι} [Fact (L.IsProjEmbedding Y.hom)] {A : CommAlg k} {F : Type}
    [Field F] [Algebra k F] {κ : A ⟶ of k F} (hκ : Function.Injective κ) {w : ι → A} {n : ℕ}
    {Λ : Fin (n + 1) → homogeneousSubmodule ι k 1} (hw₁ : evalForms Λ w 0 = 1)
    (h_root : ∀ r : A, r ≠ 0 → ∃ P : Polynomial (MvPolynomial (Fin n) k),
      P.coeff 0 ≠ 0 ∧ P.eval₂ (aeval (R := k) (evalForms Λ w ∘ succ)).toRingHom r = 0)
    {η : PointsIn Y (of k F)} (hη : IsCoordsWithUnit L η (κ ∘ w))
    {V : Subfunctor (algPointsOf k R Y)} (hV : IsOpenSubfunctor V) (hηV : η ∈ V.obj (of k F)) :
    ∃ q : Fin n → k, ∀ K : CommAlg k, IsField K → ∀ (x : PointsIn Y K) (v : ι → K),
      IsHomogeneousSolution k (κ ∘ w) v → evalForms Λ v = structureMap ∘ Fin.cons 1 q →
      IsCoordsWithUnit L x v → x ∈ V.obj K := by
  -- Where some polynomial `b` is a unit, the cone lies in `V`; take a relation `P` of `b(w)`.
  obtain ⟨b, hb, h_unit⟩ := hη.exists_mem_open_of_isUnit hV hηV
  have hbw : aeval w b ≠ 0 := by simpa [← hκ.ne_iff, comp_aeval_apply, comp_def] using hb
  obtain ⟨P, hP₀, hP⟩ := h_root (aeval w b) hbw
  obtain ⟨q, hq⟩ : ∃ q : Fin n → k, MvPolynomial.eval q (P.coeff 0) ≠ 0 := by
    contrapose! hP₀
    exact MvPolynomial.funext (by simpa using hP₀)
  refine ⟨q, fun K hK x v hv hΛv hx ↦ ?_⟩
  let h_field : Field K := hK.toField
  -- Homogenised by `Λ 0`, the relation `P(b)` gives a form `G` with its value wherever `Λ 0` is `1`
  -- (`h_eval`); `G` vanishes at `w`, hence at `v`. If `b` vanished at `v`, so would the constant
  -- term of `P` at `q`.
  obtain ⟨G, hG, h_eval⟩ :=
    exists_homogenization (Λ 0).prop (P.eval₂ (bind₁ (Λ ·.succ)).toRingHom b) le_rfl
  have hGw : aeval w G = 0 := by
    simpa [h_eval, hw₁, P.eval₂_eq_sum_range, aeval_bind₁ w, comp_def, evalForms] using hP
  have hGκw : aeval (κ ∘ w) G = 0 := (IsHomogeneousSolution.refl.map κ.hom') hG hGw
  have hbv : aeval v b ≠ 0 := by
    intro hbv
    have hGv : aeval v G = algebraMap k K (MvPolynomial.eval q (P.coeff 0)) := by
      simp [aeval_bind₁ v, h_eval, hbv, congrFun hΛv, ← comp_def, aeval_algebraMap_apply,
        P.eval₂_eq_sum_range, sum_range_succ']
    exact hq ((map_eq_zero _).mp (hGv.symm.trans (hv hG hGκw)))
  obtain ⟨x', hx'V, hx'⟩ : ∃ z ∈ V.obj K, IsCoordsWithUnit L z v := h_unit hv (.mk0 _ hbv)
  rwa [← hx'.ext hx]

/-- Let `w` be coordinates, with a unit entry, of the point of the chart `c`, and `κ` a map of its
ring to a field. The values `κ r` lie in any intermediate field `M` that contains every `κ (w i)`:
the point of `c` over the field comes from a point of `c` over `M`. -/
lemma New.Variety.EtaleChart.apply_mem_of_coords_mem {k : Type} [Field k] {R : CommRingCat}
    [Algebra R.carrier k] {Y : Over (AlgebraicGeometry.Spec R)} {d : ℕ} {ι : Type} [Finite ι]
    {L : LineBundle Y.left ι} [Fact (L.IsProjEmbedding Y.hom)]
    (c : EtaleChart d (algPointsOf k R Y)) {F : Type} [Field F] [Algebra k F]
      {κ : c.coordRing ⟶ of k F}
    {w : ι → c.coordRing} (hw : IsCoordsWithUnit L c.point w) (M : IntermediateField k F)
    (h_mem : ∀ i : ι, κ (w i) ∈ M) (r : c.coordRing) : κ r ∈ M := by
  have hg : IsCoordsWithUnit L (PointsIn.map κ c.point) (κ ∘ w) := hw.comp κ
  -- Where a polynomial `b`, non-zero at `κ ∘ w`, is a unit, the cone gives points of `c`.
  obtain ⟨b, hb, h_lift⟩ := hg.exists_mem_open_of_isUnit c.isOpenSubfunctor ⟨_, rfl⟩
  -- The coordinates read in `M` lie on the cone and make `b` a unit, so they come from a point `φ`
  -- of `c` over `M`.
  let v : ι → M := fun i ↦ ⟨κ (w i), h_mem i⟩
  have h_unit : IsUnit (aeval v b) := by
    simpa [v, ← map_ne_zero M.val, comp_aeval_apply, comp_def] using hb
  obtain ⟨z, ⟨⟨φ⟩, rfl⟩, hφ⟩ : ∃ z ∈ c.locus.obj (of k M), IsCoordsWithUnit L z v :=
    h_lift (.of_ker M.val 1 (by simp) .refl) h_unit
  -- `φ` followed by `M → F` and `κ` both give the point with coordinates `κ ∘ w`.
  have hφκ : φ ≫ ofHom M.val = κ := c.injective (of k F) <| by
    simp only [Functor.map_comp_apply]
    exact (hφ.comp (ofHom M.val)).ext hg
  rw [← hφκ]
  exact (φ.hom' r).prop

/-- `U` is an étale projection chart for `Λ` on the cone of `g`: its étale coordinates are the
values of `Λ 1`, …, `Λ n`, and it contains the field points of the cone over `[1 : q]`. -/
structure New.Variety.IsEtaleProjection {k : Type} [Field k] {R : CommRingCat} [Algebra R k]
    {Y : Over (AlgebraicGeometry.Spec R)} {ι : Type} [Finite ι] (L : LineBundle Y.left ι)
    {F : Type} [Field F] [Algebra k F] (g : ι → F) {n : ℕ}
    (Λ : Fin (n + 1) → homogeneousSubmodule ι k 1) (U : EtaleChart n (algPointsOf k R Y))
    (w' : ι → U.coordRing) (q : Fin n → k) : Prop where
  /-- `w'` are homogeneous coordinates of the point of `U`, with a unit entry. -/
  isCoordsWithUnit : IsCoordsWithUnit L U.point w'
  /-- `w'` lies on the cone cut out by the homogeneous equations of `g`. -/
  isHomogeneousSolution : IsHomogeneousSolution k g w'
  /-- The form `Λ 0` takes the value `1` at `w'`. -/
  evalForms_zero : evalForms Λ w' 0 = 1
  /-- The étale coordinates of `U` are the values of `Λ 1`, …, `Λ n` at `w'`. -/
  coordinate_eq : U.coordinate = evalForms Λ w' ∘ succ
  /-- `U` contains the field points on the cone of `g` that `Λ` sends to `[1 : q]`. -/
  mem_locus : ∀ K : CommAlg k, IsField K → ∀ (x : PointsIn Y K) (v : ι → K),
    IsHomogeneousSolution k g v → evalForms Λ v = structureMap ∘ Fin.cons 1 q →
    IsCoordsWithUnit L x v → x ∈ U.locus.obj K

/-- Let `k` have characteristic zero and let `Y` over Spec `R` be embedded in projective space by
`L`. Let `c` be an étale chart of `Y` (a `k`-algebra `c.coordRing` with `d` étale coordinates and a
point of `Y` with values in it that embeds Spec `c.coordRing` as an open subfunctor). Let `κ` embed
`c.coordRing` in a field, let `w` be homogeneous coordinates for `L` of the chart's point with some
entry a unit, and let `Λ` be a Noether normalisation of `κ ∘ w` with `Λ 0` equal to `1` at `w`. Then
`n = d`, and there is an `n`-dimensional chart `U` whose étale coordinates are the values of `Λ 1`,
…, `Λ n` (at coordinates `w'` of its point) and which contains the field points of the cone of
`κ ∘ w` over some point `[1 : q]` (`IsEtaleProjection`). -/
lemma New.Variety.exists_etale_projection {k : Type} [Field k] [CharZero k] {R : CommRingCat}
    [Algebra R k] {Y : Over (AlgebraicGeometry.Spec R)} {d : ℕ} {ι : Type} [Finite ι]
    {L : LineBundle Y.left ι} [Fact (L.IsProjEmbedding Y.hom)]
    (c : EtaleChart d (algPointsOf k R Y)) {F : Type} [Field F] [Algebra k F]
    {κ : c.coordRing ⟶ of k F}
    {w : ι → c.coordRing} {n : ℕ} {Λ : Fin (n + 1) → homogeneousSubmodule ι k 1}
    (hκ : Function.Injective κ) (hw : IsCoordsWithUnit L c.point w) (hw₁ : evalForms Λ w 0 = 1)
    (hΛ : IsNoetherNormalization Λ (κ ∘ w)) :
    n = d ∧ ∃ (U : EtaleChart n (algPointsOf k R Y)) (w' : ι → U.coordRing) (q : Fin n → k),
      IsEtaleProjection L (κ ∘ w) Λ U w' q := by
  have h_domain : IsDomain c.coordRing := hκ.isDomain κ.hom'.toRingHom
  -- Make `c.coordRing` an algebra over the polynomial ring `S` by the values of `Λ 1`, …, `Λ n`,
  -- and make `F` an algebra over `c.coordRing` and `S` by `κ`.
  let S : Type := MvPolynomial (Fin n) k
  let y : MvPolynomial (Fin n) k →ₐ[k] c.coordRing := aeval (evalForms Λ w ∘ succ)
  algebraize [y.toRingHom, (κ.hom.comp y).toRingHom, κ.hom'.toRingHom,
    κ.hom'.toRingHom.comp y.toRingHom]
  have h_faithful : FaithfulSMul S c.coordRing :=
    (faithfulSMul_iff_algebraMap_injective S c.coordRing).mpr
      (injective_aeval_of_isNoetherNormalization κ.hom' hw₁ hΛ)
  obtain ⟨-, h_integral⟩ := hΛ
  -- The coordinates are integral over `S`, so `c.coordRing` lands in the algebraic closure `M` of
  -- `S`.
  let M : IntermediateField k F :=
    { (Subalgebra.algebraicClosure S F).restrictScalars k with inv_mem' := fun _ h ↦ h.inv }
  have h_forms : evalForms Λ (κ ∘ w) = (κ.hom.comp y) ∘ cons 1 X := by
    simp [funext_iff, forall_fin_succ, y, hw₁]
  have h_mem (i : ι) : κ (w i) ∈ M := IsIntegral.isAlgebraic (h_integral _ _ _ .refl h_forms i)
  have h_alg : Algebra.IsAlgebraic S c.coordRing :=
    ⟨fun r ↦ (isAlgebraic_algebraMap_iff hκ).mp (c.apply_mem_of_coords_mem hw M h_mem r)⟩
  -- In characteristic zero `c.coordRing` is generically étale over `S`, so it becomes étale after
  -- inverting some `δ ≠ 0`.
  have h_fp : Algebra.FinitePresentation S c.coordRing :=
    .of_restrict_scalars_finitePresentation k ..
  have h_etaleAt : IsEtaleAt S (⊥ : Ideal c.coordRing) := by
    -- The localisation at `⊥` is the fraction field, which is separable over that of `S`.
    change Algebra.FormallyEtale S (Localization (⊥ : Ideal c.coordRing).primeCompl)
    rw [primeCompl_bot]
    exact .comp S (FractionRing S) (FractionRing c.coordRing)
  obtain ⟨δ, hδ, h_etale⟩ : ∃ δ ∉ (⊥ : Ideal c.coordRing), Algebra.Etale S (Localization.Away δ) :=
    exists_etale_of_isEtaleAt ⊥
  let w' : ι → Localization.Away δ := (toAway δ).hom' ∘ w
  have h_etale' : (aeval (R := k) (evalForms Λ w' ∘ succ)).toRingHom.Etale := by
    rw [evalForms_map, Function.comp_assoc, Function.comp_def, ← comp_aeval]
    exact etale_algebraMap.mpr h_etale
  let U : EtaleChart n (algPointsOf k R Y) :=
    { c.away δ with coordinate := evalForms Λ w' ∘ succ, etale := h_etale' }
  obtain ⟨⟨χ⟩, hχ⟩ : PointsIn.map κ c.point ∈ (c.away δ).locus.obj (of k F) :=
    (c.mem_locus_away δ κ).mpr (by simpa using hκ.ne (a₂ := 0) hδ)
  have h_nontrivial : Nontrivial (c.away δ).coordRing := χ.hom'.domain_nontrivial
  -- Both families of coordinates give a basis of the differentials, so `n = d`.
  obtain ⟨b_U⟩ := U.nonempty_basis_kaehler
  obtain ⟨b_c⟩ := (c.away δ).nonempty_basis_kaehler
  have h_dim : n = d := equiv_iff_eq.mp ⟨b_U.indexEquiv b_c⟩
  -- Algebraicity over `S` puts the fibre over a general point `[1 : q]` into `U`.
  have h_root (r : c.coordRing) (hr : r ≠ 0) : ∃ P : Polynomial S, P.coeff 0 ≠ 0 ∧ P.aeval r = 0 :=
    (h_alg.isAlgebraic r).exists_nonzero_coeff_and_aeval_eq_zero (mem_nonZeroDivisors_of_ne_zero hr)
  have h_memU : PointsIn.map κ c.point ∈ U.locus.obj (of k F) := ⟨⟨χ⟩, hχ⟩
  obtain ⟨q, h_fibre⟩ :=
    exists_fibre_mem_of_isOpenSubfunctor hκ hw₁ h_root (hw.comp κ) U.isOpenSubfunctor h_memU
  -- As `κ` is injective, `w` satisfies the equations of `κ ∘ w`.
  have hw_hom : IsHomogeneousSolution k (κ ∘ w) w :=
    .of_ker κ.hom' 1 (fun r hr ↦ (map_eq_zero_iff κ.hom' hκ).mp hr) .refl
  have hw'₁ : evalForms Λ w' 0 = 1 := by rw [evalForms_map, Function.comp_apply, hw₁, map_one]
  exact ⟨h_dim, U, w', q, hw.comp _, hw_hom.map _, hw'₁, rfl, h_fibre⟩

/-- Points on one component have one class. Let `g` be the coordinates of a point `η` over a
field, `k` algebraically closed. Let `z₀` be a `k`-point with coordinates `v₀` on the cone of `g`,
and `y` a `k`-point whose image over a non-zero `k`-algebra `K` has coordinates `v` on that cone.
Then `y` and `z₀` have the same class, since global functions are constant on the cone. -/
lemma New.Variety.pointClass_eq_of_isHomogeneousSolution {k : Type} [Field k] [CharZero k]
    [IsAlgClosed k]
    {R : CommRingCat} [Algebra R.carrier k] {Y : Over (AlgebraicGeometry.Spec R)} {d : ℕ}
    [HasAtlas d (algPointsOf k R Y)] {ι : Type} [Finite ι] {L : LineBundle Y.left ι}
    [Fact (L.IsProjEmbedding Y.hom)] {F : Type} [Field F] [Algebra k F] {η : PointsIn Y (of k F)}
    {g : ι → F} (hg : IsCoordsWithUnit L η g) {z₀ : PointsIn Y (of k k)} {v₀ : ι → k}
    (hz₀ : IsCoordsWithUnit L z₀ v₀) (hv₀ : CutsOutLocus.IsHomogeneousSolution k g v₀)
    {K : CommAlg k} [Nontrivial K] {y : PointsIn Y (of k k)} {v : ι → K}
    (hy : IsCoordsWithUnit L ((algPointsOf k R Y).map structureMap y) v)
    (hv : CutsOutLocus.IsHomogeneousSolution k g v) :
    pointClass (X := algPointsOf k R Y) d y = pointClass (X := algPointsOf k R Y) d z₀ := by
  refine pointClass_eq_of_functions_eq fun f ↦ ?_
  obtain ⟨a, h_const⟩ :
      ∃ a : k, ∀ {A : CommAlg k} [Nontrivial A] {x : PointsIn Y A} {v : ι → A},
        IsCoordsWithUnit L x v →
        CutsOutLocus.IsHomogeneousSolution k g v → (f.app A x).down 0 = algebraMap k A a :=
    hg.exists_app_eq_algebraMap_of_isHomogeneousSolution f
  rw [h_const hz₀ hv₀]
  -- At the image of `y` in `K`, the function takes the image in `K` of its value at `y`.
  have h_y : (structureMap (A := K)).hom' ((f.app (of k k) y).down 0) =
      (structureMap (A := K)).hom' (algebraMap k k a) := by
    simpa using! h_const hy hv
  exact (structureMap (A := K)).hom'.injective h_y

/-- Let `W` be separated and covered by charts of dimension `d`. If `s` is the finite reduced fibre
of `u : W ⟶ X` over the `k`-point `x` (`IsCoincidenceSet` of `u` and the constant map at `x`: the
points of `s` lie over `x`, every field point over `x` comes from `s`, and every `k[ε]`-point over
`x` comes from its `k`-point), then `u` pulls the class of `x` back to the sum of the classes of the
points of `s`. -/
lemma New.Variety.map_pointClass_eq_sum {k : Type} [Field k] [CharZero k] {d : ℕ}
    {W X : CommAlg k ⥤ Type 1} [IsSeparatedFunctor W] [IsChartCovered d W] [HasAtlas d X]
    (x : X.obj (of k k)) (u : W ⟶ X) (s : Finset (W.obj (of k k)))
    (hs : IsCoincidenceSet (constMap x) u s) :
    HodgeH.map (freeAb.map u) (pointClass d x) = ∑ y ∈ s, pointClass d y :=
  map_pointClass_eq_sum_of_isCoincidenceSet u s hs

/-- Let `Γ` be the graph of the projection of `Y` to projective space by the linear forms `Λ`:
the pairs `(x, [Λ(v)])` where `v` are coordinates of `x` with a unit entry and the values `Λ(v)`
generate the unit ideal (`hΓ`). If the first projection `Γ → Y` is a monomorphism, then `Γ` is
covered by charts of the dimension `d` of `Y`. -/
lemma New.Variety.isChartCovered_graph_projection {k : Type} [Field k] [CharZero k]
    {R : CommRingCat} [Algebra R.carrier k] {Y : Over (AlgebraicGeometry.Spec R)} {d n : ℕ}
    [HasAtlas d (algPointsOf k R Y)] {ι : Type} [Finite ι] {L : LineBundle Y.left ι}
    [Fact (L.IsProjEmbedding Y.hom)] {Λ : Fin (n + 1) → homogeneousSubmodule ι k 1}
    {Γ : Subfunctor (algPointsOf k R Y ⊗ projSpace k n)}
    (hΓ : ∀ (A : CommAlg k) (x : (algPointsOf k R Y ⊗ projSpace k n).obj A),
      x ∈ Γ.obj A ↔
        ∃ (v : ι → A) (h : Ideal.span (Set.range (evalForms Λ v)) = ⊤),
          IsCoordsWithUnit L x.1 v ∧ x.2 = projSpace.mk (evalForms Λ v) h)
    [Mono (Γ.ι ≫ fst (algPointsOf k R Y) (projSpace k n))] :
    IsChartCovered d Γ.toFunctor := by
  refine ⟨fun K hK ⟨⟨x, _⟩, hx⟩ ↦ ?_⟩
  obtain ⟨v, h_span, hv, -⟩ := (hΓ K _).mp hx
  let h_field : Field K := hK.toField
  -- Shrink a chart of `Y` at `x` to where some value `g` of `Λ` is a unit.
  obtain ⟨a, ζ, v', rfl, hv'⟩ := exists_chart_coords (d := d) L x hK
  obtain ⟨u, rfl⟩ : ∃ u : Kˣ, u • ζ ∘ v' = v := (hv'.comp ζ).exists_unit_smul_eq hv
  obtain ⟨i, hi⟩ := exists_isUnit_of_span_eq_top h_span
  let g : a.coordRing := evalForms Λ v' i
  have h_unit : IsUnit (evalForms Λ (CommAlg.toAway g ∘ v') i) := by
    rw [show evalForms Λ (CommAlg.toAway g ∘ v') = (toAway g).hom' ∘ evalForms Λ v' from
      evalForms_map Λ (toAway g).hom' v']
    exact (exists_toAway_comp_iff g (toAway g)).mp ⟨𝟙 _, rfl⟩
  -- The chart `a.away g` lifts to `Γ`, and it contains `x` since `ζ g` is a unit.
  refine ⟨(a.away g).comap (Γ.ι ≫ fst (algPointsOf k R Y) (projSpace k n))
      ⟨(_, _), (hΓ ..).mpr ⟨_, span_eq_top_of_isUnit i h_unit, hv'.comp _, rfl⟩⟩ rfl,
    (range_pointMap_eq_preimage_locus _ (Γ.ι ≫ fst (algPointsOf k R Y) (projSpace k n)) rfl).ge _
      ((a.mem_locus_away g ζ).mpr ?_)⟩
  simpa [u.smul_def] using hi

/-- Let `u` and `u'` be maps to a separated `X` and `V` an open subfunctor of `W`. The points `x` of
`W` whose values in fields lie in `V` wherever `u` and `u'` agree (the `fieldLocus` of this
condition: points all of whose images in fields satisfy it) form an open subfunctor. -/
lemma New.Variety.isOpenSubfunctor_fieldLocus_eq_imp_mem {k : Type} [CommRing k]
    {W X : CommAlg k ⥤ Type 1}
    [IsSeparatedFunctor X] (u u' : W ⟶ X) {V : Subfunctor W} (hV : IsOpenSubfunctor V) :
    IsOpenSubfunctor
      (fieldLocus fun (K : CommAlg k) (x : W.obj K) ↦ u.app K x = u'.app K x → x ∈ V.obj K) := by
  refine isOpenSubfunctor_fieldLocus fun A x ↦ ?_
  obtain ⟨J, hJ⟩ : ∃ J : Ideal A, ∀ (B : CommAlg k) (φ : A ⟶ B),
      X.map φ (u.app A x) = X.map φ (u'.app A x) ↔ J ≤ ker φ.hom :=
    IsSeparatedFunctor.exists_ideal A (u.app A x) (u'.app A x)
  obtain ⟨I, hI⟩ : ∃ I : Ideal A, ∀ (B : CommAlg k) (φ : A ⟶ B),
      W.map φ x ∈ V.obj B ↔ I.map φ.hom = ⊤ := hV A x
  -- Over a field: `φ` kills `J` exactly at a coincidence, and does not kill `I` exactly on `V`.
  refine ⟨I ⊔ J, fun K φ hK ↦ ?_⟩
  let h_field : Field K := hK.toField
  have h_coin : u.app K (W.map φ x) = u'.app K (W.map φ x) ↔ J ≤ ker φ.hom := by
    rw [u.naturality_apply, u'.naturality_apply]
    exact hJ K φ
  have h_mem : W.map φ x ∈ V.obj K ↔ ¬I ≤ ker φ.hom := by
    rw [hI K φ, ← isAtom_top.ne_bot_iff_eq le_top, Ne, I.map_eq_bot_iff_le_ker]
  rw [h_coin, h_mem, sup_le_iff, not_and]
  exact imp_not_comm

/-- A point `x` with coordinates `v` on the cone of `g`, the coordinates of a field point `η`,
avoids the `k`-points of `T` whose class differs from that of `z₀`, if `z₀` has coordinates `v₀` on
that cone: no value of `x` in a field comes from such a point. -/
lemma New.Variety.mem_offPoints_of_isHomogeneousSolution {k : Type} [Field k] [CharZero k]
    [IsAlgClosed k] {R : CommRingCat} [Algebra R.carrier k] {Y : Over (AlgebraicGeometry.Spec R)}
    {d : ℕ} [HasAtlas d (algPointsOf k R Y)] {ι : Type} [Finite ι] {L : LineBundle Y.left ι}
    [Fact (L.IsProjEmbedding Y.hom)] {F : Type} [Field F] [Algebra k F] {η : PointsIn Y (of k F)}
    {g : ι → F} (hg : IsCoordsWithUnit L η g) {z₀ : PointsIn Y (of k k)} {v₀ : ι → k}
    (hz₀ : IsCoordsWithUnit L z₀ v₀) (hv₀ : CutsOutLocus.IsHomogeneousSolution k g v₀)
    {A : CommAlg k} {x : PointsIn Y A} {v : ι → A} (hx : IsCoordsWithUnit L x v)
    (hv : CutsOutLocus.IsHomogeneousSolution k g v) (T : Set (PointsIn Y (of k k))) :
    x ∈ (offPoints (T \ pointClass d ⁻¹' {pointClass d z₀})).obj A := by
  rintro K φ hK ⟨y, ⟨-, hy_class⟩, hxy⟩
  let h_field : Field K := hK.toField
  have hy_coords : IsCoordsWithUnit L ((algPointsOf k R Y).map structureMap y) (φ ∘ v) := by
    rw [← hxy]
    exact hx.comp φ
  exact hy_class (pointClass_eq_of_isHomogeneousSolution hg hz₀ hv₀ hy_coords (hv.map φ.hom'))

/-- Pull-back along a map `u` injective on points sends the class of `x` to the sum of the classes
of the points of `s`, if `u` sends the points of `s` to `x` and every field point over `x` comes
from a point of `s`. -/
lemma New.Variety.map_pointClass_eq_sum_of_injective {k : Type} [Field k] [CharZero k] {d : ℕ}
    {W X : CommAlg k ⥤ Type 1} [IsSeparatedFunctor W] [IsChartCovered d W] [HasAtlas d X]
    (x : X.obj (of k k)) (u : W ⟶ X) (hu : ∀ A : CommAlg k, Function.Injective (u.app A))
    (s : Finset (W.obj (of k k))) (hs_mem : ∀ y ∈ s, u.app (of k k) y = (constMap x).app (of k k) y)
    (hs_all : ∀ K : CommAlg k, IsField K → ∀ y : W.obj K,
      u.app K y = (constMap x).app K y → ∃ y₀ ∈ s, y = W.map structureMap y₀) :
    HodgeH.map (freeAb.map u) (pointClass d x) = ∑ y ∈ s, pointClass d y := by
  -- The fibres of `u` are reduced, as `u` is injective on `k[ε]`-points.
  refine map_pointClass_eq_sum x u s ⟨fun y h_coin ↦ hu _ ?_, hs_mem, hs_all⟩
  rw [u.naturality_apply, h_coin]
  exact (map_map_structureMap _ x).symm

/-- Pull-back along a map `u` that is injective on points sends the class of the image `u y` of a
`k`-point `y` to the class of `y`. -/
lemma New.Variety.map_pointClass_app_of_injective {k : Type} [Field k] [CharZero k] {d : ℕ}
    {W X : CommAlg k ⥤ Type 1} [IsSeparatedFunctor W] [IsChartCovered d W] [HasAtlas d X]
    (u : W ⟶ X) (hu : ∀ A : CommAlg k, Function.Injective (u.app A)) (y : W.obj (of k k)) :
    HodgeH.map (freeAb.map u) (pointClass d (u.app (of k k) y)) = pointClass d y := by
  have h_fibre : ∀ K : CommAlg k, IsField K → ∀ y' : W.obj K,
      u.app K y' = (constMap (u.app (of k k) y)).app K y' →
      ∃ y₀ ∈ ({y} : Finset (W.obj (of k k))), y' = W.map structureMap y₀ := by
    intro K hK y' hy'
    refine ⟨y, Finset.mem_singleton_self y, hu K ?_⟩
    rw [hy', u.naturality_apply]
    rfl
  rw [map_pointClass_eq_sum_of_injective _ u hu {y} (by simp [constMap]) h_fibre, sum_singleton]

/-- Pull-back along a map `u` that is injective on points kills the class of a `k`-point `z` over
which `u` has no field point. -/
lemma New.Variety.map_pointClass_eq_zero_of_injective {k : Type} [Field k] [CharZero k] {d : ℕ}
    {W X : CommAlg k ⥤ Type 1} [IsSeparatedFunctor W] [IsChartCovered d W] [HasAtlas d X]
    (u : W ⟶ X) (hu : ∀ A : CommAlg k, Function.Injective (u.app A)) (z : X.obj (of k k))
    (h_none : ∀ K : CommAlg k, IsField K → ∀ y : W.obj K, u.app K y ≠ (constMap z).app K y) :
    HodgeH.map (freeAb.map u) (pointClass d z) = 0 := by
  simpa using map_pointClass_eq_sum_of_injective z u hu ∅ (by simp)
    fun K hK y hy ↦ absurd hy (h_none K hK y)

/-- Let `O` be separated and covered by charts of dimension `n`, with a map `proj` to projective
space `ℙⁿ` such that pull-back along `proj` is injective on the `genericCoeff` classes of degree
`n + n` (`h_inj`). If the fibre of `proj` over a `k`-point `Q` is a finite reduced set `t` of points
whose classes all equal `c`, then the Hodge–Tate map does not kill `c`. -/
lemma New.Variety.hodgeTateMap_ne_zero_of_isCoincidenceSet {p : ℕ} {k : Type} [Field k]
    [EmbeddedInQpBar p k] {n : ℕ} {O : CommAlg k ⥤ Type 1} [IsSeparatedFunctor O]
    [IsChartCovered n O] (proj : O ⟶ projSpace k n)
    (h_inj : Function.Injective
      (H.map genericCoeff (genericOver.whiskerLeft (freeAb.map proj)) (n + n)))
    (Q : (projSpace k n).obj (of k k)) (t : Finset (O.obj (of k k)))
    (ht : IsCoincidenceSet (constMap Q) proj t) (c : HodgeH (freeAb.obj O) n)
    (h_class : ∀ y ∈ t, pointClass n y = c) :
    hodgeTateMap n c ≠ 0 := by
  intro h_zero
  -- The Hodge–Tate image of the class of `Q` is `restrictToPairs η`. Its pull-back along `proj` is
  -- the sum over `t` of `hodgeTateMap n c`, which is zero; so `η = 0`, against the non-vanishing
  -- on `ℙⁿ`.
  obtain ⟨η, hη⟩ := IsChartCovered.pairRestrictBijective.exists_hodgeTateMap_eq n (pointClass n Q)
  have h_sum : hodgeTateMap n (∑ y ∈ t, pointClass n y) = 0 := by
    simp [sum_congr rfl h_class, h_zero]
  have hη₀ : η = 0 := by
    refine h_inj (IsChartCovered.pairRestrictBijective.injective_restrictToPairs ?_)
    rw [restrictToPairs_map, ← hη, ← hodgeTateMap_map, map_pointClass_eq_sum Q proj t ht, h_sum,
      map_zero, map_zero]
  exact hodgeTateMap_pointClass_ne_zero Q (by rw [hη, hη₀, map_zero])

/-- A functor with a map `j` to a separated functor `X` that is injective on points is separated. -/
lemma New.Variety.isSeparatedFunctor_of_injective {k : Type} [CommRing k] {W X : CommAlg k ⥤ Type 1}
    [hX : IsSeparatedFunctor X] (j : W ⟶ X) (hj : ∀ A : CommAlg k, Function.Injective (j.app A)) :
    IsSeparatedFunctor W :=
  ⟨fun A y y' ↦ by
    simpa only [← (hj _).eq_iff, j.naturality_apply] using
      hX.exists_ideal A (j.app A y) (j.app A y')⟩

/-- Let `k` be algebraically closed of characteristic zero with an embedding in Q̄_p, and let `Y` be
a scheme over Spec `R`, embedded in projective space by `L` and having an atlas of étale charts of
dimension `d`. Let `pointClass d z` denote the class of a `k`-point `z` of `Y` in degree-`d` Hodge
cohomology. Then for a `k`-point `z₀` and a finite set `T` of `k`-points, there are a functor `W`
from `k`-algebras to sets and a map `j : W ⟶ Y` with two properties: pull-back along `j` kills the
class of every point of `T` whose class differs from that of `z₀`, and the Hodge–Tate map
`hodgeTateMap d` does not kill the pull-back of the class of `z₀`. -/
lemma New.Variety.exists_map_separating_class {p : ℕ} {k : Type} [Field k] [EmbeddedInQpBar p k]
    [IsAlgClosed k] {R : CommRingCat} [Algebra R.carrier k] {Y : Over (AlgebraicGeometry.Spec R)}
    {d : ℕ} [HasAtlas d (algPointsOf k R Y)] {ι : Type} [Finite ι] (L : LineBundle Y.left ι)
    [Fact (L.IsProjEmbedding Y.hom)] (z₀ : PointsIn Y (of k k)) {T : Set (PointsIn Y (of k k))}
    (hT : T.Finite) :
    ∃ (W : CommAlg k ⥤ Type 1) (j : W ⟶ algPointsOf k R Y),
      hodgeTateMap d (HodgeH.map (freeAb.map j) (pointClass d z₀)) ≠ 0 ∧
      ∀ z ∈ T,
        pointClass d z ≠ pointClass d z₀ → HodgeH.map (freeAb.map j) (pointClass d z) = 0 := by
  -- Project the component of `z₀` by a Noether normalisation `Λ`. Over a point `Q` the class of
  -- `Q` pulls back to points with the class of `z₀`; pull-back along the projection is injective.
  obtain ⟨c, F, _, _, κ, w₀, n, Λ, v₀, ⟨hκ, hw₀, hw₀₁, hΛ, hz₀, hv₀⟩⟩ :=
    exists_generic_chart (d := d) L z₀
  obtain ⟨rfl, U, w, q, hw, hw_hom, hw₁, hU, h_fibre⟩ := exists_etale_projection c hκ hw₀ hw₀₁ hΛ
  have hg : IsCoordsWithUnit L (PointsIn.map κ c.point) (κ ∘ w₀) := hw₀.comp κ
  let Q : (projSpace k n).obj (of k k) := projSpace.affinePoint 0 q
  -- `Γ` is the graph of the projection; its first projection `π` is injective.
  let Γ : Subfunctor (algPointsOf k R Y ⊗ projSpace k n) :=
    ⟨fun _ x ↦ ∃ v h, IsCoordsWithUnit L x.1 v ∧ x.2 = projSpace.mk (evalForms Λ v) h,
      fun φ _ ⟨v, _, hv, e⟩ ↦ ⟨φ ∘ v, evalForms_map Λ φ.hom' _ ▸ ⟨_, hv.comp φ, congrArg _ e⟩⟩⟩
  let π : Γ.toFunctor ⟶ algPointsOf k R Y := Γ.ι ≫ fst (algPointsOf k R Y) (projSpace k n)
  have h_mono : Mono π := mono_of_app_injective <| by
    rintro A ⟨⟨⟩, v, _, hv, ⟨⟩⟩ ⟨⟨⟩, v', _, hv', ⟨⟩⟩ ⟨⟩
    obtain ⟨u, rfl⟩ : ∃ u : Aˣ, u • v = v' := hv.exists_unit_smul_eq hv'
    congrm ⟨(_, $(mk_eq_mk_iff_exists_unit.mpr ⟨u, (evalForms_smul _).symm⟩)), _⟩
  -- `O` is `Γ` without the points of `T` of another class and the points over `Q` outside `U`.
  let O : Subfunctor Γ.toFunctor :=
    (offPoints (T \ pointClass n ⁻¹' {pointClass n z₀})).preimage π ⊓
      fieldLocus fun K x ↦ (constMap Q).app K x = x.val.2 → x.val.1 ∈ U.locus.obj K
  let j : O.toFunctor ⟶ algPointsOf k R Y := O.ι ≫ π
  have hj (A : CommAlg k) : Function.Injective (j.app A) := injective_of_mono _
  have hΓ : IsChartCovered n Γ.toFunctor := isChartCovered_graph_projection fun _ _ ↦ .rfl
  -- `O` is open in `Γ`, as `T` is finite, projective space is separated and `U` is open.
  have h_open : IsOpenSubfunctor (Subfunctor.range O.ι) := by
    rw [O.range_ι]
    have h_finite : _root_.Finite ↑(T \ pointClass n ⁻¹' {pointClass n z₀}) := hT.sdiff
    exact .inf (isOpenSubfunctor_offPoints.preimage _)
      (isOpenSubfunctor_fieldLocus_eq_imp_mem (constMap Q)
        (Γ.ι ≫ SemiCartesianMonoidalCategory.snd (algPointsOf k R Y) (projSpace k n))
        (U.isOpenSubfunctor.preimage π))
  have hO : IsChartCovered n O.toFunctor := IsChartCovered.comap O.ι h_open
  -- `U` is also a chart `C` of `O`, and it contains all points of `O` over `Q`.
  let C : EtaleChart n O.toFunctor :=
    U.comap j ⟨⟨(_, _), _, span_eq_top_of_isUnit 0 (by simp [hw₁]), hw, rfl⟩,
      mem_offPoints_of_isHomogeneousSolution hg hz₀ hv₀ hw hw_hom T,
      fun _ φ _ _ ↦ ⟨⟨φ⟩, rfl⟩⟩ rfl
  have h_over {A : CommAlg k} {y : O.toFunctor.obj A}
      (hy : y.val.val.2 = (projSpace k n).map structureMap Q) : y ∈ C.locus.obj A :=
    (U.range_pointMap_eq_preimage_locus j rfl).ge _ <|
      U.isOpenSubfunctor.fieldLocus_le _ fun K φ hK ↦
      y.prop.2 K φ hK (show (projSpace k n).map structureMap Q = (projSpace k n).map φ y.val.val.2
        by rw [hy, map_map_structureMap])
  -- The fibre over `Q` is finite and reduced: a tangent vector in it fixes the coordinates of `U`.
  let proj : O.toFunctor ⟶ projSpace k n :=
    O.ι ≫ Γ.ι ≫ SemiCartesianMonoidalCategory.snd (algPointsOf k R Y) (projSpace k n)
  obtain ⟨t, ht⟩ :
      ∃ t : Finset (O.toFunctor.obj (of k k)), IsCoincidenceSet (constMap Q) proj t := by
    refine exists_isCoincidenceSet _ _ (fun y hy ↦ ?_) ![C] fun _ _ _ hy ↦ ⟨0, h_over hy⟩
    obtain ⟨⟨ψ : U.coordRing ⟶ _⟩, ⟨⟩⟩ : y ∈ C.locus.obj (of k (DualNumber k)) := h_over hy
    have hψ : (ψ ≫ SqZeroExt.fst) ≫ structureMap = ψ := by
      refine U.lift_unique (π := SqZeroExt.fst) fst_surjective_and_kerIdeal_sq_eq_bot (by rfl)
        fun i ↦ ?_
      have h_coord := mk_eq_mk_iff_cross_mul (v := ψ ∘ _).mp hy i.succ 0
      simp [hw₁, hU] at h_coord ⊢
      erw [h_coord]
      rfl
    erw [← Functor.map_comp_apply, hψ]
    rfl
  have h_sep : IsSeparatedFunctor O.toFunctor := isSeparatedFunctor_of_injective j hj
  -- Pull-back along `proj` is injective, by the Noether normalisation `Λ`.
  have h_inj :
      Function.Injective
        (H.map genericCoeff (genericOver.whiskerLeft (freeAb.map proj)) (n + n)) :=
    hΛ.pullback_injective hg (O := O) fun hv hx ↦
      ⟨⟨_, _, hx, rfl⟩, mem_offPoints_of_isHomogeneousSolution hg hz₀ hv₀ hx hv _, fun K φ hK e ↦ by
        obtain ⟨u, hu⟩ := mk_eq_mk_iff_exists_unit.mp e.symm
        exact h_fibre K hK _ _ (hv.smul _ _) (by simpa using! hu) (hx.map_unit_smul φ u)⟩
  refine ⟨O.toFunctor, j, ?_, fun z hz h_ne ↦ ?_⟩
  · -- A point `y` of `t` lies in `U`, so `j y` has the class of `z₀`. The fibre of `j` over
    -- `j y` is `{y}`, so the class of `y` is the pull-back of the class of `z₀`.
    refine hodgeTateMap_ne_zero_of_isCoincidenceSet proj h_inj Q t ht _ fun y hy ↦ ?_
    obtain ⟨-, h_t_mem, -⟩ := ht
    obtain ⟨ζ, hζ⟩ : y ∈ C.locus.obj (of k k) := h_over (h_t_mem y hy)
    -- `ζ` sends the point of `U` to `j y`, so `j y` avoids the points of another class.
    have h_point : (algPointsOf k R Y).map ζ.down U.point =
        (algPointsOf k R Y).map structureMap (j.app (of k k) y) := by
      simp [← hζ]
      rfl
    have h_eq : pointClass n (j.app (of k k) y) = pointClass n z₀ := by
      by_contra h_ne
      exact mem_offPoints_of_isHomogeneousSolution hg hz₀ hv₀ hw hw_hom {j.app _ y} _ ζ.down
        (toIsField k) ⟨_, ⟨rfl, h_ne⟩, h_point⟩
    rw [← h_eq, map_pointClass_app_of_injective j hj y]
  · -- No point of `O` lies over `z`, as `O` avoids the points of `T` of another class.
    refine map_pointClass_eq_zero_of_injective j hj z fun K hK y hy ↦ ?_
    obtain ⟨h_off, -⟩ := y.prop
    exact (mem_offPoints_iff hK).mp h_off ⟨z, ⟨hz, h_ne⟩, hy⟩

/-- Let `k` be an algebraically closed field with a map to `Q̄_p` and `Y` a projectively embedded
scheme over `R` whose points in `k`-algebras have an atlas of dimension `d`. Then the Hodge–Tate
map of weight `d` sends the distinct classes of `k`-points to linearly independent elements. -/
lemma New.Variety.linearIndepOn_hodgeTateMap_pointClass {p : ℕ} {k : Type} [Field k]
    [EmbeddedInQpBar p k] [IsAlgClosed k] {R : CommRingCat} [Algebra R.carrier k]
    {Y : Over (AlgebraicGeometry.Spec R)} {d : ℕ} [hX : HasAtlas d (algPointsOf k R Y)]
    (hE : HasProjEmbedding Y.hom) :
    LinearIndepOn k (hodgeTateMap d) (Set.range (pointClass (X := algPointsOf k R Y) d)) := by
  obtain @⟨ι, L, h_finite, hL⟩ := hE
  have h_fact : Fact (L.IsProjEmbedding Y.hom) := ⟨hL⟩
  -- Suppose that the image of the class of `z` is a combination of the images of other classes.
  simp_rw [linearIndepOn_iff_notMem_span, ← Set.image_compl_preimage, Set.image_image,
    mem_span_image_iff_exists_fun]
  rintro _ ⟨z, rfl⟩ ⟨t, ht, n, h_sum⟩
  -- Pull the relation `h_sum` back along `j`: its left side dies, its right side does not.
  obtain ⟨W, j, h_ne, h_kill⟩ := exists_map_separating_class (d := d) L z t.finite_toSet
  have h_zero (i : t) : HodgeH.map (freeAb.map j) (pointClass d i.val) = 0 :=
    h_kill i i.prop (ht i.prop)
  have h_pull : PairH.map (freeAb.map j) (hodgeTateMap d (pointClass d z)) = 0 := by
    simp [← h_sum, ← hodgeTateMap_map, h_zero]
  exact h_ne ((hodgeTateMap_map ..).trans h_pull)
