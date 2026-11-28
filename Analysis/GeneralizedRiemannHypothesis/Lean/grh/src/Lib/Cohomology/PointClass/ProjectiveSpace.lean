import Lib.Cohomology.PointClass.NoetherNormalization
import Lib.PadicComparison.Primitive.PeriodCoefficients

/-!
# Projective space as a functor, and injective pull-back along Noether normalisation

Projective space `ℙ^d` over a field `k` is defined as a functor on `k`-algebras. It is the test
variety on which the Hodge–Tate map is shown not to kill the class of a point.

## Main definitions and results

* `New.Variety.projSpace`: `A ↦` unimodular vectors in `A ^ (d + 1)` modulo units of `A`.
* `New.Variety.projSpace.stdChart`, `New.Variety.projSpace.hasAtlas`: the `d + 1` standard charts
  form an atlas.
* `New.Variety.projSpace.lineProductMap`: a map `ℙ^d × ℙ¹ → ℙ^(d+1)`, used for induction on the
  dimension; `New.Variety.projSpace.isUnit_mul_sum_of_mul_eq_zero` and
  `New.Variety.projSpace.exists_eq_map_affinePoint_of_mul_eq_zero` describe the points where all
  its coordinates but the first vanish.
* `New.Variety.CutsOutLocus.IsNoetherNormalization.pullback_injective`: pull-back along the
  projection to `ℙ^d` of a subfunctor of `Y × ℙ^d` that contains the graph of a Noether
  normalisation is injective on cohomology of `p`-adic tests.

Notions from other files:
* `New.Variety.unimodular`: the subfunctor of affine `d`-space of vectors whose entries generate
  the unit ideal.
* `New.Variety.IsCoordsWithUnit L x v`: `v` is a vector of homogeneous coordinates, for the line
  bundle `L`, of the point `x` of `Y`, and some entry of `v` is a unit.
* `New.Variety.CutsOutLocus.IsHomogeneousSolution k g v`: every homogeneous polynomial over `k` that
  vanishes at `g` vanishes at `v`.
* `New.Variety.CutsOutLocus.IsNoetherNormalization Λ g`: the values at `g` of the linear forms
  `Λ 0, …, Λ d` satisfy no non-zero homogeneous relation, and the cone of `g` is integral over them.
* `New.Variety.IsTest`: a test ring: reduced, absolutely integrally closed, and any `a`, `b`
  admit an idempotent `e` with `a ∣ e * b` and `b ∣ (1 - e) * a`.

## Relation to the literature

Known; see `Lib.Cohomology.PointClass.LinearIndependence` for sources.
-/

noncomputable section

/-! ## Projective space as a functor, standard charts and a product map -/

section ProjectiveSpace

open CategoryTheory CommAlgCat Fin Ideal IsLocalRing MvPolynomial MonoidalCategory Subfunctor Set

variable (k : Type) [Field k] (d : ℕ)

/-! ### Points of projective space -/

/-- Projective `d`-space over `k`: the functor sending `A` to the unimodular vectors in
`A ^ (d + 1)` modulo units of `A`. These are the points of the scheme `ℙ^d` whose line bundle is
trivial; no sheafification is made. -/
def New.Variety.projSpace : CommAlg k ⥤ Type 1 where
  -- Unimodular vectors of length `d + 1`, up to scaling by a unit.
  obj A := Quot ((MulAction.orbitRel Aˣ (Fin (d + 1) → A)).comap
    (·.1.1 : @unimodular k _ (d + 1) A → Fin (d + 1) → A))
  -- Vectors that differ by the unit `u` are sent to vectors that differ by the unit `f u`.
  map f := ↾Quot.map (unimodular.toFunctor.map f) fun _ _ ⟨u, h⟩ ↦ ⟨u.map _, by
    simpa [Units.smul_def, _root_.funext_iff] using! congr(f ∘ $h)⟩
  map_id _ := by
    ext ⟨⟩
    rfl
  map_comp _ _ := by
    ext ⟨⟩
    rfl

namespace New.Variety.projSpace

variable {k d} {A : CommAlg k} {v w : Fin (d + 1) → A} (i : Fin (d + 1))

/-- Over a local ring `A`, a vector whose entries generate the unit ideal has a unit entry. -/
lemma exists_isUnit_of_span_eq_top [IsLocalRing A] (hv : span (Set.range v) = ⊤) :
    ∃ i : Fin (d + 1), IsUnit (v i) := by
  -- Otherwise all entries lie in the maximal ideal, and so does the unit ideal.
  by_contra h_none
  have h_le : span (Set.range v) ≤ maximalIdeal A := by
    simpa [span_le, range_subset_iff] using h_none
  exact (maximalIdeal.isMaximal A).ne_top (eq_top_mono h_le hv)

/-- For `v` in `A ^ (d + 1)` whose entries generate the unit ideal (`h`), the point
`[v 0 : … : v d]` of projective `d`-space. -/
def mk (v : Fin (d + 1) → A) (h : span (Set.range v) = ⊤) : projSpace k d A :=
  Quot.mk _ ⟨{ down := v }, h⟩

/-- The points `[v]` and `[w]` of projective `d`-space agree iff `u • v = w` for a unit `u` of
`A`. -/
lemma mk_eq_mk_iff_exists_unit {hv : span (Set.range v) = ⊤} {hw : span (Set.range w) = ⊤} :
    mk v hv = mk w hw ↔ ∃ u : Aˣ, u • v = w :=
  eq_comm.trans Quotient.eq

/-- For unimodular vectors `v` and `w` in `A ^ (d + 1)`, the points `[v]` and `[w]` of projective
`d`-space are equal iff `v a * w b = w a * v b` for all indices `a` and `b`. In other words, all
2 × 2 minors of the matrix with rows `v` and `w` vanish. -/
lemma mk_eq_mk_iff_cross_mul {hv : span (Set.range v) = ⊤} {hw : span (Set.range w) = ⊤} :
    mk v hv = mk w hw ↔ ∀ a b : Fin (d + 1), v a * w b = w a * v b := by
  rw [mk_eq_mk_iff_exists_unit]
  refine ⟨fun ⟨u, hu⟩ a b ↦ ?_, fun h_minor ↦ ?_⟩
  · simp [← hu, Units.smul_def, mul_assoc, mul_left_comm]
  · -- Write `1 = ∑ i, a i * v i`; the factor of proportionality is `c = ∑ i, a i * w i`.
    obtain ⟨a, ha⟩ : ∃ a : Fin (d + 1) → A, ∑ i, a i * v i = 1 :=
      mem_span_range_iff_exists_fun.mp ((eq_top_iff_one _).mp hv)
    set c : A := ∑ i, a i * w i with hc
    have h_prop (l : Fin (d + 1)) : c * v l = w l :=
      calc c * v l = (∑ i, a i * v i) * w l := by simp only [hc, Finset.sum_mul, mul_assoc, h_minor]
        _ = w l := by rw [ha, one_mul]
    -- `c` divides every entry of the unimodular vector `w`, so it is a unit.
    have h_le : span (Set.range w) ≤ span {c} :=
      span_le.mpr (range_subset_iff.mpr fun l ↦ mem_span_singleton.mpr (Dvd.intro _ (h_prop l)))
    have hc_unit : IsUnit c := span_singleton_eq_top.mp (eq_top_mono h_le hw)
    exact ⟨hc_unit.unit, funext h_prop⟩

/-- For `v` in `A ^ d`, the point of projective `d`-space with coordinate `1` in place `i` and the
entries of `v` in the other places. -/
abbrev affinePoint (v : Fin d → A) : projSpace k d A :=
  mk (i.insertNth 1 v) (span_eq_top_of_isUnit i (by simp))

/-- The point `[v]` lies in the image of the `i`-th standard chart iff `v i` is a unit. The chart
is the point over the polynomial ring with coordinate `1` in place `i` and the variables in
the other places. -/
lemma mk_mem_stdChart_iff {hv : span (Set.range v) = ⊤} :
    mk v hv ∈ Subfunctor.range (pointMap (affinePoint (A := of k (MvPolynomial (Fin d) k)) i X)) A ↔
      IsUnit (v i) := by
  refine ⟨fun ⟨φ, hφ⟩ ↦ ?_, fun ⟨u, hu⟩ ↦ ?_⟩
  · -- A point of the chart has a representative with `i`-th entry `1`, and `v` is `u` times it.
    obtain ⟨u, hu⟩ :
        ∃ u : Aˣ, u • (φ.down.hom ∘ (i.insertNth 1 X : Fin (d + 1) → MvPolynomial (Fin d) k)) = v :=
      mk_eq_mk_iff_exists_unit.mp hφ
    have h_vi : v i = u := by simp [← hu, Units.smul_def]
    simp [h_vi]
  · -- If `v i = u` is a unit, the affine coordinates are the other entries divided by `u`.
    let φ : of k (MvPolynomial (Fin d) k) ⟶ A := ofHom (aeval (u⁻¹ • v ∘ i.succAbove))
    refine ⟨⟨φ⟩, mk_eq_mk_iff_exists_unit.mpr ⟨u, ?_⟩⟩
    simp [φ, i.forall_iff_succAbove, ← hu, Units.smul_def, _root_.funext_iff]

/-- The image of the point `[v]` under a map `f` of `k`-algebras is `[f ∘ v]`. -/
private lemma map_mk {B : CommAlg k} (f : A ⟶ B) (hv : span (Set.range v) = ⊤) :
    (projSpace k d).map f (mk v hv) = mk (f ∘ v) (unimodular.map f (a := ⟨v⟩) hv) :=
  rfl

/-! ### The map `ℙ^d × ℙ¹ → ℙ^(d+1)` -/

/-- Let `v`, `u` be unimodular vectors over a local algebra over a field of characteristic `0`, with
`(u 1 - i * u 0) * v i = 0` for all `i`. Then for some `j`, `v j` and `u 0` are units,
`j * u 0 = u 1`, and `v i = 0` for `i ≠ j`. -/
private lemma exists_isUnit_coord_of_mul_eq_zero [CharZero k] [IsLocalRing A] {u : Fin 2 → A}
    (hv : span (Set.range v) = ⊤) (hu : span (Set.range u) = ⊤)
    (h_mul_eq_zero : ∀ i : Fin (d + 1), (u 1 - i * u 0) * v i = 0) :
    ∃ j : Fin (d + 1), IsUnit (v j) ∧ IsUnit (u 0) ∧ j * u 0 = u 1 ∧ ∀ i ≠ j, v i = 0 := by
  -- In a local ring some coordinate `v j` is a unit, which forces `u = [1 : j]`.
  -- As `i - j` is invertible in `k` for `i ≠ j`, all other `v i` vanish.
  obtain ⟨j, hj⟩ := exists_isUnit_of_span_eq_top hv
  have hu1 : j * u 0 = u 1 := (sub_eq_zero.mp (hj.mul_left_eq_zero.mp (h_mul_eq_zero j))).symm
  -- `u 0` divides `u 1 = j * u 0`, so it generates the unit ideal.
  have h_le : span (Set.range u) ≤ span {u 0} := by
    simp [span_le, range_subset_iff, mem_span_singleton, ← hu1]
  have hu0 : IsUnit (u 0) := span_singleton_eq_top.mp (eq_top_mono h_le hu)
  refine ⟨j, hj, hu0, hu1, fun i hij ↦ by_contra fun hi ↦ hij ?_⟩
  -- Put `u 1 = j * u 0` in `h_mul_eq_zero i`; cancel the unit `u 0` and the nonzero `v i`.
  have h_mul : u 0 * ((i : k) • v i) = u 0 * ((j : k) • v i) := by grind [Nat.cast_smul_eq_nsmul]
  have h_cast : (i : k) = j := smul_left_injective k hi (hu0.mul_left_cancel h_mul)
  exact Fin.ext (Nat.cast_injective h_cast)

/-- Let `v`, `u` be unimodular vectors over a local algebra over a field of characteristic `0`,
of lengths `d + 1` and `2`, with `(u 1 - i * u 0) * v i = 0` for all `i`. Then the first
coordinate `u 0 * ∑ i, v i` of `New.Variety.projSpace.lineProductMap` at `([v], [u])` is a unit. -/
lemma isUnit_mul_sum_of_mul_eq_zero [CharZero k] [IsLocalRing A] {u : Fin 2 → A}
    (hv : span (Set.range v) = ⊤) (hu : span (Set.range u) = ⊤)
    (h_mul_eq_zero : ∀ i : Fin (d + 1), (u 1 - i * u 0) * v i = 0) :
    IsUnit (u 0 * ∑ i : Fin (d + 1), v i) := by
  -- The sum is `v j`, as the other entries vanish.
  obtain ⟨j, hj, hu0, -, h_zero⟩ := exists_isUnit_coord_of_mul_eq_zero hv hu h_mul_eq_zero
  simpa only [Fintype.sum_eq_single j h_zero] using hu0.mul hj

/-- Let `v`, `u` be unimodular vectors over a local algebra over a field of characteristic `0`, with
`(u 1 - i * u 0) * v i = 0` for all `i`. Then, with the points `affinePoint` taken over `k` and
carried to `A` by `structureMap` (the map `k → A`), for some `j` the point `[v]` is the `j`-th
coordinate point and `[u] = [1 : j]`. -/
lemma exists_eq_map_affinePoint_of_mul_eq_zero [CharZero k] [IsLocalRing A] {u : Fin 2 → A}
    (hv : span (Set.range v) = ⊤) (hu : span (Set.range u) = ⊤)
    (h_mul_eq_zero : ∀ i : Fin (d + 1), (u 1 - i * u 0) * v i = 0) :
    ∃ j : Fin (d + 1),
      (mk v hv, mk u hu) =
        (projSpace k d ⊗ projSpace k 1).map structureMap (affinePoint j 0, affinePoint 0 ![j]) := by
  obtain ⟨j, hj, hu0, hu1, h_zero⟩ := exists_isUnit_coord_of_mul_eq_zero hv hu h_mul_eq_zero
  refine ⟨j, Prod.ext ?_ ?_⟩
  · -- `v` is `v j` times the `j`-th coordinate vector, as its other entries vanish.
    show mk v hv = (projSpace k d).map structureMap (affinePoint j 0)
    rw [map_mk]
    refine (mk_eq_mk_iff_exists_unit.mpr ⟨hj.unit, ?_⟩).symm
    simp [_root_.funext_iff, j.forall_iff_succAbove, h_zero]
  · -- `u` is `u 0` times `(1, j)`.
    show mk u hu = (projSpace k 1).map structureMap (affinePoint 0 ![j])
    rw [map_mk]
    refine (mk_eq_mk_iff_exists_unit.mpr ⟨hu0.unit, ?_⟩).symm
    simp [_root_.funext_iff, ← hu1, mul_comm]

/-- Let `v`, `u` be unimodular vectors over a local algebra over a field of characteristic `0`, with
`(u 1 - i * u 0) * v i = 0` for all `i`. Then `u 0 * ∑ i, v i` is a unit, and for some `j` the point
`[v]` is the `j`-th coordinate point and `[u] = [1 : j]`. -/
lemma isUnit_and_exists_eq_affinePoint_of_mul_eq_zero [CharZero k] [IsLocalRing A] {u : Fin 2 → A}
    (hv : span (Set.range v) = ⊤) (hu : span (Set.range u) = ⊤)
    (h_mul_eq_zero : ∀ i : Fin (d + 1), (u 1 - i * u 0) * v i = 0) :
    IsUnit (u 0 * ∑ i : Fin (d + 1), v i) ∧
    ∃ j : Fin (d + 1),
      (mk v hv, mk u hu) =
        (projSpace k d ⊗ projSpace k 1).map structureMap (affinePoint j 0, affinePoint 0 ![j]) :=
  ⟨isUnit_mul_sum_of_mul_eq_zero hv hu h_mul_eq_zero,
    exists_eq_map_affinePoint_of_mul_eq_zero hv hu h_mul_eq_zero⟩

variable (k d)

/-- For `i : Fin (d + 1)`, the standard chart of projective `d`-space where the `i`-th coordinate is
invertible, on the polynomial ring in `d` variables. The chart point is `affinePoint i X` with
coordinates `X`. It is injective on points, and its image is open: the locus where the `i`-th
coordinate is a unit. -/
def stdChart : EtaleChart d (projSpace k d) where
  coordRing := of k (MvPolynomial (Fin d) k)
  point := affinePoint i X
  coordinate := X
  etale := by simpa using .containsIdentities _
  injective A φ ψ h := by
    -- The `i`-th coordinate is `1`, so the minors that involve it compare the other coordinates.
    ext j
    simpa using mk_eq_mk_iff_cross_mul.1 h (i.succAbove j) i
  isOpenSubfunctor A := by
    -- The chart is the locus where the `i`-th coordinate is a unit.
    rintro ⟨v⟩
    exact ⟨span {v.1.down i}, fun B φ ↦ (mk_mem_stdChart_iff i).trans (by simp [map_span])⟩

/-- Projective `d`-space has an atlas of dimension `d`: finitely many charts whose images contain
every field-valued point, and for any two points an ideal whose vanishing locus is where they agree.
The standard charts `New.Variety.projSpace.stdChart` contain every field-valued point. Two points
`[v]` and `[w]` agree exactly where all `v a * w b - w a * v b` vanish, so the space is
separated. -/
instance hasAtlas : HasAtlas d (projSpace k d) where
  exists_finite_charts := by
    -- Over a field some coordinate of a unimodular vector is a unit.
    refine ⟨d + 1, stdChart k d, fun K hK ↦ ?_⟩
    let fieldK : Field K := hK.toField
    rintro ⟨⟨⟨v⟩, hv⟩⟩
    exact (exists_isUnit_of_span_eq_top hv).imp fun i ↦ (mk_mem_stdChart_iff i).mpr
  exists_ideal := by
    -- Two points agree where the 2 × 2 minors of their representatives vanish.
    rintro A ⟨⟨⟨v⟩, hv⟩⟩ ⟨⟨⟨w⟩, hw⟩⟩
    refine ⟨⨆ (a) (b), span {v a * w b - w a * v b}, fun B φ ↦ mk_eq_mk_iff_cross_mul.trans ?_⟩
    simp [iSup_le_iff, span_le, RingHom.mem_ker, sub_eq_zero]

/-- In characteristic 0: if `v` and `u` are unimodular, so is the vector with entries
`u 0 * ∑ i, v i` and `(u 1 - i * u 0) * v i`. -/
lemma span_range_cons_mul_eq_top [CharZero k] {u : Fin 2 → A} (hv : span (Set.range v) = ⊤)
    (hu : span (Set.range u) = ⊤) :
    span (Set.range
      (cons (u 0 * ∑ i : Fin (d + 1), v i) fun i : Fin (d + 1) ↦ (u 1 - i * u 0) * v i :
        Fin (d + 2) → A)) = ⊤ := by
  -- It suffices that no map `ψ` to a field kills all entries; if it kills the later entries,
  -- `isUnit_mul_sum_of_mul_eq_zero` says that it sends the first one to a unit.
  rw [← (span _).map_id]
  refine (map_eq_top_iff_forall_isField _ (𝟙 A)).mpr fun K ψ hK h_le ↦ ?_
  let fieldK : Field K := hK.toField
  obtain ⟨h_first, h_rest⟩ : ψ (u 0) * ∑ i : Fin (d + 1), ψ (v i) = 0 ∧
      ∀ i : Fin (d + 1), (ψ (u 1) - i * ψ (u 0)) * ψ (v i) = 0 := by
    simpa [span_le, insert_subset_iff, range_subset_iff] using h_le
  have h_unit : IsUnit (ψ (u 0) * ∑ i : Fin (d + 1), ψ (v i)) :=
    isUnit_mul_sum_of_mul_eq_zero
      (unimodular.map ψ (a := ⟨v⟩) hv) (unimodular.map ψ (a := ⟨u⟩) hu) h_rest
  exact h_unit.ne_zero h_first

/-- In characteristic `0`, the map `ℙ^d × ℙ¹ → ℙ^(d+1)` that sends `([v], [w 0 : w 1])` to the
point with coordinates `w 0 * ∑ i, v i` and `(w 1 - i * w 0) * v i` for `i = 0, …, d`. -/
def lineProductMap [CharZero k] : projSpace k d ⊗ projSpace k 1 ⟶ projSpace k d.succ where
  app A := ↾fun x ↦ x.1.liftOn₂ x.2
    (fun ⟨⟨v⟩, hv⟩ ⟨⟨w⟩, hw⟩ ↦
      mk (cons (w 0 * ∑ i : Fin (d + 1), v i) fun i ↦ (w 1 - i * w 0) * v i)
        (span_range_cons_mul_eq_top k d hv hw))
    -- Scaling `w`, or `v`, by a unit scales every coordinate by that unit.
    (by
      rintro ⟨⟨v⟩⟩ ⟨⟨w⟩⟩ ⟨w'⟩ ⟨c, rfl⟩
      refine mk_eq_mk_iff_cross_mul.mpr ?_
      simp [forall_fin_succ, Units.smul_def]
      grind)
    (by
      rintro ⟨⟨v⟩⟩ ⟨⟨v'⟩⟩ ⟨w⟩ ⟨c, rfl⟩
      refine mk_eq_mk_iff_cross_mul.mpr ?_
      simp [forall_fin_succ, ← Finset.mul_sum, Units.smul_def]
      grind)
  naturality A B f := by
    ext ⟨⟨v⟩, ⟨w⟩⟩
    exact mk_eq_mk_iff_cross_mul.mpr (by simp [forall_fin_succ])

end New.Variety.projSpace

end ProjectiveSpace

/-!
## Injectivity of pull-back along a Noether normalisation

The proof of `New.Variety.CutsOutLocus.IsNoetherNormalization.pullback_injective` is a transfer
argument (`New.Variety.exists_transfer_map`) over the Galois hull
`New.Variety.CutsOutLocus.IsNoetherNormalization.exists_galois_closure`; its two density conditions
are checked near each maximal ideal of a test ring.
-/

section NormalizationPullback

open MvPolynomial CategoryTheory Ideal Function MonoidalCategory CartesianMonoidalCategory

/-- A test ring `A` over `k` with a prime `m` has a geometric point `κ` that sees `A` near `m`:
finitely many equations that hold under `κ` hold in `A` after multiplication by one element
outside `m`. -/
lemma New.Variety.CutsOutLocus.exists_geometric_point_near_prime {k A : Type} [Field k] [CommRing A]
    [Algebra k A] (hA : IsTest A) (m : Ideal A) [m.IsPrime] :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra k K) (κ : A →ₐ[k] K),
      ∀ {σ : Type} [Finite σ] {r s : σ → A},
      (∀ l : σ, κ (r l) = κ (s l)) → ∃ a ∉ m, ∀ l : σ, a * r l = a * s l := by
  -- the local ring at `m` is a valuation ring of an algebraically closed field `K`
  obtain ⟨-, -, K, _, hK, O, _, h_loc⟩ := hA.exists_valuationSubring_atPrime m
  algebraize [(O.subtype.comp (algebraMap A O)).comp (algebraMap k A)]
  -- `κ` is the map `A → O ⊆ K`
  let κ : A →ₐ[k] K := ⟨O.subtype.comp (algebraMap A O), fun _ ↦ rfl⟩
  refine ⟨K, inferInstance, hK, inferInstance, κ, fun {σ} _ r s h_eq ↦ ?_⟩
  -- `r` and `s` agree in the localisation `O` of `A` at `m`
  obtain ⟨⟨a, ha⟩, h_smul⟩ : ∃ a : m.primeCompl, a • r = a • s :=
    (IsLocalizedModule.pi m.primeCompl fun _ ↦ Algebra.linearMap A O).exists_of_eq
      (funext fun l ↦ Subtype.ext (h_eq l))
  exact ⟨a, ha, fun l ↦ congrFun h_smul l⟩

/-- Let `f : k[X] → B` be finite and injective, `A` a test ring (reduced, absolutely integrally
closed, and any `a`, `b` admit an idempotent `e` with `a ∣ e b` and `b ∣ (1 − e) a`) with a prime
`m`, and `w` a point of affine space over `A`. Near `m` the point lifts to `B`: there are `a ∉ m`
and a map of sets `s : B → A` such that, for each `ψ : A → C` that inverts `a`, `ψ ∘ s` is a
`k`-algebra map `v` with `v ∘ f ∘ X = ψ ∘ w`. -/
lemma New.Variety.CutsOutLocus.exists_lift_near_prime {k A B σ : Type} [Field k] [CommRing A]
    [Algebra k A] [CommRing B] [Algebra k B] [Finite σ] (hA : IsTest A) (m : Ideal A) [m.IsPrime]
    {f : MvPolynomial σ k →ₐ[k] B} (h_fin : f.toRingHom.Finite) (h_inj : Function.Injective f)
    (w : σ → A) :
    ∃ a ∉ m, ∃ s : B → A, ∀ (C : CommAlg k) (ψ : A →ₐ[k] C), IsUnit (ψ a) → ∃ v : B →ₐ[k] C,
      v ∘ f ∘ X = ψ ∘ w ∧ ∀ y : B, v y = ψ (s y) := by
  -- Lift the point to `B` at a geometric point `κ` that sees `A` near `m`. The images of
  -- generators of `B` are integral over `A`, so they come from `A`; the finitely many relations
  -- then hold in `A` after multiplication by some `a ∉ m`.
  obtain ⟨K, _, _, _, κ, h_near⟩ := exists_geometric_point_near_prime (k := k) hA m
  obtain ⟨φ, hφ⟩ : ∃ φ : B →ₐ[k] K, φ.comp f = κ.comp (aeval w) :=
    exists_algHom_comp_eq_of_integral f (κ.comp (aeval w)) h_fin.to_isIntegral
      (comap_bot_le_of_injective _ h_inj)
  -- a finite presentation `π` of `B` over `k[X]`, with finitely many relations `rel`
  obtain ⟨N, π, h_surj, rel, h_ker⟩ :=
    (RingHom.FinitePresentation.of_finiteType.mp h_fin.finiteType).out
  -- `π` is a map of algebras over `k[X]`, for the algebra structure on `B` given by `f`; as a map
  -- of `k`-algebras it is the evaluation `q` at the images `y` of the variables
  let algebraB : Algebra (MvPolynomial σ k) B := f.toRingHom.toAlgebra
  let y : Fin N → B := π ∘ X
  let q : MvPolynomial (Fin N) (MvPolynomial σ k) →ₐ[k] B := aevalTower f y
  have h_q (x : MvPolynomial (Fin N) (MvPolynomial σ k)) : q x = π x := by
    rw [aeval_unique π]
    rfl
  replace h_surj : Surjective q := fun b ↦ (h_surj b).imp fun x hx ↦ (h_q x).trans hx
  replace h_ker : span (rel : Set _) = RingHom.ker q := by simp [h_ker, Ideal.ext_iff, h_q]
  -- `y i` is integral over `k[X]`, so `φ (y i)` is integral over the image of `φ ∘ f = κ ∘ aeval w`
  have h_int (i : Fin N) : κ.toRingHom.IsIntegralElem (φ (y i)) := by
    have h_comp : (φ.comp f).toRingHom.IsIntegralElem (φ (y i)) :=
      (h_fin.to_isIntegral (y i)).map _
    rw [hφ] at h_comp
    exact .of_comp h_comp
  -- `A` is absolutely integrally closed, so elements integral over `κ` lie in its range
  have h_range (i : Fin N) : ∃ r : A, κ r = φ (y i) := hA.mem_range_of_isIntegralElem (h_int i)
  choose r hr using h_range
  let θ : MvPolynomial (Fin N) (MvPolynomial σ k) →ₐ[k] A := aevalTower (aeval (R := k) w) r
  have h_comm : κ.comp θ = φ.comp q := by
    ext i : 2
    · simp [θ, q, ← φ.comp_apply, hφ]
    · simpa [θ, q] using hr i
  have h_rel (x : rel) : κ (θ x) = κ 0 := by
    simpa [RingHom.mem_ker.mp (h_ker.le (subset_span x.prop))] using DFunLike.congr_fun h_comm x.val
  obtain ⟨a, ha, h_mul⟩ : ∃ a ∉ m, ∀ l : rel, a * θ l = a * 0 := h_near h_rel
  refine ⟨a, ha, θ ∘ surjInv h_surj, fun C ψ hψ ↦ ?_⟩
  -- `ψ ∘ θ` kills the relations, since `ψ a` is a unit, and so factors through `q`
  have h_kill : RingHom.ker q ≤ RingHom.ker (ψ.comp θ) := by
    rw [← h_ker, span_le]
    intro x hx
    have h_ax : ψ a * ψ (θ x) = 0 := by simpa using congrArg ψ (h_mul ⟨x, hx⟩)
    exact hψ.mul_right_eq_zero.mp h_ax
  let v : B →ₐ[k] C := q.liftOfSurjective h_surj (ψ.comp θ) h_kill
  have h_fac (x : MvPolynomial (Fin N) (MvPolynomial σ k)) : v (q x) = ψ (θ x) :=
    q.liftOfSurjective_apply h_surj (ψ.comp θ) h_kill x
  refine ⟨v, funext fun j ↦ ?_, fun x ↦ ?_⟩
  · simpa [θ, q] using h_fac (.C (X j))
  · simpa [surjInv_eq] using h_fac (surjInv h_surj x)

/-- Suppose that some solution `v` of the homogeneous equations of `g` has `v i ≠ 0`. Then every
solution `u` whose coordinate `u i` is a unit is a coordinate vector of a point of `Y`. -/
lemma New.Variety.CutsOutLocus.exists_point_of_isUnit_coord {k ι F : Type} [Field k] [Field F]
    {R : CommRingCat} [Algebra R k] [Finite ι] [Algebra k F] {Y : Over (AlgebraicGeometry.Spec R)}
    {L : LineBundle Y.left ι} [Fact (L.IsProjEmbedding Y.hom)] {ξ : PointsIn Y (CommAlgCat.of k F)}
    {g : ι → F} (hξ : IsCoordsWithUnit L ξ g) {A C : CommAlg k} {v : ι → A} {u : ι → C} {i : ι}
    (hv : IsHomogeneousSolution k g v) (hi : v i ≠ 0) (hu : IsHomogeneousSolution k g u)
    (h_unit : IsUnit (u i)) :
    ∃ y : PointsIn Y C, IsCoordsWithUnit L y u := by
  -- the point is the image of the universal point of `IsCoordsWithUnit.exists_universal_chart`
  obtain ⟨D, y, j, G, -, h_rep⟩ := hξ.exists_universal_chart hv hi
  obtain ⟨φ, -, hφ⟩ := h_rep hu h_unit
  exact ⟨y.map φ, hφ⟩

/-- The Galois cover of a Noether normalisation, as a functor on `k`-algebras. A point over `A` is
a family `y` of points of `Y` indexed by `G` with a map `v : B → A` of `k`-algebras, such that
`v ∘ b σ` is a coordinate vector of `y σ` with a unit entry for each `σ`, and the values
`v (f (X j))` generate the unit ideal. -/
private def New.Variety.CutsOutLocus.galoisCover {k ι G : Type} [Field k] {R : CommRingCat}
    [Algebra R.carrier k] [Finite ι] {Y : Over (AlgebraicGeometry.Spec R)}
    (L : LineBundle Y.left ι) [Fact (L.IsProjEmbedding Y.hom)] {B : CommAlg k} {d : ℕ}
    (f : MvPolynomial (Fin (d + 1)) k →ₐ[k] B) (b : G → ι → B) : CommAlg k ⥤ Type 1 :=
  .mk
    (fun A ↦
      {x : (G → PointsIn Y A) × (B →ₐ[k] A) //
        (∀ σ : G, IsCoordsWithUnit L (x.fst σ) (x.snd ∘ b σ)) ∧
          span (Set.range (x.snd ∘ f ∘ X)) = ⊤})
    fun φ ↦
      ↾fun x ↦
        ⟨(_, φ.hom.comp x.val.snd), fun σ ↦ (x.property.left σ).comp φ,
          unimodular.map φ (a := ⟨_⟩) x.property.right⟩

/-- Let `L` embed `Y` in projective space, and let `ξ` be an `F`-point of `Y` with coordinates `g`,
some `g i` a unit. Take a prime `m` of a test ring `A`, i.e. `A` is reduced and absolutely
integrally closed, and any `a, b` admit an idempotent `e` with `a ∣ e b` and `b ∣ (1 − e) a`. A
point `[w]` of projective space, with `w` generating the unit ideal, lifts near `m` to the Galois
cover of a Noether normalisation. Here `f : k[X₀, …, X_d] → B` is finite and injective, and each
`b σ` solves the homogeneous equations of `g` and is taken by `Λ` to `f ∘ X`. For some `a ∉ m`,
after every `ψ : A → C` that inverts `a`, there are `v : B → C` with `v ∘ f ∘ X = ψ ∘ w` and points
of `Y` with coordinate vectors `v ∘ b σ`. -/
lemma New.Variety.CutsOutLocus.exists_cover_point_near_prime {k ι F G : Type} [Field k] [Field F]
    [Fintype G] {R : CommRingCat} [Algebra R k] [Finite ι] [Algebra k F]
    {Y : Over (AlgebraicGeometry.Spec R)} {L : LineBundle Y.left ι} [Fact (L.IsProjEmbedding Y.hom)]
    {ξ : PointsIn Y (CommAlgCat.of k F)} {g : ι → F} (hξ : IsCoordsWithUnit L ξ g) {d : ℕ}
    {Λ : Fin (d + 1) → ↥(homogeneousSubmodule ι k 1)} {B : CommAlg k}
    {f : MvPolynomial (Fin (d + 1)) k →ₐ[k] B} {b : G → ι → B}
    (hb_hom : ∀ σ : G, IsHomogeneousSolution k g (b σ))
      (hb_forms : ∀ σ : G, evalForms Λ (b σ) = f ∘ X)
    (h_fin : f.toRingHom.Finite) (h_inj : Injective f) {A : CommAlg k} (hA : IsTest A)
    (m : Ideal A) [hm : m.IsPrime] {w : Fin (d + 1) → A} (hw : span (Set.range w) = ⊤) :
    ∃ a ∉ m, ∀ (C : CommAlg k) (ψ : A ⟶ C), IsUnit (ψ a) →
      ∃ (y : G → PointsIn Y C) (v : B →ₐ[k] C),
        (∀ σ : G, IsCoordsWithUnit L (y σ) (v ∘ b σ)) ∧ v ∘ f ∘ X = ψ ∘ w := by
  -- Lift `w` to `B` near `m` through a map of sets `s`. Each `b σ` has an entry `b σ (i σ)` whose
  -- lift does not lie in `m`; where all these lifts are units, each `v ∘ b σ` has a unit entry and
  -- so is a coordinate vector of a point of `Y`.
  obtain ⟨a, ha, s, h_lift⟩ := exists_lift_near_prime hA m h_fin h_inj w
  obtain ⟨v, hv, hv_s⟩ :
      ∃ v : B →ₐ[k] m.ResidueField, v ∘ f ∘ X = algebraMap A m.ResidueField ∘ w ∧
        ∀ y : B, v y = algebraMap A m.ResidueField (s y) :=
    h_lift (.of k m.ResidueField) (IsScalarTower.toAlgHom k A m.ResidueField) (by simpa using ha)
  -- In the residue field no `v ∘ b σ` vanishes: otherwise the forms `Λ` vanish there, so the
  -- entries of `w` lie in `m`.
  have h_ne (σ : G) : v ∘ b σ ≠ 0 := by
    intro h_zero
    have h_forms : v ∘ f ∘ X = 0 := by
      rw [← hb_forms σ, ← evalForms_map, h_zero]
      simpa [← Pi.zero_def] using evalForms_smul Λ (u := (0 : m.ResidueField)) (v := 0)
    rw [hv] at h_forms
    have h_le : span (Set.range w) ≤ m := by
      rw [span_le, Set.range_subset_iff]
      exact fun j ↦ algebraMap_residueField_eq_zero.mp (congrFun h_forms j)
    exact hm.ne_top (eq_top_mono h_le hw)
  choose i hi using fun σ : G ↦ ne_iff.mp (h_ne σ)
  have h_notMem (σ : G) : s (b σ (i σ)) ∉ m := fun h_mem ↦
    hi σ ((hv_s _).trans (algebraMap_residueField_eq_zero.mpr h_mem))
  refine ⟨a * ∏ σ : G, s (b σ (i σ)), m.primeCompl.mul_mem ha (prod_mem fun σ _ ↦ h_notMem σ),
    fun C ψ h_unit ↦ ?_⟩
  obtain ⟨ha_unit, h_unit_s⟩ : IsUnit (ψ a) ∧ ∀ σ : G, IsUnit (ψ (s (b σ (i σ)))) := by
    simpa using h_unit
  obtain ⟨v', hv', hv'_s⟩ : ∃ v' : B →ₐ[k] C, v' ∘ f ∘ X = ψ ∘ w ∧ ∀ y : B, v' y = ψ (s y) :=
    h_lift C ψ.hom ha_unit
  have h_unit' (σ : G) : IsUnit (v' (b σ (i σ))) := by simpa only [hv'_s] using h_unit_s σ
  have h_point (σ : G) : ∃ y : PointsIn Y C, IsCoordsWithUnit L y (v' ∘ b σ) :=
    exists_point_of_isUnit_coord (A := .of k m.ResidueField) (v := v ∘ b σ) (u := v' ∘ b σ) hξ
      ((hb_hom σ).map v) (hi σ) ((hb_hom σ).map v') (h_unit' σ)
  choose y hy using h_point
  exact ⟨y, v', hy, hv'⟩

/-- Near a prime `m` of a test ring `A` (reduced, absolutely integrally closed, and any `a`, `b`
admit an idempotent `e` with `a ∣ e b` and `b ∣ (1 − e) a`), two families of points over one point
of projective space differ by a shift in the finite group `G`, given that `h_conj` says this at
geometric points. If `u • v₀ ∘ f ∘ X = v₁ ∘ f ∘ X` for a unit `u`, and `y₀ σ`, `y₁ σ` are points of
`Y` with coordinate vectors `v₀ ∘ b σ`, `v₁ ∘ b σ`, then for some `a ∉ m` and `τ ∈ G`, `y₀ (τ * ρ)`
and `y₁ ρ` agree after every `ψ : A → C` that inverts `a`. -/
lemma New.Variety.CutsOutLocus.exists_map_mul_eq_map_near_prime {k ι G : Type} [Field k] [Group G]
    [Finite G] {R : CommRingCat} [Algebra R k] [Finite ι] {Y : Over (AlgebraicGeometry.Spec R)}
    {L : LineBundle Y.left ι} [Fact (L.IsProjEmbedding Y.hom)] {d : ℕ} {B : CommAlg k}
    {f : MvPolynomial (Fin (d + 1)) k →ₐ[k] B} {b : G → ι → B}
    (h_conj : ∀ {K : Type} [Field K] [IsAlgClosed K] [Algebra k K] (φ ψ : B →ₐ[k] K) (u : K),
      u • φ ∘ f ∘ X = ψ ∘ f ∘ X → ∃ τ : G, ∀ σ : G, ψ ∘ b σ = u • φ ∘ b (τ * σ))
    {A : CommAlg k} (hA : IsTest A) (m : Ideal A) [m.IsPrime] {y₀ y₁ : G → PointsIn Y A}
    {v₀ v₁ : B →ₐ[k] A} (hy₀ : ∀ σ : G, IsCoordsWithUnit L (y₀ σ) (v₀ ∘ b σ))
    (hy₁ : ∀ σ : G, IsCoordsWithUnit L (y₁ σ) (v₁ ∘ b σ)) {u : Aˣ}
    (hu : u • v₀ ∘ f ∘ X = v₁ ∘ f ∘ X) :
    ∃ a ∉ m, ∃ τ : G, ∀ (C : CommAlg k) (ψ : A ⟶ C), IsUnit (ψ a) → ∀ ρ : G,
      (y₀ (τ * ρ)).map ψ = (y₁ ρ).map ψ := by
  -- At a geometric point `κ` that sees `A` near `m` the coordinate vectors differ by a shift `τ`
  -- (`h_conj`); these finitely many equations then hold in `A` after multiplication by `a ∉ m`.
  obtain ⟨K, _, _, _, κ, h_near⟩ := exists_geometric_point_near_prime (k := k) hA m
  have h_κ : κ u • κ.comp v₀ ∘ f ∘ X = κ.comp v₁ ∘ f ∘ X :=
    funext fun j ↦ by simpa [Units.smul_def] using congrArg κ (congrFun hu j)
  obtain ⟨τ, hτ⟩ : ∃ τ : G, ∀ σ : G, κ.comp v₁ ∘ b σ = κ u • κ.comp v₀ ∘ b (τ * σ) :=
    h_conj (κ.comp v₀) (κ.comp v₁) (κ u) h_κ
  have h_eq_κ (l : G × ι) : κ (v₁ (b l.fst l.snd)) = κ (u * v₀ (b (τ * l.fst) l.snd)) := by
    simpa using congrFun (hτ l.fst) l.snd
  obtain ⟨a, ha, h_mul⟩ : ∃ a ∉ m, ∀ l : G × ι,
      a * v₁ (b l.fst l.snd) = a * (u * v₀ (b (τ * l.fst) l.snd)) :=
    h_near h_eq_κ
  refine ⟨a, ha, τ, fun C ψ h_unit ρ ↦ ?_⟩
  -- after inverting `a` the coordinate vectors are proportional, so the points of `Y` agree
  have h_coord : ψ ∘ v₁ ∘ b ρ = u.map ψ.hom.toMonoidHom • ψ ∘ v₀ ∘ b (τ * ρ) := by
    funext l
    have h_l : ψ a * ψ (v₁ (b ρ l)) = ψ a * (ψ u * ψ (v₀ (b (τ * ρ) l))) := by
      simpa using congrArg ψ (h_mul (ρ, l))
    exact h_unit.mul_left_cancel h_l
  refine ((hy₀ (τ * ρ)).map_unit_smul ψ (u.map ψ.hom.toMonoidHom)).ext ?_
  rw [← h_coord]
  exact (hy₁ ρ).comp ψ

/-- Let `ν ≫ α = n • l` for maps `α : N' ⟶ N`, `ν : Q ⟶ N'` and `l : Q ⟶ N` of abelian functors,
where `n ≠ 0` and `l` is an equivalence for a coefficient functor `F` (`IsCohomEquiv`: each
`H.map F l m`, pull-back on the cohomology `H^m(·, F)`, is bijective) on which the field `k` of
characteristic zero acts. Then pull-back along `α` is injective on `H^m(·, F)`. -/
lemma New.Variety.injective_H_map_of_comp_eq_nsmul {C : Type 1} [Category C] (k : Type) [Field k]
    [CharZero k] {F : AbFunctor C} [CoeffAction k F] {N N' Q : AbFunctor C} {α : N' ⟶ N}
    {ν : Q ⟶ N'} {l : Q ⟶ N} {n : ℕ} (hn : n ≠ 0) (h_comp : ν ≫ α = n • l)
    (h_l : IsCohomEquiv F l) (m : ℕ) :
    Injective (H.map F α m) := by
  -- `H(ν) ∘ H(α) = n • H(l)`, and multiplication by `n` is injective on a vector space over `k`.
  have h_fun : H.map F ν m ∘ H.map F α m = fun x ↦ n • H.map F l m x := by
    funext x
    rw [Function.comp_apply, ← H.map_comp]
    have h_hom : H.mapHom F Q N m (ν ≫ α) = n • H.mapHom F Q N m l := by rw [h_comp, map_nsmul]
    exact DFunLike.congr_fun h_hom x
  have h_torsionFree : HasUniqueDiv (H Q F m) := .of_isTorsionFree k (H Q F m)
  refine Injective.of_comp (f := H.map F ν m) ?_
  rw [h_fun]
  exact (nsmul_right_injective hn).comp (h_l m).injective

/-- Pull-back along a Noether normalisation is injective on cohomology. Let `Y` be embedded in
projective space by `L`, `ξ` a point of `Y` over a field with coordinates `g`, and `Λ` a Noether
normalisation of `g`. Let `O ⊆ Γ ⊆ Y × ℙ^d` contain `(x, [Λ(v)])` for every coordinate vector `v` of
`x` solving the homogeneous equations of `g` (`hO`). Then pull-back along `O → ℙ^d` is injective on
`H^n` on `p`-adic tests with coefficients `genericCoeff` (a test with ring R ↦ R[1/p]), taking the
free abelian groups on points with values in `genericOver` (R ↦ R[1/p] as a `k`-algebra). -/
lemma New.Variety.CutsOutLocus.IsNoetherNormalization.pullback_injective {p : ℕ} {k ι F : Type}
    [Field k] [EmbeddedInQpBar p k] [Field F] {R : CommRingCat} [Algebra R.carrier k] [Finite ι]
    [Algebra k F] {g : ι → CommAlgCat.of k F} {d n : ℕ} {Y : Over (AlgebraicGeometry.Spec R)}
    {Λ : Fin (d + 1) → ↥(homogeneousSubmodule ι k 1)} {L : LineBundle Y.left ι}
    [Fact (L.IsProjEmbedding Y.hom)] {ξ : PointsIn Y (CommAlgCat.of k F)}
    (hξ : IsCoordsWithUnit L ξ g) (hΛ : IsNoetherNormalization (k := k) Λ g)
    {Γ : Subfunctor (algPointsOf k R Y ⊗ projSpace k d)} {O : Subfunctor Γ.toFunctor}
    (hO :
      ∀ {A : CommAlg k} {x : PointsIn Y A} {v : ι → A} {hv : span (Set.range (evalForms Λ v)) = ⊤},
        IsHomogeneousSolution k g v → IsCoordsWithUnit L x v →
          ∃ hΓ : (x, projSpace.mk (evalForms Λ v) hv) ∈ Γ.obj A,
        ⟨(x, projSpace.mk (evalForms Λ v) hv), hΓ⟩ ∈ O A) :
    Function.Injective
      (H.map genericCoeff (genericOver.whiskerLeft
        (freeAb.map (O.ι ≫ Γ.ι ≫ snd (algPointsOf k R Y) (projSpace k d)))) n) := by
  -- Points of `W`, the Galois cover of the cone of `g`, map to `O` once for each `σ ∈ G`, over
  -- one point of `ℙ^d`; `f`, `b` and `h_conj` come from the Galois hull.
  obtain ⟨G, B, _, f, b, hb, h_fin, h_inj, h_conj⟩ := hΛ.exists_galois_closure
  obtain ⟨hb_hom, hb_forms⟩ := forall_and.mp hb
  let T : PadicTest ⥤ CommAlg k := genericOver (p := p)
  let W : PadicTest ⥤ Type 1 := T ⋙ galoisCover L f b
  -- `convert`: the point of projective space carries a proof of unimodularity, which `rw` cannot
  -- rewrite; `Λ` takes `x.val.snd ∘ b σ` to `x.val.snd ∘ f ∘ X`.
  have h_mem (σ : G) (c : PadicTest) (x : W.obj c) :
      ∃ hΓ, ⟨(x.val.fst σ, projSpace.mk _ x.property.right), hΓ⟩ ∈ O (T.obj c) := by
    convert hO ((hb_hom σ).map x.val.snd) (x.property.left σ)
    -- three like goals: the vector, its unimodularity and the point are those of `x`
    all_goals simp [hb_forms, x.property.right]
  let t (σ : G) : W ⟶ T ⋙ O.toFunctor := .mk fun c ↦ ↾fun x ↦ ⟨_, (h_mem σ c x).snd⟩
  let π : T ⋙ O.toFunctor ⟶ T ⋙ projSpace k d :=
    T.whiskerLeft (O.ι ≫ Γ.ι ≫ snd (algPointsOf k R Y) (projSpace k d))
  have h_over (σ : G) : t σ ≫ π = t 1 ≫ π := rfl
  -- The transfer gives `ν ≫ ℤ[π] = card G • l`; by `h_eqv`, `l` is an equivalence once the image
  -- of `W` is dense in `ℙ^d` and the pairs with permuted tuples `(t σ)_σ` are dense in `W ×_ℙ W`.
  obtain ⟨Q, -, l, ν, -, -, h_transfer, h_eqv⟩ := exists_transfer_map h_over
  have h_test (c : PadicTest) : IsTest (T.obj c) := c.isTest.localization
  -- by Zariski descent, density may be checked near each maximal ideal of a test ring
  have h_zar :
      HasZariskiDescent (𝟭 PadicTest ⋙ genericOver ⋙ forget₂ (CommAlg k) CommRingCat)
        genericCoeff := by
    obtain ⟨e, -⟩ := exists_periodAlg_iso_genericAlg (p := p)
    exact hasZariskiDescent_genericOver (k := k) (𝟭 _) (hasPartitions_periodAlg _ e)
  suffices h_l : IsCohomEquiv genericCoeff l by
    exact injective_H_map_of_comp_eq_nsmul k Fintype.card_ne_zero h_transfer h_l n
  refine h_eqv _ (h_zar fun c x (m : Ideal (T.obj c)) hm ↦ ?_)
    (h_zar fun c x (m : Ideal (T.obj c)) hm ↦ ?_)
  · -- near `m`, a point `[w]` of projective space comes from `W`
    obtain ⟨⟨w⟩, hw : span (.range w) = ⊤⟩ := x
    obtain ⟨a, ha, h_cover⟩ :=
      exists_cover_point_near_prime hξ hb_hom hb_forms h_fin h_inj (h_test c) m hw
    refine ⟨a, ha, fun c' φ h_unit ↦ ?_⟩
    obtain ⟨y, v', hy, hv'⟩ :
        ∃ (y : G → PointsIn Y (T.obj c')) (v' : B →ₐ[k] T.obj c'),
          (∀ σ : G, IsCoordsWithUnit L (y σ) (v' ∘ b σ)) ∧ v' ∘ f ∘ X = T.map φ ∘ w :=
      h_cover _ (T.map φ) h_unit
    have h_span_w : span (Set.range (T.map φ ∘ w)) = ⊤ := unimodular.map (T.map φ) (a := ⟨w⟩) hw
    have h_span : span (Set.range (v' ∘ f ∘ X)) = ⊤ := by rwa [hv']
    have h_pt : projSpace.mk (v' ∘ f ∘ X) h_span = projSpace.mk (T.map φ ∘ w) h_span_w := by
      simp only [hv']
    exact ⟨⟨(y, v'), hy, h_span⟩, h_pt⟩
  · -- near `m`, two points of `W` over one point of projective space differ by some `τ : G`
    let x₀ : W.obj c := x.val 0
    let x₁ : W.obj c := x.val 1
    obtain ⟨u, hu⟩ : ∃ u : (T.obj c)ˣ, u • x₀.val.snd ∘ f ∘ X = x₁.val.snd ∘ f ∘ X :=
      projSpace.mk_eq_mk_iff_exists_unit.mp (x.property 0 1)
    obtain ⟨a, ha, τ, h_shift⟩ :=
      exists_map_mul_eq_map_near_prime h_conj (h_test c) m x₀.property.left x₁.property.left hu
    refine ⟨a, ha, fun c' φ h_unit ↦ ⟨.mulLeft τ, fun ρ ↦ ?_⟩⟩
    -- the two points lie over one point of projective space
    have h_base : (t 1 ≫ π).app c' (((cech (t 1 ≫ π) 1).map φ x).val 1) =
        (t 1 ≫ π).app c' (((cech (t 1 ≫ π) 1).map φ x).val 0) :=
      ((cech (t 1 ≫ π) 1).map φ x).property 1 0
    have h_eq : (x₀.val.fst (τ * ρ)).map (T.map φ) = (x₁.val.fst ρ).map (T.map φ) :=
      h_shift _ (T.map φ) h_unit ρ
    -- a point of `O` is determined by its point of `Y` and its point of projective space
    exact Subtype.ext (Subtype.ext (Prod.ext h_eq.symm h_base))

end NormalizationPullback

end
