import Lib.Cohomology.Etale.DenseSubfunctors

/-!
# Functors of points on algebras: open subfunctors, étale charts, atlases, charted schemes

A space over `k` is a functor `X` from commutative `k`-algebras (`New.Variety.CommAlg k`) to types.
`New.Variety.reprBy A` is the functor represented by `A`, and `New.Variety.pointMap y` is the map
`reprBy A ⟶ X` given by a point `y ∈ X(A)`. The file defines open subfunctors and separated
functors. It also defines étale charts `a`, which are algebras `R` with étale coordinates and a
point `y ∈ X(R)` embedding `Spec R` as an open subfunctor `a.locus`. For `k` Noetherian it develops
the calculus of charts and shows that an atlas yields a cover by pieces étale over tori.

## Main definitions and results

* `New.Variety.IsOpenSubfunctor`, `New.Variety.IsSeparatedFunctor`: open subfunctors and separated
  functors, each defined by an ideal attached to one or two points. `New.Variety.IsAffinelyCovered`:
  separated, and covered by one affine after restriction along a functor `ι : C ⥤ CommAlg k`.
* `New.Variety.EtaleChart`, `New.Variety.IsChartCovered`, `New.Variety.HasAtlas`: affine open charts
  with étale coordinates, and covers of the field-valued points by charts.
* `New.Variety.etale_polyEval_iff`: for `k` Noetherian and `R` of finite type, coordinates are étale
  iff maps lift uniquely along square-zero extensions once the values of the coordinates are lifted.
* `New.Variety.HasAtlas.exists_isCharting`: an atlas gives a subfunctor satisfying
  `New.Variety.IsCharting`. It is found as a finite union of charts whose coordinates are units,
  that is, of pieces étale over a torus.
* `New.Variety.Comparison.isClosedClass`: for a comparison of cohomologies on categories over `D`,
  the functors on `D` for which it is bijective form a closed class
  (`New.Variety.IsClosedClass`: contains `0` and, given a short exact sequence whose first term is
  in it, contains the second term iff the third).
* `New.Variety.IsCharted`: a scheme is charted if its functor of points has a subfunctor satisfying
  `New.Variety.IsCharting`.

Notions from other files:
* `New.Variety.IsPointwiseSurjective p`: the map `p : E ⟶ Y` of functors is surjective on `A`-points
  for every object `A`.
* `New.Variety.IsZariskiLocallyTop`: every point maps into the given subfunctor once some element
  outside any given maximal ideal of the algebra is made a unit.
* `CategoryTheory.Subfunctor.whisker`: for a subfunctor `U` of `Y` and `φ : C' ⥤ C`, the subfunctor
  `φ ⋙ U` of `φ ⋙ Y`.
* `New.Variety.restrictAlg k k'`: restriction of scalars, which regards a commutative `k'`-algebra
  as a `k`-algebra.

## Relation to the literature

Known; see `Lib.Cohomology.Etale.FilteredLimits` and `Lib.PadicComparison.ToricTower` for sources.
-/

noncomputable section

/-!
## Open and separated functors, étale charts and atlases

* `New.Variety.fieldLocus`: the subfunctor cut out by a condition on values in fields; examples are
  `New.Variety.offPoints` (avoiding given points) and `New.Variety.offDiagonal` (off the diagonal).
-/

section OpenSubfunctors

open CategoryTheory Function Set MonoidalCategory CommAlgCat RingHom Ideal Quotient

namespace New.Variety

section Definitions

variable {C : Type 1} [Category.{0} C] (k : Type) [CommRing k] (d : outParam ℕ)

/-- A test for Hodge cohomology over k: a commutative k-algebra A and a finite index set ι,
standing for the pair (A, M) with M = A^ι. -/
structure HodgeTest where
  /-- The commutative `k`-algebra `A`. -/
  baseAlg : CommAlg k
  /-- The index set of the standard basis of the free module `M = A^ι`. -/
  Index : Type
  /-- The index set is finite. -/
  [fintypeIndex : Fintype Index]
  /-- A chosen linear order on the index set. -/
  [linearOrderIndex : LinearOrder Index]

attribute [instance] HodgeTest.fintypeIndex HodgeTest.linearOrderIndex

/-- Affine d-space: the functor A ↦ A^d on k-algebras. -/
def affineSpace : CommAlg k ⥤ Type 1 where
  obj A := ULift (Fin d → A)
  map f := ↾fun v ↦ ⟨f ∘ v.down⟩

variable {k} {X Y : CommAlg k ⥤ Type 1} (V : Subfunctor X) {A B : CommAlg k}
  (P : (K : CommAlg k) → X.obj K → Prop)

/-- The subfunctor of affine d-space of vectors whose entries generate the unit ideal: the
complement of the origin. -/
def unimodular {d : ℕ} : Subfunctor (affineSpace k d) where
  obj _ := {v | span (Set.range v.down) = ⊤}
  map := by
    delta affineSpace
    simp_all [range_comp, ← map_span, Ideal.map_top]

/-- The structure map k → A of a k-algebra A. -/
@[simp]
abbrev structureMap : of k k ⟶ A := ofHom (Algebra.ofId k A)

/-- The subfunctor of points x in X(A) whose image in X(K) satisfies P for every map from A to a
field K. -/
def fieldLocus : Subfunctor X where
  obj _ := {x | ∀ (K : CommAlg k) φ, IsField K.carrier → P K (X.map φ x)}
  map := by grind [=_ X.map_comp_apply]

/-- A point `x` of `X(K)` comes from `s` if it is the image of some `k`-point `z` in `s` under the
structure map `k → K`. -/
def ComesFromPoints (s : Set (X.obj (of k k))) (K : CommAlg k) (x : X K) : Prop :=
  ∃ z ∈ s, x = X.map structureMap z

/-- For a set s of k-points of X, the subfunctor of points none of whose values in fields comes
from s. -/
def offPoints (s : Set (X.obj (of k k))) : Subfunctor X :=
  fieldLocus (X := X) fun K x ↦ ¬ComesFromPoints s K x

/-- V is an open subfunctor of X: each x ∈ X(A) has an ideal I of A such that, for φ: A → B,
φ(x) ∈ V(B) iff φ(I)B = B. -/
def IsOpenSubfunctor : Prop :=
  ∀ (A : CommAlg k) (x : X.obj A), ∃ I : Ideal A, ∀ (B : CommAlg k) (φ : A ⟶ B),
    X.map (X := A) (Y := B) φ x ∈ V B ↔ Ideal.map φ.hom I = ⊤

variable (X) (ι : C ⥤ CommAlg k)

/-- X is separated: for x, y in X(A) there is an ideal J of A such that φ: A → B makes x and y
equal exactly when φ kills J. -/
class IsSeparatedFunctor where
  /-- For two points of `X(A)`, an ideal `J` of `A` such that a map `φ : A → B` makes them equal
  exactly when `φ` kills `J`. -/
  exists_ideal (A : CommAlg k) (x y : X.obj A) : ∃ J : Ideal A, ∀ (B : CommAlg k) (φ : A ⟶ B),
    X.map (X := A) (Y := B) φ x = X.map φ y ↔ J ≤ ker φ.hom

/-- `X` is separated and, after restriction along `ι`, covered by one affine: there are a
`k`-algebra `B` and a point `y` of `X(B)` such that, for every object `c`, each point of `X(ι c)` is
the image of `y` under some map `B → ι c`. -/
def IsAffinelyCovered (X : CommAlg k ⥤ Type 1) : Prop :=
  IsSeparatedFunctor X ∧
  ∃ (B : CommAlg k) (y : X.obj B), IsPointwiseSurjective (ι.whiskerLeft (pointMap y))

/-- Every k-algebra B with a map to some ι(c) has a map y : B → ι(c'), for some c', such that
`pointMap y`, the map from the functor on `C` represented by c' to `ι ⋙ reprBy B`, is surjective on
points: each map B → ι(c'') is ι(f) ∘ y for some f : c' → c''. -/
class HasCoveringPoints where
  /-- Each `k`-algebra with a map to some `ι(c)` has a map to some `ι(c')` through which, followed
  by some `ι(f)` with `f : c' ⟶ c''`, every map to an `ι(c'')` factors. -/
  exists_surjective_point (B : CommAlg k) {c : C} (z : (ι ⋙ reprBy B).obj c) :
      ∃ (c' : C) (y : (ι ⋙ reprBy B).obj c'), IsPointwiseSurjective (pointMap y)

/-- The complement of the diagonal in X × X: pairs of points whose values in every field are
distinct. -/
def offDiagonal : Subfunctor (X ⊗ X) := fieldLocus fun (_ : CommAlg k) x ↦ x.1 ≠ x.2

/-- A chart of X: a k-algebra R (`coordRing`) with d étale coordinates (`coordinate`) and a point y
(`point`) in X(R) that embeds Spec R as an open subfunctor. -/
structure EtaleChart where
  /-- The `k`-algebra of functions on the chart. -/
  coordRing : CommAlg k
  /-- The point of `X` over `R`, that is, the map `Spec R → X`. -/
  point : X.obj coordRing
  /-- The `d` coordinates on the chart. -/
  coordinate : Fin d → coordRing
  /-- The coordinates make `R` étale over the polynomial ring in `d` variables. -/
  etale : (MvPolynomial.aeval (R := k) coordinate).1.Etale
  /-- The map `Spec R → X` is injective on `A`-points, for every `A`. -/
  injective (A : CommAlg k) : Function.Injective (X.map (X := coordRing) (Y := A) · point)
  /-- The image of `Spec R → X` is an open subfunctor. -/
  isOpenSubfunctor : IsOpenSubfunctor (Subfunctor.range (pointMap point))

variable {X d} (a : EtaleChart d X)

/-- φ: A → B is a square-zero extension: surjective, with kernel of square zero. -/
def IsSquareZero {A B : CommAlg k} (φ : A ⟶ B) : Prop := Surjective φ ∧ ker φ.hom ^ 2 = ⊥

/-- For a chart a of X, with ring R = a.coordRing and point y = a.point, the open subfunctor that is
the image of Spec R → X, φ ↦ φ(y). -/
abbrev EtaleChart.locus : Subfunctor X := Subfunctor.range (pointMap a.point)

/-- The map `Spec R → X` given by the point of a chart is a monomorphism. -/
instance EtaleChart.mono_pointMap : Mono (pointMap a.point) :=
  mono_of_app_injective fun A ↦ (a.injective A).comp ULift.down_injective

end Definitions

section Properties

variable {k : Type} [CommRing k] {d : ℕ} {X Y : CommAlg k ⥤ Type 1} {V W : Subfunctor X}
  {A B : CommAlg k} (I : Ideal A)

lemma EtaleChart.mem_locus_iff (a : EtaleChart d X) {x : X.obj B} :
    x ∈ a.locus B ↔ ∃ φ : a.coordRing ⟶ B, X.map φ a.point = x :=
  ULift.exists

/-- Let `a` be a chart of `X` with ring `a.coordRing` and point `a.point ∈ X(a.coordRing)`. A map
`χ` out of `a.coordRing` is the composite `ψ ≫ φ` if it sends `a.point` to the image under `φ` of
the point given by `ψ`. -/
lemma EtaleChart.eq_comp_of_map_point_eq (a : EtaleChart d X) (φ : A ⟶ B) {ψ : a.coordRing ⟶ A}
    {χ : a.coordRing ⟶ B} (h_map : X.map χ a.point = X.map φ (X.map ψ a.point)) : χ = ψ ≫ φ :=
  a.injective B (by simp [h_map])

lemma projSpace.span_eq_top_of_isUnit {v : Fin d → A} (i : Fin d) (hi : IsUnit (v i)) :
    span (Set.range v) = ⊤ :=
  eq_top_of_isUnit_mem _ (subset_span (mem_range_self i)) hi

/-! ### Properties of open subfunctors and of points -/

/-- The image of the ideal `I` of `A` under `φ : A ⟶ B` generates the unit ideal of `B` exactly when
no map from `B` to a field kills it. -/
lemma map_eq_top_iff_forall_isField (φ : A ⟶ B) :
    I.map φ.hom = ⊤ ↔ ∀ (K : CommAlg k) (ψ : B ⟶ K), IsField K → ¬I ≤ ker (φ ≫ ψ).hom := by
  constructor
  · intro h_top K ψ hK h_le
    have : Nontrivial K := hK.nontrivial
    have h_bot : (I.map φ.hom).map ψ.hom = ⊥ := by
      simpa [← map_eq_bot_iff_le_ker, ← map_mapₐ] using h_le
    simp [h_top, Ideal.map_top] at h_bot
  · -- A proper ideal lies in a maximal ideal `m`, and dies in the residue field.
    intro h_fields
    by_contra h_ne
    obtain ⟨m, hm, h_le⟩ := exists_le_maximal _ h_ne
    refine h_fields (CommAlgCat.of k (B ⧸ m)) (ofHom (mkₐ k m)) (Quotient.field m).toIsField ?_
    simpa [← map_eq_bot_iff_le_ker, ← map_mapₐ] using! map_mk_eq_bot_of_le h_le

/-- If `V` is open, a point lies in `V` as soon as all its values in fields do. Here
`fieldLocus V` is the subfunctor of points whose values in fields lie in `V`. -/
lemma IsOpenSubfunctor.fieldLocus_le (hV : IsOpenSubfunctor V) : fieldLocus V ≤ V := by
  intro A x hx
  obtain ⟨I, hI⟩ : ∃ I : Ideal A, ∀ (B : CommAlg k) (φ : A ⟶ B),
      X.map φ x ∈ V B ↔ I.map φ.hom = ⊤ := hV A x
  -- `I` generates the unit ideal in every field over `A`, so it is the unit ideal.
  have h_top : I.map (𝟙 A : A ⟶ A).hom = ⊤ := by
    refine (map_eq_top_iff_forall_isField I _).2 fun K ψ hK h_le ↦ ?_
    have : Nontrivial K := hK.nontrivial
    have h_bot : I.map ψ.hom = ⊥ := by simpa [← map_eq_bot_iff_le_ker] using h_le
    simpa [h_bot] using (hI K ψ).1 (hx K ψ hK)
  simpa using (hI A (𝟙 A)).2 h_top

/-- If the image of `x ∈ X(A)` under a map `φ` to a field `B` lies in the open subfunctor `V` of
`X`, there is an `f ∈ A`, non-zero in `B`, such that `x` maps into `V` wherever `f` becomes a
unit. -/
lemma IsOpenSubfunctor.exists_basicOpen (φ : A ⟶ B) (hV : IsOpenSubfunctor V) (x : X.obj A)
    (hB : IsField B) (hx : X.map φ x ∈ V B) :
    ∃ f : A, φ f ≠ 0 ∧ ∀ (B' : CommAlg k) (ψ : A ⟶ B'), IsUnit (ψ f) → X.map ψ x ∈ V B' := by
  obtain ⟨I, hI⟩ : ∃ I : Ideal A, ∀ (B' : CommAlg k) (ψ : A ⟶ B'),
      X.map ψ x ∈ V B' ↔ I.map ψ.hom = ⊤ := hV A x
  -- `I` generates the unit ideal in the field `B`, so some `f ∈ I` does not vanish there.
  have h_top : I.map φ.hom = ⊤ := (hI B φ).1 hx
  have h_not_le : ¬I ≤ ker φ.hom := by
    simpa using (map_eq_top_iff_forall_isField I φ).1 h_top B (𝟙 B) hB
  obtain ⟨f, hf, hf_ne⟩ : ∃ f ∈ I, φ f ≠ 0 := IsConcreteLE.not_le_iff_exists.1 h_not_le
  -- Where `f` is a unit, so is the ideal generated by the image of `I`.
  refine ⟨f, hf_ne, fun B' ψ hψ ↦ (hI B' ψ).2 ?_⟩
  exact eq_top_of_isUnit_mem _ (mem_map_of_mem _ hf) hψ

/-- The subfunctor cut out by a condition `P` on values in fields is open if, for each point `x`,
`P` fails exactly on the zero locus of an ideal `J`. -/
lemma isOpenSubfunctor_fieldLocus {P : (K : CommAlg k) → X.obj K → Prop}
    (h_ideal : ∀ (A : CommAlg k) (x : X.obj A), ∃ J : Ideal A, ∀ (K : CommAlg k) (φ : A ⟶ K),
      IsField K.carrier → (P K (X.map φ x) ↔ ¬J ≤ ker φ.hom)) :
    IsOpenSubfunctor (fieldLocus P) := by
  intro A x
  obtain ⟨J, hJ⟩ := h_ideal A x
  -- Both sides are conditions on the maps from `B` to fields.
  refine ⟨J, fun B φ ↦ Iff.trans ?_ (map_eq_top_iff_forall_isField J φ).symm⟩
  exact forall₃_congr fun K ψ hK ↦ by rw [← hJ K _ hK, X.map_comp_apply]

/-- A point `x ∈ X(A)` lies in the open subfunctor `V` of `X` if its image under a square-zero
extension `φ` (a surjection whose kernel has square zero) does. -/
lemma IsOpenSubfunctor.mem_of_isSquareZero (φ : A ⟶ B) (hV : IsOpenSubfunctor V)
    (hφ : IsSquareZero φ) (x : X.obj A) (hx : X.map φ x ∈ V B) : x ∈ V A := by
  obtain ⟨h_surj, h_sq⟩ := hφ
  obtain ⟨I, hI⟩ : ∃ I : Ideal A, ∀ (C : CommAlg k) (ψ : A ⟶ C),
      X.map ψ x ∈ V C ↔ I.map ψ.hom = ⊤ := hV A x
  -- The image of `I` in `B` is the unit ideal, so `I` and the kernel of `φ` are comaximal.
  have h_map : I.map φ.hom = ⊤ := (hI B φ).1 hx
  have h_sup : I ⊔ ker φ.hom = ⊤ := by
    rw [← comap_map_of_surjective' φ.hom h_surj I, h_map, comap_top]
  -- The kernel has square zero, so `I` itself is the unit ideal.
  have hI_top : I = ⊤ := by simpa [h_sq] using I.sup_pow_eq_top (n := 2) h_sup
  simpa [hI_top] using hI _ (𝟙 _)

/-- The intersection of two open subfunctors is open; its ideal is the product. -/
lemma IsOpenSubfunctor.inf (hV : IsOpenSubfunctor V) (hW : IsOpenSubfunctor W) :
    IsOpenSubfunctor (V ⊓ W) := by
  intro A x
  -- `φ` maps `x` into `V`, resp. `W`, exactly when `I`, resp. `J`, generates the unit ideal in `B`.
  obtain ⟨I, hI⟩ := hV A x
  obtain ⟨J, hJ⟩ := hW A x
  -- A product of ideals is the unit ideal iff both factors are.
  exact ⟨I * J, fun B φ ↦ by simp [hI, hJ, Ideal.map_mul, ← one_eq_top]⟩

lemma IsOpenSubfunctor.preimage (hV : IsOpenSubfunctor V) (u : Y ⟶ X) :
    IsOpenSubfunctor (V.preimage u) := by
  intro A y
  obtain ⟨I, hI⟩ := hV A (u.app A y)
  exact ⟨I, fun (B : CommAlg k) φ ↦ by simpa [NatTrans.naturality_apply] using hI B φ⟩

/-- An open subfunctor stays open after base change to a `k`-algebra `E`. -/
lemma IsOpenSubfunctor.whisker_restrictAlg {E : Type} [CommRing E] [Algebra k E]
    (hV : IsOpenSubfunctor V) :
    IsOpenSubfunctor (X := restrictAlg k E ⋙ X) (V.whisker (restrictAlg k E)) := by
  intro A x
  -- An `E`-algebra map is a `k`-algebra map, so the same ideal works.
  obtain ⟨I, hI⟩ := hV ((restrictAlg k E).obj A) x
  exact ⟨I, fun B φ ↦ hI _ ((restrictAlg k E).map φ)⟩

/-- The images of a `k`-point are compatible with maps of `k`-algebras. -/
@[simp]
lemma map_map_structureMap (φ : A ⟶ B) (z : X.obj (of k k)) :
    X.map φ (X.map structureMap z) = X.map structureMap z := by
  -- there is only one map of `k`-algebras out of `k`
  rw [← X.map_comp_apply]
  rcongr

/-! ### Open subfunctors of separated functors, and covers -/

/-- If `X` is separated and `s` is a finite set of `k`-points of `X`, then `offPoints s`, the
subfunctor of points none of whose values in fields comes from `s`, is open. -/
lemma isOpenSubfunctor_offPoints [IsSeparatedFunctor X] {s : Set (X.obj (of k k))} [Finite s] :
    IsOpenSubfunctor (offPoints s) := by
  classical
  refine isOpenSubfunctor_fieldLocus fun A x ↦ ?_
  -- Separatedness: for each `k`-point `z`, an ideal `J z` cuts out the locus where `x` equals `z`.
  choose J hJ using fun z : X.obj (of k k) ↦
    IsSeparatedFunctor.exists_ideal A x (X.map structureMap z)
  -- A map to a field has prime kernel, so it kills the intersection of the `J z`, `z ∈ s`, exactly
  -- when it kills one of them, that is, when the image of `x` is one of these points.
  refine ⟨s.toFinite.toFinset.inf J, fun K φ hK ↦ not_congr ?_⟩
  have : IsDomain K := hK.isDomain
  calc ComesFromPoints s K (X.map φ x)
    _ ↔ ∃ z ∈ s.toFinite.toFinset, J z ≤ ker φ.hom := by simp [ComesFromPoints, ← hJ]
    _ ↔ s.toFinite.toFinset.inf J ≤ ker φ.hom := (ker_isPrime φ.hom).inf_le'.symm

lemma isOpenSubfunctor_offDiagonal [IsSeparatedFunctor X] : IsOpenSubfunctor (offDiagonal X) :=
  isOpenSubfunctor_fieldLocus fun A ⟨x, y⟩ ↦
    (IsSeparatedFunctor.exists_ideal A x y).imp fun _ hJ K φ _ ↦ (hJ K φ).not

/-- If `X` is separated, two distinct points with values in a field `A` form a pair in the
complement of the diagonal: their images in every field over `A` are distinct. -/
lemma mem_offDiagonal_of_ne [IsSeparatedFunctor X] (hA : IsField A) {x y : X.obj A} (hxy : x ≠ y) :
    (x, y) ∈ offDiagonal X A := by
  obtain ⟨J, hJ⟩ := IsSeparatedFunctor.exists_ideal A x y
  -- The ideal `J` where `x` and `y` agree is not zero, as `x ≠ y`, so it is all of the field `A`,
  -- and no map to a field kills it.
  let : Field A := hA.toField
  have hJ_top : J = ⊤ := J.eq_bot_or_top.resolve_left fun hJ_bot ↦
    hxy (by simpa [hJ_bot] using (hJ A (𝟙 A)).2)
  intro K φ hK h_eq
  have : Nontrivial K := hK.nontrivial
  simpa [hJ_top, ker_ne_top] using (hJ K φ).1 h_eq

/-- Let `Θ : C ⥤ CommAlg k` and `T ⊆ Θ ⋙ X` be such that each field point of `X` lies in an open
`O` whose restriction along `Θ` is contained in `T`. Then `T` is locally everything: for `y` in
`X (Θ c)` and `m` maximal in `Θ c`, some `f ∉ m` has `y` in `T` wherever `f` becomes a unit. -/
lemma isZariskiLocallyTop_of_open_cover {C : Type 1} [Category.{0} C] {k : Type} [CommRing k]
    {X : CommAlg k ⥤ Type 1} {Θ : C ⥤ CommAlg k} {T : Subfunctor (Θ ⋙ X)}
    (h_cover : ∀ K : CommAlg k, IsField K.carrier → ∀ x : X K, ∃ O : Subfunctor X,
      IsOpenSubfunctor O ∧ x ∈ O K ∧ O.whisker Θ ≤ T) :
    IsZariskiLocallyTop (Θ ⋙ forget₂ (CommAlg k) CommRingCat) T := by
  intro c y (m : Ideal (Θ.obj c)) hm
  -- The image of `y` in the residue field at `m` lies in some open `O`.
  have hfield : IsField (Θ.obj c ⧸ m) := (Quotient.field m).toIsField
  let res : Θ.obj c ⟶ of k (Θ.obj c ⧸ m) := ofHom (mkₐ k m)
  obtain ⟨O, hO_open, hyO, hOT⟩ := h_cover _ hfield (X.map res y)
  -- By openness, `y` lies in `O` wherever some `f`, nonzero in the residue field, is a unit.
  obtain ⟨f, hf, hloc⟩ := hO_open.exists_basicOpen res y hfield hyO
  exact ⟨f, mt eq_zero_iff_mem.2 hf, fun c' ψ hunit ↦ hOT c' (hloc (Θ.obj c') (Θ.map ψ) hunit)⟩

end Properties

variable {k : Type} [CommRing k] (d : outParam ℕ) (X : CommAlg k ⥤ Type 1)

/-- Every field-valued point of X lies in some chart, an affine open with d étale coordinates. -/
class IsChartCovered where
  /-- Each point of `X` with values in a field lies in the locus of some chart. -/
  exists_chart (K : CommAlg k) :
      IsField K.carrier → ∀ x : X.obj K, ∃ a : EtaleChart d X, x ∈ a.locus.obj K

/-- X is separated and has finitely many charts, each with exactly d étale coordinates, that
contain every field-valued point. -/
class HasAtlas extends IsSeparatedFunctor X where
  /-- Finitely many charts contain every field-valued point of `X`. -/
  exists_finite_charts : ∃ (n : ℕ) (a : Fin n → EtaleChart d X),
    ∀ K : CommAlg k, IsField K.carrier → ∀ x : X.obj K, ∃ i : Fin n, x ∈ (a i).locus.obj K

end New.Variety

end OpenSubfunctors

/-!
## Calculus of étale charts and covers by pieces étale over tori

* `New.Variety.EtaleChart.exists_eq_iff_coordinate_eq`: two points of a chart are equal iff their
  coordinates agree and a fixed element of `a.coordRing ⊗ a.coordRing` maps to a unit.
-/

namespace New.Variety

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Algebra TensorProduct EtaleChart
  CommAlgCat MvPolynomial Ideal IsLocalization.Away KaehlerDifferential Set Functor Fin Quotient
  AlgHom FormallyUnramified

variable {k : Type} [CommRing k] {X Y : CommAlg k ⥤ Type 1} {A B R : CommAlg k} {d n : ℕ}
  (x : Fin d → R) (a : EtaleChart d X) (b : EtaleChart n Y) (u : Y ⟶ X) [Mono u]

/-- The product of two separated functors is separated. -/
instance [IsSeparatedFunctor X] [IsSeparatedFunctor Y] : IsSeparatedFunctor (X ⊗ Y) := by
  -- Two pairs become equal when both components do: take the sum of the two ideals.
  refine ⟨fun A x y ↦ ?_⟩
  obtain ⟨I, hI⟩ := IsSeparatedFunctor.exists_ideal A x.1 y.1
  obtain ⟨J, hJ⟩ := IsSeparatedFunctor.exists_ideal A x.2 y.2
  refine ⟨I ⊔ J, fun B φ ↦ ?_⟩
  rw [sup_le_iff, ← hI, ← hJ]
  exact Prod.ext_iff

/-- The localisation map A → A[1/g] of k-algebras. -/
abbrev CommAlg.toAway (g : A) : CommAlgCat.of k A ⟶ CommAlgCat.of k (Localization.Away g) :=
  ofHom (IsScalarTower.toAlgHom k A (Localization.Away g))

/-- A map `φ : A ⟶ B` factors through `toAway g`, the localization map `A ⟶ A[1/g]`, iff it sends
`g` to a unit. -/
lemma CommAlg.exists_toAway_comp_iff (g : A) (φ : A ⟶ B) :
    (∃ χ : CommAlgCat.of k (Localization.Away g) ⟶ B, toAway g ≫ χ = φ) ↔ IsUnit (φ g) := by
  constructor
  · rintro ⟨χ, rfl⟩
    exact (algebraMap_isUnit g).map χ.hom
  · -- The factorization is the lift of `φ` to the localization.
    exact fun h_unit ↦ ⟨ofHom (liftAlgHom _ h_unit), by aesop⟩

lemma EtaleChart.point_mem_locus : a.point ∈ a.locus a.coordRing :=
  a.mem_locus_iff.2 ⟨𝟙 a.coordRing, X.map_id_apply a.coordRing a.point⟩

/-- A subfunctor `V` of the image `a.locus` of a chart `a` that is open in `a.locus` is cut out by
its values in fields: a point whose values in fields lie in `V` lies in `V`. -/
lemma EtaleChart.fieldLocus_eq_of_le_locus {V : Subfunctor X} (h_le : V ≤ a.locus)
    (hV : IsOpenSubfunctor (V.preimage a.locus.ι)) : fieldLocus V = V := by
  refine le_antisymm (fun A x hx ↦ ?_) fun A x hx K φ _ ↦ V.map φ hx
  have hx_chart : x ∈ a.locus A :=
    a.isOpenSubfunctor.fieldLocus_le A fun K ψ hK ↦ h_le _ (hx K ψ hK)
  exact hV.fieldLocus_le A (a := ⟨x, hx_chart⟩) hx

/-- A subfunctor `V` of the image `a.locus` of a chart `a` is open in `X` if it is open in
`a.locus`. -/
lemma EtaleChart.isOpenSubfunctor_of_le_locus {V : Subfunctor X} (h_le : V ≤ a.locus)
    (hV : IsOpenSubfunctor (V.preimage a.locus.ι)) : IsOpenSubfunctor V := by
  -- `V` is cut out by its values in fields, so `isOpenSubfunctor_fieldLocus` applies; the ideal of
  -- `x` is spanned by the `f` whose inversion puts `x` in `V`.
  rw [← a.fieldLocus_eq_of_le_locus h_le hV]
  refine isOpenSubfunctor_fieldLocus fun A x ↦
    ⟨span {f | ∀ (B : CommAlg k) (ψ : A ⟶ B), IsUnit (ψ f) → X.map ψ x ∈ V B}, fun K φ hK ↦ ?_⟩
  let : Field K := hK.toField
  rw [span_le, not_subset]
  refine ⟨fun hx ↦ ?_, fun ⟨f, hf, hf_ne⟩ ↦ hf K φ (Ne.isUnit hf_ne)⟩
  -- Over `A[1/f]` the point `x` gives a point `z` of the chart, and `φ` factors as `χ`.
  obtain ⟨f, hf, h_chart⟩ := a.isOpenSubfunctor.exists_basicOpen φ x hK (h_le _ hx)
  let Af : CommAlg k := .of k (Localization.Away f)
  let z : a.locus.toFunctor.obj Af :=
    ⟨X.map (A.toAway f) x, h_chart Af (A.toAway f) (algebraMap_isUnit f)⟩
  obtain ⟨χ, rfl⟩ : ∃ χ : Af ⟶ K, A.toAway f ≫ χ = φ :=
    (A.exists_toAway_comp_iff f φ).2 hf.isUnit
  -- Over `A[1/f][1/g]` the point `z` maps into `V`; take `f` times a numerator `r` of `g`.
  obtain ⟨g, hg, h_sub⟩ : ∃ g : Af, χ g ≠ 0 ∧ ∀ (B : CommAlg k) (ω : Af ⟶ B),
      IsUnit (ω g) → a.locus.toFunctor.map ω z ∈ (V.preimage a.locus.ι) B :=
    hV.exists_basicOpen χ z hK (by simpa [z] using! hx)
  obtain ⟨r, m, hr⟩ : ∃ (r : A) (m : ℕ), A.toAway f r = g * A.toAway f f ^ m :=
    ⟨(sec f g).1, (sec f g).2, by simpa using (sec_spec f g).symm⟩
  have hf' : χ (A.toAway f f) ≠ 0 := hf
  have h_ne : χ (A.toAway f (f * r)) ≠ 0 := by
    simp only [map_mul, map_pow, hr]
    exact mul_ne_zero hf' (mul_ne_zero hg (pow_ne_zero m hf'))
  refine ⟨f * r, fun B ψ hψ ↦ ?_, h_ne⟩
  obtain ⟨hψf, hψr⟩ : IsUnit (ψ f) ∧ IsUnit (ψ r) := by simpa using hψ
  obtain ⟨ω, rfl⟩ : ∃ ω : Af ⟶ B, A.toAway f ≫ ω = ψ := (A.exists_toAway_comp_iff f ψ).2 hψf
  -- `ω g` divides the image of `r` in `B`, which is a unit.
  replace hψr : IsUnit (ω (A.toAway f r)) := hψr
  rw [hr, map_mul] at hψr
  rw [X.map_comp_apply]
  exact h_sub B ω (isUnit_of_mul_isUnit_left hψr)

/-! ### The lifting criterion for étale coordinates -/

/-- The ring homomorphism k[X_i] → R sending X_i to x_i. -/
abbrev polyEval : MvPolynomial (Fin d) k →+* R := (aeval (R := k) x).toRingHom

/-- The ring of a chart a as an algebra over the polynomial ring k[X_1, …, X_d], with X_i sent
to the i-th coordinate of a. -/
abbrev EtaleChart.polyAlgebra : Algebra (MvPolynomial (Fin d) k) a.coordRing :=
  (polyEval a.coordinate).toAlgebra

attribute [local instance] EtaleChart.polyAlgebra

/-- The ring of a chart is smooth over `k`. -/
instance : Smooth k a.coordRing := by
  -- `a.coordRing` is étale over the polynomial ring, which is smooth over `k`.
  have : Smooth k (MvPolynomial (Fin d) k) := {}
  have : Smooth (MvPolynomial (Fin d) k) a.coordRing := a.etale.instSmooth
  exact .comp k (MvPolynomial (Fin d) k) a.coordRing

/-- If a map φ : R → A of k-algebras sends each x i to b i, it sends the value of a polynomial at x
to its value at b. -/
lemma map_aeval_of_forall_eq {x : Fin d → R} {b : Fin d → A} (φ : R ⟶ A)
    (hφ : ∀ i : Fin d, φ (x i) = b i) (p : MvPolynomial (Fin d) k) :
    φ (aeval x p) = aeval b p := by
  rw [← funext hφ]
  exact comp_aeval_apply _ φ.hom p

variable {x} [IsNoetherianRing k]

omit [IsNoetherianRing k] in
/-- Let x₁, …, x_d be elements of a k-algebra R for which k[X_i] → R, X_i ↦ x_i, is étale.
Along a square-zero extension π: B → A of k-algebras each ζ: R → A lifts uniquely once lifts
b_i of the ζ(x_i) are prescribed. -/
lemma existsUnique_lift_of_etale_polyEval (h_et : (polyEval x).Etale) {π : B ⟶ A}
    (hπ : IsSquareZero π) (ζ : R ⟶ A) (b : Fin d → B) (hb : ∀ i : Fin d, π (b i) = ζ (x i)) :
    ∃! s : R ⟶ B, s ≫ π = ζ ∧ ∀ i : Fin d, s (x i) = b i := by
  obtain ⟨h_surj, h_sq⟩ := hπ
  -- View `R`, `B`, `A` as algebras over the polynomial ring through `x`, `b`, `ζ ∘ x`. Then `ζ`
  -- and `π` are algebra maps, and so is a map `t : R ⟶ B` exactly when it sends `x` to `b`.
  algebraize [polyEval x, polyEval b, polyEval (ζ ∘ x)]
  let ζ' : R →ₐ[MvPolynomial (Fin d) k] A := ⟨ζ.hom, map_aeval_of_forall_eq ζ fun i ↦ rfl⟩
  let π' : B →ₐ[MvPolynomial (Fin d) k] A := ⟨π.hom, map_aeval_of_forall_eq π hb⟩
  -- The lift `s` exists by formal smoothness.
  have h_smooth : FormallySmooth (MvPolynomial (Fin d) k) R := h_et.instSmooth.formallySmooth
  let s := FormallySmooth.liftOfSurjective ζ' π' h_surj ⟨2, h_sq⟩
  have hs (r : R) : π (s r) = ζ r :=
    FormallySmooth.liftOfSurjective_apply ζ' π' h_surj ⟨2, h_sq⟩ r
  refine ⟨ofHom (s.restrictScalars k), ⟨hom_ext (ext hs), fun i ↦ ?_⟩, fun t ⟨ht, htb⟩ ↦ ?_⟩
  · simpa [RingHom.algebraMap_toAlgebra] using! s.commutes (X i)
  · -- It is unique because `R` is formally unramified.
    let t' : R →ₐ[MvPolynomial (Fin d) k] B := ⟨t.hom, map_aeval_of_forall_eq t htb⟩
    have h_eq : t' = s := h_et.formallyUnramified.ext' π.hom.toRingHom ⟨2, h_sq⟩ t' s (by aesop)
    exact hom_ext (ext fun r ↦ DFunLike.congr_fun h_eq r)

/-- Let x₁, …, x_d be elements of a k-algebra R of finite type, k Noetherian. If each ζ: R → A lifts
uniquely along square-zero extensions B → A once lifts of the ζ(x_i) are prescribed, then
k[X_i] → R, X_i ↦ x_i, is étale. -/
lemma etale_polyEval_of_existsUnique_lift [FiniteType k R]
    (h_lift : ∀ ⦃A B : CommAlg k⦄ (π : B ⟶ A), IsSquareZero π → ∀ (ζ : R ⟶ A) (b : Fin d → B),
      (∀ i : Fin d, π (b i) = ζ (x i)) →
        ∃! s : R ⟶ B, s ≫ π = ζ ∧ ∀ i : Fin d, s (x i) = b i) :
    (polyEval x).Etale := by
  let : Algebra (MvPolynomial (Fin d) k) R := (polyEval x).toAlgebra
  suffices h_formal : FormallyEtale (MvPolynomial (Fin d) k) R from
    -- Finite presentation comes from finite type, the polynomial ring being Noetherian.
    ⟨h_formal, Algebra.FinitePresentation.of_finiteType.1
      (.of_restrictScalars_finiteType k (MvPolynomial (Fin d) k) R)⟩
  -- Maps `ζ : R → B ⧸ I` with `I ^ 2 = 0` have to lift uniquely to `B`.
  refine FormallyEtale.iff_comp_bijective.2 fun B _ _ I hI ↦ ?_
  rw [Function.bijective_iff_existsUnique]
  intro ζ
  -- Apply `h_lift` to `B → B ⧸ I`, with the images of the variables in `B` as prescribed lifts.
  algebraize [(algebraMap (MvPolynomial (Fin d) k) B).comp C]
  have h_sq : IsSquareZero (ofHom (mkₐ k I)) :=
    ⟨Quot.mk_surjective, show RingHom.ker (Ideal.Quotient.mk I) ^ 2 = ⊥ by rw [mk_ker, hI]⟩
  have h_var (i : Fin d) : mkₐ k I (algebraMap (MvPolynomial (Fin d) k) B (X i)) = ζ (x i) := by
    simpa [RingHom.algebraMap_toAlgebra] using (ζ.commutes (X i)).symm
  obtain ⟨s, ⟨hs, hsx⟩, h_uniq⟩ : ∃! s : R ⟶ CommAlgCat.of k B,
      s ≫ ofHom (mkₐ k I) = ofHom (ζ.restrictScalars k) ∧
        ∀ i : Fin d, s (x i) = algebraMap (MvPolynomial (Fin d) k) B (X i) :=
    h_lift _ h_sq _ _ h_var
  -- `s` is linear over the polynomial ring, since it sends each `x i` to the image of `X i`.
  have h_comm : s.hom.comp (aeval x) = algHom k (MvPolynomial (Fin d) k) B := by aesop
  let s' : R →ₐ[MvPolynomial (Fin d) k] B := ⟨s.hom, AlgHom.congr_fun h_comm⟩
  refine ⟨s', ext fun r ↦ ConcreteCategory.congr_hom hs r, fun t ht ↦ ?_⟩
  have ht_var (i : Fin d) : t (x i) = algebraMap (MvPolynomial (Fin d) k) B (X i) := by
    simpa [RingHom.algebraMap_toAlgebra] using t.commutes (X i)
  have ht_lift : ofHom (t.restrictScalars k) ≫ ofHom (mkₐ k I) = ofHom (ζ.restrictScalars k) := by
    aesop
  have h_eq : ofHom (t.restrictScalars k) = s := h_uniq _ ⟨ht_lift, ht_var⟩
  exact ext fun r ↦ ConcreteCategory.congr_hom h_eq r

/-- Infinitesimal criterion: for k Noetherian, R of finite type and finitely many x_i ∈ R,
k[X_i] → R, X_i ↦ x_i, is étale iff each ζ: R → A lifts uniquely along square-zero
extensions B → A of k-algebras once lifts of the ζ(x_i) are prescribed. -/
lemma etale_polyEval_iff [FiniteType k R] :
    (polyEval x).Etale ↔
      ∀ ⦃A B : CommAlg k⦄ (π : B ⟶ A), IsSquareZero π → ∀ (ζ : R ⟶ A) (b : Fin d → B),
        (∀ i : Fin d, π (b i) = ζ (x i)) →
          ∃! s : R ⟶ B, s ≫ π = ζ ∧ ∀ i : Fin d, s (x i) = b i :=
  ⟨fun h_et _ _ _ hπ ζ b hb ↦ existsUnique_lift_of_etale_polyEval h_et hπ ζ b hb,
    etale_polyEval_of_existsUnique_lift⟩

/-- Over a Noetherian ring k, two maps out of the ring of an étale chart are equal if they agree
modulo a square-zero ideal and agree on the coordinates. -/
lemma EtaleChart.lift_unique (a : EtaleChart d X) {π : B ⟶ A} (hπ : IsSquareZero π)
    {s t : a.coordRing ⟶ B} (h_comp : s ≫ π = t ≫ π)
    (h_coord : ∀ i : Fin d, s (a.coordinate i) = t (a.coordinate i)) :
    s = t := by
  have h_exists : ∃! r : a.coordRing ⟶ B,
      r ≫ π = t ≫ π ∧ ∀ i : Fin d, r (a.coordinate i) = t (a.coordinate i) :=
    etale_polyEval_iff.1 a.etale π hπ (t ≫ π) _ fun i ↦ rfl
  exact h_exists.unique ⟨h_comp, h_coord⟩ ⟨rfl, fun i ↦ rfl⟩

/-! ### Shrinking a chart -/

/-- Over a Noetherian ring k, let a be a chart with ring a.coordRing and point a.point, and φ a map
from a.coordRing to an algebra R of finite type that sends a.point to y. If y embeds Spec R as an
open subfunctor, this is the chart on R with point y and the images of the coordinates of a. -/
def EtaleChart.restrict [FiniteType k R] {φ : a.coordRing ⟶ R} {y : X.obj R}
    (e : X.map φ a.point = y)
    (i : ∀ A : CommAlg k, Function.Injective (X.map (X := R) (Y := A) · y))
    (h : IsOpenSubfunctor (Subfunctor.range (pointMap y))) :
    EtaleChart d X where
  coordRing := R
  point := y
  coordinate := φ ∘ a.coordinate
  etale := by
    -- Lift `φ ≫ ζ` in the chart `a`, then factor the lift through `φ`.
    subst e
    refine etale_polyEval_iff.2 fun A B π hπ ζ v hv ↦ ?_
    obtain ⟨s, hs, h_unique⟩ := etale_polyEval_iff.1 a.etale π hπ (φ ≫ ζ) v hv
    -- Membership in the open image of `y` is not changed by a square-zero extension.
    have h_mem : X.map π (X.map s a.point) ∈ Subfunctor.range (pointMap (X.map φ a.point)) A := by
      rw [← X.map_comp_apply, hs.1, X.map_comp_apply]
      exact ⟨⟨ζ⟩, rfl⟩
    obtain ⟨⟨t : R ⟶ B⟩, ht⟩ := h.mem_of_isSquareZero π hπ _ h_mem
    obtain rfl : s = φ ≫ t := a.eq_comp_of_map_point_eq _ ht.symm
    -- `φ` can be cancelled on the left, so `t` is the unique lift of `ζ`.
    refine ⟨t, ?_⟩
    simp_rw [← (i _).eq_iff, ← map_comp_apply, (a.injective _).eq_iff]
    exact ⟨⟨(Category.assoc φ t π).symm.trans hs.1, hs.2⟩,
      fun t' ⟨ht', ht'_coord⟩ ↦ h_unique (φ ≫ t') ⟨(Category.assoc φ t' π).trans ht', ht'_coord⟩⟩
  injective := i
  isOpenSubfunctor := h

/-- For k Noetherian, a chart a of X and an element g of its ring R, the chart on R[1/g] with the
images of the point and coordinates of a. -/
def EtaleChart.away (g : a.coordRing) : EtaleChart d X :=
  a.restrict (φ := CommAlg.toAway g) rfl
    (i := by
      -- Maps out of the localization that agree on `a.coordRing` are equal.
      intro A φ ψ e
      have h_agree : a.coordRing.toAway g ≫ φ = a.coordRing.toAway g ≫ ψ :=
        a.eq_comp_of_map_point_eq _ ((map_comp_apply ..).trans e)
      exact hom_ext (IsLocalization.algHom_ext (Submonoid.powers g) (congrArg Hom.hom h_agree)))
    (h := by
      -- The image lies in `a.locus`, so by `EtaleChart.isOpenSubfunctor_of_le_locus` it is enough
      -- that it is open in `a.locus`.
      refine a.isOpenSubfunctor_of_le_locus ?_ ?_
      · rintro A _ ⟨χ, rfl⟩
        exact a.locus.map _ (a.mem_locus_iff.2 ⟨_, rfl⟩)
      · -- The ideal of the point given by `ψ` is spanned by `ψ g`: a map factors through the
        -- localization if and only if it sends `g` to a unit.
        rintro A ⟨z, ⟨ψ : a.coordRing ⟶ A⟩, rfl⟩
        refine ⟨span {ψ g}, fun B φ ↦ ULift.exists.trans ?_⟩
        -- By injectivity of the chart, equal points come from equal maps out of `a.coordRing`.
        simpa [← (injective ..).eq_iff, map_span]
          using! CommAlg.exists_toAway_comp_iff g (ψ ≫ φ))

/-- Over a Noetherian ring k, the point given by φ: a.coordRing → B lies in the part of the chart a
where g is inverted iff φ(g) is a unit. -/
lemma EtaleChart.mem_locus_away (a : EtaleChart d X) (g : a.coordRing) {B : CommAlg k}
    (φ : a.coordRing ⟶ B) :
    X.map φ a.point ∈ (a.away g).locus B ↔ IsUnit (φ g) := by
  calc X.map φ a.point ∈ (a.away g).locus B
    _ ↔ ∃ χ : .of k (Localization.Away g) ⟶ B,
        X.map χ (X.map (CommAlg.toAway g) a.point) = X.map φ a.point := (a.away g).mem_locus_iff
    _ ↔ ∃ χ : .of k (Localization.Away g) ⟶ B, CommAlg.toAway g ≫ χ = φ :=
      exists_congr fun χ ↦ by simp only [← X.map_comp_apply, (a.injective B).eq_iff]
    _ ↔ IsUnit (φ g) := CommAlg.exists_toAway_comp_iff g φ

/-- Charts can be shrunk, for k Noetherian: if U ⊂ X is open, charts of dimension d cover the points
of X in fields, and x ∈ U(A) with A a field, then x lies in the image of a chart of dimension d
whose point lies in U. -/
lemma IsOpenSubfunctor.exists_mem_locus_and_point_mem [IsChartCovered d X] {U : Subfunctor X}
    {A : CommAlg k} {x : X.obj A} (hU : IsOpenSubfunctor U) (hA : IsField A) (hx : x ∈ U A) :
    ∃ a : EtaleChart d X, x ∈ a.locus A ∧ a.point ∈ U a.coordRing := by
  -- Take a chart around `x` and invert a function `f` on it that does not vanish at `x` and
  -- whose non-vanishing locus lies in `U`.
  obtain ⟨a, ha⟩ := IsChartCovered.exists_chart (d := d) A hA x
  obtain ⟨φ, rfl⟩ := a.mem_locus_iff.1 ha
  obtain ⟨f, hf, h_sub⟩ := hU.exists_basicOpen φ a.point hA hx
  let : Field A := hA.toField
  exact ⟨a.away f, (a.mem_locus_away f φ).2 hf.isUnit,
    h_sub _ (a.coordRing.toAway f) (algebraMap_isUnit f)⟩

/-! ### Products and intersections of charts -/

/-- For commutative k-algebras A and B, the k-algebra map A → A ⊗_k B, a ↦ a ⊗ 1, as a morphism in
`New.Variety.CommAlg` k. -/
abbrev tensorInl : A ⟶ CommAlgCat.of k (A ⊗[k] B) := ofHom includeLeft

/-- For commutative k-algebras A and B, the k-algebra map B → A ⊗_k B, b ↦ 1 ⊗ b, as a morphism in
`New.Variety.CommAlg` k. -/
abbrev tensorInr : B ⟶ CommAlgCat.of k (A ⊗[k] B) := ofHom includeRight

omit [IsNoetherianRing k] in
/-- Two maps φ: A → R and ψ: B → R of k-algebras come from a unique map
A ⊗_k B → R. -/
lemma existsUnique_tensor_desc (φ : A ⟶ R) (ψ : B ⟶ R) :
    ∃! χ : CommAlgCat.of k (A ⊗[k] B) ⟶ R, tensorInl ≫ χ = φ ∧ tensorInr ≫ χ = ψ :=
  ⟨ofHom (productMap φ.hom' ψ.hom'), by aesop⟩

omit [IsNoetherianRing k] in
/-- Let `a` be a chart of `X` and `b` a chart of `Y`. Their points give a point of `X × Y` over
`a.coordRing ⊗ b.coordRing`. Its image in `X × Y` is the intersection of the preimages of `a.locus`
and `b.locus` under the two projections. -/
lemma range_pointMap_prod (a : EtaleChart d X) (b : EtaleChart n Y) :
    Subfunctor.range (pointMap (X.map tensorInl a.point, Y.map tensorInr b.point)) =
      a.locus.preimage (SemiCartesianMonoidalCategory.fst X Y) ⊓
        b.locus.preimage (SemiCartesianMonoidalCategory.snd X Y) := by
  apply le_antisymm
  · -- A map out of `a.coordRing ⊗ b.coordRing` restricts to a map out of each factor.
    rintro A _ ⟨⟨χ : CommAlgCat.of k (a.coordRing ⊗[k] b.coordRing) ⟶ A⟩, rfl⟩
    exact ⟨a.locus.map χ (a.mem_locus_iff.2 ⟨tensorInl, rfl⟩),
      b.locus.map χ (b.mem_locus_iff.2 ⟨tensorInr, rfl⟩)⟩
  · -- Maps `φ`, `ψ` out of the factors come from one map `χ` out of the tensor product.
    rintro A ⟨x, y⟩ ⟨hx : x ∈ a.locus A, hy : y ∈ b.locus A⟩
    obtain ⟨φ, rfl⟩ := a.mem_locus_iff.1 hx
    obtain ⟨ψ, rfl⟩ := b.mem_locus_iff.1 hy
    obtain ⟨χ, rfl, rfl⟩ := (existsUnique_tensor_desc φ ψ).exists
    exact ⟨.up χ, Prod.ext (X.map_comp_apply ..).symm (Y.map_comp_apply ..).symm⟩

/-- For k Noetherian and charts a of X and b of Y, the chart of X×Y on a.coordRing ⊗ b.coordRing,
with coordinates x_i⊗1 and 1⊗y_j, where x and y are the coordinates of a and b. -/
def EtaleChart.prod : EtaleChart (d + n) (X ⊗ Y) :=
  -- The point is the pair of the images of `a.point` and `b.point`.
  mk (coordRing := CommAlgCat.of k (a.coordRing ⊗[k] b.coordRing))
    (point := (X.map tensorInl a.point, Y.map tensorInr b.point))
    (coordinate := append (fun i ↦ a.coordinate i ⊗ₜ 1) fun j ↦ 1 ⊗ₜ b.coordinate j)
    (etale := by
      -- A map out of the tensor product is a pair of maps (`existsUnique_tensor_desc`): lift each
      -- factor.
      have h_smooth : Smooth k (a.coordRing ⊗[k] b.coordRing) := .comp k a.coordRing _
      refine etale_polyEval_iff.2 fun A B π hπ ζ v hv ↦ ?_
      simp only [forall_fin_add, append_left, append_right] at hv ⊢
      obtain ⟨hv_left, hv_right⟩ := hv
      obtain ⟨s, ⟨hs, hs_coord⟩, hs_unique⟩ :=
        etale_polyEval_iff.1 a.etale π hπ (tensorInl ≫ ζ) _ hv_left
      obtain ⟨t, ⟨ht, ht_coord⟩, ht_unique⟩ :=
        etale_polyEval_iff.1 b.etale π hπ (tensorInr ≫ ζ) _ hv_right
      obtain ⟨χ, ⟨rfl, rfl⟩, hχ_unique⟩ := existsUnique_tensor_desc s t
      refine ⟨χ, ⟨(existsUnique_tensor_desc (tensorInl ≫ ζ) (tensorInr ≫ ζ)).unique ⟨hs, ht⟩
        ⟨rfl, rfl⟩, hs_coord, ht_coord⟩, ?_⟩
      -- Another lift restricts to lifts on both factors, which are unique.
      rintro χ' ⟨rfl, h_left, h_right⟩
      exact hχ_unique χ' ⟨hs_unique _ ⟨rfl, h_left⟩, ht_unique _ ⟨rfl, h_right⟩⟩)
    (injective :=
      fun A φ ψ e ↦ by
        -- The two components of `e` say that `φ` and `ψ` agree on `a.coordRing` and on
        -- `b.coordRing`.
        have h_comp : tensorInl ≫ φ = tensorInl ≫ ψ ∧ tensorInr ≫ φ = tensorInr ≫ ψ := by
          simpa [← (injective ..).eq_iff] using! Prod.ext_iff.1 e
        exact (existsUnique_tensor_desc (tensorInl ≫ ψ) (tensorInr ≫ ψ)).unique h_comp ⟨rfl, rfl⟩)
    -- The image is the intersection of the preimages of `a.locus` and `b.locus`.
    (isOpenSubfunctor := by
      rw [range_pointMap_prod]
      exact (a.isOpenSubfunctor.preimage (SemiCartesianMonoidalCategory.fst X Y)).inf
        (b.isOpenSubfunctor.preimage (SemiCartesianMonoidalCategory.snd X Y)))

/-- The pair `(x, y)` lies in the image of the product of the charts `a` and `b` iff `x` lies in the
image of `a` and `y` in that of `b`. -/
lemma EtaleChart.mem_locus_prod_iff (a : EtaleChart d X) (b : EtaleChart n Y) {x : X.obj A}
    {y : Y.obj A} : (x, y) ∈ (a.prod b).locus.obj A ↔ x ∈ a.locus.obj A ∧ y ∈ b.locus.obj A := by
  have h_locus : (a.prod b).locus = a.locus.preimage (SemiCartesianMonoidalCategory.fst X Y) ⊓
      b.locus.preimage (SemiCartesianMonoidalCategory.snd X Y) :=
    range_pointMap_prod a b
  rw [h_locus]
  exact Iff.rfl

/-- If `X` has an atlas of dimension d, charts of dimension d cover the field-valued points of
`X`. -/
instance HasAtlas.isChartCovered [h : HasAtlas d X] : IsChartCovered d X := by
  obtain ⟨n, a, h_cover⟩ := h.exists_finite_charts
  exact ⟨fun K hK x ↦ (h_cover K hK x).elim fun i hi ↦ ⟨a i, hi⟩⟩

/-- Let k be Noetherian. If charts of dimension d cover the field-valued points of `X` and charts
of dimension n cover those of `Y`, then products of such charts, of dimension d + n, cover the
field-valued points of `X × Y`. -/
instance IsChartCovered.prod [IsChartCovered d X] [IsChartCovered n Y] :
    IsChartCovered (d + n) (X ⊗ Y) := by
  -- Take the product of charts around the two components.
  refine ⟨fun K hK ⟨x₁, x₂⟩ ↦ ?_⟩
  obtain ⟨a, ha⟩ := exists_chart (d := d) K hK x₁
  obtain ⟨b, hb⟩ := exists_chart (d := n) K hK x₂
  exact ⟨a.prod b, (a.mem_locus_prod_iff b).2 ⟨ha, hb⟩⟩

/-- Over a Noetherian ring k, if `X` is separated, the intersection of the images of two charts `a`
and `b` is the image of a chart with as many coordinates as `b`. -/
lemma EtaleChart.exists_locus_eq_inf (a : EtaleChart d X) [IsSeparatedFunctor X]
    (b : EtaleChart n X) : ∃ c : EtaleChart n X, c.locus = a.locus ⊓ b.locus := by
  -- Let `p` be the universal pair of points over `a.coordRing ⊗ b.coordRing` and `J` the ideal
  -- where its two components agree. The common value `y` over the quotient by `J` represents
  -- `a.locus ⊓ b.locus`.
  let p : (X ⊗ X).obj (a.prod b).coordRing := (a.prod b).point
  obtain ⟨J, hJ⟩ : ∃ J : Ideal (a.prod b).coordRing,
    ∀ (B : CommAlg k) (φ : (a.prod b).coordRing ⟶ B),
      X.map φ p.1 = X.map φ p.2 ↔ J ≤ RingHom.ker φ.hom :=
    IsSeparatedFunctor.exists_ideal (a.prod b).coordRing p.1 p.2
  let π : (a.prod b).coordRing ⟶ .of k ((a.prod b).coordRing ⧸ J) := ofHom (mkₐ k J)
  have hπ : X.map π p.1 = X.map π p.2 := (hJ _ π).2 mk_ker.ge
  let y : X.obj (.of k ((a.prod b).coordRing ⧸ J)) := X.map π p.2
  have h_diag {B : CommAlg k} (χ : .of k ((a.prod b).coordRing ⧸ J) ⟶ B) :
      (X ⊗ X).map (π ≫ χ) p = (X.map χ y, X.map χ y) := by
    rw [(X ⊗ X).map_comp_apply]
    exact Prod.ext (congrArg (X.map χ) hπ) rfl
  -- `χ` is determined by `X.map χ y`, since the product is a chart and `π` is surjective.
  have h_inj (B : CommAlg k) :
      Function.Injective fun χ : .of k ((a.prod b).coordRing ⧸ J) ⟶ B ↦ X.map χ y := by
    intro χ χ' h_eq
    have h_pair : (X ⊗ X).map (π ≫ χ) p = (X ⊗ X).map (π ≫ χ') p := by
      rw [h_diag, h_diag]
      exact Prod.ext h_eq h_eq
    have h_comp : π ≫ χ = π ≫ χ' := (a.prod b).injective B h_pair
    exact hom_ext (algHom_ext _ (congrArg Hom.hom h_comp))
  have h_range : Subfunctor.range (pointMap y) = a.locus ⊓ b.locus := by
    ext B x
    refine Iff.trans ?_ (mem_locus_prod_iff a b)
    constructor
    · rintro ⟨⟨χ⟩, hχ : X.map χ y = x⟩
      exact ⟨⟨π ≫ χ⟩, (h_diag χ).trans (by rw [hχ])⟩
    · -- A map `ψ` that sends `p` to the diagonal kills `J`, so it factors through `π`.
      rintro ⟨⟨ψ⟩, hψ : (X ⊗ X).map ψ p = (x, x)⟩
      obtain ⟨h_fst, h_snd⟩ : X.map ψ p.1 = x ∧ X.map ψ p.2 = x := Prod.ext_iff.1 hψ
      have h_ker : J ≤ RingHom.ker ψ.hom := (hJ B ψ).1 (h_fst.trans h_snd.symm)
      let χ : .of k ((a.prod b).coordRing ⧸ J) ⟶ B := ofHom (liftₐ J ψ.hom h_ker)
      exact ⟨⟨χ⟩, (X.map_comp_apply π χ p.2).symm.trans h_snd⟩
  have h_open : IsOpenSubfunctor (Subfunctor.range (pointMap y)) := by
    simpa [h_range] using a.isOpenSubfunctor.inf b.isOpenSubfunctor
  exact ⟨b.restrict (φ := tensorInr ≫ π) (map_comp_apply ..) h_inj h_open, h_range⟩

/-! ### Differentials, equality of points, preimages of charts -/

section

omit [IsNoetherianRing k]

/-- The Kähler differentials over k of the ring of a chart with d étale
coordinates have a basis of d elements. -/
lemma EtaleChart.nonempty_basis_kaehler (a : EtaleChart d X) :
    Nonempty (Module.Basis (Fin d) a.coordRing Ω[a.coordRing⁄k]) := by
  -- Differentials commute with formally étale base change from the polynomial ring.
  have : FormallyEtale (MvPolynomial (Fin d) k) a.coordRing := a.etale.formallyEtale
  exact ⟨(isBaseChange_of_formallyEtale k (MvPolynomial (Fin d) k) a.coordRing).basis
    (mvPolynomialBasis k (Fin d))⟩

/-- Let a be a chart with ring R, point y and coordinates x_i. There is e ∈ R ⊗ R such that, for
every map χ: R ⊗ R → C, the images of y in X(C) along r ↦ χ(r ⊗ 1) and r ↦ χ(1 ⊗ r)
agree exactly when χ(e) is a unit and χ kills x_i ⊗ 1 - 1 ⊗ x_i for each i. -/
lemma EtaleChart.exists_eq_iff_coordinate_eq (a : EtaleChart d X) :
    ∃ e : ↑(a.coordRing ⊗ a.coordRing), ∀ (C : CommAlg k) (χ : a.coordRing ⊗ a.coordRing ⟶ C),
      X.map χ (X.map tensorInl a.point) = X.map χ (X.map tensorInr a.point) ↔
        IsUnit (χ e) ∧ ∀ i : Fin d, χ (a.coordinate i ⊗ₜ 1 - 1 ⊗ₜ a.coordinate i) = 0 := by
  -- `a.coordRing` is unramified over the polynomial ring `P` of the coordinates, so
  -- `a.coordRing ⊗[P] a.coordRing` has an element `elem` with product 1 on which `1 ⊗ s` and
  -- `s ⊗ 1` act alike; `T` lists its terms.
  obtain ⟨h_etale, h_finite⟩ := a.etale
  obtain ⟨T, hT⟩ := (elem (MvPolynomial (Fin d) k) a.coordRing).exists_finset
  refine ⟨∑ j ∈ T, j.1 ⊗ₜ j.2, fun C χ ↦ ?_⟩
  -- Restate the claim for the restrictions `p`, `q` of `χ` to the two factors, using `a.injective`.
  let p : a.coordRing ⟶ C := tensorInl ≫ χ
  let q : a.coordRing ⟶ C := tensorInr ≫ χ
  have h_point : X.map χ (X.map tensorInl a.point) = X.map χ (X.map tensorInr a.point) ↔
      p = q := by
    simp only [← X.map_comp_apply]
    exact (a.injective C).eq_iff
  have h_tmul (r s : a.coordRing) : χ (r ⊗ₜ s) = p r * q s := by simp [p, q, ← map_mul]
  suffices h_iff : p = q ↔ IsUnit (∑ j ∈ T, p j.1 * q j.2) ∧
      ∀ i : Fin d, p (a.coordinate i) = q (a.coordinate i) by
    simpa [h_tmul, sub_eq_zero] using h_point.trans h_iff
  refine ⟨fun h_eq ↦ ?_, fun ⟨h_unit, h_eq⟩ ↦ ?_⟩
  · -- For `p = q` the sum is the image of the product of `elem`, which is 1.
    have h_elem : IsUnit (p (lmul' _ (∑ j ∈ T, j.1 ⊗ₜ[MvPolynomial (Fin d) k] j.2))) := by
      simp [← hT, lmul_elem]
    simpa [← h_eq] using h_elem
  · -- Equal coordinates make `p` and `q` maps of `P`-algebras, so `p ⊗ q` is defined on
    -- `a.coordRing ⊗[P] a.coordRing`; it turns the property of `elem` into `q s * ∑ = p s * ∑`.
    let : Algebra (MvPolynomial (Fin d) k) C := (polyEval (p ∘ a.coordinate)).toAlgebra
    let p' : a.coordRing →ₐ[MvPolynomial (Fin d) k] C :=
      ⟨p.hom, map_aeval_of_forall_eq p fun i ↦ rfl⟩
    let q' : a.coordRing →ₐ[MvPolynomial (Fin d) k] C :=
      ⟨q.hom, map_aeval_of_forall_eq q fun i ↦ (h_eq i).symm⟩
    have h_elem : productMap p' q' (elem (MvPolynomial (Fin d) k) a.coordRing) =
        ∑ j ∈ T, p j.1 * q j.2 := by
      simp [hT]
      rfl
    refine hom_ext (ext fun s ↦ h_unit.mul_right_cancel ?_)
    calc p s * ∑ j ∈ T, p j.1 * q j.2
      _ = productMap p' q' ((s ⊗ₜ 1) * elem (MvPolynomial (Fin d) k) a.coordRing) := by
        simp [h_elem, show p' s = p s from rfl]
      _ = productMap p' q' ((1 ⊗ₜ s) * elem (MvPolynomial (Fin d) k) a.coordRing) := by
        rw [one_tmul_mul_elem]
      _ = q s * ∑ j ∈ T, p j.1 * q j.2 := by
        simp [h_elem, show q' s = q s from rfl]

/-- For a monomorphism u: Y → X and a point y of Y over the ring of a
chart a with u(y) the point of a, the image of y is the preimage under u of the image of a. -/
lemma EtaleChart.range_pointMap_eq_preimage_locus {y : Y.obj a.coordRing}
    (h : u.app a.coordRing y = a.point) :
    Subfunctor.range (pointMap y) = a.locus.preimage u := by
  ext A z
  simp [← h, (injective_of_mono _).eq_iff, ← pointMap_comp]

end

/-- For u: Y → X injective on points and a chart a of X whose point is u(y), the chart of Y with the
same ring and coordinates and the point y. -/
def EtaleChart.comap (y : Y.obj a.coordRing) (h : u.app a.coordRing y = a.point) :
    EtaleChart d Y where
  coordRing := a.coordRing
  point := y
  coordinate := a.coordinate
  etale := a.etale
  -- `u` sends `Y.map φ y` to `X.map φ a.point`.
  injective A φ ψ e := a.injective A (by simpa [h] using congrArg (u.app A) e)
  isOpenSubfunctor := by
    rw [a.range_pointMap_eq_preimage_locus u h]
    exact a.isOpenSubfunctor.preimage u

/-- Let u: Y → X be a monomorphism with open image, over a Noetherian ring k. If charts of dimension
d cover the field-valued points of X, the same holds for Y. -/
lemma IsChartCovered.comap [IsChartCovered d X] (hu : IsOpenSubfunctor (Subfunctor.range u)) :
    IsChartCovered d Y := by
  -- Shrink a chart around `u K x` until its point is `u _ y` for some `y`, and pull it back.
  refine ⟨fun K hK x ↦ ?_⟩
  obtain ⟨a, hx, y, hy⟩ := hu.exists_mem_locus_and_point_mem (d := d) hK (x := u.app K x) ⟨x, rfl⟩
  exact ⟨a.comap u y hy, (a.range_pointMap_eq_preimage_locus u hy).ge _ hx⟩

/-! ### Covering by pieces étale over tori -/

/-- Two properties of a subfunctor `V` of `X`.
(a) `V` is locally everything: for each `y ∈ X(A)` and maximal ideal `m` of `A` there is an
`a ∉ m` such that `y` maps into `V` along every `A → B` that makes `a` a unit.
(b) `ℤ[V]` lies in every class `P` of functors to abelian groups that satisfies
`New.Variety.IsClosedClass` and contains `ℤ[Hom(R, -)]` for the ring `R` of each chart of `X` (of
any dimension) whose coordinates are all units, that is, étale over a torus. -/
def IsCharting (V : Subfunctor X) : Prop :=
  IsZariskiLocallyTop (forget₂ (CommAlg k) CommRingCat) V ∧
  ∀ P : CommAlg k ⥤ Ab → Prop, IsClosedClass P →
    (∀ {d : ℕ} (b : EtaleChart d X),
      (∀ j : Fin d, IsUnit (b.coordinate j)) → P (freeAb (reprBy b.coordRing))) →
    P (freeAb V.toFunctor)

open Classical in
/-- Over a Noetherian ring k, the coordinates of a chart stay étale when those with index in `S` are
shifted by 1. -/
lemma EtaleChart.etale_polyEval_coordinate_add_ite (a : EtaleChart d X) (S : Set (Fin d)) :
    (polyEval (k := k) fun j : Fin d ↦ a.coordinate j + if j ∈ S then 1 else 0).Etale := by
  refine etale_polyEval_iff.2 fun A B π hπ ζ v hv ↦ ?_
  -- Lifting the shifted coordinates is lifting the old ones, with the values shifted back.
  let v' (j : Fin d) : B := v j - if j ∈ S then 1 else 0
  have hv' (j : Fin d) : π (v' j) = ζ (a.coordinate j) := by
    by_cases hj : j ∈ S <;> simpa [v', hj, sub_eq_iff_eq_add] using hv j
  simpa [v', eq_sub_iff_add_eq] using etale_polyEval_iff.1 a.etale π hπ ζ v' hv'

/-- Let k be Noetherian, `X` separated and `u` a finite family of charts of `X` whose coordinates
are units. Let `P` be a closed class of functors to abelian groups (it contains `0` and, given a
short exact sequence whose first term is in it, contains the second term iff the third). If `P`
contains the free abelian functor `ℤ[Hom(b.coordRing, -)]` for each chart `b` whose coordinates are
units, it contains `ℤ[⋃ (u p).locus]`. -/
lemma IsClosedClass.freeAb_iSup_locus [IsSeparatedFunctor X] {P : CommAlg k ⥤ Ab → Prop}
    (hP : IsClosedClass P)
    (h_unit : ∀ b : EtaleChart d X, (∀ j : Fin d, IsUnit (b.coordinate j)) →
      P (freeAb (reprBy b.coordRing)))
    {ι : Type} [Finite ι] (u : ι → EtaleChart d X)
    (hu : ∀ (p : ι) (j : Fin d), IsUnit ((u p).coordinate j)) :
    P (freeAb (⨆ p : ι, (u p).locus).toFunctor) := by
  -- Apply `IsClosedClass.freeAb_iSup` to the set of images of the charts inside some `u p`.
  let S : Set (Subfunctor X) := {V | ∃ b : EtaleChart d X, b.locus = V ∧ ∃ p, V ≤ (u p).locus}
  have h_mem (p : ι) : (u p).locus ∈ S := ⟨u p, rfl, p, le_rfl⟩
  have h_class : ∀ V ∈ S, P (freeAb V.toFunctor) := by
    -- On `b.coordRing` the coordinates of `u p` give a chart `b'` whose coordinates are units.
    rintro _ ⟨b, rfl, p, hb⟩
    obtain ⟨φ, hφ⟩ := (u p).mem_locus_iff.1 (hb b.coordRing b.point_mem_locus)
    let b' : EtaleChart d X := (u p).restrict hφ b.injective b.isOpenSubfunctor
    exact (hP.iff_of_isIso (freeAb.map (Subfunctor.toRange (pointMap b.point)))).1
      (h_unit b' fun j ↦ (hu p j).map φ.hom)
  have h_inf : ∀ V ∈ S, ∀ W ∈ S, V ⊓ W ∈ S := by
    -- `X` is separated, so the intersection of two charts is a chart.
    rintro _ ⟨b, rfl, p, hb⟩ _ ⟨c, rfl, -⟩
    exact (b.exists_locus_eq_inf c).imp fun e he ↦ ⟨he, p, inf_le_left.trans hb⟩
  exact hP.freeAb_iSup S h_class h_inf h_mem

/-- Let `k` be Noetherian and let `X` be a functor on commutative `k`-algebras with an atlas of
dimension `d` (`HasAtlas d X`): `X` is separated and has finitely many charts, each with exactly `d`
étale coordinates, that together contain every field-valued point. Then some subfunctor `V` of `X`
satisfies `IsCharting`. (a) For each `y ∈ X(A)` and maximal ideal `m` of `A` there is an `a ∉ m`
such that `y` maps into `V` along every `A → B` that makes `a` a unit. (b) The free abelian group
functor `ℤ[V]` lies in every class of functors to abelian groups that satisfies `IsClosedClass` and
contains `ℤ[Hom(R, -)]` for the ring `R` of each chart of `X`, of any dimension, whose coordinates
are units. -/
lemma HasAtlas.exists_isCharting (hX : HasAtlas d X) : ∃ V : Subfunctor X, IsCharting V := by
  classical
  -- Shift some coordinates of each chart by 1 and invert the product of the new coordinates: the
  -- resulting charts have unit coordinates and still cover all field points. The subfunctor is
  -- their union.
  obtain ⟨n, a, h_cover⟩ := hX.exists_finite_charts
  let x (i : Fin n) (S : Set (Fin d)) (j : Fin d) : (a i).coordRing :=
    (a i).coordinate j + if j ∈ S then 1 else 0
  have h_etale (i : Fin n) (S : Set (Fin d)) : (polyEval (k := k) (x i S)).Etale :=
    (a i).etale_polyEval_coordinate_add_ite S
  let u (p : Fin n × Set (Fin d)) : EtaleChart d X :=
    away { a p.1 with coordinate := x p.1 p.2, etale := h_etale p.1 p.2 } (∏ j, x p.1 p.2 j)
  have hu_unit (p : Fin n × Set (Fin d)) (j : Fin d) : IsUnit ((u p).coordinate j) := by
    change IsUnit (algebraMap _ (Localization.Away (∏ j, x p.1 p.2 j)) (x p.1 p.2 j))
    exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)))
      (algebraMap_isUnit _)
  have hu_cover (K : CommAlg k) (hK : IsField K) (y : X.obj K) :
      ∃ p : Fin n × Set (Fin d), y ∈ (u p).locus K := by
    -- At a field point `φ` of a chart, shift exactly the coordinates that vanish there.
    obtain ⟨i, hi⟩ := h_cover K hK y
    obtain ⟨φ, rfl⟩ := (a i).mem_locus_iff.1 hi
    let S : Set (Fin d) := {j | φ ((a i).coordinate j) = 0}
    let : Field K := hK.toField
    have h_ne (j : Fin d) : φ (x i S j) ≠ 0 := by
      by_cases hj : φ ((a i).coordinate j) = 0 <;> simp [x, S, hj]
    have h_prod : IsUnit (φ (∏ j, x i S j)) := by simp [Finset.prod_ne_zero_iff, h_ne]
    exact ⟨(i, S), (mem_locus_away _ _ φ).2 h_prod⟩
  refine ⟨⨆ p, (u p).locus, ?_, fun P hP h_unit ↦ hP.freeAb_iSup_locus h_unit u hu_unit⟩
  exact isZariskiLocallyTop_of_open_cover (Θ := 𝟭 _) fun K hK y ↦
    have ⟨p, hp⟩ := hu_cover K hK y
    ⟨(u p).locus, (u p).isOpenSubfunctor, hp, le_iSup_of_le p le_rfl⟩

end New.Variety

/-!
## Closed classes of bijective comparisons and charted schemes

The functors `N` (first arguments of `Extⁿ`) on which a comparison of cohomologies is bijective form
a closed class, as used in the definition of charting subfunctors; a scheme is charted if it has
such a subfunctor. A comparison `c` (`New.Variety.Comparison`) is a functor `φ : C' ⥤ C` with a map
`φ ⋙ F ⟶ F'`. `c.IsBijective α` says that `Extⁿ(N, F) → Extⁿ(N', F')` along `α : N' ⟶ φ ⋙ N` is
bijective for all `n`. Both sides lie over a category `D` through `ψ`, `ψ'` and `η : ψ' ⟶ φ ⋙ ψ`.
-/

section ChartedSchemes

open CategoryTheory Functor AlgebraicGeometry

namespace New.Variety

variable {C C' : Type 1} {D : Type*} [Category C] [Category C'] [Category D]
  {F : AbFunctor C} {F' : AbFunctor C'} (c : Comparison F F') {ψ : C ⥤ D} {ψ' : C' ⥤ D}
  (η : ψ' ⟶ c.functor ⋙ ψ)

/-- Let the comparison `c` consist of a functor `c.functor : C' ⥤ C` and a map of coefficients from
`F` on `C` to `F'` on `C'`. The functors `N : D ⥤ Ab` for which the maps
`Extⁿ(ψ ⋙ N, F) → Extⁿ(ψ' ⋙ N, F')` induced by `c` and `η` are bijective for all n form a closed
class: it contains `0` and, given a short exact sequence whose first term is in it, contains the
second term iff the third. -/
lemma Comparison.isClosedClass :
    IsClosedClass fun N : D ⥤ Ab ↦ c.IsBijective (N := ψ ⋙ N) (whiskerRight η N) :=
  -- Precomposition with `ψ` and with `ψ'` is exact and `η` gives the map between the two results:
  -- use `Comparison.devissage`.
  (c.devissage ((whiskeringLeft C D Ab).obj ψ) ((whiskeringLeft C' D Ab).map η)).isClosedClass

/-- The comparison `c` is bijective on the set-valued functor `P` on `D`: the maps
`Hⁿ(ψ ⋙ P, F) → Hⁿ(ψ' ⋙ P, F')` induced along `η` are bijective for all `n`. -/
abbrev Comparison.IsBijectiveOn (P : D ⥤ Type 1) : Prop :=
  c.IsBijective (freeAbMap (Y := ψ ⋙ P) (whiskerRight η P))

/-- The scheme `Y` over `R` is *charted* over the `R`-algebra `k`: the functor of points of `Y` on
`k`-algebras has a subfunctor `V` with `New.Variety.IsCharting V`. -/
class IsCharted {R : CommRingCat} (Y : Over (Spec R)) (k : Type) [CommRing k] [Algebra R k] :
    Prop where
  /-- The functor of points of `Y` has a subfunctor `V` with `New.Variety.IsCharting V`. -/
  exists_isCharting : ∃ V : Subfunctor (algPointsOf k R Y), IsCharting V

end New.Variety

end ChartedSchemes

end
