import Lib.Cohomology.Etale.FilteredLimits

/-!
# The space of places of residue fields and its properness over the base

Spaces are functors from rings to sets (`New.Variety.PointFunctor`). For `s : Z ⟶ reprBy D` and a
point `x ∈ Z(C)`, the ring map under `x` is `baseRingMap s x : D ⟶ C`. The space of places is a form
of the Riemann–Zariski space. It is used to cover a proper functor `Z` over `D`.

A place of a `D`-algebra `P` is a prime `q` of `P` together with a valuation ring of `κ(q)` over
`D`. For `α : D ⟶ P`, the ring `T = prodValuationRing α` is the product of these valuation rings.
Each `t ∈ P` is a ratio `a t / b t` in it, with `a = numerator` and `b = denominator`. The space of
places `W` of a valuative lift `z`, with `z.point ∈ Z(T)`, has as points over `C` the classes of
maps `f : T → C`. Two maps are identified if they give the same point `Z.map f z.point` of `Z(C)`
and the same ratios `(f (a t) : f (b t))`.

* `New.Variety.IsProperOver`: properness, as a closed diagonal and a valuative criterion.
* `New.Variety.ResiduePlace.placeSpace`: the space of places `W`.
* `New.Variety.ResiduePlace.exists_isLocalHom_eq_projHom_comp`: a point of `W` in a local ring comes
  from one place.
* `New.Variety.ResiduePlace.isProperOver_placeSpace`: the space of places is proper over `D`.

Notions from other files:
* `New.Variety.reprBy D`: the functor `Hom(D, −)` represented by `D`.

## Relation to the literature

Known; see `Lib.Cohomology.ProperBaseChange.Theorem` for sources.
-/

noncomputable section

open Pi CategoryTheory CommRingCat IsLocalRing RingHom Ideal ResidueField Set algebraMap

namespace New.Variety

variable {Z : CommRingCat ⥤ Type 1} {D P C C' : CommRingCat} (α : D ⟶ P) {s : Z ⟶ reprBy D}
  {F : Type} [Field.{0} F]

/-! ### Proper functors -/

/-- The functor `Z` on rings, with structure map `s : Z ⟶ reprBy D`, is proper over `D`: its
diagonal is closed, and it satisfies a valuative criterion with one ring `T` and one point
`a ∈ Z(T)` serving all valuation rings of algebraically closed fields (which includes
quasi-compactness). -/
structure IsProperOver (s : Z ⟶ reprBy D) where
  /-- The diagonal is closed: for points `x`, `y` over `C`, some ideal `I` of `C` is killed exactly
  by the maps `C ⟶ C'` that make `x` and `y` equal. -/
  diagonal_closed (C : CommRingCat) (x y : Z.obj C) :
    ∃ I : Ideal C, ∀ (C' : CommRingCat) (f : C ⟶ C'),
    Z.map f x = Z.map f y ↔ I ≤ ker f.hom
  /-- For one ring `T` and one point `a` over it, each point in an algebraically closed field `K`
  that maps `D` into a valuation ring `O` of `K` is the image of `a` under some `T → O ⊆ K`. -/
  valuative_cover : ∃ (T : CommRingCat) (a : Z.obj T),
    ∀ {K : Type} [Field K] [IsAlgClosed K] (O : ValuationSubring K) (z : Z.obj (of K)),
    (∀ d : D, baseRingMap (B := of K) s z d ∈ O) →
      ∃ u : T ⟶ of O, Z.map (u ≫ ofHom O.subtype) a = z

/-- Two points of a proper functor over `C` are equal if they become equal along a jointly
injective family of ring maps `C ⟶ K j`. -/
lemma IsProperOver.ext_of_jointly_injective (hs : IsProperOver s) {J : Sort*} {K : J → CommRingCat}
    (π : ∀ j : J, C ⟶ K j) (hπ : ∀ c : C, (∀ j : J, π j c = 0) → c = 0) {x y : Z.obj C}
    (h_eq : ∀ j : J, Z.map (π j) x = Z.map (π j) y) :
    x = y := by
  -- The ideal where `x = y` dies under every `π j`, so it is zero; now use the identity map.
  obtain ⟨I, hI⟩ : ∃ I : Ideal C, ∀ (C' : CommRingCat) (f : C ⟶ C'),
      Z.map f x = Z.map f y ↔ I ≤ ker f.hom := hs.diagonal_closed C x y
  have h_le : I ≤ ker (𝟙 C : C ⟶ C).hom := fun c hc ↦
    hπ c fun j ↦ (hI (K j) (π j)).mp (h_eq j) hc
  simpa using (hI C (𝟙 C)).mpr h_le

/-- For `Z` proper over `D` and a valuation subring `U` of a field `F`, the map `Z(U) → Z(F)` is
injective. -/
lemma IsProperOver.injective_map_valuationSubring (hs : IsProperOver s) (U : ValuationSubring F) :
    (Z.map (ofHom U.subtype) ·).Injective := fun _ _ hxy ↦
  hs.ext_of_jointly_injective (fun _ : Unit ↦ ofHom U.subtype) (by simp) fun _ ↦ hxy

/-- For `α : D → P`, a place is a prime `q` of `P` together with a valuation ring `O` of the residue
field `κ(q)` that contains the image of `D`. -/
structure ResiduePlace where
  /-- A prime ideal of `P`. -/
  prime : PrimeSpectrum P
  /-- A valuation ring of the residue field of that prime. -/
  valuationSubring : ValuationSubring prime.asIdeal.ResidueField
  /-- The valuation ring contains the image of `D`. -/
  base_mem (d : D) : ↑(α d) ∈ valuationSubring

namespace ResiduePlace

/-- For α: D → P, the product of the valuation rings O over all places (q, O) of
`New.Variety.ResiduePlace`. -/
abbrev prodValuationRing : CommRingCat := of (∀ j : ResiduePlace α, j.valuationSubring)

variable {α} (s) (f : prodValuationRing α ⟶ C) (t : P) (j : ResiduePlace α)

/-- For a place j, the projection ring homomorphism from the product of all the valuation rings
to the valuation ring of j. -/
abbrev projHom : prodValuationRing α ⟶ of j.valuationSubring :=
  ofHom (evalRingHom (fun j ↦ j.valuationSubring) j)

/-- For a place j=(q,O), the residue field κ(q) of the prime q of P. -/
abbrev PlaceField : Type := j.prime.asIdeal.ResidueField

/-- The componentwise inclusion ∏ O → ∏ κ(q), both products over all places (q, O). -/
abbrev toFieldProd : prodValuationRing α ⟶ ⟨∀ j : ResiduePlace α, j.PlaceField⟩ :=
  ofHom (algebraMap ..)

lemma ne_zero_of_notMem_valuationSubring (h_notMem : ↑t ∉ j.valuationSubring) :
    ↑t ≠ (0 : j.PlaceField) :=
  fun h_zero ↦ by simp [h_zero] at h_notMem

open scoped Classical in
/-- For t∈P and a place (q,O), the element of O equal to 1 if the image of t in κ(q) lies in O,
and its inverse otherwise. -/
def denominator : j.valuationSubring :=
  if h : ↑t ∈ j.valuationSubring then 1 else
    ⟨t⁻¹, (j.valuationSubring.mem_or_inv_mem' t).resolve_left h⟩

/-- For t∈P and a place (q,O), the element of O given by the image of t in κ(q) times the
denominator. -/
def numerator : j.valuationSubring :=
  ⟨t * j.denominator t, by
    -- the product is `t` if `t ∈ j.valuationSubring`, and `t * t⁻¹ = 1` otherwise
    by_cases h_mem : ↑t ∈ j.valuationSubring
    · simp [denominator, h_mem]
    · simp [denominator, h_mem, mul_inv_cancel₀ (ne_zero_of_notMem_valuationSubring t j h_mem)]⟩

/-- For `f : prodValuationRing α ⟶ C` and `t ∈ P`, `f (denominator t)` and `f (numerator t)` are
coprime. -/
lemma isCoprime_denominator_numerator : IsCoprime (f (denominator t)) (f (numerator t)) := by
  -- At each place `denominator t = 1` or `numerator t = 1`, so
  -- `(1 - numerator t) * denominator t + numerator t = 1`.
  refine IsCoprime.map ⟨1 - numerator t, 1, ?_⟩ f.hom
  ext j
  by_cases h_mem : ↑t ∈ j.valuationSubring
  · simp [numerator, denominator, h_mem]
  · simp [numerator, denominator, h_mem, mul_inv_cancel₀
    (ne_zero_of_notMem_valuationSubring t j h_mem)]

/-- For `f : ∏ O → C`, the subring of pairs `(t, c)` in `P × C` with the following property: there
are `r`, `r'` in the product of the valuation rings such that `f r` is a unit, `r · t = r'` in
`∏ κ(q)`, and `f r · c = f r'`. -/
def fractionGraph : Subring (P × C) :=
  letI : Algebra (prodValuationRing α) C := f.hom.toAlgebra
  ((⊥ : Subalgebra (prodValuationRing α) _).saturation
    (_ ⊓ (IsUnit.submonoid C).comap (snd ((j : ResiduePlace α) → j.PlaceField) C))
      inf_le_left).toSubring.comap
    ((algebraMap P (∀ j : ResiduePlace α, j.PlaceField)).prodMap (RingHom.id C))

/-- For `ξ ∈ Z(P)`: a point of `Z` over the product of the valuation rings of all places that agrees
with `ξ` over the product of the residue fields. It comes with three facts: `Z` is proper over `D`,
`P` is absolutely flat, and all residue fields of `P` are algebraically closed. -/
structure ValuativeLift (ξ : Z P) where
  /-- A point of `Z` over the product of the valuation rings of all places. -/
  point : Z (prodValuationRing (baseRingMap s ξ))
  /-- Over the product `∏ⱼ κ(j.prime)` of residue fields, indexed by the places `j`, the point
  agrees with `ξ`; the map on the right is the algebra map `P → ∏ⱼ κ(j.prime)`,
  `t ↦ (t mod j.prime)_j`. -/
  map_point_eq : Z.map toFieldProd point = Z.map (ofHom (algebraMap ..)) ξ
  /-- `Z` is proper over `D`. -/
  isProperOver : IsProperOver s
  /-- Each `a ∈ P` satisfies `y * a * a = a` for some `y ∈ P`. -/
  absolutely_flat (a : P) : ∃ y : P, y * a * a = a
  /-- Every residue field of `P` is algebraically closed. -/
  isAlgClosed_residueField (q : Ideal P) [q.IsPrime] : IsAlgClosed q.ResidueField

variable {f t s} {ξ : Z P} (z : ValuativeLift s ξ)

/-- A pair `(t, c)` lies in the graph of `f` iff `f (numerator t) = f (denominator t) * c`. -/
lemma mem_fractionGraph {c : C} :
    (t, c) ∈ fractionGraph f ↔ f (numerator t) = f (denominator t) * c := by
  constructor
  · -- a witness: `r`, `r'` with `f r` a unit, `r' = r t` in the residue fields, `f r' = f r * c`
    rintro ⟨_, ⟨⟨r, rfl⟩, h_unit : IsUnit (f r)⟩, r', h⟩
    have h_snd : f r' = f r * c := congrArg Prod.snd h
    have h_fst (j : ResiduePlace α) : (r' j : PlaceField j) = r j * algebraMap P _ t :=
      congrFun (congrArg Prod.fst h) j
    -- at each place `numerator t = t * denominator t` and `r' = r * t`
    have h_key : r * numerator t = denominator t * r' := by
      ext j
      change (r j : j.PlaceField) * (algebraMap P _ t * denominator t j) = denominator t j * r' j
      rw [h_fst, ← mul_assoc, mul_comm]
    refine h_unit.mul_left_cancel ?_
    calc f r * f (numerator t) = f (denominator t) * f r' := by rw [← map_mul, h_key, map_mul]
      _ = f r * (f (denominator t) * c) := by rw [h_snd, mul_left_comm]
  · -- `f (denominator t)` divides `f (numerator t)` and is coprime to it, so it is a unit: the
    -- witness is `denominator t`, `numerator t`
    intro h
    have h_unit : IsUnit (f (denominator t)) :=
      (isCoprime_denominator_numerator f t).isUnit_of_dvd ⟨c, h⟩
    refine ⟨_, ⟨⟨denominator t, rfl⟩, h_unit⟩, numerator t, Prod.ext ?_ h⟩
    -- at each place `numerator t = t * denominator t`
    ext j
    exact mul_comm (algebraMap P j.PlaceField t) (denominator t j)

/-! ### The space of places and its loci -/

/-- The space of places of a valuative lift `z` of `ξ ∈ Z(P)`. With `T` the product
`prodValuationRing (baseRingMap s ξ)` of the valuation rings of all places, its points over `C` are
classes of maps `f : T ⟶ C`. Two maps are identified when they send the point of `z` to the same
point of `Z(C)` and give the same ratios `f (numerator t) : f (denominator t)` for all `t ∈ P`. -/
def placeSpace : PointFunctor where
  obj C := ULift <| Quotient
    { r (f g : prodValuationRing (baseRingMap s ξ) ⟶ C) :=
        Z.map f z.point = Z.map g z.point ∧
        ∀ t : P, f (numerator t) * g (denominator t) = g (numerator t) * f (denominator t)
      iseqv := by
        -- transitivity: the middle pair can be cancelled because it is coprime
        constructor <;> intros <;> grind [!isCoprime_denominator_numerator, IsCoprime] }
  map k := ↾fun x ↦ ULift.up (x.1.map' (· ≫ k) (by simp_all [← map_mul]))
  map_id C := by
    ext ⟨⟨f⟩⟩
    rfl
  map_comp k k' := by
    ext ⟨⟨f⟩⟩
    rfl

/-- The map from the space of places of `z` to `Z` that sends the class of `f` to `f z ∈ Z(C)`. -/
def placeSpaceMap : placeSpace z ⟶ Z where
  app _ := ↾fun x ↦ x.1.lift (fun f ↦ Z.map f z.point) fun _ _ ↦ And.left
  naturality _ _ _ := by
    ext ⟨⟨f⟩⟩
    apply Z.map_comp_apply

variable {z} {R : Type} [CommRing R] [IsLocalRing R] {q : Ideal P} [M : q.IsMaximal]
  (x : placeSpace z C)

/-- A ring map `g : P ⟶ F` to a field factors through the residue field of some prime `q` of
`P`. -/
lemma exists_algebraMap_residueField_comp_eq (g : P ⟶ of F) :
    ∃ᵉ (q : PrimeSpectrum P) (l : of q.asIdeal.ResidueField ⟶ of F),
      ofHom (algebraMap P q.asIdeal.ResidueField) ≫ l = g := by
  -- Take `q = ker g`: elements outside it go to units of the field `F`.
  have := ker_isPrime g.hom
  have h_unit : (ker g.hom).primeCompl ≤ (IsUnit.submonoid F).comap g.hom := fun p hp ↦ .mk0 _ hp
  exact ⟨⟨ker g.hom, inferInstance⟩, ofHom (lift _ g.hom le_rfl h_unit),
    hom_ext (RingHom.ext (lift_algebraMap _ g.hom le_rfl h_unit))⟩

/-- For a point `x` of the space of places over `C`, the subring of `P × C` of pairs `(t, c)` such
that `x` gives `t` the finite value `c`. For any representative `f` of `x`, these are the pairs of
`New.Variety.ResiduePlace.fractionGraph f`, that is, `f (numerator t) = f (denominator t) * c`. This
does not depend on the choice of `f`. -/
def placeGraph : Subring (P × C) :=
  x.1.lift fractionGraph (by
    -- equal values give the same graph, by `mem_fractionGraph` and coprimality
    rintro _ _ ⟨⟩
    grind +extAll [mem_fractionGraph, isCoprime_denominator_numerator, IsCoprime])

/-- If `x` gives `t` the value `c`, then the image of `x` under `k : C ⟶ C'` gives `t` the value
`k c`. -/
lemma placeGraph_map {k : C ⟶ C'} {c : C} :
    ∀ {x : (placeSpace z).obj C}, (t, c) ∈ placeGraph x →
      (t, k c) ∈ placeGraph ((placeSpace z).map k x) := by
  rintro ⟨⟨f⟩⟩ (h_mem : (t, c) ∈ fractionGraph f)
  -- apply `k` to the equation of `mem_fractionGraph`
  change (t, k c) ∈ fractionGraph (f ≫ k)
  simp [mem_fractionGraph, mem_fractionGraph.mp h_mem]

variable (z) (J : Ideal D) (B : Subring q.ResidueField)

/-- For an ideal I of P, the subfunctor of the space of places W of points that give every t ∈ I
the value 0. -/
def killingPlaces (I : Ideal P) : Subfunctor (placeSpace z) where
  obj _ := {x | ∀ t ∈ I, (t, 0) ∈ placeGraph x}
  map k x hx t ht := by simpa using placeGraph_map (k := k) (hx t ht)

/-- For a maximal ideal q of P and a place y killing q, the subring of κ(q) = P/q formed by the
images of the t ∈ P finite at y, that is, of those `t` with a value at `y`: some
`(t, c) ∈ placeGraph y`. -/
def finiteValueSubring (y : killingPlaces z q C) : Subring q.ResidueField :=
  (((algebraMap P q.ResidueField).comp (fst P C)).domRestrict (placeGraph y.val)).range

/-- For an ideal J of D and a subring B of κ(q), the subfunctor of places vanishing on q that
are finite on B and whose structure map from D kills J. -/
def placesFiniteOn : Subfunctor (killingPlaces z q).toFunctor :=
  zeroPoints ((killingPlaces z q).ι ≫ placeSpaceMap z ≫ s) J ⊓
    { obj _ := {y | B ≤ finiteValueSubring z y}
      map k y hy u hb := by
        -- if `u` is the residue of `t` and `t` has the value `c`, then it now has the value `k c`
        obtain ⟨⟨⟨t, c⟩, htc⟩, ht⟩ := hy hb
        exact ⟨⟨(t, k c), placeGraph_map htc⟩, ht⟩ }

variable {z J B x}

/-- A point `x` of the space of places gives an element `t ∈ P` at most one finite value: if
`(t, c)` and `(t, d)` both lie in `New.Variety.ResiduePlace.placeGraph x`, then `c = d`. -/
lemma placeGraph_unique {c d : C} (hc : (t, c) ∈ placeGraph x) (hd : (t, d) ∈ placeGraph x) :
    c = d := by
  obtain ⟨⟨f⟩⟩ := x
  -- `f (denominator t)` divides `f (numerator t)` and is coprime to it, so it is a unit and cancels
  have hc_eq : f (numerator t) = f (denominator t) * c := mem_fractionGraph.mp hc
  have h_unit : IsUnit (f (denominator t)) :=
    (isCoprime_denominator_numerator f t).isUnit_of_dvd ⟨c, hc_eq⟩
  exact h_unit.mul_left_cancel (hc_eq.symm.trans (mem_fractionGraph.mp hd))

/-- For an ideal `I` of `P`, the inclusion of the places that give every `t ∈ I` the value `0`
(`New.Variety.ResiduePlace.killingPlaces z I`) into the space of places is relatively affine. -/
lemma isRelAffine_killingPlaces (I : Ideal P) : IsRelAffine (killingPlaces z I).ι := by
  refine isRelAffine_ι_of_forall_map_mem_iff ?_
  rintro C ⟨⟨f⟩⟩
  -- by `mem_fractionGraph`, the place kills `t` iff `numerator t` is sent to `0`
  exact ⟨f '' (numerator '' I), ∅, fun C' k ↦
    (forall₂_congr fun t _ ↦ mem_fractionGraph).trans (by simp)⟩

/-- Let `q` be a maximal ideal of `P` and let the class of `f : prodValuationRing → C` be a place
that kills `q`. Then the place is finite at the residue of `t ∈ P` in `κ(q)` iff `f (denominator t)`
is a unit. -/
lemma mem_finiteValueSubring_iff {f : prodValuationRing (baseRingMap s ξ) ⟶ C}
    (h_kill : { down := ⟦f⟧ } ∈ (killingPlaces z q).obj C) :
    ↑t ∈ finiteValueSubring z (⟨⟨⟦f⟧⟩, h_kill⟩ : killingPlaces z q C) ↔
      IsUnit (f (denominator t)) := by
  refine ⟨?_, fun h_unit ↦ ?_⟩
  · -- some `u ≡ t` mod `q` has a value `c`; as the place kills `t - u`, `t` has the value `c` too
    rintro ⟨⟨⟨u, c⟩, huc⟩, hu⟩
    have h_diff : t - u ∈ q := by simp_all [← algebraMap_residueField_eq_zero]
    have h_sum : (u, c) + (t - u, 0) ∈ fractionGraph f := add_mem huc (h_kill _ h_diff)
    have h_mem : (t, c) ∈ fractionGraph f := by simpa using h_sum
    exact (isCoprime_denominator_numerator f t).isUnit_of_dvd ⟨c, mem_fractionGraph.mp h_mem⟩
  · obtain ⟨c, hc⟩ : f (denominator t) ∣ f (numerator t) := h_unit.dvd
    exact ⟨⟨(t, c), mem_fractionGraph.mpr hc⟩, rfl⟩

/-- Through the place `j`, an element `t` with residue in the valuation ring of `j` has as value the
image of that residue. -/
lemma mem_fractionGraph_projHom {φ : of j.valuationSubring ⟶ C} (t : P)
    (h_mem : ↑t ∈ j.valuationSubring) :
    (t, φ ⟨t, h_mem⟩) ∈ fractionGraph (j.projHom ≫ φ) := by
  simp [mem_fractionGraph, numerator, denominator, h_mem]

/-- A point that factors through the place `j` kills the prime of `j`. -/
lemma projHom_mem_killingPlaces {Z : CommRingCat ⥤ Type 1} {D P C : CommRingCat}
    {s : Z ⟶ reprBy D} {ξ : Z P} {z : ValuativeLift s ξ} (j : ResiduePlace (baseRingMap s ξ))
    (φ : of j.valuationSubring ⟶ C) :
    ⟨⟦projHom j ≫ φ⟧⟩ ∈ killingPlaces z j.prime.asIdeal C := by
  intro t ht
  -- `t` is zero in the residue field of `j`, hence so is `j.numerator t`
  have h_num : j.numerator t = 0 := by
    simp [Subtype.ext_iff, numerator, algebraMap_residueField_eq_zero.mpr ht]
  exact mem_fractionGraph.mpr (by simp [h_num])

/-- For an ideal `J` of `D` and a subring `B` of `κ(q)`, the inclusion of the places that kill the
maximal ideal `q` of `P`, are finite on `B` and whose structure map kills `J`
(`New.Variety.ResiduePlace.placesFiniteOn z J B`) into the places that kill `q` is relatively
affine. -/
lemma isRelAffine_placesFiniteOn : IsRelAffine (placesFiniteOn z J B).ι := by
  refine isRelAffine_ι_of_forall_map_mem_iff ?_
  rintro C ⟨⟨⟨f⟩⟩, hf⟩
  -- the image of `J` must vanish, and `denominator t` must become a unit for each `t` over `B`
  -- (`mem_finiteValueSubring_iff`)
  refine ⟨baseRingMap s (Z.map f z.point) '' J,
    (fun t ↦ f (denominator t)) '' {t | algebraMap P q.ResidueField t ∈ B},
    fun C' k ↦ .trans (.and ?_ ?_) (forall_mem_image.and forall_mem_image).symm⟩
  · -- the structure map of the image under `k` is that of `Z.map f z.point` followed by `k`
    refine forall₂_congr fun d _ ↦ ?_
    change baseRingMap s (Z.map (f ≫ k) z.point) d = 0 ↔ k (baseRingMap s (Z.map f z.point) d) = 0
    simp
  · exact q.algebraMap_residueField_surjective.forall.trans
      (forall₂_congr fun _ _ ↦ mem_finiteValueSubring_iff _)

/-- For `d ∈ D`, the point `x` of the space of places gives the image `baseRingMap s ξ d` of `d` in
`P` the value `baseRingMap (placeSpaceMap z ≫ s) x d`, the image of `d` under the structure map
of `x`. -/
lemma baseRingMap_mem_placeGraph {Z : CommRingCat ⥤ Type 1} {D P C : CommRingCat}
    {s : Z ⟶ reprBy D} {ξ : Z P} {z : ValuativeLift s ξ} {x : placeSpace z C} (d : D) :
    (baseRingMap s ξ d, baseRingMap (placeSpaceMap z ≫ s) x d) ∈ placeGraph x := by
  obtain ⟨⟨f⟩⟩ := x
  -- `baseRingMap s z.point d` lifts both components: the first by `z.map_point_eq`, the second by
  -- `baseRingMap_map`
  refine ⟨1, one_mem _, baseRingMap s z.point d, Prod.ext ?_ ?_⟩
  · simpa using congrArg (baseRingMap s · d) z.map_point_eq
  · change f (baseRingMap s z.point d) = 1 * baseRingMap s (Z.map f z.point) d
    simp

/-! ### Points in local rings, and properness -/

/-- Let `z` be a valuative lift of `ξ ∈ Z(P)`. This is a point of `Z` over `prodValuationRing`, the
product of the valuation rings of all places `(q, O)`, and it agrees with `ξ` over the product of
the residue fields. Here a place is a prime `q` of `P` together with a valuation ring `O` of `κ(q)`
containing the image of `D` under `baseRingMap s ξ`. Let `R` be a local ring and `x` a point over
`R` of the space of places of `z`, that is, a class of maps `prodValuationRing → R`; then there is a
place `(q, O')` with two properties. (a) There is a local map `φ : O' → R`. (b) For every valuation
ring `O ⊆ O'` of `κ(q)` containing the image of `D`, `x` is the class of the composite
`prodValuationRing → O ⊆ O' → R` of the projection, the inclusion and `φ`. -/
lemma exists_isLocalHom_eq_projHom_comp {Z : CommRingCat ⥤ Type 1} {D P : CommRingCat}
    {s : Z ⟶ reprBy D} {ξ : Z P} {z : ValuativeLift s ξ} {R : Type} [CommRing R] [IsLocalRing R]
    (x : (placeSpace z).obj (of R)) :
    ∃ (j : ResiduePlace (baseRingMap s ξ)) (φ : j.valuationSubring →+* R),
      IsLocalHom φ ∧
      -- `x` comes from `φ` on every smaller valuation ring `O` over `D`
      ∀ (O : ValuationSubring j.prime.asIdeal.ResidueField)
        (hO : ∀ d : D, ↑(baseRingMap s ξ d) ∈ O) (h_le : O ≤ j.valuationSubring),
        x = ⟨⟦projHom ⟨j.prime, O, hO⟩ ≫ ofHom
          (φ.comp (O.inclusion j.valuationSubring h_le))⟧⟩ := by
  -- Localise the product ring at the preimage of the maximal ideal; as it is a test ring, this
  -- gives a valuation ring `U` of a field `L`. The map to `L` extends to the product of the residue
  -- fields, so on `P` it factors through an embedding `l` of one residue field; the place is the
  -- preimage of `U`.
  obtain ⟨⟨f⟩⟩ := x
  have (q : Ideal P) [q.IsPrime] : IsAlgClosed q.ResidueField := z.isAlgClosed_residueField q
  have h_test : IsTest (prodValuationRing (baseRingMap s ξ)) :=
    IsTest.pi fun _ ↦ isTest_of_preValuationRing
  obtain ⟨-, -, L, _, _, U, _, hU : IsLocalization.AtPrime U ((maximalIdeal R).comap f.hom)⟩ :=
    h_test.exists_valuationSubring_atPrime ((maximalIdeal R).comap f.hom)
  -- `f` factors through the localisation `U`, as `R` is local.
  obtain ⟨ψ, rfl⟩ : ∃ ψ : of U ⟶ of R, ofHom (algebraMap _ U) ≫ ψ = f :=
    ⟨_, hom_ext (hU.lift_comp (by simp))⟩
  -- The product of the residue fields is a localisation of `prodValuationRing` at
  -- non-zero-divisors, which stay nonzero in `L`.
  obtain ⟨G, hG⟩ : ∃ G : of (∀ j : ResiduePlace (baseRingMap s ξ), j.PlaceField) ⟶ of L,
      toFieldProd ≫ G = ofHom (algebraMap _ U) ≫ ofHom U.subtype := by
    refine ⟨_, hom_ext (IsLocalization.map_comp
      (M := .pi univ fun j ↦ nonZeroDivisors j.valuationSubring)
      fun _ _ ↦ hU.nonZeroDivisors_le_comap _ _ ?_)⟩
    simp_all [funext_iff, Submonoid.mem_pi, mem_nonZeroDivisors_iff]
  obtain ⟨q, l, hl⟩ : ∃ (q : PrimeSpectrum P) (l : of q.asIdeal.ResidueField ⟶ of L),
      ofHom (algebraMap P _) ≫ l = ofHom (algebraMap P _) ≫ G :=
        exists_algebraMap_residueField_comp_eq _
  have h_finite (d : D) : algebraMap P _ (baseRingMap s ξ d) ∈ U.comap l.hom := by
    -- the image of `baseRingMap s ξ d` in `L` is that of an element `r` of `prodValuationRing`
    let r : prodValuationRing (baseRingMap s ξ) := fun j ↦ ⟨_, j.base_mem d⟩
    have h_eq : l (algebraMap P _ (baseRingMap s ξ d)) = ((algebraMap _ U r : U) : L) :=
      (ConcreteCategory.congr_hom hl _).trans (ConcreteCategory.congr_hom hG r)
    simp [h_eq]
  refine ⟨⟨q, U.comap l.hom, h_finite⟩, ψ.hom.comp (l.hom.restrict _ U (by simp)),
    ⟨fun a ↦ not_imp_not.mp fun ha ↦ ?_⟩, fun O hO h_le ↦ ?_⟩
  · -- `ψ` is local, and `l` sends nonunits to nonunits.
    have h_nonunit : (l.hom.restrict _ U (by simp)) a ∈ maximalIdeal U := by
      simp_all [Submonoid.isUnit_iff_and]
    exact hU.map_eq_maximalIdeal.ge.trans ((maximalIdeal R).comap ψ.hom).map_comap_le h_nonunit
  -- The maps `f₀` and `f'` define the same point of `placeSpace z` over `U`; push this forward
  -- along `ψ`.
  let f₀ : prodValuationRing (baseRingMap s ξ) ⟶ of U := ofHom (algebraMap _ U)
  let f' : prodValuationRing (baseRingMap s ξ) ⟶ of U :=
    projHom ⟨q, O, hO⟩ ≫ ofHom (restrict l.hom O U h_le)
  have h_point : Z.map f₀ z.point = Z.map f' z.point := by
    refine z.isProperOver.injective_map_valuationSubring U ?_
    -- By `z.map_point_eq`, both sides over `L` are the image of `ξ`.
    have h_map : Z.map G (Z.map toFieldProd z.point) =
        Z.map (ofHom (evalRingHom PlaceField ⟨q, O, hO⟩) ≫ l) (Z.map toFieldProd z.point) := by
      rw [z.map_point_eq, ← Z.map_comp_apply, ← Z.map_comp_apply, ← hl]
      rfl
    simp_rw [← Z.map_comp_apply, hG] at h_map ⊢
    exact h_map
  have h_value (t : P) :
      f₀ (numerator t) * f' (denominator t) = f' (numerator t) * f₀ (denominator t) := by
    have h_num : toFieldProd (α := baseRingMap s ξ) (numerator t) =
        algebraMap P _ t * toFieldProd (denominator t) := rfl
    have h_G (r : prodValuationRing (baseRingMap s ξ)) : (f₀ r : L) = G (toFieldProd r) :=
      ConcreteCategory.congr_hom hG.symm r
    have h_l : G (algebraMap P _ t) = l (algebraMap P _ t) := ConcreteCategory.congr_hom hl.symm t
    -- in `L`, both `f₀` and `f'` send `numerator t` to `l t` times the image of `denominator t`
    have h₁ : (f₀ (numerator t) : L) = l (algebraMap P _ t) * (f₀ (denominator t) : L) :=
      calc (f₀ (numerator t) : L)
        _ = G (toFieldProd (numerator t)) := h_G _
        _ = G (algebraMap P _ t) * G (toFieldProd (denominator t)) := by rw [h_num, map_mul]
        _ = l (algebraMap P _ t) * (f₀ (denominator t) : L) := by rw [h_l, h_G]
    have h₂ : (f' (numerator t) : L) = l (algebraMap P _ t) * (f' (denominator t) : L) :=
      map_mul l.hom _ _
    have h_coe : (f₀ (numerator t) : L) * f' (denominator t) =
        f' (numerator t) * f₀ (denominator t) := by rw [h₁, h₂, mul_right_comm]
    exact Subtype.ext h_coe
  -- so `f₀` and `f'` have the same class, and so do their composites with `ψ`
  have h_class : (⟨⟦f₀⟧⟩ : (placeSpace z).obj (of U)) = ⟨⟦f'⟧⟩ :=
    congrArg ULift.up (Quot.sound ⟨h_point, h_value⟩)
  exact congrArg ((placeSpace z).map ψ) h_class

/-- Let `z` be a valuative lift of `ξ ∈ Z(P)`: `Z` is proper over `D`, `P` is absolutely flat, the
residue fields of `P` are algebraically closed, and the point of `z` agrees with `ξ` over the
product of the residue fields. Then the space of places of `z` is proper over `D`. -/
lemma isProperOver_placeSpace {Z : CommRingCat ⥤ Type 1} {D P : CommRingCat} {s : Z ⟶ reprBy D}
    {ξ : Z P} {z : ValuativeLift s ξ} : IsProperOver (placeSpaceMap z ≫ s) := by
  refine ⟨?_, prodValuationRing (baseRingMap s ξ), ⟨⟦𝟙 _⟧⟩, fun {K} _ _ O x hx ↦ ?_⟩
  · -- Separatedness: add the equations for equal values to the ideal that `z.isProperOver` gives.
    rintro C ⟨⟨f⟩⟩ ⟨⟨g⟩⟩
    obtain ⟨I, hI⟩ := z.isProperOver.diagonal_closed C (Z.map f z.point) (Z.map g z.point)
    refine ⟨I ⊔ ⨆ t : P,
      span {f (numerator t) * g (denominator t) - g (numerator t) * f (denominator t)},
      fun C' k ↦ ?_⟩
    -- two classes are equal iff the points and all the ratios agree
    refine ULift.up_inj.trans (Quotient.eq.trans ?_)
    simp [← hI, sub_eq_zero]
  -- Valuative criterion: `x` comes from a local map `φ : j.valuationSubring → K`, and the preimage
  -- `O'` of `O` is a valuation ring inside `j.valuationSubring` that gives the lift.
  obtain ⟨j, φ, hφ : IsLocalHom φ, hx_eq⟩ := exists_isLocalHom_eq_projHom_comp x
  let O' : Subring j.PlaceField := (O.toSubring.comap φ).map j.valuationSubring.subtype
  have h_val (y : j.PlaceField) : y ∈ O' ∨ y⁻¹ ∈ O' := by
    -- if `y ∉ j.valuationSubring`, then `y⁻¹ ∈ j.valuationSubring` and the claim for `y⁻¹` gives it
    wlog hy : y ∈ j.valuationSubring generalizing y
    · grind [j.valuationSubring.mem_or_inv_mem]
    -- If `y ∉ O'` then `φ y ≠ 0`, so `y` is a unit of `j.valuationSubring` and `φ y⁻¹ ∈ O`.
    refine or_iff_not_imp_left.mpr fun h_not ↦ ?_
    have hφ_unit : IsUnit (φ ⟨y, hy⟩) := by aesop
    obtain ⟨u, hu⟩ : IsUnit (⟨y, hy⟩ : j.valuationSubring) := hφ.map_nonunit _ hφ_unit
    have h_inv_mem : (φ u)⁻¹ ∈ O :=
      (O.mem_or_inv_mem _).resolve_left fun h_mem ↦ h_not ⟨u, h_mem, by simp [hu]⟩
    exact ⟨↑u⁻¹, by simpa using h_inv_mem, by aesop⟩
  -- `O'` lies over `D`: the value of `x` at `baseRingMap s ξ d` is both its image under `φ`
  -- (`mem_fractionGraph_projHom`) and the image of `d` under the structure map of `x`
  -- (`baseRingMap_mem_placeGraph`), which lies in `O`.
  have h_finite (d : D) : algebraMap P _ (baseRingMap s ξ d) ∈ O' := by
    have h_graph : (baseRingMap s ξ d, φ ⟨_, j.base_mem d⟩) ∈ placeGraph x := by
      rw [hx_eq _ _ le_rfl]
      exact j.mem_fractionGraph_projHom (baseRingMap s ξ d) (j.base_mem d)
    have h_value : baseRingMap (placeSpaceMap z ≫ s) x d = φ ⟨_, j.base_mem d⟩ :=
      placeGraph_unique (baseRingMap_mem_placeGraph d) h_graph
    exact ⟨⟨_, j.base_mem d⟩, by simpa [← h_value] using hx d, rfl⟩
  refine ⟨projHom ⟨_, ⟨O', h_val⟩, h_finite⟩ ≫ ofHom ((φ.comp _).codRestrict O ?_),
    (hx_eq _ _ image_val_subset).symm⟩
  -- an element of `O'` comes from an element of `j.valuationSubring` that `φ` sends into `O`
  rintro ⟨_, w, hw, rfl⟩
  exact hw

/-- Let `q` be a maximal ideal of `P` and `x` a point of the space of places in a local ring `R`
that kills `q`. There are a valuation ring `V` of `κ(q)` over `D` and a map `φ : V → R` such that
`V` is the subring of `κ(q)` on which `x` is finite, and `x` is the class of
`prodValuationRing → O ⊆ V → R` for every valuation ring `O ⊆ V` over `D`. -/
private lemma exists_valuationSubring_eq_finiteValueSubring {x : placeSpace z ⟨R⟩}
    (hq : x ∈ (killingPlaces z q).obj ⟨R⟩) :
    ∃ (V : ValuationSubring q.ResidueField) (_ : ∀ d : D, ↑(baseRingMap s ξ d) ∈ V) (φ : V →+* R),
      finiteValueSubring z ⟨x, hq⟩ = V.toSubring ∧
      ∀ (O : ValuationSubring q.ResidueField) (hO : ∀ d : D, ↑(baseRingMap s ξ d) ∈ O)
        (h_le : O ≤ V),
        x = ⟨⟦projHom ⟨⟨q, M.isPrime⟩, O, hO⟩ ≫ ofHom (φ.comp (O.inclusion V h_le))⟧⟩ := by
  obtain ⟨⟨⟨q', hq'⟩, V, hV⟩, φ, φ_local : IsLocalHom φ, hx⟩ := exists_isLocalHom_eq_projHom_comp x
  have h_kill : x ∈ (killingPlaces z q').obj (of R) := by
    simpa [hx V hV le_rfl] using projHom_mem_killingPlaces ⟨⟨q', hq'⟩, V, hV⟩ _
  -- The place lies over `q`: for `t ∈ q` with `y * t * t = t`, either `t ∈ q'` or `1 - y * t ∈ q'`.
  -- In the second case `x` kills `y * t` and `1 - y * t`, so `1` would have the value `0`.
  have h_le : q ≤ q' := by
    intro t ht
    obtain ⟨y, hy : y * t * t = t⟩ := z.absolutely_flat t
    have h_prod : (1 - y * t) * t ∈ q' := by simp [sub_mul, hy]
    refine (hq'.mem_or_mem h_prod).resolve_left fun hmem ↦ ?_
    have h_one : ((1 : P), (0 : R)) ∈ placeGraph x := by
      simpa using add_mem (hq _ (q.mul_mem_left y ht)) (h_kill _ hmem)
    exact one_ne_zero (placeGraph_unique (one_mem _) h_one)
  -- `q'` is `q`, as `q` is maximal, and `x` is the class of `projHom ≫ φ`
  obtain rfl : q = q' := M.eq_of_le hq'.ne_top h_le
  obtain rfl := hx V hV le_rfl
  -- the ring where the place is finite is the valuation ring `V`
  refine ⟨V, hV, φ, Subring.ext (q.algebraMap_residueField_surjective.forall.mpr fun t ↦ ?_), hx⟩
  rw [mem_finiteValueSubring_iff]
  by_cases ht : algebraMap P _ t ∈ V
  · simp [denominator, ht]
  · -- `φ` is local, and `t⁻¹` is not a unit of `V` when `t ∉ V`
    have h_nonunit (h_inv : (algebraMap P _ t)⁻¹ ∈ V) : ¬IsUnit (⟨_, h_inv⟩ : V) := by
      simp [Submonoid.isUnit_iff_and, ht]
    simp [denominator, ht]
    exact h_nonunit _

/-- Let `x` be a point of the space of places in a local ring that kills the maximal ideal `q`. The
subring of `κ(q)` on which `x` is finite is a valuation ring. -/
lemma finiteValueSubring_mem_or_inv_mem {x : placeSpace z ⟨R⟩}
    (hq : x ∈ (killingPlaces z q).obj ⟨R⟩) (t : q.ResidueField) :
    t ∈ finiteValueSubring z ⟨x, hq⟩ ∨ t⁻¹ ∈ finiteValueSubring z ⟨x, hq⟩ := by
  obtain ⟨V, -, -, h_eq, -⟩ := exists_valuationSubring_eq_finiteValueSubring hq
  simpa [h_eq] using V.mem_or_inv_mem t

/-- Let `x` be a point of the space of places in a local ring `R` that kills the maximal ideal `q`,
and `O` a valuation ring of `κ(q)` over `D` inside the subring on which `x` is finite. Then `x` is
the class of `prodValuationRing → O → R` for some map `O → R`. -/
lemma exists_eq_projHom_comp_of_le_finiteValueSubring {x : placeSpace z ⟨R⟩}
    (hq : x ∈ (killingPlaces z q).obj ⟨R⟩) (O : ValuationSubring q.ResidueField)
    (hO : ∀ d : D, ↑(baseRingMap s ξ d) ∈ O) (h_le : O.toSubring ≤ finiteValueSubring z ⟨x, hq⟩) :
    ∃ φ : of O ⟶ ⟨R⟩, x = ⟨⟦projHom ⟨⟨q, M.isPrime⟩, O, hO⟩ ≫ φ⟧⟩ := by
  obtain ⟨V, -, φ, h_eq, hx⟩ := exists_valuationSubring_eq_finiteValueSubring hq
  exact ⟨_, hx O hO (h_le.trans_eq h_eq)⟩

end ResiduePlace

end New.Variety

end
