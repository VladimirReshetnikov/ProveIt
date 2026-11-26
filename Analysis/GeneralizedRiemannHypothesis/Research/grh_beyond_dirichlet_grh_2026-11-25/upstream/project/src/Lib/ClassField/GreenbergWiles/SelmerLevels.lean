import Lib.ClassField.Global.ExistenceTheorem

/-!
# Selmer cocycles, N-units, split places and the equivariant S-unit theorem

This file prepares the counting of Selmer groups over a number field `K`. Here `G` is the profinite
Galois group of an algebraically closed field `Ω` over `K`, and finite places of `Ω` are valuation
subrings (`ClosurePlace`), and `B N` is the valuation of `N` at `B`. `New.DiscreteUnits Ω` is `Ωˣ`
written additively, and `New.Z1` are the continuous 1-cocycles.

## Main definitions and results

* `New.IsLargeLevel.sUnits`, `New.IsLargeLevel.fixedSUnits`, `New.IsLargeLevel.fixedSUnitsRep`: the
  `N`-units of `Ω`, those fixed by an open normal subgroup `U`, and the latter as a representation
  of `G ⧸ U`.
* `New.selmerZ1`: cocycles with local conditions.
* `New.IsLargeLevel.SplitPlaces`: a family of distinct primes outside `N`, each with a Frobenius
  element in `U`. Here `N` is adapted to `U`: inertia above primes not dividing `N` lies in `U`, and
  the primes dividing `N` generate the class groups of the number fields between `K` and the fixed
  field of `U`.
* `New.IsLargeLevel.dirichlet_fixedSUnits`: for an open normal subgroup `Q` of `G`, the `N`-units of
  the fixed field of `Q`, times `ℤ`, form a finitely generated group of rank at most the number of
  places of that field above `N` and infinity, and have linearly independent equivariant additive
  maps to `ℝ` indexed by these places.

Notions from other files:
* `New.IsProGalois`: a profinite group acts on the Galois extension Ω/K as its Galois group, with
  open stabilisers.
* `New.IsPlaceOver`: the valuation subring A of Ω lies over the prime w of E: an integer of E is in
  the maximal ideal of A exactly when it lies in w.
* `New.IsFrob`: for a given q, σ stabilises A and σx ≡ x^q modulo the maximal ideal of A for every x
  in A.
* `New.inertiaAbove`: for a set S of primes of K, the union of the inertia groups in Gal(Ω/K) of all
  valuation subrings of Ω over a prime in S.

## Relation to the literature

Known; see `Lib.ClassField.GreenbergWiles.CocycleCounts` and `Lib.ClassField.Places.LocalFields` for
sources.
-/

noncomputable section

namespace New

variable {G K R X : Type} [Group G] [TopologicalSpace G] [Field K] [EmbeddedNumberField K]
  [MulSemiringAction G Ω] [IsProGalois G K Ω] [CommRing R]
  (m N : ℕ) [NeZero m] [MulAction G X]
  (I : Set G) {M : DiscreteModule R G} (x : Z1 M.ρ) (V : DiscreteModule R Gal(Ω/K)) {v : FinPlace K}
  {B : ClosurePlace} (U : OpenNormalSubgroup G)

open NeZero NumberField Pointwise MulSemiringAction Set QuotientGroup

/-! ### Inertia, places above `N` and cocycles -/

/-- The element `γ` of `G` acts as a standard generator of tame inertia of order `m` at the
valuation subring `A`: it lies in the inertia group of `A`, and, for some uniformiser `π` of `K`
for `A` and some `m`-th root `y` of `π`, the quotient `γ y / y` is the fixed primitive `m`-th root
of unity `New.rootPowHom Ω m 1`. -/
def IsTameGeneratorFor (A : ClosurePlace) (γ : G) : Prop :=
  γ ∈ inertiaGroup G A ∧
  ∃ (π : Kˣ) (y : DiscreteUnits Ω),
    -- `π` is a uniformiser, `y ^ m = π`, and `γ y / y` is the fixed primitive `m`-th root of
    -- unity, written additively
    IsUniformiser A π.1 ∧
    m • y = ↑(DiscreteUnits.ofBase G Ω (Additive.ofMul π)) ∧
    unitsRep γ y - y = (rootPowHom Ω m).1 1

variable (G) in
/-- Let the profinite group `G` act on `Ω` as the Galois group of `Ω/K`, and let the valuation
subring `B` of `Ω` lie over the prime `v` of `K`. Then, for every `m ≠ 0`, some `γ ∈ G` is a tame
generator of order `m` at `B`. That is, `γ` lies in the inertia group of `B`, and for some
uniformiser `π` of `K` for `B` and some `m`-th root `y` of `π`, the quotient `γ y / y` is the fixed
primitive `m`-th root of unity `rootPowHom Ω m 1`. -/
lemma exists_isTameGeneratorFor (h : IsPlaceOver B v) : ∃ γ : G, IsTameGeneratorFor m B γ := by
  -- Take a uniformiser `π` of `K` that stays one in the decomposition field, and `y ^ m = π`.
  obtain ⟨π, hπ, hπ_local⟩ := h.exists_uniformiser G
  obtain ⟨y, hy⟩ := (DiscreteUnits.ofBase G Ω (.ofMul π)).val.exists_nsmul (n := m) out
  let ζ : DiscreteUnits Ω := (rootPowHom Ω m).val 1
  have hy_pow : (y.toMul : Ω) ^ m = algebraMap K Ω π := congrArg (·.toMul.val) hy
  -- With `ζ` the fixed `m`-th root of unity, `ζ * y` is another `m`-th root of `π`, and inertia
  -- is transitive on these roots.
  have same_pow : ((ζ + y).toMul : Ω) ^ m = (y.toMul : Ω) ^ m :=
    mod_cast by simp [ζ, mul_pow, (isPrimitiveRoot_rootPowHom_one ..).pow_eq_one]
  obtain ⟨h_galois, -, -⟩ := h.isLocalGalois_and_residueCard_eq_and_isUniformiser G
  -- so some `γ` in inertia carries `y` to `ζ * y`
  obtain ⟨γ, hγ, hγy⟩ := h_galois.exists_inertia_smul_eq_of_pow_eq hπ_local (pos m) hy_pow same_pow
  have h_act : unitsRep (γ : G) y = ζ + y := Additive.toMul.injective (Units.ext hγy)
  exact ⟨γ, hγ, π, y, h.isUniformiser_iff.2 hπ, hy, by rw [h_act, add_sub_cancel_right]⟩

/-- The places of Ω above N and infinity: valuation subrings in which N has valuation below 1,
together with the infinite places. -/
def PlaceAboveLevel : Type := {B : ClosurePlace // B N < 1} ⊕ InfinitePlace Ω
  deriving Nonempty

instance : MulAction G (PlaceAboveLevel N) :=
  @Sum.instMulAction G {B : ClosurePlace // B N < 1} (InfinitePlace Ω) _
    -- the places above `N` form a set that is stable under `G`, as `G` fixes `N`
    (SubMulAction.mk _ fun g _ hB ↦ by simpa using! (smul_apply_smul_lt_one_iff g).mpr hB).mulAction
    -- on the infinite places `G` acts through the automorphisms of `Ω` over `ℚ`
    (.compHom _ (toAlgAut G ℚ Ω))

instance (Q : Subgroup G) [Q.Normal] : MulAction (G ⧸ Q) (MulAction.orbitRel.Quotient Q X) where
  -- if `a` and `b` are in one coset and `q • y = x`, then `a * q * b⁻¹` lies in `Q` and carries
  -- `b • y` to `a • x`
  smul :=
    .map₂ (· • ·) fun a b hab x y ⟨q, hq⟩ ↦
      ⟨⟨a * q * b⁻¹, by simp [← eq_one_iff, Quotient.sound hab]⟩,
        by simp [← hq, mul_smul, Q.smul_def]⟩
  one_smul := Quotient.ind fun x ↦ congrArg _ (one_smul G x)
  mul_smul := by
    rintro ⟨a⟩ ⟨b⟩ ⟨x⟩
    exact congrArg _ (mul_smul a b x)

/-- A continuous 1-cocycle that vanishes on the inertia group and at a Frobenius element of a
place `B` above the prime `v`, whose residue field has `v.q` elements, vanishes on the
decomposition group of `B`. -/
lemma DiscreteModule.Z1.eq_zero_on_decompGroup {M : DiscreteModule R G} (x : Z1 M.ρ)
    {v : FinPlace K} {B : ClosurePlace} {φ : G} (h : IsPlaceOver B v) (hφ : IsFrob B v.q φ)
    (h_ine : ∀ g ∈ inertiaGroup G B, x.val g = 0) (h_frob : x.val φ = 0) :
    ∀ g ∈ decompGroup G B, x.val g = 0 := by
  obtain ⟨hx_cont, hx_mul⟩ := x.property
  -- the zeros of `x` form an open subgroup that contains inertia and `φ`
  exact h.decompGroup_le (U := cocycleKer M.ρ hx_mul) hφ
    (hx_cont.isOpen_preimage {0} (isOpen_discrete {0})) h_ine h_frob

/-! ### Selmer cocycles, `N`-units and split places -/

/-- The Selmer cocycles: the submodule of continuous 1-cocycles `x : Gal(Ω/K) → V` that satisfy
three conditions. (a) `x g = 0` for every `g` in the inertia group of a place over a prime outside
`S ∪ P`. (b) For every prime `v ∈ S`, the restriction of `x` to the decomposition group of the
chosen valuation subring `A v` lies in the given submodule `L v` of functions on that group.
(c) `x c = 0` for every complex conjugation `c`. The conditions are put on cocycles, not on
cohomology classes. -/
def selmerZ1 (S : Set (FinPlace K)) (A : FinPlace K → ClosurePlace)
    (L : ∀ v : FinPlace K, Submodule R (decompGroup Gal(Ω/K) (A v) → V)) (P : Set (FinPlace K)) :
    Submodule R (Gal(Ω/K) → V) :=
  Z1 V.ρ ⊓
    -- (a) the values on the inertia groups above the primes outside `S ∪ P` are zero
    Submodule.pi (inertiaAbove (S ∪ P)ᶜ) ⊥ ⊓
    -- (b) for `v ∈ S`, the restriction to the decomposition group of `A v` lies in `L v`
    (Submodule.comap
        (LinearMap.pi fun v ↦ LinearMap.funLeft R V (decompGroup Gal(Ω/K) (A v)).subtype)
        (Submodule.pi S L) ⊓
      -- (c) the values at complex conjugations are zero
      Submodule.pi {c : Gal(Ω/K) | IsComplexConj c} ⊥)

/-- Let `G` be a Galois group of `Ω` over a number field `K`, for instance an open subgroup of
another such group, and `S` a finite set of primes of `K`. For a finite discrete `G`-module, only
finitely many continuous cocycles vanish on the inertia group of every valuation subring of `Ω`
that lies over a prime outside `S` (`New.IsPlaceOver`). This is usually deduced from the
Hermite–Minkowski theorem; the proof here uses class field theory. -/
theorem finite_cocycles_unramified_outside (V : DiscreteModule R G) [Finite V]
    {S : Set (FinPlace K)} (hS : S.Finite) :
    {z ∈ Z1 V.ρ | ∀ v ∉ S, ∀ A : ClosurePlace, IsPlaceOver A v →
      ∀ g ∈ inertiaGroup G A, z g = 0}.Finite := by
  -- On an open subgroup `U` that acts trivially and contains no complex conjugation, a cocycle is
  -- a homomorphism; if unramified outside `S`, it is determined by its restrictions to the
  -- decomposition groups at a finite set `T` of primes. So a cocycle is determined by these and
  -- its values at representatives modulo `U`.
  obtain ⟨N, hN⟩ : ∃ N : OpenNormalSubgroup G, ∀ u ∈ N, ∀ y : V, V.ρ u y = V.ρ 1 y :=
    exists_openNormalSubgroup_apply_eq V.continuous
  -- `U`: the elements of `N` that fix the cube roots of unity.
  let U : Subgroup G :=
    (N.toOpenSubgroup ⊓ ⟨(cyclotomicCharMod Ω 3).ker, isOpen_ker_cyclotomicCharMod.out⟩).toSubgroup
  have h_act (u : U) (y : V) : V.ρ u y = y := by simpa using hN u u.property.left y
  have h_cyc (u : U) : cyclotomicCharMod Ω 3 (u : G) = 1 := u.property.right
  have h_fin_above : (FinPlace.below K ⁻¹' S : Set (FinPlace (fixedFieldOf U))).Finite := by
    simpa [preimage_compl] using
      tendsto_place_comap_cofinite (algebraMap K (fixedFieldOf U)) hS.compl_mem_cofinite
  -- `T`: a finite set of primes of the fixed field of `U` that contains those above `S`, such that
  -- principal ideles and ideles that are units outside `T` generate all finite ideles.
  obtain ⟨T, hT_fin : Finite T, hST : FinPlace.below K ⁻¹' S ⊆ T,
    hT_gen : principalIdele.range ⊔ idelesUnitOff T = ⊤⟩ :=
      exists_superset_sup_idelesUnitOff_eq_top h_fin_above
  -- `res z`: the values of `z` at representatives modulo `U` and on the decomposition groups at
  -- the places in `T`.
  let res : (G → V) →+ (G ⧸ U → V) × ∀ w : T, decompGroup U (placeOver w.1) → V :=
    .mk' (fun z ↦ (fun q ↦ z q.out⁻¹, fun _ g ↦ z g)) fun _ _ ↦ rfl
  -- The decomposition group at each `w ∈ T` has finitely many continuous cocycles.
  have h_local (w : T) :
      Finite (Z1 ((V.restrictTo U).restrictTo (decompGroup U (placeOver w.1))).ρ) :=
    (w.1.isPlaceOver_placeOver.isLocalGalois_and_residueCard_eq_and_isUniformiser U).1.finite_Z1 _
  -- `res` maps the unramified cocycles into a finite set, and is injective on them.
  refine (finite_univ.prod (.pi' h_local)).of_injOn (f := res) ?_ ?_
  · exact fun z ⟨⟨hz_cont, hz_mul⟩, _⟩ ↦
      ⟨mem_univ _, fun w ↦ ⟨hz_cont.comp (by fun_prop), fun g h ↦ hz_mul g h⟩⟩
  intro z₁ ⟨hz₁, h_unr₁⟩ z₂ ⟨hz₂, h_unr₂⟩ h_eq
  let z : G → V := z₁ - z₂
  obtain ⟨hz_cont, hz_mul⟩ : z ∈ Z1 V.ρ := sub_mem hz₁ hz₂
  have h_res : res z = 0 := by rw [map_sub, h_eq, sub_self]
  have h_coset (q : G ⧸ U) : z q.out⁻¹ = 0 := congrFun (congrArg Prod.fst h_res) q
  have h_dec (w : T) (u : decompGroup U (placeOver w.1)) : z u = 0 :=
    congrFun (congrFun (congrArg Prod.snd h_res) w) u
  have h_hom : (fun u : U ↦ z u) ∈ Z1 (.trivial ℤ U V) :=
    ⟨hz_cont.comp continuous_subtype_val, fun u u' ↦ by simp [hz_mul, h_act]⟩
  -- A continuous homomorphism on `U` that kills complex conjugations, the decomposition groups at
  -- `T` and the inertia groups outside `T` is zero.
  have h_zero : ∀ u : U, z u = 0 := by
    refine QZChar.eq_zero_of_unramified_off T hT_gen ⟨_, h_hom⟩ (fun c hc ↦ ?_)
      (fun w hw u hu ↦ h_dec ⟨w, hw⟩ ⟨u, hu⟩) fun w hw u hu ↦ ?_
    · -- A complex conjugation inverts the cube roots of unity, which `U` fixes.
      have h_sign : (1 : (ZMod 3)ˣ) = -1 := (h_cyc c).symm.trans hc.cyclotomicCharMod_eq_neg_one
      exact absurd h_sign (by decide)
    · -- A place outside `T` lies over a place outside `S`, where `z₁` and `z₂` are unramified.
      have h_below : w.below K ∉ S := fun h_mem ↦ hw (hST h_mem)
      have h_over : IsPlaceOver (placeOver w) (w.below K) :=
        w.isPlaceOver_placeOver.isPlaceOver_below
      simp [z, h_unr₁ _ h_below _ h_over u hu, h_unr₂ _ h_below _ h_over u hu]
  -- `z` vanishes at `r⁻¹`, for `r` the representative of `g`, and at `r⁻¹ * g ∈ U`; its zeros
  -- form a subgroup.
  refine sub_eq_zero.1 (funext fun g ↦ ?_)
  have h_prod : z ((g : G ⧸ U).out⁻¹ * g) = 0 := h_zero ⟨_, by simp [← QuotientGroup.eq]⟩
  exact ((cocycleKer V.ρ hz_mul).mul_mem_cancel_left (h_coset g)).1 h_prod

/-- For a finite discrete module `V` of `Gal(Ω/K)` and a finite set `S` of primes of `K`, only
finitely many continuous 1-cocycles with values in `V` vanish on all inertia groups above the primes
outside `S`. This is the case `G = Gal(Ω/K)` of `finite_cocycles_unramified_outside`.

Compare the finiteness of Galois cohomology with restricted ramification in Milne's Arithmetic
Duality Theorems. Here only degree one is treated, for cocycles rather than classes, and `V` itself
need not be unramified outside `S`. -/
lemma selmerZ1.finite_unramified_cocycles (V : DiscreteModule R Gal(Ω/K)) [Finite V]
    {S : Set (FinPlace K)} (hS : S.Finite) :
    (Z1 V.ρ ⊓ Submodule.pi (inertiaAbove Sᶜ) ⊥).carrier.Finite :=
  (finite_cocycles_unramified_outside V hS).subset fun _ ⟨hz, h_ine⟩ ↦
    ⟨hz, fun v hv A hA g hg ↦ h_ine g ⟨v, hv, A, hA, hg⟩⟩

namespace IsLargeLevel

/-- The N-units of Ω: elements of Ω^× that are units in every valuation subring in which N does
not have valuation below 1. -/
def sUnits : Submodule ℤ (DiscreteUnits Ω) :=
  -- `x` lies in the unit group of every place `B` at which `N` is a unit
  Submodule.comap (LinearMap.const (R := ℤ) (M₂ := DiscreteUnits Ω) (ι := ClosurePlace))
    (Submodule.pi {B : ClosurePlace | B N = 1} fun B ↦ B.unitGroup.toAddSubgroup.toIntSubmodule)

variable {N} in
lemma mem_sUnits_iff {x : DiscreteUnits Ω} :
    x ∈ sUnits N ↔ ∀ B : ClosurePlace, B N = 1 → B (x.toMul : Ω) = 1 :=
  Iff.rfl

/-- The N-units of the fixed field of U: the N-units of Ω that are fixed by U. -/
abbrev fixedSUnits : Submodule ℤ (DiscreteUnits Ω) := sUnits N ⊓ (unitsModule U.1.1).H0

/-- The `N`-units of the fixed field of `U`, as a representation of `G ⧸ U` over `ℤ`. -/
abbrev fixedSUnitsRep : Representation ℤ (G ⧸ U.1.1) (fixedSUnits N U) :=
  lift U.1.1
    (unitsRep.subrepresentation (fixedSUnits N U) fun g x ⟨hx_unit, hx_fix⟩ ↦
      ⟨mem_sUnits_iff.2 fun B hB ↦ isEquiv_comap.eq_one_iff_eq_one.1 <|
        -- `g • x` is a unit at `B` because `x` is a unit at the preimage of `B` under `g`.
        mem_sUnits_iff.1 hx_unit (B.comap (toRingHom G Ω g))
          (isEquiv_comap.eq_one_iff_eq_one.2 (by simpa using hB)),
        unitsRep.le_comap_invariants U.1.1 g hx_fix⟩)
    fun u hu ↦ LinearMap.ext fun ⟨x, _, hx_fix⟩ ↦ Subtype.ext (hx_fix ⟨u, hu⟩)

/-- Split places for `U`. The subgroup `U` fixes the `m`-th roots of unity, and `m` divides `N`. The
primes `v i` are distinct and do not divide `N`. Each has a place above it with a Frobenius element
in `U`. The set `I` is the union of the inertia groups above the other primes not dividing `N`.
Inertia above every prime not dividing `N` lies in `U`. The primes dividing `N` generate the class
group of every number field between `K` and the fixed field of `U`. -/
structure SplitPlaces (ι : Type) where
  /-- `U` fixes the `m`-th roots of unity: the cyclotomic character modulo `m` is trivial on it. -/
  cyclotomicCharMod_eq_one : ∀ g ∈ U, cyclotomicCharMod Ω m g = 1
  /-- `m` divides `N`. -/
  dvd_level : m ∣ N
  /-- The chosen primes of `K`. -/
  v : ι → FinPlace K
  /-- The chosen primes are distinct. -/
  v_injective : v.Injective
  /-- No chosen prime divides `N`. -/
  level_notMem (i : ι) : ↑N ∉ (v i).1
  /-- A place of `Ω` for each chosen prime. -/
  valuationSubring : ι → ClosurePlace
  /-- The place `valuationSubring i` lies over `v i`. -/
  isPlaceOver (i : ι) : IsPlaceOver (valuationSubring i) (v i)
  /-- An element of `G` for each chosen prime. -/
  φ : ι → G
  /-- `φ i` is an arithmetic Frobenius at `valuationSubring i` and lies in `U`. -/
  isFrob (i : ι) : IsFrob (valuationSubring i) (v i).q (φ i) ∧ φ i ∈ U
  /-- `I` is the union of the inertia groups of the places over the primes of `K` that are not
  chosen and do not divide `N`. -/
  mem_inertia_iff (g : G) :
      g ∈ I ↔ ∃ w : FinPlace K,
        ↑N ∉ w.1 ∧ w ∉ range v ∧ ∃ B : ClosurePlace, IsPlaceOver B w ∧ g ∈ inertiaGroup G B
  /-- The inertia group of every place over a prime not dividing `N` lies in `U`. -/
  inertiaGroup_le {v : FinPlace K} {B : ClosurePlace} :
      ↑N ∉ v.1 → IsPlaceOver B v → inertiaGroup G B ≤ U
  /-- For each number field `F` between `K` and the fixed field of `U`, the principal ideles and the
  ideles that are units away from the primes dividing `N` generate all finite ideles. -/
  principal_sup_idelesUnitOff (F : IntermediateField K Ω) [NumberField F] :
      F ≤ fixedFieldOf U.1.1 →
      (principalIdele (K := F)).range ⊔ idelesUnitOff {w : FinPlace F | ↑N ∈ w.1} = ⊤

variable {m N I U} {ι : Type} (s : SplitPlaces m N I U ι)

/-! ### `N`-units of `K` and split primes -/

/-- An element `x` of `Kˣ`, sent to `Ωˣ` by `DiscreteUnits.ofBase`, is an `N`-unit of `Ω` exactly
when it is an `S`-unit of `K` (`Set.unit`) for `S` the set of primes that divide `N`, that is, a
unit at every prime of `K` that does not divide `N`. -/
lemma ofBase_mem_sUnits {N : ℕ} {x : Kˣ} :
    (DiscreteUnits.ofBase G Ω (Additive.ofMul x)).val ∈ sUnits N ↔
      x ∈ unit {w : FinPlace K | ↑N ∈ w.asIdeal} K := by
  -- For `B` over `w`, the condition on `x` at `B` is the condition on `x` at `w`.
  have h_same {B : ClosurePlace} {w : FinPlace K} (hB : IsPlaceOver B w) :
      (B N = 1 → valuationVia K B x = 1) ↔ (↑N ∉ w.asIdeal → w.valuation K x = 1) :=
    hB.valuation_natCast_eq_one_iff.imp hB.valuationVia_eq_one_iff
  change (∀ B : ClosurePlace, B N = 1 → valuationVia K B x = 1) ↔ _
  refine ⟨fun h (w : FinPlace K) ↦ (h_same w.isPlaceOver_placeOver).1 (h _),
    fun h B hN ↦ by_contra fun hx ↦ ?_⟩
  -- If `x` is not a unit at `B`, then `B` is not trivial on `K`, so it lies over some prime `w`.
  obtain ⟨w, hB⟩ := exists_isPlaceOver_of_val_ne_one K (A := B) (by simp) hx
  exact hx ((h_same hB).2 (h w) hN)

/-- The property that the Frobenius elements `s.φ i` detect `m`-th roots: every `y` in `Ωˣ` whose
`m`-th power is an `N`-unit of the fixed field of `U`, and which every `s.φ i` fixes, is fixed by
all of `U`. -/
abbrev SplitPlaces.FrobeniiDetectRoots : Prop :=
  ∀ y : DiscreteUnits Ω, m • y ∈ fixedSUnits N U →
    (∀ i : ι, unitsRep (s.φ i) y = y) → ∀ g ∈ U, unitsRep g y = y

/-- For `m ≠ 0`, an element of Ωˣ whose `m`-th power is an `N`-unit of the fixed field of `U` is
itself an `N`-unit of Ω. -/
lemma mem_sUnits_of_nsmul_mem {r : DiscreteUnits Ω} {y : fixedSUnits N U} (hr : m • r = y.val) :
    r ∈ sUnits N :=
  fun B hB ↦ by simpa [← hr, ne] using y.property.left B hB

/-- Let `s : SplitPlaces m N I U ι` be split places for the open normal subgroup `U`, with chosen
primes `s.v i` indexed by a type `ι`. If the valuation subring `B` lies over a chosen prime `s.v i`,
then its decomposition group lies in `U`. -/
lemma SplitPlaces.decompGroup_le (s : SplitPlaces m N I U ι) {i : ι}
    (h : IsPlaceOver B (s.v i)) : decompGroup G B ≤ U := by
  -- `U` is open and normal, and contains inertia and a conjugate of `s.φ i`, a Frobenius at `B`
  obtain ⟨g, rfl⟩ : ∃ g : G, g • s.valuationSubring i = B := (s.isPlaceOver i).exists_smul G h
  obtain ⟨h_frob, hφ_mem⟩ := s.isFrob i
  exact h.decompGroup_le (h_frob.conj g) U.isOpen (s.inertiaGroup_le (s.level_notMem i) h)
    (U.isNormal'.conj_mem _ hφ_mem g)

/-- Given split places `s : SplitPlaces m N I U ι`, with chosen primes indexed by a type `ι`, pass
to an open subgroup `B` that contains `U`. Let `Q` be an open normal subgroup of `B` that contains
`U` and fixes the `m`-th roots of unity. Let `σ` pick a representative of each coset of `B`. Take
the places `(σ x)⁻¹ • s.valuationSubring i`, the primes below them in the fixed field of `B`, and
the conjugated Frobenius elements. They form split places for `Q`, indexed by `ι × G ⧸ B`. Their
inertia set is the preimage of `I` in `B`. -/
def SplitPlaces.liftToSubgroup (B : OpenSubgroup G) (Q : OpenNormalSubgroup B.1) (hUB : U.1.1 ≤ B)
    (hUQ : U.1.1.subgroupOf B ≤ Q) (h_fix : ∀ g ∈ Q, cyclotomicCharMod Ω m g = 1) (σ : G ⧸ B.1 → G)
    (hσ : ∀ x : G ⧸ (B : Subgroup G), σ x = x) :
    SplitPlaces m N ((↑) ⁻¹' I) Q (ι × G ⧸ B.1) := by
  -- The place of index `(i, x)` is the translate of `s.valuationSubring i` by `(σ x)⁻¹`; it lies
  -- over `s.v i`, and over a prime `w (i, x)` of the field of `B`.
  have h_over (θ : ι × G ⧸ B.1) : IsPlaceOver ((σ θ.2)⁻¹ • s.valuationSubring θ.1) (s.v θ.1) :=
    (s.isPlaceOver θ.1).smul (σ θ.2)⁻¹
  -- `w (i, x)`: the prime of the field of `B` below the translate, and its prime in `K`.
  choose w hw h_below using fun θ ↦ (h_over θ).exists_above (L := fixedFieldOf B.1)
  have h_conj (θ : ι × G ⧸ B.1) : (σ θ.2)⁻¹ * s.φ θ.1 * (σ θ.2)⁻¹⁻¹ ∈ U := U.2.1 _ (s.isFrob _).2 _
  refine
    { cyclotomicCharMod_eq_one := h_fix
      dvd_level := s.dvd_level
      v := w
      v_injective := fun ⟨i, x⟩ ⟨j, y⟩ h_eq ↦ ?_
      level_notMem θ := s.level_notMem θ.1 ∘ by simp [← h_below]
      valuationSubring θ := (σ θ.2)⁻¹ • s.valuationSubring θ.1
      isPlaceOver := hw
      φ θ := ⟨_, hUB (h_conj θ)⟩
      isFrob θ := ⟨?_, hUQ (h_conj θ)⟩
      mem_inertia_iff g := (s.mem_inertia_iff g).trans ⟨?_, ?_⟩
      inertiaGroup_le hN hC _ hg := hUQ (s.inertiaGroup_le (by simpa) hC.isPlaceOver_below hg)
      principal_sup_idelesUnitOff F hF h_le :=
        have : NumberField (F.restrictScalars K) := hF
        s.principal_sup_idelesUnitOff (F.restrictScalars K) fun _ ha ⟨g, hg⟩ ↦
          h_le ha ⟨⟨g, hUB hg⟩, hUQ hg⟩ }
  · -- Equal primes lie over the same `s.v i`, and their two places differ by some `t ∈ B`. The
    -- decomposition groups over `s.v i` are in `U ≤ B`, so the two cosets agree.
    obtain rfl : i = j :=
      s.v_injective (by simpa [h_below] using congrArg (FinPlace.below K) h_eq)
    obtain ⟨t, ht⟩ := (h_eq ▸ hw (i, x) : IsPlaceOver _ (w (i, y))).exists_smul B.1 (hw (i, y))
    have h_dec : t * ((σ x)⁻¹ * σ y) ∈ decompGroup G ((σ y)⁻¹ • s.valuationSubring i) := by
      simpa [mul_smul]
    rw [← hσ x, ← hσ y, QuotientGroup.eq.2
      ((mul_mem_cancel_left t.2).1 (hUB (s.decompGroup_le (h_over (i, y)) h_dec)))]
  · -- The decomposition group lies in `B`, so the residue field does not grow.
    have h_card : (w θ).q = (s.v θ.1).q :=
      (((h_over θ).ramification_in_tower _ (hw θ)).1 ((s.decompGroup_le (h_over θ)).trans hUB)).1
    exact h_card ▸ (s.isFrob _).1.conj _
  · -- A prime above an unchosen prime is unchosen.
    rintro ⟨v, hN, hv, C, hC, hg⟩
    obtain ⟨v', hC', rfl⟩ := hC.exists_above (L := fixedFieldOf B.1)
    exact ⟨v', hN ∘ by simp, fun ⟨θ, hθ⟩ ↦ hv (by simp [← hθ, h_below]), C, hC', hg⟩
  · -- Every prime above `s.v i` is chosen: if `a` carries `C` to `s.valuationSubring i`, it is
    -- `w (i, a)`.
    rintro ⟨v, hN, hv, C, hC, hg⟩
    refine ⟨_, by simpa, fun ⟨i, hi⟩ ↦ ?_, C, hC.isPlaceOver_below, hg⟩
    obtain ⟨a, ha⟩ := hC.isPlaceOver_below.exists_smul G (hi ▸ s.isPlaceOver i)
    -- The place of index `(i, a)` is the translate of `C` by `(σ a)⁻¹ * a ∈ B`.
    exact hv ⟨(i, a), (hw _).unique
      (by simpa [smul_smul, ← ha] using! hC.smul (⟨_, QuotientGroup.eq.1 (hσ a)⟩ : B.1))⟩

/-- For split places `s : SplitPlaces m N I U ι`, with chosen primes indexed by a type `ι`, the set
`I` (the union of the inertia groups above the primes that are not chosen and do not divide `N`)
lies in `U` and is stable under conjugation. -/
lemma SplitPlaces.mem_and_conj_mem (s : SplitPlaces m N I U ι) (g : G) (hg : g ∈ I) :
    g ∈ U ∧ ∀ t : G, t⁻¹ * g * t ∈ I := by
  obtain ⟨w, hN, hw, B, hB, hgB⟩ := (s.mem_inertia_iff g).1 hg
  -- The prime `w` is outside `N`, so its inertia lies in `U`; a conjugate of `g` is in the
  -- inertia of a translate of `B`, which lies over the same `w`.
  refine ⟨s.inertiaGroup_le hN hB hgB, fun t ↦ ?_⟩
  have h_conj : t⁻¹ * g * t⁻¹⁻¹ ∈ inertiaGroup G (t⁻¹ • B) := hgB.conj t⁻¹
  rw [inv_inv] at h_conj
  exact (s.mem_inertia_iff _).2 ⟨w, hN, hw, t⁻¹ • B, hB.smul _, h_conj⟩

end IsLargeLevel

end New

/-!
## Places above N and infinity and the equivariant unit theorem

For an open normal subgroup `Q` of `G`, `New.IsLargeLevel.fixedSUnits N Q` is the group of `N`-units
of `Ω` fixed by `Q`, written additively, with its action of `G ⧸ Q`. The unit theorem is stated for
its product with `ℤ`: this summand shifts all the logarithms at infinity at once and makes up for
the `- 1` in Dirichlet's rank.
-/

section EquivariantUnits

open Quot NumberField Pointwise MulAction InfinitePlace Units Matrix NeZero Function Module
  LinearMap Set Ideal

namespace New

variable (G : Type)
  {K : Type} [Group G] [TopologicalSpace G] [Field K] [NumberField K] (N : ℕ) [NeZero N]

/-- If an abelian group `B` is the image of a finitely generated one `A`, the rank of `B × ℤ` is
at most that of `A` plus one. -/
lemma finrank_prod_int_le_of_surjective {A B : Type} [AddCommGroup A] [AddCommGroup B]
    [Module.Finite ℤ A] {f : A →ₗ[ℤ] B} (hf : Surjective f) :
    finrank ℤ (B × ℤ) ≤ finrank ℤ A + 1 := by
  refine finrank_le_of_rank_le ?_
  calc Module.rank ℤ (B × ℤ)
    _ ≤ Module.rank ℤ A + Module.rank ℤ ℤ := by
      grw [rank_eq_of_surjective fst_surjective, ker_fst, rank_range_le,
        rank_le_of_surjective _ hf]
    _ = (finrank ℤ A + 1 : ℕ) := by simp

/-- Let `M` give, for each place in `S` or at infinity, a function on pairs of an `S`-unit `u` and
an integer `n`: at `v ∈ S` it vanishes exactly when `u` is a unit at `v`, and at an infinite place
`w` it is `log |u|_w + n`. These functions are linearly independent over ℝ. For logarithms at all
places this is the nonvanishing of the `S`-regulator. -/
lemma linearIndependent_sUnit_log {S : Set (FinPlace K)} [Fintype S]
    {M : S ⊕ InfinitePlace K → S.unit K × ℤ → ℝ}
    (h_fin : ∀ (v : S) (u : S.unit K × ℤ), M (Sum.inl v) u = 0 ↔ v.val.valuation K u.1.val = 1)
    (h_inf : ∀ (w : InfinitePlace K) (u : S.unit K × ℤ),
      M (Sum.inr w) u = Real.log (w u.1.val) + u.2) :
    LinearIndependent ℝ M := by
  classical
  -- It is enough to find one pair for each place such that the matrix of values is invertible. At
  -- `v ∈ S` take an `S`-unit of valuation `exp h` at `v` and one elsewhere in `S`; at infinity,
  -- `(1, 1)` and the fundamental units. The matrix is block triangular.
  obtain ⟨h, h_ne, h_principal⟩ : ∃ h ≠ (0 : ℕ), ∀ d : S → ℤ, ∃ x : S.unit K, ∀ v : S,
      (v : FinPlace K).valuation K ((x : Kˣ) : K) = WithZero.exp (h * d v) :=
    exists_valuation_eq_exp_mul S.toFinite
  choose y hy using h_principal
  let η : {w // w ≠ dirichletUnitTheorem.w₀} ≃ Fin (Units.rank K) := (equivFinRank K).symm
  let atInfinite (w : InfinitePlace K) : S.unit K × ℤ :=
    if hw : w = dirichletUnitTheorem.w₀ then (1, 1) else
      (⟨.mk0 _ (coe_ne_zero (fundSystem K (η ⟨w, hw⟩))),
        by simp [notMem_of_isUnit, unit, Subgroup.copy]⟩, 0)
  let pair : S ⊕ InfinitePlace K → S.unit K × ℤ :=
    Sum.elim (fun v ↦ (y (Pi.single v 1), 0)) atInfinite
  let A : Matrix (S ⊕ InfinitePlace K) (S ⊕ InfinitePlace K) ℝ := of fun i j ↦ M j (pair i)
  refine .of_comp (funLeft ℝ ℝ pair) (linearIndependent_cols_of_det_ne_zero (A := A) ?_)
  -- Units of `𝓞 K` have valuation one at every finite place, so `M` vanishes on them at `v ∈ S`.
  have h_lower : A.toBlocks₂₁ = 0 := by
    ext w v
    show M (Sum.inl v) (atInfinite w) = 0
    by_cases hw : w = dirichletUnitTheorem.w₀ <;> simp [h_fin, atInfinite, hw, notMem_of_isUnit]
  -- The block of the places in `S` is diagonal, with nonzero diagonal as `h ≠ 0`.
  have h_finite : A.toBlocks₁₁.det ≠ 0 := det_ne_zero_of_sum_col_lt_diag fun v ↦ by
    -- the entries off the diagonal vanish
    rw [Finset.sum_eq_zero (by simp +contextual [A, pair, toBlocks₁₁, h_fin, hy])]
    simp [A, pair, toBlocks₁₁, h_fin, hy, h_ne]
  -- The block of the infinite places, with column `w` scaled by `w.mult`, is the matrix whose
  -- determinant is `[K : ℚ]` times the regulator, up to sign.
  have h_reg : finrank ℚ K * regulator K =
      |(of fun i (w : InfinitePlace K) ↦ (w.mult : ℝ) * A.toBlocks₂₂ i w).det| := by
    convert finrank_mul_regulator_eq_det K _ η using 3
    ext i w
    by_cases hi : i = dirichletUnitTheorem.w₀ <;> simp [A, pair, atInfinite, toBlocks₂₂, h_inf, hi]
  have h_infinite : A.toBlocks₂₂.det ≠ 0 := fun h_zero ↦ by
    simp [det_mul_row, h_zero, regulator_ne_zero, finrank_pos.ne'] at h_reg
  rw [← A.fromBlocks_toBlocks, h_lower, det_fromBlocks_zero₂₁]
  exact mul_ne_zero h_finite h_infinite

variable [Algebra K Ω] [MulSemiringAction G Ω] [IsProGalois G K Ω]

/-- Let the profinite group `G` act on `Ω` as the Galois group of `Ω` over the number field `K`,
let `N ≠ 0`, and let the valuation subring `A v` of `Ω` lie over `v` for each prime `v` of `K`.
Lift each prime `v` dividing `N` to `A v`, and each infinite place of `K` to a chosen infinite
place of `Ω` over it. The lifts lie in `PlaceAboveLevel N`: the valuation subrings of `Ω` in which
`N` has valuation below one, together with the infinite places of `Ω`. Then sending a place of `K`
above `N` or infinity to the orbit of its lift is a bijection onto the `G`-orbits of
`PlaceAboveLevel N`. -/
lemma PlaceAboveLevel.bijective_orbits (G : Type) {K : Type} [Group G] [TopologicalSpace G]
    [Field K] [NumberField K] (N : ℕ) [NeZero N] [Algebra K Ω] [MulSemiringAction G Ω]
    [IsProGalois G K Ω] {A : FinPlace K → ClosurePlace}
    (hA : ∀ v : FinPlace K, IsPlaceOver (A v) v) :
    let liftFinite (v : {v : FinPlace K | (N : 𝓞 K) ∈ v.asIdeal}) :
        {B : ClosurePlace // B.valuation N < 1} :=
      ⟨A v, (hA v).valuation_natCast_lt_one_iff.mpr v.property⟩
    let liftInfinite : InfinitePlace K → InfinitePlace Ω := surjInv comap_surjective
    Bijective
      (Quotient.mk (orbitRel G (PlaceAboveLevel N)) ∘ Sum.map liftFinite liftInfinite) := by
  intro liftFinite liftInfinite
  have comap_lift (w : InfinitePlace K) : (liftInfinite w).comap (algebraMap K Ω) = w :=
    surjInv_eq comap_surjective w
  constructor
  · -- Injectivity: two places of `Ω` in one orbit lie over the same place of `K`.
    rintro (v | v) (w | w) h_eq
    · obtain ⟨g, hg⟩ := Quotient.exact h_eq
      have h_smul : g • A w = A v := congrArg Subtype.val (Sum.inl.inj hg)
      have h_over : IsPlaceOver (A v) (w : FinPlace K) := by
        rw [← h_smul]
        exact (hA w).smul g
      exact congrArg Sum.inl (Subtype.ext ((hA v).unique h_over))
    · obtain ⟨g, hg⟩ := Quotient.exact h_eq
      cases hg
    · obtain ⟨g, hg⟩ := Quotient.exact h_eq
      cases hg
    · obtain ⟨g, hg⟩ := Quotient.exact h_eq
      have h_smul : MulSemiringAction.toAlgEquiv K Ω g • liftInfinite w = liftInfinite v :=
        Sum.inr.inj hg
      have h_under :
          (liftInfinite w).comap (algebraMap K Ω) = (liftInfinite v).comap (algebraMap K Ω) :=
        InfinitePlace.mem_orbit_iff.1 ⟨MulSemiringAction.toAlgEquiv K Ω g, h_smul⟩
      rw [comap_lift, comap_lift] at h_under
      rw [h_under]
  · -- Surjectivity: `G` is transitive on the places of `Ω` over a given place of `K`.
    rintro ⟨⟨B, hB⟩ | u⟩
    · obtain ⟨v, hv⟩ : ∃ v : FinPlace K, IsPlaceOver B v :=
        exists_isPlaceOver_of_val_ne_one K out hB.ne
      obtain ⟨g, hg⟩ : ∃ g : G, g • B = A v := hv.exists_smul G (hA v)
      exact ⟨.inl ⟨v, hv.valuation_natCast_lt_one_iff.1 hB⟩,
        sound ⟨g, congrArg Sum.inl (Subtype.ext hg)⟩⟩
    · let w : InfinitePlace K := u.comap (algebraMap K Ω)
      obtain ⟨g, hg⟩ : ∃ g : G, MulSemiringAction.toAlgAut G K Ω g • u = liftInfinite w :=
        (toAlgAut_surjective G).exists.1 (mem_orbit_iff.2 (comap_lift w).symm)
      exact ⟨.inr w, sound ⟨g, congrArg Sum.inr hg⟩⟩

omit [NeZero N] in
/-- For an open normal subgroup `Q`, the units of the fixed field `F` of `Q` away from the primes
dividing `N` map onto the `N`-units of `Ω` fixed by `Q`, by the inclusion of `Fˣ` in `Ωˣ`. -/
lemma exists_surjective_sUnit_to_fixedSUnits (Q : OpenNormalSubgroup G) :
    let F : IntermediateField K Ω := fixedFieldOf Q.1.1
    let S : Set (FinPlace F) := {v : FinPlace F | ↑N ∈ v.asIdeal}
    ∃ ε : Additive (S.unit F) →+ IsLargeLevel.fixedSUnits N Q,
      Surjective ε ∧ ∀ x : Additive (S.unit F),
        (ε x).1 = (DiscreteUnits.ofBase Q.1.1 Ω (.ofMul x.toMul.1)).1 := by
  intro F S
  -- An `S`-unit of `F` is an `N`-unit of `Ω` fixed by `Q`.
  let ε : Additive (S.unit F) →+ IsLargeLevel.fixedSUnits N Q :=
    .mk' (fun x ↦ ⟨(DiscreteUnits.ofBase Q.1.1 Ω (.ofMul x.toMul.1)).1,
        IsLargeLevel.ofBase_mem_sUnits.2 x.toMul.2, Subtype.prop _⟩) fun x y ↦ Subtype.ext (by simp)
  refine ⟨ε, fun ⟨y, y_unit, y_fix⟩ ↦ ?_, fun x ↦ rfl⟩
  -- Conversely, a unit of `Ω` fixed by `Q` comes from some `x : Fˣ`, which is then an `S`-unit.
  obtain ⟨x, hx⟩ := (DiscreteUnits.ofBase_bijective Q.1.1 (K := F)).surjective ⟨y, y_fix⟩
  obtain rfl : (DiscreteUnits.ofBase Q.1.1 Ω x).1 = y := congrArg Subtype.val hx
  exact ⟨.ofMul ⟨x.toMul, IsLargeLevel.ofBase_mem_sUnits.1 y_unit⟩, rfl⟩

include K

/-- The order, normalised on `K`, of `g⁻¹ y` at a place `B` above `N` is the order of `y` at
`g • B`. -/
lemma ordRat_inv_smul {B : ValuationSubring Ω} (hB : B.valuation N < 1) (g : G)
    (y : DiscreteUnits Ω) : ordRat K B (unitsRep g⁻¹ y) = ordRat K (g • B) y := by
  obtain ⟨v, hv⟩ := exists_isPlaceOver_of_val_ne_one K out hB.ne
  simp [← hv.ordRat_smul g]

/-- Dirichlet's theorem for the group `E = fixedSUnits N Q` of `N`-units of the fixed field of `Q`,
with the action of `G ⧸ Q` (`fixedSUnitsRep`). Let `X` be the set of `Q`-orbits of
`PlaceAboveLevel N`, the places of `Ω` above `N` and infinity. Then `E` is finitely generated, and
there are additive maps `Λ z` from `E × ℤ` to `ℝ`, for `z : X`, such that (a) `G ⧸ Q`, acting
trivially on `ℤ`, permutes the `Λ z` as it permutes the `z`, and (b) the `Λ z` are linearly
independent over `ℝ`. Moreover (c) the rank of `E × ℤ` is at most `#X`. -/
lemma IsLargeLevel.dirichlet_fixedSUnits (Q : OpenNormalSubgroup G) :
    let X := orbitRel.Quotient Q.toOpenSubgroup.toSubgroup (PlaceAboveLevel N)
    Module.Finite ℤ (fixedSUnits N Q) ∧
    ∃ Λ : X → fixedSUnits N Q × ℤ →ₗ[ℤ] ℝ,
      -- (a)
      (∀ (g : G ⧸ Q.toOpenSubgroup.toSubgroup) (z : X) (y : fixedSUnits N Q × ℤ),
        Λ z
            ((fixedSUnitsRep N Q).prod
              (Representation.trivial ℤ (G ⧸ Q.toOpenSubgroup.toSubgroup) ℤ) g⁻¹ y) =
          Λ (g • z) y) ∧
      -- (b)
      LinearIndependent ℝ Λ ∧
      -- (c)
      finrank ℤ (fixedSUnits N Q × ℤ) ≤ Nat.card X := by
  intro X
  -- The orbits `X` are the places of the fixed field `F` of `Q` above `N` and infinity.
  let F : IntermediateField K Ω := fixedFieldOf Q.1.1
  let S : Set (FinPlace F) := {v : FinPlace F | ↑N ∈ v.1}
  have : Fintype S := (finite_natCast_mem N).fintype
  let e : S ⊕ InfinitePlace F ≃ X :=
    .ofBijective _ (PlaceAboveLevel.bijective_orbits _ N FinPlace.isPlaceOver_placeOver)
  -- `fixedSUnits N Q` is the image of the `S`-units of `F`, to which Dirichlet's theorem applies.
  obtain ⟨S_units_finite, rank_eq⟩ : Module.Finite ℤ (Additive (S.unit F)) ∧
      finrank ℤ (Additive (S.unit F)) + 1 = S.ncard + Fintype.card (InfinitePlace F) :=
    SUnit.dirichlet_unit_theorem S.toFinite
  obtain ⟨ε, ε_onto, hε⟩ := exists_surjective_sUnit_to_fixedSUnits G (K := K) N Q
  let ε' : S.unit F × ℤ → fixedSUnits N Q × ℤ := fun u ↦ (ε (.ofMul u.1), u.2)
  -- The order of `y` at a finite place, `log |y|_w + n` at an infinite one; both are equivariant.
  let lg (y : DiscreteUnits Ω) (n : ℤ) : PlaceAboveLevel N → ℝ :=
    Sum.elim (fun B ↦ ordRat K B.1 y) fun w ↦ (w y.toMul.1).log + n
  have lg_smul (g : G) (y : DiscreteUnits Ω) (n : ℤ) :
      ∀ z : PlaceAboveLevel N, lg (unitsRep g⁻¹ y) n z = lg y n (g • z)
    | .inl B => congrArg Rat.cast (ordRat_inv_smul G N B.2 g y)
    | .inr _ => rfl
  have lg_orbit (y : fixedSUnits N Q) (n : ℤ) (z z' : PlaceAboveLevel N) :
      orbitRel Q.1.1 _ z z' → lg y n z = lg y n z' := by
    rintro ⟨g, rfl⟩
    have h_fix : unitsRep (g : G)⁻¹ (y : DiscreteUnits Ω) = y := y.2.2 g⁻¹
    exact (lg_smul g y n z').symm.trans (by rw [h_fix])
  let Λ (x : X) : fixedSUnits N Q × ℤ →+ ℝ :=
    -- Both branches of `lg` are additive in `(y, n)`.
    .mk' (fun y ↦ x.liftOn (lg y.1 y.2) (lg_orbit y.1 y.2)) <| by
      obtain ⟨_ | _⟩ := x <;> simp [lg, Real.log_mul, add_add_add_comm]
  -- Read through `e` and `ε'`, the `Λ x` are as in `linearIndependent_sUnit_log`.
  have Λ_fin (v : S) (u : S.unit F × ℤ) :
      Λ (e (.inl v)) (ε' u) = 0 ↔ v.1.valuation F u.1.1 = 1 := by
    change (ordRat K (placeOver v.1) (ε (.ofMul u.1)).1 : ℝ) = 0 ↔ _
    rw [hε, Rat.cast_eq_zero, v.1.isPlaceOver_placeOver.isPlaceOver_below.ordRat_eq_zero_iff]
    exact v.1.isPlaceOver_placeOver.valuationVia_eq_one_iff
  have Λ_inf (w : InfinitePlace F) (u : S.unit F × ℤ) :
      Λ (e (.inr w)) (ε' u) = (w u.1.1).log + u.2 := by
    change Real.log (surjInv comap_surjective w (ε (.ofMul u.1)).1.toMul.1) + u.2 = _
    rw [hε]
    change Real.log ((surjInv comap_surjective w).comap (algebraMap F Ω) u.1.1) + u.2 = _
    rw [surjInv_eq comap_surjective w]
  have h_indep : LinearIndependent ℝ fun z u ↦ Λ (e z) (ε' u) :=
    linearIndependent_sUnit_log Λ_fin Λ_inf
  refine ⟨.of_surjective ε.toIntLinearMap ε_onto, fun x ↦ (Λ x).toIntLinearMap, ?_, ?_, ?_⟩
  · rintro ⟨g⟩ ⟨z⟩ y
    exact lg_smul g y.1 y.2 z
  · exact (linearIndependent_equiv e).1 (.of_comp (pi fun u ↦ applyₗ' ℝ (ε' u)) h_indep)
  · -- The summand `ℤ` makes up for the `- 1` in Dirichlet's rank.
    rw [← Nat.card_congr e]
    calc finrank ℤ (fixedSUnits N Q × ℤ)
      _ ≤ finrank ℤ (Additive (S.unit F)) + 1 :=
        finrank_prod_int_le_of_surjective (f := ε.toIntLinearMap) ε_onto
      _ = Nat.card (S ⊕ InfinitePlace F) := by simp [rank_eq]

end New

end EquivariantUnits

end
