import Lib.ClassField.GreenbergWiles.CocycleCounts
import Lib.ClassField.GreenbergWiles.SelmerRelations

/-!
# Relations at split primes

Let `M` be a discrete Galois module with local conditions at a finite set `S` of primes; `Z(P)`
(`cocycles P`) is the group of cocycles allowed at each prime of `S`, zero at complex conjugations,
unramified outside `S ∪ P`. A relation is a function on an open normal subgroup `U` with values in
the dual of `M` that has the properties of the restriction of a dual cocycle, among them the
reciprocity law at primes that are split for `U`. The module of relations takes the place of the
dual Selmer group: at a split prime where the relation `y` is unramified, `y(φ)(z(γ))` is the local
pairing of `y` with a cocycle `z`.

* `New.SplitPrime`, `New.RelationSetting`: split primes, and the module with its local conditions.
* `New.RelationSetting.relations`: the relations off a finite set `T`; there are finitely many if
  `M` is finite.
* `New.RelationSetting.exists_splitPlaces_forall_exists_mem_relations`: one family of split primes
  gives relations at all split primes.
* `New.RelationSetting.exists_card_cocycles_le`: a lower bound for the number of relations.

Notions from other files:
* `New.IsLargeLevel.SplitPlaces`: a family `s` of distinct primes `s.v i` prime to a level `q`, with
  Frobenius elements `s.φ i` in `U` at places `s.valuationSubring i` above `s.v i`; inertia at the
  primes prime to `q` lies in `U`, and `I` is the union of the inertia groups above those primes not
  in the family. Its property `FrobeniiDetectRoots` says that an `m`-th root of a `q`-unit of the
  field of `U` that all `s.φ i` fix is fixed by `U`.
* `New.IsLargeLevel.fixedSUnits q U`: the `q`-units of the field of `U`; `New.unitsRep` is the
  Galois action on `Ωˣ`, written additively.
* `New.cyclotomicCharMod`: the cyclotomic character modulo `m`.

## Relation to the literature

Part of a known result: Greenberg–Wiles formula, as a lower bound for the dual side. See
`Lib.ClassField.GreenbergWiles.CocycleCounts`. Source: Darmon, Diamond, Taylor, Fermat's Last
Theorem, Theorem 2.19; the case that is used is proved here.
-/

noncomputable section

namespace New

open NumberField Function Finset DiscreteModule Fintype commutatorElement

variable {K R : Type} [Field K] [EmbeddedNumberField K] [CommRing R]

/-- A place above a prime of `K`, with a Frobenius element in the open normal subgroup `U` and a
tame generator of inertia modulo `m`. The Frobenius element is arithmetic; passing to its inverse
only changes the sign of each relation. That the prime avoids a given finite set is imposed where
the structure is used. -/
structure SplitPrime (m : ℕ) [NeZero m] (U : OpenNormalSubgroup Gal(Ω/K)) where
  /-- The prime of `K`. -/
  prime : FinPlace K
  /-- The place of `Ω` above it. -/
  place : ClosurePlace
  /-- The place lies above the prime. -/
  isPlaceOver : IsPlaceOver place prime
  /-- The Frobenius element. -/
  frob : Gal(Ω/K)
  /-- `frob` is a Frobenius element at the place. -/
  isFrob : IsFrob place prime.q frob
  /-- `frob` lies in `U`; where inertia above `prime` lies in `U`, this says that `prime` splits in
  its field. -/
  frob_mem : frob ∈ U
  /-- The inertial element. -/
  tameGenerator : Gal(Ω/K)
  /-- `tameGenerator` multiplies an `m`-th root of a uniformiser by the fixed root of unity. -/
  isTameGeneratorFor : IsTameGeneratorFor (K := K) m place tameGenerator

/-- The setting for relations among values of cocycles at split primes: a module `M` killed by `m`
and fixed by complex conjugations, an open normal subgroup `U` (`subgroup`) that fixes `M` and the
`m`-th roots of unity, and local conditions on a finite set `S` (`localPrimes`) of primes outside
which `M` is unramified. In addition `U` contains no complex conjugation. The number `m` need not be
a prime power, `S` need not contain the primes above `m`, and a local condition is a module of
functions, whose cocycles form the group `A_v`. -/
structure RelationSetting (M : DiscreteModule R Gal(Ω/K)) (m : ℕ) [NeZero m] where
  /-- The module is killed by `m`. -/
  nsmul_eq_zero (a : M) : m • a = 0
  /-- The open normal subgroup. -/
  subgroup : OpenNormalSubgroup Gal(Ω/K)
  /-- `U` fixes the module. -/
  apply_eq_of_mem : ∀ g ∈ subgroup, ∀ a : M, M.ρ g a = a
  /-- `U` fixes the `m`-th roots of unity. -/
  cyclotomicCharMod_eq_one : ∀ g ∈ subgroup, cyclotomicCharMod Ω m g = 1
  /-- `U` contains no complex conjugation. -/
  notMem_of_isComplexConj {c : Gal(Ω/K)} : IsComplexConj c → c ∉ subgroup
  /-- Complex conjugations fix the module. -/
  ρ_eq_one_of_isComplexConj {c : Gal(Ω/K)} : IsComplexConj c → M.ρ c = 1
  /-- The finite set of primes with local conditions. -/
  localPrimes : Finset (FinPlace K)
  /-- The module is unramified outside `S`. -/
  unramified : ∀ g ∈ inertiaAbove (localPrimes : Set (FinPlace K))ᶜ, M.ρ g = 1
  /-- A place of `Ω` above each prime. -/
  place : FinPlace K → ClosurePlace
  /-- The place lies above the prime. -/
  isPlaceOver (v : FinPlace K) : IsPlaceOver (place v) v
  /-- The local condition: the functions on the decomposition group that are allowed. -/
  allowed (v : FinPlace K) : Submodule R (decompGroup Gal(Ω/K) (place v) → M)
  /-- Local coboundaries are allowed. -/
  coboundary_le : ∀ v ∈ localPrimes, (coboundaryMap
    (M.restrictTo (decompGroup Gal(Ω/K) (place v))).ρ).range ≤ allowed v

namespace RelationSetting

variable {M : DiscreteModule R Gal(Ω/K)} {m : ℕ} [NeZero m] (D : RelationSetting M m)

/-- The group `Z(P)` of the cocycles that are allowed at each prime of `S`, vanish at complex
conjugations and are unramified outside `S ∪ P`. -/
abbrev cocycles (P : Set (FinPlace K)) : Submodule R (Gal(Ω/K) → M) :=
  selmerZ1 M D.localPrimes D.place D.allowed P

/-- The group `A_v` of the local cocycles that are allowed at `v`. -/
abbrev localCocycles (v : FinPlace K) : Submodule R (decompGroup Gal(Ω/K) (D.place v) → M) :=
  D.allowed v ⊓ Z1 (M.restrictTo (decompGroup Gal(Ω/K) (D.place v))).ρ

/-- A relation off the finite set `T`: a continuous equivariant homomorphism `y` from `U` to
`Hom(M, ℚ/ℤ)`, extended by zero and unramified outside `T`, whose values at Frobenius elements give
a linear relation among the values of cocycles at tame generators. By global duality, the
restriction to `U` of a dual cocycle has these properties if `T` contains `S` and the primes above
`m`. -/
structure IsRelation (T : Finset (FinPlace K)) (y : Gal(Ω/K) → CharacterModule M) : Prop where
  /-- `y` is continuous for the discrete topology. -/
  isLocallyConstant : IsLocallyConstant y
  /-- `y` is extended by zero outside `U`. -/
  eq_zero_of_notMem : ∀ g ∉ D.subgroup, y g = 0
  /-- `y` is a homomorphism on `U`. -/
  map_mul : ∀ a ∈ D.subgroup, ∀ b ∈ D.subgroup, y (a * b) = y a + y b
  /-- `y (g u g⁻¹) = cyc(g) · y u ∘ g⁻¹`. -/
  map_conj (g : Gal(Ω/K)) : ∀ u ∈ D.subgroup, ∀ a : M,
    y (g * u * g⁻¹) a = (cyclotomicCharMod Ω m g : ZMod m).val • y u (M.ρ g⁻¹ a)
  /-- `y` is unramified outside `T`. -/
  unramified : ∀ τ ∈ inertiaAbove (T : Set (FinPlace K))ᶜ, y τ = 0
  /-- Reciprocity at every finite family of distinct split primes outside `T`. -/
  sum_eq_zero {J : Type} [Fintype J] (p : J → SplitPrime m D.subgroup) :
    Injective (fun j : J ↦ (p j).prime) → (∀ j : J, (p j).prime ∉ T) →
    ∀ z ∈ D.cocycles (Set.range fun j : J ↦ (p j).prime),
      ∑ j : J, y (p j).frob (z (p j).tameGenerator) = 0

/-- The module of relations off `T`. It takes the place of the group `Z*` of dual cocycles: only the
restrictions to `U` of dual cocycles are used, and only through the properties in `IsRelation`; the
set `T` may be larger than `S`. -/
def relations (T : Finset (FinPlace K)) : Submodule R (Gal(Ω/K) → CharacterModule M) where
  carrier := {y : Gal(Ω/K) → CharacterModule M.V | D.IsRelation T y}
  zero_mem' :=
    { isLocallyConstant := .const 0
      eq_zero_of_notMem := fun _ _ ↦ rfl
      map_mul := fun _ _ _ _ ↦ (add_zero _).symm
      map_conj := fun _ _ _ _ ↦ (nsmul_zero _).symm
      unramified := fun _ _ ↦ rfl
      sum_eq_zero := fun _ _ _ _ _ ↦ sum_const_zero }
  add_mem' {y y'} hy hy' :=
    { isLocallyConstant := hy.isLocallyConstant.add hy'.isLocallyConstant
      eq_zero_of_notMem := fun g hg ↦ by
        simp [hy.eq_zero_of_notMem g hg, hy'.eq_zero_of_notMem g hg]
      map_mul := fun a ha b hb ↦ by
        simp [hy.map_mul a ha b hb, hy'.map_mul a ha b hb, add_add_add_comm]
      map_conj := fun g u hu a ↦ by
        change y (g * u * g⁻¹) a + y' (g * u * g⁻¹) a =
          (cyclotomicCharMod Ω m g : ZMod m).val • (y u (M.ρ g⁻¹ a) + y' u (M.ρ g⁻¹ a))
        rw [hy.map_conj g u hu, hy'.map_conj g u hu, nsmul_add]
      unramified := fun τ hτ ↦ by simp [hy.unramified τ hτ, hy'.unramified τ hτ]
      sum_eq_zero := fun p hp hT z hz ↦ by
        change ∑ j, (y (p j).frob (z (p j).tameGenerator) + y' (p j).frob (z (p j).tameGenerator)) =
          0
        simp [sum_add_distrib, hy.sum_eq_zero p hp hT z hz, hy'.sum_eq_zero p hp hT z hz] }
  smul_mem' r y hy :=
    { isLocallyConstant := hy.isLocallyConstant.comp (r • ·)
      eq_zero_of_notMem := fun g hg ↦ by simp [hy.eq_zero_of_notMem g hg]
      map_mul := fun a ha b hb ↦ by simp [hy.map_mul a ha b hb]
      map_conj := fun g u hu a ↦ by simp [hy.map_conj g u hu]
      unramified := fun τ hτ ↦ by simp [hy.unramified τ hτ]
      sum_eq_zero := fun p hp hT z hz ↦ by
        simpa using hy.sum_eq_zero p hp hT (r • z) (Submodule.smul_mem _ r hz) }

/-- Membership in `relations T` is the predicate `IsRelation T`. -/
@[simp] lemma mem_relations {T : Finset (FinPlace K)} {y : Gal(Ω/K) → CharacterModule M} :
    y ∈ D.relations T ↔ D.IsRelation T y := Iff.rfl

/-- There are finitely many relations off `T`, by the finiteness of cocycles with bounded
ramification for the group `U`. -/
instance finite_relations [Finite M] (T : Finset (FinPlace K)) : Finite (D.relations T) := by
  have : Finite (CharacterModule M) := inferInstanceAs (Finite (M →+ QZ))
  let _ : TopologicalSpace (CharacterModule M) := ⊥
  have : DiscreteTopology (CharacterModule M) := ⟨rfl⟩
  -- A relation is a cocycle of `U` for the trivial action, unramified outside the primes of the
  -- field `F` of `U` above `T`.
  let F : IntermediateField K Ω := fixedFieldOf D.subgroup.toSubgroup
  let V : DiscreteModule ℤ D.subgroup.toSubgroup :=
    .of (.trivial ℤ D.subgroup.toSubgroup (CharacterModule M))
  have h_above : {w : FinPlace F | w.below K ∈ T}.Finite := by
    simpa [Set.preimage, Set.compl_ofPred, FinPlace.below] using
      tendsto_place_comap_cofinite (algebraMap K F) T.finite_toSet.compl_mem_cofinite
  refine Set.Finite.of_injOn (s := {y | D.IsRelation T y})
    (f := fun (y : Gal(Ω/K) → CharacterModule M) (u : D.subgroup.toSubgroup) ↦ y u)
    (fun y hy ↦ ?_) (fun y hy y' hy' h ↦ funext fun g ↦ ?_)
    (finite_cocycles_unramified_outside V h_above)
  · exact ⟨⟨hy.isLocallyConstant.continuous.comp continuous_subtype_val,
      fun a b ↦ hy.map_mul a a.2 b b.2⟩,
      fun w hw A hA τ hτ ↦ hy.unramified τ ⟨w.below K, hw, A, hA.isPlaceOver_below, hτ⟩⟩
  · by_cases hg : g ∈ D.subgroup
    · exact congrFun h ⟨g, hg⟩
    · rw [hy.eq_zero_of_notMem g hg, hy'.eq_zero_of_notMem g hg]

lemma cocycles_mono : Monotone D.cocycles := fun _ _ hP _ ⟨⟨hz_cocycle, hz_unram⟩, hz_local⟩ ↦
  ⟨⟨hz_cocycle, fun τ ⟨v, hv, hτ⟩ ↦
    hz_unram τ ⟨v, fun h ↦ hv (Set.union_subset_union_right _ hP h), hτ⟩⟩, hz_local⟩

include D in
lemma val_one_nsmul (a : M) : (1 : ZMod m).val • a = a := by
  let : Module (ZMod m) M := AddCommGroup.zmodModule D.nsmul_eq_zero
  simp [← Nat.cast_smul_eq_nsmul (ZMod m)]

section Family

open IsLargeLevel Set

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- Let the primes of `S` divide `q`. A cocycle in `Z(P)` vanishes at a tame generator at the split
prime `s.v i` when `s.v i ∉ P`, since it is unramified there. -/
lemma apply_eq_zero_of_notMem (hS : ∀ v ∈ D.localPrimes, ↑q ∈ v.asIdeal) {I : Set Gal(Ω/K)}
    {J : Type} (s : SplitPlaces m q I D.subgroup J) {i : J} {γ : Gal(Ω/K)}
    (hγ : IsTameGeneratorFor (K := K) m (s.valuationSubring i) γ) {P : Set (FinPlace K)}
    {z : Gal(Ω/K) → M} (hz : z ∈ D.cocycles P) (hi : s.v i ∉ P) : z γ = 0 := by
  obtain ⟨⟨-, hz_unram⟩, -⟩ := hz
  obtain ⟨hγ_inertia, -⟩ := hγ
  have hi_notMem_S : s.v i ∉ D.localPrimes := fun h ↦ s.level_notMem i (hS _ h)
  exact hz_unram γ
    ⟨s.v i, not_or_intro hi_notMem_S hi, s.valuationSubring i, s.isPlaceOver i, hγ_inertia⟩

/-- Let the primes of `S` divide `q`, let the split primes `s` have tame generators `γ n`, and let
`s.φ j * (g * s.φ k * g⁻¹)` act like `s.φ i` on the `m`-th roots of the `q`-units fixed by `U`.
Then some cocycle in `Z(range s.v)` has the values `a`, `-a`, `-cyc(g) g⁻¹ a` at `γ i`, `γ j`,
`γ k` (added where indices coincide) and `0` at the other `γ n`. -/
lemma exists_cocycle_three_values (hS : ∀ v ∈ D.localPrimes, ↑q ∈ v.asIdeal) {I : Set Gal(Ω/K)}
    {J : Type} [Fintype J] [DecidableEq J] (s : SplitPlaces m q I D.subgroup J) {γ : J → Gal(Ω/K)}
    (hγ : ∀ i : J, IsTameGeneratorFor (K := K) m (s.valuationSubring i) (γ i)) {i j k : J}
    {g : Gal(Ω/K)}
    (hφ : ∀ y : DiscreteUnits Ω, m • y ∈ fixedSUnits q D.subgroup →
      unitsRep (s.φ j * (g * s.φ k * g⁻¹)) y = unitsRep (s.φ i) y) (a : M) :
    ∃ z ∈ D.cocycles (range s.v), ∀ n : J, z (γ n) =
      (if n = i then a else 0) - (if n = j then a else 0) -
        if n = k then (cyclotomicCharMod Ω m g : ZMod m).val • M.ρ g⁻¹ a else 0 := by
  let : Module (ZMod m) M := AddCommGroup.zmodModule D.nsmul_eq_zero
  obtain ⟨⟨P₀, z⟩, hP, z_val⟩ := selmerZ1.exists_three_values s hγ D.apply_eq_of_mem
    D.notMem_of_isComplexConj hφ a
  refine ⟨z, selmerZ1.trivialised_mem_selmer D.unramified D.isPlaceOver D.allowed D.coboundary_le
    D.ρ_eq_one_of_isComplexConj s hS hP, fun n ↦ ?_⟩
  simpa [← Nat.cast_smul_eq_nsmul (ZMod m)] using z_val n

/-- Let the primes of `S` divide `q`, let the split primes `s` be indexed by the cosets of `O`, and
let `ν`, a character of `M` for each coset of `O`, kill the values at their tame generators `γ i` of
the cocycles in `Z(range s.v)`. If `s.φ j * (g * s.φ k * g⁻¹)` acts like `s.φ i` on the `m`-th roots
of the `q`-units fixed by `U`, then `ν i = ν j + cyc(g) · (ν k ∘ g⁻¹)`. -/
lemma form_eq_add (hS : ∀ v ∈ D.localPrimes, ↑q ∈ v.asIdeal)
    {O : OpenNormalSubgroup Gal(Ω/K)} [Fintype (Gal(Ω/K) ⧸ O.toSubgroup)]
    {I : Set Gal(Ω/K)} {s : SplitPlaces m q I D.subgroup (Gal(Ω/K) ⧸ O.toSubgroup)}
    {γ : Gal(Ω/K) ⧸ O.toSubgroup → Gal(Ω/K)}
    (hγ : ∀ i : Gal(Ω/K) ⧸ O.toSubgroup, IsTameGeneratorFor (K := K) m (s.valuationSubring i) (γ i))
    {ν : Gal(Ω/K) ⧸ O.toSubgroup → CharacterModule M}
    (hν : ∀ z ∈ D.cocycles (range s.v),
      ∑ i : Gal(Ω/K) ⧸ (O.toOpenSubgroup : Subgroup Gal(Ω/K)), ν i (z (γ i)) = 0)
    {i j k : Gal(Ω/K) ⧸ O.toSubgroup} {g : Gal(Ω/K)}
    (hφ : ∀ y : DiscreteUnits Ω, m • y ∈ fixedSUnits q D.subgroup →
      unitsRep (s.φ j * (g * s.φ k * g⁻¹)) y = unitsRep (s.φ i) y) (a : M) :
    ν i a = ν j a + (cyclotomicCharMod Ω m g : ZMod m).val • ν k (M.ρ g⁻¹ a) := by
  classical
  obtain ⟨z, hz, z_val⟩ := D.exists_cocycle_three_values hS s hγ hφ a
  -- Substitute the values of `z` into `∑ n, ν n (z (γ n)) = 0`.
  simpa [z_val, apply_ite (ν _), sub_eq_iff_eq_add'] using hν z hz

/-- Let the primes of `S` divide `q`, let elements in one coset of `O` act alike on the `m`-th roots
of the `q`-units fixed by `U`, let the split primes `s` be indexed by the cosets of `O`, let the
Frobenius element at the coset of `g ∈ U` lie in that coset, and let `ν` kill the values at the tame
generators `γ i` of the cocycles in `Z(range s.v)`. Then the coefficient of `ν` at the trivial coset
is zero. -/
lemma form_one_eq_zero (hS : ∀ v ∈ D.localPrimes, ↑q ∈ v.asIdeal)
    {O : OpenNormalSubgroup Gal(Ω/K)} [Fintype (Gal(Ω/K) ⧸ O.toSubgroup)]
    (hO : ∀ g h : Gal(Ω/K), (g : Gal(Ω/K) ⧸ O.toSubgroup) = h →
      ∀ y : DiscreteUnits Ω, m • y ∈ fixedSUnits q D.subgroup → unitsRep h y = unitsRep g y)
    {I : Set Gal(Ω/K)} {s : SplitPlaces m q I D.subgroup (Gal(Ω/K) ⧸ O.toSubgroup)}
    (φ_coset : ∀ g ∈ D.subgroup, (s.φ g : Gal(Ω/K) ⧸ O.toSubgroup) = g)
    {γ : Gal(Ω/K) ⧸ O.toSubgroup → Gal(Ω/K)}
    (hγ : ∀ i : Gal(Ω/K) ⧸ O.toSubgroup, IsTameGeneratorFor (K := K) m (s.valuationSubring i) (γ i))
    {ν : Gal(Ω/K) ⧸ O.toSubgroup → CharacterModule M}
    (hν : ∀ z ∈ D.cocycles (range s.v),
      ∑ i : Gal(Ω/K) ⧸ (O.toOpenSubgroup : Subgroup Gal(Ω/K)), ν i (z (γ i)) = 0)
    (a : M) : ν 1 a = 0 := by
  have h_coset : (s.φ 1 : Gal(Ω/K) ⧸ O.toSubgroup) = ↑(s.φ 1 * (1 * s.φ 1 * 1⁻¹)) := by
    simpa using φ_coset 1
  have h_add : ν 1 a = ν 1 a + ν 1 a := by
    simpa [← map_nsmul, D.val_one_nsmul] using D.form_eq_add hS hγ hν (hO _ _ h_coset) a
  exact left_eq_add.1 h_add

/-- Let the primes of `S` divide `q`, let elements in one coset of `O` act alike on the `m`-th roots
of the `q`-units fixed by `U`, let the split primes `s` be indexed by the cosets of `O` with
`s.φ g ∈ g O` for `g ∈ U`, and let `ν` kill the values at the tame generators `γ i` of the cocycles
in `Z(range s.v)`. Then the coefficient of `ν` at the coset of an element `τ` of the inertia group
at a place `A` above a prime `v` that does not divide `q` is zero. -/
lemma form_eq_zero_of_mem_inertiaGroup (hS : ∀ v ∈ D.localPrimes, ↑q ∈ v.asIdeal)
    {O : OpenNormalSubgroup Gal(Ω/K)} [Fintype (Gal(Ω/K) ⧸ O.toSubgroup)]
    (hO : ∀ g h : Gal(Ω/K), (g : Gal(Ω/K) ⧸ O.toSubgroup) = h →
      ∀ y : DiscreteUnits Ω, m • y ∈ fixedSUnits q D.subgroup → unitsRep h y = unitsRep g y)
    {I : Set Gal(Ω/K)} {s : SplitPlaces m q I D.subgroup (Gal(Ω/K) ⧸ O.toSubgroup)}
    (φ_coset : ∀ g ∈ D.subgroup, (s.φ g : Gal(Ω/K) ⧸ O.toSubgroup) = g)
    {γ : Gal(Ω/K) ⧸ O.toSubgroup → Gal(Ω/K)}
    (hγ : ∀ i : Gal(Ω/K) ⧸ O.toSubgroup, IsTameGeneratorFor (K := K) m (s.valuationSubring i) (γ i))
    {ν : Gal(Ω/K) ⧸ O.toSubgroup → CharacterModule M}
    (hν : ∀ z ∈ D.cocycles (range s.v),
      ∑ i : Gal(Ω/K) ⧸ (O.toOpenSubgroup : Subgroup Gal(Ω/K)), ν i (z (γ i)) = 0)
    {v : FinPlace K} (hv : ↑q ∉ v.asIdeal) {A : ClosurePlace} (hA : IsPlaceOver A v)
    {τ : Gal(Ω/K)} (hτ : τ ∈ inertiaGroup Gal(Ω/K) A) (a : M) : ν τ a = 0 := by
  -- `τ` lies in `U` and fixes the `m`-th roots of the `q`-units, as `s.φ 1` does.
  have φ_one : s.φ 1 ∈ O.toSubgroup := by simpa using φ_coset 1
  have hτU : τ ∈ D.subgroup := s.inertiaGroup_le hv hA hτ
  have hm_notMem : ↑m ∉ v.asIdeal := hv ∘ v.asIdeal.mem_of_dvd s.dvd_level.natCast
  have τ_fix (y : DiscreteUnits Ω) (hy : m • y ∈ fixedSUnits q D.subgroup) : unitsRep τ y = y := by
    obtain ⟨hy_units, hy_fixed⟩ := hy
    have hy_fix : τ • ((m • y).toMul : Ω) = (m • y).toMul :=
      congrArg (fun x : DiscreteUnits Ω ↦ (x.toMul : Ω)) (hy_fixed ⟨τ, hτU⟩)
    exact DiscreteUnits.ext <| Cohomology.inertia_fixes_root_of_unit hτ
      (hA.valuation_natCast_eq_one_iff.2 hm_notMem) (by simp)
      (hy_units A (hA.valuation_natCast_eq_one_iff.2 hv)) hy_fix
  have hφ (y : DiscreteUnits Ω) (hy : m • y ∈ fixedSUnits q D.subgroup) :
      unitsRep (s.φ 1 * (1 * s.φ 1 * 1⁻¹)) y = unitsRep (s.φ τ) y := by
    have h_coset : ((s.φ 1 * (1 * s.φ 1 * 1⁻¹) : Gal(Ω/K)) : Gal(Ω/K) ⧸ O.toSubgroup) =
        ↑(1 : Gal(Ω/K)) := by simp [φ_one]
    rw [← hO _ _ (φ_coset τ hτU) y hy, τ_fix y hy, ← hO _ _ h_coset y hy]
    simp
  simpa [D.form_one_eq_zero hS hO φ_coset hγ hν] using D.form_eq_add hS hγ hν hφ a

/-- In the relation setting `D` (with `M` killed by `m`, the subgroup `U`, and local conditions at
the finite set `S`), write `Z(P)` for the cocycles that are allowed at each prime of `S`, vanish at
complex conjugations and are unramified outside `S ∪ P`. Let the primes of `S` divide `q`, let
elements in one coset of `O` act alike on the `m`-th roots of the `q`-units fixed by `U`, let the
split primes `s` be indexed by the cosets of `O` with `s.φ g ∈ g O` for `g ∈ U`, and let `ν` kill
the values at the tame generators `γ i` of the cocycles in `Z(range s.v)`. Then for any family `p`
of distinct split primes, prime to `q` and different from those of `s`, and any cocycle `x` in `Z`
of the primes of `p`, we have `∑ j, ν (p j).frob (x (p j).tameGenerator) = 0` (`ν` taken at the
coset of `(p j).frob` modulo `O`). -/
lemma form_sum_eq_zero (hS : ∀ v ∈ D.localPrimes, ↑q ∈ v.asIdeal)
    {O : OpenNormalSubgroup Gal(Ω/K)} [Fintype (Gal(Ω/K) ⧸ O.toSubgroup)]
    (hO : ∀ g h : Gal(Ω/K), (g : Gal(Ω/K) ⧸ O.toSubgroup) = h →
      ∀ y : DiscreteUnits Ω, m • y ∈ fixedSUnits q D.subgroup → unitsRep h y = unitsRep g y)
    {I : Set Gal(Ω/K)} {s : SplitPlaces m q I D.subgroup (Gal(Ω/K) ⧸ O.toSubgroup)}
    (φ_coset : ∀ g ∈ D.subgroup, (s.φ g : Gal(Ω/K) ⧸ O.toSubgroup) = g)
    {γ : Gal(Ω/K) ⧸ O.toSubgroup → Gal(Ω/K)}
    (hγ : ∀ i : Gal(Ω/K) ⧸ O.toSubgroup, IsTameGeneratorFor (K := K) m (s.valuationSubring i) (γ i))
    {ν : Gal(Ω/K) ⧸ O.toSubgroup → CharacterModule M}
    (hν : ∀ z ∈ D.cocycles (range s.v),
      ∑ i : Gal(Ω/K) ⧸ (O.toOpenSubgroup : Subgroup Gal(Ω/K)), ν i (z (γ i)) = 0)
    {J : Type} [Fintype J] (p : J → SplitPrime m D.subgroup)
    (p_inj : Injective fun j : J ↦ (p j).prime) (p_notMem : ∀ j : J, ↑q ∉ (p j).prime.asIdeal)
    (p_ne : ∀ (i : Gal(Ω/K) ⧸ O.toSubgroup) (j : J), s.v i ≠ (p j).prime) {x : Gal(Ω/K) → M}
    (hx : x ∈ D.cocycles (range fun j : J ↦ (p j).prime)) : ∑ j : J,
      ν (p j).frob (x (p j).tameGenerator) = 0 := by
  classical
  -- Join the primes `p j` to the family `s` and move the ramification of `x` from `p j` to the
  -- primes of `s` at the coset of its Frobenius element and at `1`, where `ν` is zero.
  have φ_one : s.φ 1 ∈ O.toSubgroup := by simpa using φ_coset 1
  let s' : SplitPlaces m q _ D.subgroup ((Gal(Ω/K) ⧸ O.toSubgroup) ⊕ J) :=
    { s with
      v := Sum.elim s.v fun j ↦ (p j).prime
      v_injective := s.v_injective.sumElim p_inj p_ne
      level_notMem := Sum.forall.2 ⟨s.level_notMem, p_notMem⟩
      valuationSubring := Sum.elim s.valuationSubring fun j ↦ (p j).place
      isPlaceOver := Sum.forall.2 ⟨s.isPlaceOver, fun j ↦ (p j).isPlaceOver⟩
      φ := Sum.elim s.φ fun j ↦ (p j).frob
      isFrob := Sum.forall.2 ⟨s.isFrob, fun j ↦ ⟨(p j).isFrob, (p j).frob_mem⟩⟩
      mem_inertia_iff _ := Iff.rfl }
  have hγ' : ∀ n : (Gal(Ω/K) ⧸ O.toSubgroup) ⊕ J,
      IsTameGeneratorFor (K := K) m (s'.valuationSubring n)
        (Sum.elim γ (fun j ↦ (p j).tameGenerator) n) :=
    Sum.forall.2 ⟨hγ, fun j ↦ (p j).isTameGeneratorFor⟩
  have move (j : J) : ∃ z ∈ D.cocycles (range s'.v),
      (∀ b : J, z (p b).tameGenerator = if b = j then x (p j).tameGenerator else 0) ∧
        ∑ i, ν i (z (γ i)) = -ν (p j).frob (x (p j).tameGenerator) := by
    have h_coset : (s'.φ (.inr j) : Gal(Ω/K) ⧸ O.toSubgroup) =
        ↑(s'.φ (.inl (p j).frob) * (1 * s'.φ (.inl 1) * 1⁻¹)) := by
      simp [s', φ_coset, (p j).frob_mem, φ_one]
    obtain ⟨z, hz, z_val⟩ := D.exists_cocycle_three_values hS s' hγ' (hO _ _ h_coset)
      (x (p j).tameGenerator)
    have z_γ (i : Gal(Ω/K) ⧸ O.toSubgroup) : z (γ i) =
        -(if i = (p j).frob then x (p j).tameGenerator else 0) -
          if i = 1 then (1 : ZMod m).val • x (p j).tameGenerator else 0 := by
      simpa using z_val (.inl i)
    exact ⟨z, hz, fun b ↦ by simpa using z_val (.inr b),
      by simp [z_γ, apply_ite (ν _), D.form_one_eq_zero hS hO φ_coset hγ hν]⟩
  choose z z_mem z_at_p ν_sum_z using move
  -- `x - ∑ j, z j` vanishes at the tame generators of the `p j`, so it is unramified there.
  have diff_mem : x - ∑ j, z j ∈ D.cocycles (range s.v) := by
    obtain ⟨⟨cocycle, unram⟩, rest⟩ : x - ∑ j, z j ∈ D.cocycles (range s'.v) :=
      sub_mem (D.cocycles_mono (by simp [s']) hx) (sum_mem fun j _ ↦ z_mem j)
    refine ⟨⟨cocycle, fun τ ⟨w, hw, B, hB, hτ⟩ ↦ ?_⟩, rest⟩
    by_cases hwp : w ∈ range fun j ↦ (p j).prime
    · obtain ⟨j, hj⟩ := hwp
      let : Module (ZMod m) M := AddCommGroup.zmodModule D.nsmul_eq_zero
      exact s'.apply_inertia_eq_zero (V := M) hB (i := .inr j) hj (p j).isTameGeneratorFor
        ⟨x - ∑ b, z b, cocycle⟩ D.apply_eq_of_mem (by simp [z_at_p]) hτ
    · exact unram τ ⟨w, by simpa [s', hwp] using hw, B, hB, hτ⟩
  have x_γ (i : Gal(Ω/K) ⧸ O.toSubgroup) : x (γ i) = 0 :=
    D.apply_eq_zero_of_notMem hS s (hγ i) hx fun ⟨j, hj⟩ ↦ p_ne i j hj.symm
  calc ∑ j, ν (p j).frob (x (p j).tameGenerator) = -∑ j, ∑ i, ν i (z j (γ i)) := by simp [ν_sum_z]
    _ = ∑ i, ν i ((x - ∑ j, z j) (γ i)) := by
      rw [sum_comm]
      simp [x_γ]
    _ = 0 := hν _ diff_mem

/-- Let the primes of `S` (of `D`) divide `q`, let elements in one coset of `O` act alike on the
`m`-th roots of the `q`-units fixed by `U`, and let the split primes `s` be indexed by the cosets of
`O` with `s.φ g ∈ g O` for `g ∈ U`. Let `ν` kill the values at the tame generators `γ i` of the
cocycles in `Z(range s.v)`, which are allowed on `S`, zero at complex conjugations, and unramified
off `S` and the `s.v i`. Then `g ↦ ν (g O)` on `U`, zero off `U`, is a relation off any finite `T`
containing the primes dividing `q` and those of `s`: a continuous equivariant map to `Hom(M, ℚ/ℤ)`,
unramified off `T`, whose Frobenius values give linear relations among cocycle values at tame
generators. -/
lemma isRelation_ite_form (hS : ∀ v ∈ D.localPrimes, ↑q ∈ v.asIdeal)
    {O : OpenNormalSubgroup Gal(Ω/K)} [Fintype (Gal(Ω/K) ⧸ O.toSubgroup)]
    (hO : ∀ g h : Gal(Ω/K), (g : Gal(Ω/K) ⧸ O.toSubgroup) = h →
      ∀ y : DiscreteUnits Ω, m • y ∈ fixedSUnits q D.subgroup → unitsRep h y = unitsRep g y)
    {I : Set Gal(Ω/K)} {s : SplitPlaces m q I D.subgroup (Gal(Ω/K) ⧸ O.toSubgroup)}
    (φ_coset : ∀ g ∈ D.subgroup, (s.φ g : Gal(Ω/K) ⧸ O.toSubgroup) = g)
    {γ : Gal(Ω/K) ⧸ O.toSubgroup → Gal(Ω/K)}
    (hγ : ∀ i : Gal(Ω/K) ⧸ O.toSubgroup, IsTameGeneratorFor (K := K) m (s.valuationSubring i) (γ i))
    {ν : Gal(Ω/K) ⧸ O.toSubgroup → CharacterModule M}
    (hν : ∀ z ∈ D.cocycles (range s.v),
      ∑ i : Gal(Ω/K) ⧸ (O.toOpenSubgroup : Subgroup Gal(Ω/K)), ν i (z (γ i)) = 0)
    [DecidablePred (· ∈ D.subgroup)] {T : Finset (FinPlace K)}
    (hqT : ∀ v : FinPlace K, ↑q ∈ v.asIdeal → v ∈ T)
    (hsT : ∀ i : Gal(Ω/K) ⧸ O.toSubgroup, s.v i ∈ T) :
    D.IsRelation T fun g : Gal(Ω/K) ↦ if g ∈ D.subgroup then ν g else 0 := by
  have ν_conj (g : Gal(Ω/K)) {a b : Gal(Ω/K)} (ha : a ∈ D.subgroup) (hb : b ∈ D.subgroup) (x : M) :
      ν ↑(a * (g * b * g⁻¹)) x = ν a x + (cyclotomicCharMod Ω m g : ZMod m).val • ν b
        (M.ρ g⁻¹ x) := by
    refine D.form_eq_add hS hγ hν (hO _ _ ?_) x
    rw [φ_coset _ (mul_mem ha (D.subgroup.isNormal'.conj_mem b hb g))]
    simp [φ_coset, ha, hb]
  refine
    { isLocallyConstant := ?_
      eq_zero_of_notMem := fun g hg ↦ ite_eq_right hg
      map_mul := fun a ha b hb ↦ ?_
      map_conj := fun g u hu a ↦ ?_
      unramified := fun τ ⟨v, hv, A, hA, hτ⟩ ↦ ?_
      sum_eq_zero := fun p p_inj hp x hx ↦ ?_ }
  · -- The function depends only on the cosets of `g` modulo `U` and `O`.
    let f (c : (Gal(Ω/K) ⧸ D.subgroup.toSubgroup) × (Gal(Ω/K) ⧸ O.toSubgroup)) :
      CharacterModule M :=
      if c.1 = 1 then ν c.2 else 0
    have h_eq (g : Gal(Ω/K)) : (if g ∈ D.subgroup then ν g else 0) = f (g, g) :=
      if_congr (QuotientGroup.eq_one_iff g).symm rfl rfl
    rw [funext h_eq]
    exact .comp ((IsLocallyConstant.iff_continuous _).2 (by fun_prop)) f
  · ext x
    simp only [ha, hb, mul_mem ha hb, ite_true]
    change ν ↑(a * b) x = ν a x + ν b x
    simpa [← map_nsmul, D.val_one_nsmul] using ν_conj 1 ha hb x
  · have h_conj : g * u * g⁻¹ ∈ D.subgroup := D.subgroup.isNormal'.conj_mem u hu g
    simpa [hu, h_conj, D.form_one_eq_zero hS hO φ_coset hγ hν] using ν_conj g D.subgroup.one_mem hu
      a
  · have ν_τ : ν τ = 0 :=
      DFunLike.ext _ _ (D.form_eq_zero_of_mem_inertiaGroup hS hO φ_coset hγ hν
        (fun h ↦ hv (hqT v h)) hA hτ)
    simp [ν_τ]
  · simp only [(p _).frob_mem, ite_true]
    exact D.form_sum_eq_zero hS hO φ_coset hγ hν p p_inj (fun j h ↦ hp j (hqT _ h))
      (fun i j h ↦ hp j (by simpa [← h] using hsT i)) hx

/-- Let the primes of `S` divide `q`, let elements in one coset of `O` act alike on the `m`-th roots
of the `q`-units fixed by `U`, let the split primes `s` be indexed by the cosets of `O` with
`s.φ g ∈ g O` for `g ∈ U`, and let `ν` kill the values at the tame generators `γ i` of the cocycles
in `Z(range s.v)`. Then the coefficient of `ν` at the coset of the Frobenius element `s.φ i` is the
coefficient at `i`. -/
lemma form_frobenius_eq (hS : ∀ v ∈ D.localPrimes, ↑q ∈ v.asIdeal)
    {O : OpenNormalSubgroup Gal(Ω/K)} [Fintype (Gal(Ω/K) ⧸ O.toSubgroup)]
    (hO : ∀ g h : Gal(Ω/K), (g : Gal(Ω/K) ⧸ O.toSubgroup) = h →
      ∀ y : DiscreteUnits Ω, m • y ∈ fixedSUnits q D.subgroup → unitsRep h y = unitsRep g y)
    {I : Set Gal(Ω/K)} {s : SplitPlaces m q I D.subgroup (Gal(Ω/K) ⧸ O.toSubgroup)}
    (φ_coset : ∀ g ∈ D.subgroup, (s.φ g : Gal(Ω/K) ⧸ O.toSubgroup) = g)
    {γ : Gal(Ω/K) ⧸ O.toSubgroup → Gal(Ω/K)}
    (hγ : ∀ i : Gal(Ω/K) ⧸ O.toSubgroup, IsTameGeneratorFor (K := K) m (s.valuationSubring i) (γ i))
    {ν : Gal(Ω/K) ⧸ O.toSubgroup → CharacterModule M}
    (hν : ∀ z ∈ D.cocycles (range s.v),
      ∑ i : Gal(Ω/K) ⧸ (O.toOpenSubgroup : Subgroup Gal(Ω/K)), ν i (z (γ i)) = 0)
    (i : Gal(Ω/K) ⧸ O.toSubgroup) : ν (s.φ i) = ν i := by
  -- Compare the coefficients at `i`, at the coset of `s.φ i` and at `1`.
  have φ_one : s.φ 1 ∈ O.toSubgroup := by simpa using φ_coset 1
  obtain ⟨-, hi_mem⟩ := s.isFrob i
  have hi : (s.φ i : Gal(Ω/K) ⧸ O.toSubgroup) = ↑(s.φ (s.φ i) * (1 * s.φ 1 * 1⁻¹)) := by
    simp [φ_coset, hi_mem, φ_one]
  ext a
  simp [D.form_eq_add hS hγ hν (hO _ _ hi), D.form_one_eq_zero hS hO φ_coset hγ hν]

end Family

/-- The natural number `p` can be avoided: it is prime to `m`, no prime of `S` divides it, and the
primes dividing it are unramified in the field of `U`. -/
structure Avoids (p : ℕ) : Prop where
  /-- `p` is prime to the modulus. -/
  coprime : m.Coprime p
  /-- No prime of `S` divides `p`. -/
  notMem : ∀ v ∈ D.localPrimes, ↑p ∉ v.asIdeal
  /-- The primes dividing `p` are unramified in the field of `U`. -/
  inertiaGroup_le (v : FinPlace K) (hv : ↑p ∈ v.asIdeal) (B : ClosurePlace)
    (hB : IsPlaceOver B v) : inertiaGroup Gal(Ω/K) B ≤ D.subgroup

lemma avoids_one : D.Avoids 1 :=
  have h_one (v : FinPlace K) : ((1 : ℕ) : 𝓞 K) ∉ v.asIdeal := by
    simpa using (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top
  ⟨m.coprime_one_right, fun v _ ↦ h_one v, fun v hv ↦ absurd hv (h_one v)⟩

open IsLargeLevel in
/-- One family of split primes gives relations at all split primes. Let `p` be a natural number
that can be avoided. There are a level `q`, a finite family `s` of split primes with Frobenius
elements `s.φ i` and tame generators `γ i`, and a finite set `T ⊇ S` of primes not dividing `p`,
such that every linear form `ν` that kills the values at the `γ i` of the cocycles in
`Z(range s.v)` consists of the values of a relation off `T` at the `s.φ i`. Moreover the primes of
`S` divide `q`, and an `m`-th root of a `q`-unit of the field of `U` that all `s.φ i` fix is fixed
by `U`. The set `I` is the union of the inertia groups above the primes that are prime to `q` and
not in the family. The proof rests on Artin's reciprocity law for Kummer characters of units, in
place of the reciprocity law for local pairings. -/
theorem exists_splitPlaces_forall_exists_mem_relations {p : ℕ} [NeZero p] (hp : D.Avoids p) :
    ∃ (q : ℕ) (_ : NeZero q) (ι : Type) (_ : Fintype ι) (I : Set Gal(Ω/K))
      (s : SplitPlaces m q I D.subgroup ι) (γ : ι → Gal(Ω/K)) (T : Finset (FinPlace K)),
      -- (a) the primes of `S` divide `q`
      (∀ v ∈ D.localPrimes, ↑q ∈ v.asIdeal) ∧
      -- (b) `T` contains `S`
      D.localPrimes ⊆ T ∧
      -- (c) no prime of `T` divides `p`
      (∀ v ∈ T, ↑p ∉ v.asIdeal) ∧
      -- (d) `U` fixes the `m`-th roots of `q`-units of its field that all `s.φ i` fix
      s.FrobeniiDetectRoots ∧
      -- (e) `γ i` is a tame generator of inertia at the `i`-th prime
      (∀ i : ι, IsTameGeneratorFor (K := K) m (s.valuationSubring i) (γ i)) ∧
      -- (f) a form that kills the values of the cocycles at the `γ i` comes from a relation off `T`
      ∀ ν : ι → CharacterModule M,
        (∀ z ∈ D.cocycles (Set.range s.v), ∑ i : ι, ν i (z (γ i)) = 0) →
        ∃ y ∈ D.relations T, ∀ i : ι, y (s.φ i) = ν i := by
  classical
  -- Take `q` large, `O` open normal fixing the `m`-th roots of the `q`-units fixed by `U`, and one
  -- split prime for each coset of `O`, with Frobenius element in that coset if it meets `U`.
  obtain ⟨q, hq, hqp, hS, exists_spl⟩ := selmerZ1.exists_splitPlaces_frob_mem_coset
    D.cyclotomicCharMod_eq_one D.localPrimes
    hp.coprime hp.notMem hp.inertiaGroup_le
  obtain ⟨O, hO⟩ : ∃ O : OpenNormalSubgroup Gal(Ω/K),
      ∀ g h : Gal(Ω/K), (g : Gal(Ω/K) ⧸ O.toSubgroup) = h →
        ∀ y : DiscreteUnits Ω, m • y ∈ fixedSUnits q D.subgroup → unitsRep h y = unitsRep g y :=
    selmerZ1.exists_fix_roots_of_units D.subgroup q
  let : Fintype (Gal(Ω/K) ⧸ O.toSubgroup) := ofFinite _
  obtain ⟨I, s, hsp, φ_coset⟩ : ∃ (I : Set Gal(Ω/K))
      (s : SplitPlaces m q I D.subgroup (Gal(Ω/K) ⧸ O.toSubgroup)),
      (∀ i : Gal(Ω/K) ⧸ O.toSubgroup, ↑p ∉ (s.v i).asIdeal) ∧
      ∀ g ∈ D.subgroup, (s.φ g : Gal(Ω/K) ⧸ O.toSubgroup) = g := exists_spl O
  have exists_tame (i : Gal(Ω/K) ⧸ O.toSubgroup) :
      ∃ γ : Gal(Ω/K), IsTameGeneratorFor (K := K) m (s.valuationSubring i) γ :=
    exists_isTameGeneratorFor Gal(Ω/K) m (s.isPlaceOver i)
  choose γ hγ using exists_tame
  -- `T` consists of the primes dividing `q` and the primes of the family.
  let T : Finset (FinPlace K) :=
    ((finite_natCast_mem (K := K) q).union (Set.finite_range s.v)).toFinset
  have hqT (v : FinPlace K) (hv : ↑q ∈ v.asIdeal) : v ∈ T := by simp [T, hv]
  have hsT (i : Gal(Ω/K) ⧸ O.toSubgroup) : s.v i ∈ T := by simp [T]
  have hTp (v : FinPlace K) (hv : v ∈ T) : ↑p ∉ v.asIdeal := by
    obtain hqv | ⟨i, rfl⟩ : ↑q ∈ v.asIdeal ∨ v ∈ Set.range s.v := by simpa [T] using hv
    · exact natCast_notMem_of_coprime hqp hqv
    · exact hsp i
  have h_detect : s.FrobeniiDetectRoots := fun y hy h_fix g hg ↦ by
    -- `g ∈ U` acts on `y` as the Frobenius element in its coset.
    rw [hO _ _ (φ_coset g hg) y hy, h_fix]
  refine ⟨q, hq, _, inferInstance, I, s, γ, T, hS, fun v hv ↦ hqT v (hS v hv), hTp, h_detect, hγ,
    fun ν hν ↦ ?_⟩
  -- The relation is `g ↦ ν (g O)` on `U`; its value at each Frobenius element is the one of `ν`.
  refine ⟨_, D.isRelation_ite_form hS hO φ_coset hγ hν hqT hsT, fun i ↦ ?_⟩
  obtain ⟨-, hi_mem⟩ := s.isFrob i
  simp only [ite_eq_left hi_mem, D.form_frobenius_eq hS hO φ_coset hγ hν i]

/-- A case of the formula of Greenberg and Wiles (Darmon–Diamond–Taylor, Theorem 2.19), giving only
a lower bound. Let `K` be totally complex, `M` finite and killed by `ℓ ^ r` with `r ≠ 0`, and let
`σ` fix the `ℓ`-power roots of unity, be central modulo `U` and fix no nonzero element of `M`. If
`p` can be avoided, there is a finite set `T ⊇ S` of primes not dividing `p` with `#Z(∅) · #M ^
(#S + r₂) ≤ #(relations off T) · #M · ∏_{v ∈ S} #A_v`, where `A_v` (`localCocycles v`) is the group
of allowed local cocycles at `v` and `r₂` is the number of infinite places. The factor `#M` comes
from the `#M` coboundaries, which are the dual cocycles vanishing on `U`. -/
theorem exists_card_cocycles_le {ℓ r : ℕ} [Fact ℓ.Prime] [IsTotallyComplex K] [Finite M]
    (D : RelationSetting M (ℓ ^ r)) (hr : r ≠ 0) {σ : Gal(Ω/K)} (hσ_cyc : cyclotomicChar Ω ℓ σ = 1)
    (hσ_comm : ∀ g : Gal(Ω/K), ⁅σ, g⁆ ∈ D.subgroup) (hσ_fix : ∀ a : M, M.ρ σ a = a → a = 0)
    {p : ℕ} [NeZero p] (hp : D.Avoids p) :
    ∃ T : Finset (FinPlace K), D.localPrimes ⊆ T ∧ (∀ v ∈ T, ↑p ∉ v.asIdeal) ∧
      Nat.card (D.cocycles ∅) * Nat.card M ^ (#D.localPrimes + card (InfinitePlace K)) ≤
        Nat.card (D.relations T) * Nat.card M * ∏ v ∈ D.localPrimes,
          Nat.card (D.localCocycles v) := by
  obtain ⟨q, _, ι, _, I, s, γ, T, hS, hST, hTp, h_detect, hγ, h_forms⟩ :=
    D.exists_splitPlaces_forall_exists_mem_relations hp
  refine ⟨T, hST, hTp, ?_⟩
  -- There are few trivialised cocycles, hence many forms that kill the values at the `γ i`.
  have h_inj : Injective ⇑(M.ρ σ - ((1 : ℕ) : Module.End R M)) :=
    (injective_iff_map_eq_zero _).2 fun a ha ↦ hσ_fix a (by simpa [sub_eq_zero] using ha)
  have h_few : M.HasFewCocycles (PlaceAboveLevel q) I (card ι + 1) :=
    s.hasFewCocycles_of_central hr ⟨inferInstance, D.nsmul_eq_zero, D.apply_eq_of_mem, h_inj⟩
      hσ_cyc hσ_comm h_detect
  let F : Set (ι → M →+ QZ) := {ν | ∀ z ∈ D.cocycles (Set.range s.v), ∑ i, ν i (z (γ i)) = 0}
  have h_count : Nat.card (D.cocycles ∅) * Nat.card M ^ (#D.localPrimes + card (InfinitePlace K)) ≤
      Nat.card F * Nat.card M * ∏ v ∈ D.localPrimes, Nat.card (D.localCocycles v) :=
    selmerZ1.card_relations_ge D.unramified D.isPlaceOver D.allowed D.coboundary_le
      D.ρ_eq_one_of_isComplexConj s γ hS h_few (D.cocycles_mono (Set.empty_subset _))
      fun z hz i ↦ D.apply_eq_zero_of_notMem hS s (hγ i) hz (Set.notMem_empty _)
  -- Every form is the restriction of a relation to the Frobenius elements.
  have h_le : Nat.card F ≤ Nat.card (D.relations T) := by
    choose y hy y_val using fun ν : F ↦ h_forms ν.1 ν.2
    refine Nat.card_le_card_of_injective (fun ν : F ↦ ⟨y ν, hy ν⟩) fun ν ν' h ↦
      Subtype.ext (funext fun i ↦ ?_)
    rw [← y_val ν i, ← y_val ν' i, Subtype.mk.inj h]
  exact h_count.trans (by gcongr)

end RelationSetting

end New

end
