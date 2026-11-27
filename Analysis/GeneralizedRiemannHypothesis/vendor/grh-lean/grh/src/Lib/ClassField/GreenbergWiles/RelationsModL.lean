import Lib.ClassField.GreenbergWiles.Relations

/-!
# Relations modulo ℓ

A lower bound for the number of reductions modulo `ℓ` of the relations off a finite set `T` of
primes, for a module whose submodule of points killed by `ℓ` has order `ℓ`. Here the forms on the
points killed by `ℓ` are lifted to relations, and the cocycles killed by `ℓ` are bounded by the
count for `M[ℓ]`.

* `New.RelationSetting.reductions`: the reductions modulo `ℓ` of the relations off `T`.
* `New.RelationSetting.exists_pow_le_card_reductions`: the lower bound for their number.

Notions from other files:
* `New.RelationSetting`: a module `M` over `Gal(Ω/K)`, where `Ω` is the fixed algebraic closure in
  which the number field `K` is embedded (`EmbeddedNumberField K`), unramified outside a finite set
  `S` of primes and with trivial complex conjugations, with a chosen place `D.place v` above each
  prime `v`, with local conditions at `S` on its decomposition group that contain the coboundaries,
  and an open normal subgroup `U` that fixes `M` and the `m`-th roots of unity;
* `New.RelationSetting.cocycles`: the cocycles that satisfy the local conditions, vanish at complex
  conjugations and are unramified outside `S` and a given set of primes;
* `New.RelationSetting.relations`: the functions, supported on `U`, with values in the characters of
  `M`, that have the properties of restrictions of dual cocycles; those off `T` satisfy the
  reciprocity law with the cocycles ramified at finitely many split primes outside `T`;
* `New.IsLargeLevel.SplitPlaces`: a family of primes prime to the level that split in the field of
  an open normal subgroup, with places above them and Frobenius elements.

## Relation to the literature

Known; see `Lib.ClassField.GreenbergWiles.CocycleCounts` for sources.
-/

noncomputable section

namespace New

open NumberField Function Finset DiscreteModule Fintype Subgroup IsLargeLevel

/-- The image of a finite abelian group has no more points killed by `ℓ` than the group. -/
lemma card_torsionBy_le_of_surjective {Y B : Type} [AddCommGroup Y] [AddCommGroup B] [Finite Y]
    (ℓ : ℕ) {p : Y →+ B} (hp : Surjective p) :
    Nat.card (Submodule.torsionBy ℕ B ℓ) ≤ Nat.card (Submodule.torsionBy ℕ Y ℓ) := by
  have : Finite B := .of_surjective p hp
  let mulY : Y →+ Y := ℓ • .id Y
  let mulB : B →+ B := ℓ • .id B
  have h_map : mulY.range.map p = mulB.range := by
    ext b
    simp [mulY, mulB, hp.exists]
  calc Nat.card mulB.ker = mulB.range.index := AddSubgroup.index_range.symm
    _ ≤ mulY.range.index := Nat.le_of_dvd (Nat.pos_of_ne_zero AddSubgroup.index_ne_zero_of_finite)
      (by simpa only [h_map] using mulY.range.index_map_dvd hp)
    _ = Nat.card mulY.ker := AddSubgroup.index_range

namespace RelationSetting

variable {K R : Type} [Field K] [EmbeddedNumberField K] [CommRing R]
  {M : DiscreteModule R Gal(Ω/K)} {m : ℕ} [NeZero m] (D : RelationSetting M m)

/-- The reductions modulo `ℓ` of the relations off `T`, with values in `M* / ℓ M*`. -/
def reductions (ℓ : ℕ) (T : Finset (FinPlace K)) :
    Submodule R (Gal(Ω/K) → QuotSMulTop (ℓ : R) (CharacterModule M)) :=
  (D.relations T).map ((Submodule.mkQ _).compLeft Gal(Ω/K))

/-- If `M` is finite, then `D.reductions ℓ T` is finite, as the image of the finite set
`D.relations T`. -/
instance finite_reductions [Finite M] (ℓ : ℕ) (T : Finset (FinPlace K)) :
    Finite (D.reductions ℓ T) :=
  Set.Finite.image _ (D.finite_relations T)

/-- Two characters of `M` that are congruent modulo `ℓ` agree on the points killed by `ℓ`. -/
lemma apply_eq_of_mkQ_eq {ℓ : ℕ} {χ χ' : CharacterModule M}
    (h_mk : (Submodule.Quotient.mk χ : QuotSMulTop (ℓ : R) (CharacterModule M)) =
      Submodule.Quotient.mk χ') {a : M} (ha : ℓ • a = 0) : χ a = χ' a := by
  -- The difference `χ - χ'` lies in `ℓ • M*`, so it is `ℓ • η` for some character `η`.
  obtain ⟨η, -, hη⟩ :=
    (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 ((Submodule.Quotient.eq _).1 h_mk)
  have h_val : η ((ℓ : R) • a) = χ a - χ' a := DFunLike.congr_fun hη a
  rwa [Nat.cast_smul_eq_nsmul, ha, map_zero, eq_comm, sub_eq_zero] at h_val

/-- In the relation setting `D` with `M` finite, let `P` be a finite set of finite places, and let
`γ` and `φ` be families of Galois elements indexed by `ι`. Let `D.cocycles P` be the cocycles
allowed at `S`, vanishing at complex conjugations and unramified outside `S ∪ P`. Suppose every
family `ν` of characters of `M` that kills the families `i ↦ z (γ i)` for all `z` in `D.cocycles P`
is the family of values at the `φ i` of a relation off `T` (an element of `D.relations T`). Then
`#M[ℓ] ^ #ι` is at most the number of reductions modulo `ℓ` of the relations off `T` (with values in
`M* / ℓ M*`), times the number of cocycles in `D.cocycles P` killed by `ℓ`. -/
lemma pow_le_card_reductions_mul [Finite M] (ℓ : ℕ) {ι : Type} [Fintype ι]
    {φ γ : ι → Gal(Ω/K)} {P : Set (FinPlace K)} (hP : P.Finite) {T : Finset (FinPlace K)}
    (h_forms : ∀ ν : ι → CharacterModule M, (∀ z ∈ D.cocycles P, ∑ i : ι, ν i (z (γ i)) = 0) →
      ∃ y ∈ D.relations T, ∀ i : ι, y (φ i) = ν i) :
    Nat.card {a : M // ℓ • a = 0} ^ card ι ≤
      Nat.card (D.reductions ℓ T) * Nat.card (Submodule.torsionBy ℕ (D.cocycles P) ℓ) := by
  classical
  -- Let `B ⊆ M ^ ι` be the group of the families of values at the `γ i`. A character of `M[ℓ] ^ ι`
  -- that kills `B[ℓ]` extends to a character of `M ^ ι` that kills `B`, so it comes from a
  -- relation, whose reduction determines it.
  have : Finite (D.cocycles P) :=
    (selmerZ1.finite_unramified_cocycles M (D.localPrimes.finite_toSet.union hP)).subset inf_le_left
  let values : D.cocycles P →+ ι → M := .mk' (fun z i ↦ z.1 (γ i)) fun _ _ ↦ rfl
  -- `X = M[ℓ] ^ ι` maps by `f` to `M ^ ι / B`, with kernel `B[ℓ]`.
  let X : AddSubgroup (ι → M) := (ℓ • AddMonoidHom.id (ι → M)).ker
  let f : X →+ (ι → M) ⧸ values.range := (QuotientAddGroup.mk' _).comp X.subtype
  have h_rel (χ : X ⧸ f.ker →+ QZ) : ∃ y ∈ D.relations T, ∀ x : X, ∑ i, y (φ i) (x.1 i) = χ x := by
    obtain ⟨η, hη⟩ : ∃ η : (ι → M) ⧸ values.range →+ QZ, ∀ x : X, η (f x) = χ x :=
      QZ.exists_extend f (χ.comp (QuotientAddGroup.mk' _)) fun x hx ↦ by
        simp [(QuotientAddGroup.eq_zero_iff x).2 hx]
    let ν (i : ι) : M →+ QZ := η.comp ((QuotientAddGroup.mk' _).comp (.single (fun _ ↦ M) i))
    have ν_sum (x : ι → M) : ∑ i, ν i (x i) = η x := by
      conv_rhs => rw [← univ_sum_single x]
      simp [ν]
    have ν_kills (z : Gal(Ω/K) → M) (hz : z ∈ D.cocycles P) : ∑ i, ν i (z (γ i)) = 0 := by
      have h_mem : (fun i ↦ z (γ i)) ∈ values.range := ⟨⟨z, hz⟩, rfl⟩
      rw [ν_sum, (QuotientAddGroup.eq_zero_iff _).2 h_mem]
      exact map_zero η
    obtain ⟨y, hy, y_val⟩ := h_forms ν ν_kills
    refine ⟨y, hy, fun x ↦ ?_⟩
    simp only [y_val]
    exact (ν_sum x).trans (hη x)
  choose y hy y_sum using h_rel
  have h_chars : Nat.card (X ⧸ f.ker →+ QZ) ≤ Nat.card (D.reductions ℓ T) := by
    -- The map from `χ` to the reduction of `y χ` is injective.
    refine Nat.card_le_card_of_injective
      (fun χ ↦ ⟨_, Submodule.mem_map_of_mem (hy χ)⟩) fun χ χ' h ↦ ?_
    ext x
    have h_mk (g : Gal(Ω/K)) : (Submodule.Quotient.mk (y χ g) :
        QuotSMulTop (ℓ : R) (CharacterModule M)) = Submodule.Quotient.mk (y χ' g) :=
      congrFun (Subtype.ext_iff.1 h) g
    have h_sum : ∑ i, y χ (φ i) (x.1 i) = ∑ i, y χ' (φ i) (x.1 i) :=
      sum_congr rfl fun i _ ↦ apply_eq_of_mkQ_eq (h_mk (φ i)) (congrFun x.2 i)
    exact (y_sum χ x).symm.trans (h_sum.trans (y_sum χ' x))
  have h_ker : Nat.card f.ker ≤ Nat.card (Submodule.torsionBy ℕ values.range ℓ) := by
    have h_range (x : f.ker) : (x : X).1 ∈ values.range := (QuotientAddGroup.eq_zero_iff _).1 x.2
    have h_torsion (x : f.ker) : ℓ • (x : X).1 = 0 := (x : X).2
    exact Nat.card_le_card_of_injective (fun x ↦ ⟨⟨_, h_range x⟩, Subtype.ext (h_torsion x)⟩)
      fun x x' h ↦ by simpa only [Subtype.ext_iff] using h
  calc Nat.card {a : M // ℓ • a = 0} ^ card ι
    _ = Nat.card X := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_fun]
      exact Nat.card_congr (Equiv.subtypePiEquivPi.symm.trans
        (Equiv.subtypeEquivRight fun x ↦ by simp [X, funext_iff]))
    _ = Nat.card (X ⧸ f.ker →+ QZ) * Nat.card f.ker := by
      rw [card_hom_QZ, ← f.ker.card_eq_card_quotient_mul_card_addSubgroup]
    _ ≤ Nat.card (D.reductions ℓ T) * Nat.card (Submodule.torsionBy ℕ (D.cocycles P) ℓ) := by
      grw [h_chars, h_ker, card_torsionBy_le_of_surjective ℓ values.rangeRestrict_surjective]

end RelationSetting
namespace IsLargeLevel.SplitPlaces

variable {K ι : Type} [Field K] [EmbeddedNumberField K] {ℓ m N : ℕ} [NeZero m]
  {U O : OpenNormalSubgroup Gal(Ω/K)} {I : Set Gal(Ω/K)}
/-- Let `ℓ` divide `m` and let `O ⊇ U` fix the `ℓ`-th roots of unity. A family `s` of primes not
dividing `N` and split for `U` and `m` extends by two new primes to such a family for `O` and `ℓ`,
whose new Frobenius elements lie in the cosets `(x j)⁻¹ U` of two given elements `x j` of `O`. The
sets `I` and `I'` are the unions of the inertia groups above the other primes not dividing `N`. -/
lemma exists_add_two_primes [NeZero ℓ] [NeZero N]
    [Finite ι] (s : SplitPlaces (K := K) m N I U ι) (hm : ℓ ∣ m)
    (hUO : U.toSubgroup ≤ O.toSubgroup) (hO : ∀ g ∈ O, cyclotomicCharMod Ω ℓ g = 1) (x : Bool → O) :
    ∃ (I' : Set Gal(Ω/K)) (s' : SplitPlaces (K := K) ℓ N I' O (ι ⊕ Bool)),
      (∀ i : ι, s'.v (.inl i) = s.v i) ∧
      (∀ i : ι, s'.φ (.inl i) = s.φ i) ∧
      ∀ j : Bool, (x j).1 * s'.φ (.inr j) ∈ U := by
  -- Chebotarev: for `g` in `O`, a new prime other than `w` with a Frobenius in `g⁻¹ U`.
  have cheb (g : O) (w : FinPlace K) : ∃ v : FinPlace K, (v ≠ w ∧ ↑N ∉ v.1 ∧ ∀ i, s.v i ≠ v) ∧
      ∃ B : ClosurePlace, IsPlaceOver B v ∧ ∃ φ : Gal(Ω/K), g.1 * φ ∈ U ∧ IsFrob B v.q φ := by
    obtain ⟨v, hv, -, B, hB, φ, hφU, hφ, -⟩ :=
      chebotarev (U.isOpen.preimage (continuous_const_mul g.1)) ⟨g⁻¹, by simp⟩
        (((finite_natCast_mem N).union (Set.finite_range s.v)).insert w)
    exact ⟨v, by simpa using hv, B, hB, φ, hφU, hφ⟩
  -- The first new prime avoids an arbitrary prime, the second avoids the first.
  obtain ⟨v, B, φ, v_inj, hv⟩ :
      ∃ (v : Bool → FinPlace K) (B : Bool → ClosurePlace) (φ : Bool → Gal(Ω/K)),
        Injective v ∧ ∀ j, (↑N ∉ (v j).1 ∧ ∀ i, s.v i ≠ v j) ∧ IsPlaceOver (B j) (v j) ∧
          (x j).1 * φ j ∈ U ∧ IsFrob (B j) (v j).q (φ j) := by
    obtain ⟨v₁, ⟨-, hv₁⟩, B₁, hB₁, φ₁, hφ₁⟩ := cheb (x true) Classical.ofNonempty
    obtain ⟨v₀, ⟨h_ne, hv₀⟩, B₀, hB₀, φ₀, hφ₀⟩ := cheb (x false) v₁
    exact ⟨fun j ↦ cond j v₁ v₀, fun j ↦ cond j B₁ B₀, fun j ↦ cond j φ₁ φ₀,
      Bool.injective_iff.2 h_ne, Bool.forall_bool.2 ⟨⟨hv₀, hB₀, hφ₀⟩, hv₁, hB₁, hφ₁⟩⟩
  choose hv hB hφU hφ using hv
  let s' : SplitPlaces (K := K) ℓ N _ O (ι ⊕ Bool) :=
    { cyclotomicCharMod_eq_one := hO
      dvd_level := hm.trans s.dvd_level
      v := Sum.elim s.v v
      v_injective := s.v_injective.sumElim v_inj fun i j ↦ (hv j).2 i
      level_notMem := Sum.forall.2 ⟨s.level_notMem, fun j ↦ (hv j).1⟩
      valuationSubring := Sum.elim s.valuationSubring B
      isPlaceOver := Sum.forall.2 ⟨s.isPlaceOver, hB⟩
      φ := Sum.elim s.φ φ
      isFrob := Sum.forall.2 ⟨fun i ↦ ⟨(s.isFrob i).1, hUO (s.isFrob i).2⟩,
        fun j ↦ ⟨hφ j, (mul_mem_cancel_left (x j).2).1 (hUO (hφU j))⟩⟩
      mem_inertia_iff _ := .rfl
      inertiaGroup_le hv hB := (s.inertiaGroup_le hv hB).trans hUO
      principal_sup_idelesUnitOff F _ h :=
        s.principal_sup_idelesUnitOff F fun y hy g ↦ h hy (inclusion hUO g) }
  exact ⟨_, s', fun i ↦ rfl, fun i ↦ rfl, hφU⟩

/-- Descent of root detection from `m` to a divisor `ℓ`. Let `U ≤ O` and let the Frobenius elements
of `s` detect `m`-th roots: whatever they fix among the `m`-th roots of `N`-units of the field of
`U` is fixed by `U`. Then `U` also fixes every `ℓ`-th root `y` of an `N`-unit of the field of `O`
that they all fix. -/
lemma le_stabilizer (s : SplitPlaces (K := K) m N I U ι) (h_detect : s.FrobeniiDetectRoots)
    (hm : ℓ ∣ m) (hUO : U.toSubgroup ≤ O.toSubgroup) {y : DiscreteUnits Ω}
    (hy : ℓ • y ∈ fixedSUnits N O) (h_frob : ∀ i : ι, unitsRep (s.φ i) y = y) :
    U.toSubgroup ≤ MulAction.stabilizer Gal(Ω/K) y.toMul := by
  obtain ⟨m', rfl⟩ := hm
  have hyU : ℓ • y ∈ fixedSUnits N U := ⟨hy.1, fun g ↦ hy.2 (inclusion hUO g)⟩
  exact h_detect y (by simpa only [mul_nsmul] using nsmul_mem hyU m') h_frob

end IsLargeLevel.SplitPlaces

/-- The submodule `M[ℓ]` of the points killed by `ℓ`. -/
abbrev DiscreteModule.torsion {R G : Type} [CommRing R] [Group G] [TopologicalSpace G]
    (M : DiscreteModule R G) (ℓ : ℕ) : DiscreteModule R G :=
  M.submodule (ℓ • LinearMap.id).ker fun g a (h : ℓ • a = 0) ↦
    show ℓ • M.ρ g a = 0 by rw [← map_nsmul, h, map_zero]

namespace RelationSetting

variable {K R : Type} [Field K] [EmbeddedNumberField K] [CommRing R]
  {M : DiscreteModule R Gal(Ω/K)} {m : ℕ} [NeZero m] (D : RelationSetting M m)
  {ℓ : ℕ} [Fact ℓ.Prime]

variable (M ℓ) in
/-- The action of the Galois group on `M[ℓ]` and on the `ℓ`-th roots of unity. -/
def torsionAction : Gal(Ω/K) →* Multiplicative (AddAut (M.torsion ℓ)) × (ZMod ℓ)ˣ :=
  ((DistribMulAction.toAddAut _ (M.torsion ℓ)).comp (M.torsion ℓ).ρ.asGroupHom).prod
    (cyclotomicCharMod Ω ℓ)

/-- An element of the kernel of the action on `M[ℓ]` and `μ_ℓ` fixes the `ℓ`-th roots of unity. -/
lemma cyclotomicCharMod_eq_one_of_mem_ker_torsionAction {g : Gal(Ω/K)}
    (hg : g ∈ (torsionAction M ℓ).ker) : cyclotomicCharMod Ω ℓ g = 1 :=
  congrArg Prod.snd (MonoidHom.mem_ker.1 hg)

/-- The kernel of the action on `M[ℓ]` and `μ_ℓ` acts trivially on `M[ℓ]`. -/
lemma trivialOn_ker_torsionAction : (M.torsion ℓ).TrivialOn (torsionAction M ℓ).ker := fun _ hg a ↦
  DFunLike.congr_fun (congrArg (fun p ↦ Multiplicative.toAdd p.1) (MonoidHom.mem_ker.1 hg)) a

/-- If `ℓ ∣ m`, the subgroup `U` of the setting acts trivially on `M[ℓ]` and on the `ℓ`-th roots of
unity. -/
lemma le_ker_torsionAction (hm : ℓ ∣ m) : D.subgroup.toSubgroup ≤ (torsionAction M ℓ).ker :=
  fun g hg ↦
  MonoidHom.mem_ker.2 <| Prod.ext (AddEquiv.ext fun a ↦ Subtype.ext (D.apply_eq_of_mem g hg a.1))
    (cyclotomicCharMod_eq_one_of_dvd hm (D.cyclotomicCharMod_eq_one g hg))

/-- If `M[ℓ]` has order `ℓ`, the kernel of the action on `M[ℓ]` and `μ_ℓ` has index prime to `ℓ`:
the index divides `(ℓ - 1) ^ 2`. -/
lemma coprime_index_ker_torsionAction [Finite M] (h_card : Nat.card (M.torsion ℓ) = ℓ) :
    ℓ.Coprime (torsionAction M ℓ).ker.index := by
  have hℓ : ℓ.Prime := Fact.out
  have h_mul : Nat.card (Multiplicative (M.torsion ℓ)) = ℓ := h_card
  have h_aut : Nat.card (Multiplicative (AddAut (M.torsion ℓ))) = ℓ - 1 := by
    rw [← Nat.card_congr (MulAutMultiplicative (M.torsion ℓ)).toEquiv,
      (isCyclic_of_prime_card h_mul).card_mulAut, h_mul, Nat.totient_prime hℓ]
  have h_dvd : (torsionAction M ℓ).ker.index ∣ (ℓ - 1) ^ 2 := by
    grw [index_ker, card_subgroup_dvd_card, Nat.card_prod, h_aut, Nat.card_units, Nat.card_zmod, sq]
  have h_coprime : ℓ.Coprime (ℓ - 1) := (Nat.coprime_self_sub_right hℓ.one_le).2 (by simp)
  exact (h_coprime.pow_right 2).of_dvd_right h_dvd

variable (ℓ) in
/-- The local condition for `M[ℓ]`: the functions on the decomposition group of the chosen place
`D.place v` above `v`, with values in `M[ℓ]`, that are allowed for `M`. -/
def allowedTorsion (v : FinPlace K) :
    Submodule R (decompGroup Gal(Ω/K) (D.place v) → M.torsion ℓ) :=
  (D.allowed v).comap ((Submodule.subtype _).compLeft _)

omit [Fact ℓ.Prime] in
/-- Let `P ⊆ P'` with `P'` finite. A cocycle in `D.cocycles P` killed by `ℓ` takes its values in
`M[ℓ]`, so there are at most as many of them as Selmer cocycles (`selmerZ1`) of `M[ℓ]` for `P'`:
cocycles in the local conditions at `S`, zero at complex conjugations and unramified outside
`S ∪ P'`. -/
lemma card_torsionBy_cocycles_le [Finite M] {P P' : Set (FinPlace K)} (hP : P ⊆ P')
    (hP' : P'.Finite) : Nat.card (Submodule.torsionBy ℕ (D.cocycles P) ℓ) ≤
      Nat.card (selmerZ1 (M.torsion ℓ) D.localPrimes D.place (D.allowedTorsion ℓ) P') := by
  have : Finite (selmerZ1 (M.torsion ℓ) D.localPrimes D.place (D.allowedTorsion ℓ) P') :=
    (selmerZ1.finite_unramified_cocycles _ (D.localPrimes.finite_toSet.union hP')).subset
      inf_le_left
  let lift (z : Submodule.torsionBy ℕ (D.cocycles P) ℓ) (g : Gal(Ω/K)) : M.torsion ℓ :=
    ⟨(z : D.cocycles P).1 g, congrFun (Subtype.ext_iff.1 z.2) g⟩
  have lift_mem (z : Submodule.torsionBy ℕ (D.cocycles P) ℓ) :
      lift z ∈ selmerZ1 (M.torsion ℓ) D.localPrimes D.place (D.allowedTorsion ℓ) P' := by
    obtain ⟨⟨⟨h_cont, h_mul⟩, h_unram⟩, h_loc, h_conj⟩ := D.cocycles_mono hP (z : D.cocycles P).2
    -- As `M[ℓ] → M` is injective, each condition on `lift z` is the same condition on `z`.
    exact ⟨⟨⟨h_cont.subtype_mk _, fun g h ↦ Subtype.ext (h_mul g h)⟩,
      fun g hg ↦ Subtype.ext (h_unram g hg)⟩, h_loc, fun g hg ↦ Subtype.ext (h_conj g hg)⟩
  exact Nat.card_le_card_of_injective (fun z ↦ ⟨lift z, lift_mem z⟩) fun z w h ↦ by
    simpa only [lift, Subtype.ext_iff, funext_iff] using h

section Procyclic

variable {κ : Gal(Ω/K) →* ℤ_[ℓ]ˣ}

/-- Let `κ` be continuous with values in `1 + 4 ℤ_ℓ`, so that the image of a closed subgroup `H` is
procyclic. Some `γ ∈ H` and `H ⊓ ker κ` generate `H` topologically: every open subgroup of `H` that
contains both is all of `H`. -/
lemma exists_generator_mod_ker (hκ : Continuous κ) (hκ_four : ∀ g : Gal(Ω/K), 4 ∣ (κ g).1 - 1)
    (H : Subgroup Gal(Ω/K)) (hH : IsClosed (H : Set Gal(Ω/K))) :
    ∃ γ : H, ∀ F ≥ (κ.domRestrict H).ker, F.IsOpen → γ ∈ F → ∀ g : H, g ∈ F :=
  Selmer.exists_procyclic_generator (κ.domRestrict H) hκ.continuousOn.domRestrict
    fun g ↦ hκ_four g

open Classical in
/-- Let `κ` be continuous with values in `1 + 4 ℤ_ℓ`. Suppose the local condition at each prime `v`
consists of the functions that vanish on the whole decomposition group if `v` is not above `ℓ`, and
on its intersection with `ker κ` if `v` is above `ℓ`. Then there is at most one allowed local
cocycle with values in `M[ℓ]` if `v` is not above `ℓ`, and at most `#M[ℓ]` if it is, as a cocycle
that vanishes on the kernel of `κ` is determined by one value. -/
lemma card_allowedTorsion_le (hκ : Continuous κ) (hκ_four : ∀ g : Gal(Ω/K), 4 ∣ (κ g).1 - 1)
    [Finite M] (h_allowed : ∀ v : FinPlace K,
      D.allowed v = .pi {g : decompGroup Gal(Ω/K) (D.place v) | ↑ℓ ∈ v.1 → κ g = 1} ⊥)
    (v : FinPlace K) :
    Nat.card ↥(D.allowedTorsion ℓ v ⊓
      Z1 ((M.torsion ℓ).restrictTo (decompGroup Gal(Ω/K) (D.place v))).ρ) ≤
      if ↑ℓ ∉ v.1 then 1 else Nat.card (M.torsion ℓ) := by
  let G : Subgroup Gal(Ω/K) := decompGroup Gal(Ω/K) (D.place v)
  have h_zero {z : G → M.torsion ℓ} (hz : z ∈ D.allowedTorsion ℓ v) (g : G)
      (hg : ↑ℓ ∈ v.1 → κ g = 1) : z g = 0 := by
    rw [allowedTorsion, h_allowed] at hz
    exact Subtype.ext (hz g hg)
  split_ifs with hv
  · obtain ⟨δ, hδ⟩ := exists_generator_mod_ker hκ hκ_four G inferInstance
    refine Nat.card_le_card_of_injective _
      ((injective_iff_map_eq_zero ((LinearMap.proj δ).domRestrict _)).2 fun ⟨z, hz, hZ⟩ hzδ ↦ ?_)
    -- The zeros of `z` form an open subgroup that contains `δ` and the kernel of `κ`.
    exact Subtype.ext <| funext <| hδ (cocycleKer ((M.torsion ℓ).restrictTo G).ρ hZ.2)
      (fun g hg ↦ h_zero hz g fun _ ↦ hg) (hZ.1.isOpen_preimage {0} (by simp)) hzδ
  · exact (Nat.card_eq_one_iff_exists.2 ⟨0, fun ⟨z, hz, _⟩ ↦
      Subtype.ext (funext fun g ↦ h_zero hz g fun h ↦ absurd h hv)⟩).le

/-- Let `κ` be continuous with values in `1 + 4 ℤ_ℓ`, let `ℓ ∣ m`, let `M[ℓ]` have order `ℓ`, and
let `ker κ` lie in `U ∪ U c⁻¹`. Adding two split primes to a family `s` whose Frobenius elements
detect roots gives a family `s'` of split primes for some open normal subgroup `O`. The primes of
`s` are among those of `s'`, and `M[ℓ]` has few cocycles for `s'`: at most `ℓ ^ (#ι + 3)`
cocycles trivialised above the level and infinity and on the inertia groups of the other primes.
That the Frobenius elements detect roots means that `U` fixes every `m`-th root of a `q`-unit of
its field that they all fix. -/
lemma exists_hasFewCocycles_torsion (hκ : Continuous κ)
    (hκ_four : ∀ g : Gal(Ω/K), 4 ∣ (κ g).1 - 1) [Finite M] (hm : ℓ ∣ m) {c : Gal(Ω/K)}
    (hU : ∀ g : Gal(Ω/K), κ g = 1 → g ∈ D.subgroup ∨ g * c ∈ D.subgroup)
      (h_card : Nat.card (M.torsion ℓ) = ℓ)
    {q : ℕ} [NeZero q] {ι : Type} [Fintype ι] {I : Set Gal(Ω/K)}
    (s : SplitPlaces (K := K) m q I D.subgroup ι) (h_detect : s.FrobeniiDetectRoots) :
    ∃ (O : OpenNormalSubgroup Gal(Ω/K)) (I' : Set Gal(Ω/K))
      (s' : SplitPlaces (K := K) ℓ q I' O (ι ⊕ Bool)), Set.range s.v ⊆ Set.range s'.v ∧
      (M.torsion ℓ).HasFewCocycles (PlaceAboveLevel q) I' (card ι + 3) := by
  classical
  -- Let `O ⊇ U` be the kernel of the action on `M[ℓ]` and `μ_ℓ`. It is generated by `U`, one
  -- element `γ`, and `c` if `c ∈ O`; the new Frobenius elements are their inverses modulo `U`.
  have hUO : D.subgroup.1.1 ≤ (torsionAction M ℓ).ker := D.le_ker_torsionAction hm
  let O : OpenNormalSubgroup Gal(Ω/K) := .mk
    ⟨(torsionAction M ℓ).ker, isOpen_mono hUO D.subgroup.1.2⟩
  obtain ⟨γ, hγ⟩ := exists_generator_mod_ker hκ hκ_four _ O.isClosed
  let x (j : Bool) : O := cond j γ (if h : c ∈ O then ⟨c, h⟩ else 1)
  obtain ⟨I', s', v_eq, φ_eq, φ_mem⟩ := s.exists_add_two_primes (O := O) hm hUO
    (fun _ ↦ cyclotomicCharMod_eq_one_of_mem_ker_torsionAction) x
  refine ⟨O, I', s', Set.range_subset_iff.2 fun i ↦ ⟨.inl i, v_eq i⟩, ?_⟩
  -- An `ℓ`-th root `y` of a `q`-unit that the Frobenius elements of `s'` fix is fixed by `O`: its
  -- stabiliser `F` is open and contains `U`, `γ` and `O ⊓ ker κ`.
  have fixed (y : DiscreteUnits Ω) (hy : ℓ • y ∈ fixedSUnits q O)
      (h_frob : ∀ i, unitsRep (s'.φ i) y = y) (g : O) : unitsRep g.1 y = y := by
    let F := MulAction.stabilizer Gal(Ω/K) y.toMul
    have hUF : D.subgroup.1.1 ≤ F := s.le_stabilizer h_detect hm hUO hy fun i ↦ by
      rw [← φ_eq i, h_frob]
    have hxF (j : Bool) : (x j).1 ∈ F :=
      (F.mul_mem_cancel_right (h_frob (.inr j))).1 (hUF (φ_mem j))
    have h_ker : (κ.domRestrict O.1.1).ker ≤ F.subgroupOf O.1.1 := by
      refine fun g hg ↦ (hU g hg).elim (fun hgU ↦ hUF hgU) fun hgc ↦ ?_
      -- `g c ∈ U` forces `c ∈ O`, so `c = x false ∈ F`.
      have hcO : c ∈ O := (mul_mem_cancel_left g.2).1 (hUO hgc)
      exact (F.mul_mem_cancel_right (by simpa [x, hcO] using hxF false)).1 (hUF hgc)
    exact hγ _ h_ker (isOpen_mono hUF D.subgroup.1.2).preimage_val (hxF true) g
  -- `M[ℓ]` is finite, killed by `ℓ`, fixed by `O`, and `ρ 1 - 0` is injective on it.
  have hV : (M.torsion ℓ).FiniteKilledFixedInj ℓ O 1 0 :=
    ⟨inferInstance, fun a ↦ Subtype.ext a.2, trivialOn_ker_torsionAction, by simp [Injective]⟩
  -- Higman's criterion holds because the index of `O` is prime to `ℓ`.
  obtain ⟨h_few, -⟩ := s'.card_trivialised_of_isHigmanProjective hV
    (hV.isHigmanProjective_of_coprime (coprime_index_ker_torsionAction h_card))
    fun y hy h_frob g ↦ by
      simp only [map_one, Module.End.one_apply, zero_smul, sub_zero]
      exact fixed y hy h_frob g
  -- The family `s'` has `#ι + 2` primes and the bound has one further factor `#M[ℓ]`.
  simpa using h_few

open Classical in
/-- Let `κ` be continuous with values in `1 + 4 ℤ_ℓ` and kernel in `U ∪ U c⁻¹`, let `ℓ ∣ m`, let
`M[ℓ]` have order `ℓ`, let the local conditions be zero away from `ℓ` and vanishing on `ker κ`
above `ℓ`, and let `K` have at least four infinite places. Then the cocycles unramified outside `S`
and the split primes have few points killed by `ℓ`, if the primes of `S` divide the level `q` and
the Frobenius elements of the split primes detect the roots of `q`-units: the number of these
points times `ℓ ^ (k + 1)` is at most `ℓ ^ #ι`, where `k` counts the primes of `S` that are not
above `ℓ`. Indeed the bound `ℓ ^ (#ι + 3)` of `exists_hasFewCocycles_torsion` loses one factor `ℓ`
for each of four infinite places and for each of these `k` primes. -/
lemma card_torsionBy_cocycles_mul_pow_le (hκ : Continuous κ)
    (hκ_four : ∀ g : Gal(Ω/K), 4 ∣ (κ g).1 - 1) [Finite M] (hm : ℓ ∣ m)
    (h_places : 4 ≤ card (InfinitePlace K)) {c : Gal(Ω/K)}
    (hU : ∀ g : Gal(Ω/K), κ g = 1 → g ∈ D.subgroup ∨ g * c ∈ D.subgroup)
      (h_card : Nat.card (M.torsion ℓ) = ℓ)
    (h_allowed : ∀ v : FinPlace K,
      D.allowed v = .pi {g : decompGroup Gal(Ω/K) (D.place v) | ↑ℓ ∈ v.1 → κ g = 1} ⊥)
    {q : ℕ} [NeZero q] (hS : ∀ v ∈ D.localPrimes, ↑q ∈ v.1) {ι : Type} [Fintype ι]
      {I : Set Gal(Ω/K)}
    (s : SplitPlaces (K := K) m q I D.subgroup ι) (h_detect : s.FrobeniiDetectRoots) :
    Nat.card (Submodule.torsionBy ℕ (D.cocycles (Set.range s.v)) ℓ) *
      ℓ ^ (#{v ∈ D.localPrimes | ↑ℓ ∉ v.1} + 1) ≤ ℓ ^ card ι := by
  obtain ⟨O, I', s', h_range, h_few⟩ :=
    D.exists_hasFewCocycles_torsion hκ hκ_four hm hU h_card s h_detect
  have triv {g : Gal(Ω/K)} (hg : M.ρ g = 1) : (M.torsion ℓ).ρ g = 1 :=
    LinearMap.ext fun a ↦ Subtype.ext (LinearMap.congr_fun hg (a : M))
  -- The numbers of Selmer cocycles of `M[ℓ]` and of its allowed local cocycles at `v`.
  let sel : ℕ := Nat.card (selmerZ1 _ D.localPrimes D.place (D.allowedTorsion ℓ) (Set.range s'.v))
  let loc (v : FinPlace K) : ℕ := Nat.card ↥(D.allowedTorsion ℓ v ⊓
    Z1 ((M.torsion ℓ).restrictTo (decompGroup Gal(Ω/K) (D.place v))).ρ)
  have h_selmer : sel * ℓ ^ (#D.localPrimes + card (InfinitePlace K)) ≤
      ℓ ^ (card ι + 3) * ∏ v ∈ D.localPrimes, loc v := by
    simpa only [h_card] using selmerZ1.card_mul_pow_le (fun g hg ↦ triv (D.unramified g hg))
      D.isPlaceOver (D.allowedTorsion ℓ)
      (fun v hv ↦ Set.range_subset_iff.2 fun a ↦ D.coboundary_le v hv ⟨a.1, rfl⟩)
      (fun hc ↦ triv (D.ρ_eq_one_of_isComplexConj hc)) s' h_few hS
  set t : ℕ := Nat.card (Submodule.torsionBy ℕ (D.cocycles (Set.range s.v)) ℓ)
  set k : ℕ := #{v ∈ D.localPrimes | ↑ℓ ∉ v.1}
  set k' : ℕ := #{v ∈ D.localPrimes | ¬↑ℓ ∉ v.1}
  have h_prod : ∏ v ∈ D.localPrimes, loc v ≤ ℓ ^ k' := by
    unfold loc
    grw [D.card_allowedTorsion_le hκ hκ_four h_allowed, h_card]
    simp [prod_ite, k']
  have h_split : k + k' = #D.localPrimes := D.localPrimes.card_filter_add_card_filter_not (↑ℓ ∉ ·.1)
  refine Nat.le_of_mul_le_mul_right ?_ (pow_pos (NeZero.pos ℓ) (k' + 3))
  calc t * ℓ ^ (k + 1) * ℓ ^ (k' + 3) = t * ℓ ^ (k + k' + 4) := by ring
    _ ≤ sel * ℓ ^ (#D.localPrimes + card (InfinitePlace K)) :=
      Nat.mul_le_mul (D.card_torsionBy_cocycles_le h_range (Set.finite_range _))
        (Nat.pow_le_pow_right (NeZero.pos ℓ) (by omega))
    _ ≤ ℓ ^ (card ι + 3) * ℓ ^ k' := by grw [h_selmer, h_prod]
    _ = ℓ ^ card ι * ℓ ^ (k' + 3) := by ring

end Procyclic

/-- Relations modulo `ℓ`. Let `ℓ ∣ m`, and let `M[ℓ]` have order `ℓ`. Let `κ` be a continuous
character with values in `1 + 4 ℤ_ℓ` (so its image is procyclic) whose kernel lies in `U ∪ U c⁻¹`.
Let the local condition be zero at the primes not above `ℓ` and vanishing on `ker κ` above `ℓ`. If
`K` has at least four infinite places, then for some `T ⊇ S` the reductions modulo `ℓ` of the
relations off `T` form a group of order at least `ℓ ^ (k + 1)`, where `k` counts the primes of `S`
not above `ℓ`. A relation off `T` is a continuous equivariant map from `U` to `M* = Hom(M, ℚ/ℤ)`,
unramified outside `T`, whose Frobenius values give linear relations among cocycle values at tame
generators. This is weaker than the count given by the formula of Greenberg and Wiles, which grows
with the number of infinite places; here only four of these places are used. -/
theorem exists_pow_le_card_reductions [Finite M] (hm : ℓ ∣ m)
    (h_places : 4 ≤ card (InfinitePlace K)) {κ : Gal(Ω/K) →* ℤ_[ℓ]ˣ} (hκ : Continuous κ)
    (hκ_four : ∀ g : Gal(Ω/K), 4 ∣ (κ g).1 - 1) {c : Gal(Ω/K)}
    (hU : ∀ g : Gal(Ω/K), κ g = 1 → g ∈ D.subgroup ∨ g * c ∈ D.subgroup)
    (h_card : Nat.card {a : M // ℓ • a = 0} = ℓ)
    (h_allowed : ∀ v : FinPlace K,
      D.allowed v = .pi {g : decompGroup Gal(Ω/K) (D.place v) | ↑ℓ ∈ v.1 → κ g = 1} ⊥) :
    open Classical in
    ∃ T : Finset (FinPlace K), D.localPrimes ⊆ T ∧
      ℓ ^ (#{v ∈ D.localPrimes | ↑ℓ ∉ v.1} + 1) ≤ Nat.card (D.reductions ℓ T) := by
  classical
  -- A family of split primes whose Frobenius elements detect roots, such that every family of
  -- characters that kills the values of the cocycles at the `γ i` comes from a relation off `T`.
  obtain ⟨q, _, ι, _, I, s, γ, T, hS, hST, -, h_detect, -, h_forms⟩ :=
    D.exists_splitPlaces_forall_exists_mem_relations D.avoids_one
  set t : ℕ := Nat.card (Submodule.torsionBy ℕ (D.cocycles (Set.range s.v)) ℓ)
  have h_few : t * ℓ ^ (#{v ∈ D.localPrimes | ↑ℓ ∉ v.1} + 1) ≤ ℓ ^ card ι :=
    D.card_torsionBy_cocycles_mul_pow_le hκ hκ_four hm h_places hU h_card h_allowed hS s h_detect
  have h_many : ℓ ^ card ι ≤ Nat.card (D.reductions ℓ T) * t := by
    simpa only [h_card] using D.pow_le_card_reductions_mul ℓ (Set.finite_range s.v) h_forms
  have t_pos : 0 < t := Nat.pos_of_mul_pos_left ((pow_pos (NeZero.pos ℓ) _).trans_le h_many)
  exact ⟨T, hST, Nat.le_of_mul_le_mul_left (h_few.trans (h_many.trans_eq (mul_comm _ _))) t_pos⟩

end RelationSetting

end New

end
