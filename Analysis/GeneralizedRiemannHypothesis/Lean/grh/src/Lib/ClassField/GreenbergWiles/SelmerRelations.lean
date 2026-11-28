import Lib.ClassField.Global.Chebotarev
import Lib.ClassField.GreenbergWiles.SplitPrimeReciprocity

/-!
# Relations at split primes and their number (Greenberg–Wiles)

Relations are families of additive maps `n i` on `M` such that `∑ i, n i (x (γ i)) = 0` for all
Selmer cocycles `x`, with `γ i` elements at auxiliary split primes. They take the place of the dual
Selmer group.

* `New.selmerZ1.card_mul_pow_le`: a bound for trivialised cocycles gives a bound for Selmer
  cocycles.
* `New.selmerZ1.exists_splitPlaces_frob_mem_coset`, `New.selmerZ1.exists_three_values`: split primes
  with Frobenius elements in given cosets, and trivialised cocycles with given values at them.
* `New.selmerZ1.card_relations_ge`: a lower bound for the number of relations.

Notions from other files:
* `New.DiscreteUnits`: The multiplicative group Ω^×, written additively. Here Ω is an algebraic
  closure of ℚ that contains each `EmbeddedNumberField` K, and a `ClosurePlace` is a finite place of
  Ω.
* `New.unitsRep`: the ℤ-linear representation of `G` on Ω^× (written additively) coming from the
  action of `G` on the field Ω by ring automorphisms.
* `New.DiscreteModule`: A discrete Γ-module over R: an R-module with the discrete topology and a
  continuous R-linear action of the topological group Γ.
* `New.IsLargeLevel.fixedSUnits`: The N-units of the fixed field of U: the N-units of Ω that are
  fixed by U.
* `New.IsLargeLevel.SplitPlaces`: Split places for `U`: distinct primes `s.v i` not dividing `N`,
  each with a Frobenius element `s.φ i` in `U`, where `U` fixes the `m`-th roots of unity and
  `m ∣ N`. The set `I` is the union of the inertia groups over the other primes not dividing `N`.
* `New.DiscreteModule.trivialisedCocycles`: pairs of f : X → V and continuous z : G → V vanishing on
  I, with g f(g⁻¹x) = f(x) + z(g) for all g, x. Here X is `New.PlaceAboveLevel q`, the places of Ω
  above q and infinity.

## Relation to the literature

Known; see `Lib.ClassField.GreenbergWiles.CocycleCounts` for sources.
-/

namespace New.selmerZ1

open NumberField Function Finset QuotientGroup InfinitePlace DiscreteModule Fintype
  IsLargeLevel Submodule Filter Set Pi NeZero
variable {K R : Type} [Field K] [EmbeddedNumberField K] [CommRing R]
  {M : DiscreteModule R Gal(Ω/K)} {S : Finset (FinPlace K)} {A : FinPlace K → ClosurePlace}

/-- Let `N` lie in every prime of `S`, let `A v` lie over `v`, let complex conjugations act
trivially on `M`, and let `y` be a Selmer cocycle (`selmerZ1`) that may ramify at the split primes
of `s` and is, for each prime `v` dividing `N`, the coboundary of `a v` on the decomposition group
of `A v`. Then `y` vanishes on the set `I` of `s` and is trivialised above `N` and infinity by a map
with the values `a w` at the chosen places over the primes dividing `N` and the infinite places
`w`. -/
lemma exists_trivialisation_of_mem (hA : ∀ v : FinPlace K, IsPlaceOver (A v) v)
    {L : ∀ v : FinPlace K, Submodule R (decompGroup Gal(Ω/K) (A v) → M)}
    (hcM : ∀ {c : Gal(Ω/K)}, IsComplexConj c → M.ρ c = 1) {m N : ℕ} [NeZero m] [NeZero N]
    {U : OpenNormalSubgroup Gal(Ω/K)} {I : Set Gal(Ω/K)} {ι : Type} (s : SplitPlaces m N I U ι)
    (hT : ∀ v ∈ S, ↑N ∈ v.1) {y : Gal(Ω/K) → M} (hy : y ∈ selmerZ1 M S A L (range s.v))
    (a : {v : FinPlace K | (N : 𝓞 K) ∈ v.1} ⊕ InfinitePlace K → M)
    (h_dec : ∀ (v : FinPlace K) (hv : ↑N ∈ v.1), ∀ g ∈ decompGroup Gal(Ω/K) (A v),
      y g = M.ρ g (a (.inl ⟨v, hv⟩)) - a (.inl ⟨v, hv⟩)) :
    ∃ f : PlaceAboveLevel N → M, (f, y) ∈ M.trivialisedCocycles (PlaceAboveLevel N) I ∧
      ∀ i : ↑{v : FinPlace K | ↑N ∈ v.asIdeal} ⊕ InfinitePlace K, f (Sum.map
        (fun v : {v : FinPlace K | (N : 𝓞 K) ∈ v.1} ↦
          ⟨A v, (hA v).valuation_natCast_lt_one_iff.mpr v.2⟩)
        (surjInv (comap_surjective (k := K))) i) = a i := by
  obtain ⟨⟨h_coc, h_unr⟩, -, h_real⟩ := hy
  refine trivialisedCocycles.exists_mem_of_orbit_reps (PlaceAboveLevel.bijective_orbits _ N hA)
    h_coc (I := I) (fun g hg ↦ ?_) a ?_
  · obtain ⟨v, hv⟩ := (s.mem_inertia_iff g).1 hg
    exact h_unr g ⟨v, by grind⟩
  rintro (⟨v, hv⟩ | w) g h_fix
  · exact h_dec v hv g (congrArg Subtype.val (Sum.inl.inj h_fix))
  -- The stabiliser of an infinite place holds only `1` and a complex conjugation.
  rcases eq_one_or_isComplexConj (Sum.inr.inj h_fix) with rfl | hc
  · have h_one : y 1 = 0 := by simpa using h_coc.2 1 1
    simp [h_one]
  · have h_conj : y g = 0 := h_real g hc
    simp [h_conj, hcM hc]

/-- Selmer cocycles against trivialised cocycles. Let the discrete module `M` be unramified outside
`S`, let complex conjugations act trivially on it, let `A v` lie over `v`, and let `L v` contain
the local coboundaries for `v ∈ S`. If `N` lies in every prime of `S` and there are at most `#M ^ k`
cocycles that vanish on `I` and are trivialised above `N` and infinity, then the number of Selmer
cocycles that may ramify at the split primes of `s`, times `#M ^ (#S + #(infinite places of K))`,
is at most `#M ^ k * ∏ v ∈ S, #Z_v`. Here `M` is finite, `Z_v` is the group of the local cocycles in
`L v`, and the Selmer cocycles (`selmerZ1`) are those in `L v` at `v ∈ S` that vanish at complex
conjugations and on inertia outside `S` and the split primes.

It replaces part of the Greenberg–Wiles formula: an upper bound on Selmer cocycles only, with no
dual Selmer group. -/
theorem card_mul_pow_le (hu : ∀ g ∈ inertiaAbove (S : Set (FinPlace K))ᶜ, M.ρ g = 1)
    (hA : ∀ v : FinPlace K, IsPlaceOver (A v) v)
    (L : ∀ v : FinPlace K, Submodule R (decompGroup Gal(Ω/K) (A v) → M))
    (hL : ∀ v ∈ S, (coboundaryMap (M.restrictTo (decompGroup Gal(Ω/K) (A v))).ρ).range ≤ L v)
    (hcM : ∀ {c : Gal(Ω/K)}, IsComplexConj c → M.ρ c = 1) {m : ℕ} [NeZero m] [Finite M]
    {k N : ℕ} {U : OpenNormalSubgroup Gal(Ω/K)} {I : Set Gal(Ω/K)}
    {ι : Type} [NeZero N] (s : SplitPlaces m N I U ι)
    (hk : M.HasFewCocycles (PlaceAboveLevel N) I k) (hT : ∀ v ∈ S, ↑N ∈ v.1) :
    Nat.card (selmerZ1 M S A L (range s.v)) * Nat.card M ^ (#S + card (InfinitePlace K)) ≤
      Nat.card M ^ k *
        ∏ v ∈ S, Nat.card ↥(L v ⊓ Z1 (M.restrictTo (decompGroup Gal(Ω/K) (A v))).ρ) := by
  -- Let `T` be the primes dividing `N`. A Selmer cocycle `y` with a vector `a w` for each place `w`
  -- in `T` or at infinity is sent by `F` to local data of `y - coboundaryMap M.ρ (a v)`, `v ∈ T`.
  -- The kernel of `F` embeds in the trivialised cocycles, and the quotient by it in the target of
  -- `F`.
  let Y : Submodule R (Gal(Ω/K) → M) := selmerZ1 M S A L (range s.v)
  let J (v : FinPlace K) : Submodule R (decompGroup Gal(Ω/K) (A v) → M) :=
    L v ⊓ Z1 (M.restrictTo (decompGroup Gal(Ω/K) (A v))).ρ
  let T : Set (FinPlace K) := {v : FinPlace K | ↑N ∈ v.1}
  have : Finite T := finite_natCast_mem N
  obtain ⟨h_pos, h_few⟩ := hk
  have : Finite (M.trivialisedCocycles (PlaceAboveLevel N) I) := (Nat.card_pos_iff.1 h_pos).2
  choose frob h_frob using fun v : FinPlace K ↦ (hA v).exists_isFrob Gal(Ω/K)
  have h_coc (y : Y) : y.1 ∈ Z1 M.ρ := y.2.1.1
  have h_loc (y : Y) (v : FinPlace K) (hv : v ∈ S) :
      (fun g : decompGroup Gal(Ω/K) (A v) ↦ y.1 g) ∈ J v :=
    ⟨y.2.2.1 v hv, (h_coc y).1.comp continuous_subtype_val, fun g h ↦ (h_coc y).2 g h⟩
  have h_cob (v : FinPlace K) (hv : v ∈ S) (a : M) :
      coboundaryMap (M.restrictTo (decompGroup Gal(Ω/K) (A v))).ρ a ∈ J v :=
    ⟨hL v hv ⟨a, rfl⟩, ((M.restrictTo _).coboundary a).2⟩
  have h_unr (y : Y) : ∀ g ∈ inertiaAbove (S ∪ range s.v)ᶜ, y.1 g = 0 := y.2.1.2
  -- The local data: the restriction in `J v` for `v ∈ S`, the value at a Frobenius for `v ∈ T \ S`.
  let F : Y × (T ⊕ InfinitePlace K → M) →+ (∀ v : S, J v) × (↥(T \ S) → M) :=
    .mk' (fun (y, a) ↦
      (fun ⟨v, hv⟩ ↦ ⟨_, sub_mem (h_loc y v hv) (h_cob v hv (a (.inl ⟨v, hT v hv⟩)))⟩,
        fun v ↦ (y - coboundaryMap M.ρ (a (.inl ⟨v, v.2.1⟩))) (frob v)))
      fun p p' ↦ by ext <;> simp [add_sub_add_comm]
  -- In the kernel, `y` is the coboundary of `a v` on the decomposition group at each `v ∈ T`.
  have h_dec (y : Y) (a : T ⊕ InfinitePlace K → M) (h : F (y, a) = 0) (v : FinPlace K)
      (hv : v ∈ T) (g : Gal(Ω/K)) (hg : g ∈ decompGroup Gal(Ω/K) (A v)) :
      y.1 g = M.ρ g (a (.inl ⟨v, hv⟩)) - a (.inl ⟨v, hv⟩) := by
    rw [← sub_eq_zero]
    by_cases hS : v ∈ S
    · exact congrFun (congrArg Subtype.val (congrFun (congrArg Prod.fst h) ⟨v, hS⟩)) ⟨g, hg⟩
    -- Off `S`, the difference is a cocycle that vanishes on inertia and at the Frobenius `frob v`.
    let z : Z1 M.ρ := ⟨y, h_coc y⟩ - M.coboundary (a (.inl ⟨v, hv⟩))
    have hz_frob : z.1 (frob v) = 0 := congrFun (congrArg Prod.snd h) ⟨v, hv, hS⟩
    have hz_inertia : ∀ τ ∈ inertiaGroup Gal(Ω/K) (A v), z.1 τ = 0 := by
      intro τ hτ
      have h_not : v ∉ ↑S ∪ range s.v := by
        clear h
        grind [s.level_notMem]
      have hy_τ : y.1 τ = 0 := h_unr y τ ⟨v, h_not, A v, hA v, hτ⟩
      simp [z, hy_τ, hu τ ⟨v, hS, A v, hA v, hτ⟩]
    exact Z1.eq_zero_on_decompGroup z (hA v) (h_frob v) hz_inertia hz_frob g hg
  -- So the vectors `a w` extend to a trivialisation of `y` at all places of `Ω` above them.
  choose f hf h_val using fun x : F.ker ↦
    exists_trivialisation_of_mem hA hcM s hT x.1.1.2 x.1.2 (h_dec x.1.1 x.1.2 x.2)
  -- The trivialisation determines `y` and all the vectors `a w`.
  have h_inj : Injective fun x : F.ker ↦
      (⟨(f x, x.1.1.1), hf x⟩ : M.trivialisedCocycles (PlaceAboveLevel N) I) := by
    intro x x' h
    obtain ⟨h_f, h_y⟩ : f x = f x' ∧ x.1.1.1 = x'.1.1.1 := Prod.mk.inj (congrArg Subtype.val h)
    exact Subtype.ext (Prod.ext (Subtype.ext h_y) (funext fun i ↦ by rw [← h_val, h_f, h_val]))
  have h_ker : Nat.card F.ker ≤ Nat.card M ^ k :=
    (Nat.card_le_card_of_injective _ h_inj).trans h_few
  have : ∀ v : FinPlace K, Finite (J v) := fun v ↦
    .inter_of_right (((hA v).isLocalGalois_and_residueCard_eq_and_isUniformiser _).1.finite_Z1
      (M.restrictTo _)) _
  have h_index : F.ker.index ≤ Nat.card ((∀ v : S, J v) × (↥(T \ S) → M)) :=
    (AddSubgroup.index_ker F).trans_le F.range.card_le_card_addGroup
  have h_count : Nat.card (Y × (T ⊕ InfinitePlace K → M)) ≤
      Nat.card M ^ k * Nat.card ((∀ v : S, J v) × (↥(T \ S) → M)) :=
    F.ker.card_mul_index.ge.trans (mul_le_mul' h_ker h_index)
  -- As `#T = #(T \ S) + #S`, the factor `#M ^ #(T \ S)` cancels from both sides.
  have h_split : (T \ ↑S).ncard + #S = T.ncard := by
    simpa using ncard_sdiff_add_ncard_of_subset (t := T) hT
  refine Nat.le_of_mul_le_mul_right ?_ (pow_pos (Nat.card_pos (α := M)) (T \ ↑S).ncard)
  calc
    _ = Nat.card Y * Nat.card M ^ (T.ncard + card (InfinitePlace K)) := by rw [← h_split]; ring
    _ ≤ Nat.card M ^ k * ((∏ v ∈ S, Nat.card (J v)) * Nat.card M ^ (T \ ↑S).ncard) := by
      simpa [Nat.card_fun, Nat.card_pi, ← S.prod_attach] using h_count
    _ = _ := by ring

/-- A prime does not divide two coprime integers. -/
lemma _root_.New.natCast_notMem_of_coprime {F : Type} [Field F] [NumberField F] {v : FinPlace F}
    {p q : ℕ} (hqp : q.Coprime p) (hq : ↑q ∈ v.1) : ↑p ∉ v.1 := fun hp ↦ by
  obtain ⟨c, d, h_one⟩ : IsCoprime (q : 𝓞 F) p := hqp.cast
  refine (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top ?_
  simpa [h_one] using add_mem (v.1.mul_mem_left c hq) (v.1.mul_mem_left d hp)

/-- Let `p ≠ 0` be prime to `m` and lie in no prime of `S`, and let the primes dividing `p` be
unramified in the field of `U`. There is a multiple `q ≠ 0` of `m`, prime to `p`, that lies in all
primes of `S` and in all primes ramified in the field of `U`, and such that the primes dividing `q`
generate the class group of every number field between `K` and the field of `U`. -/
lemma exists_dvd_coprime_sup_idelesUnitOff_eq_top (U : OpenNormalSubgroup Gal(Ω/K))
    (S : Finset (FinPlace K)) (m : ℕ)
    [NeZero m] {p : ℕ} [NeZero p] (hm : m.Coprime p) (hS : ∀ v ∈ S, ↑p ∉ v.1)
    (hU : ∀ v : FinPlace K, ↑p ∈ v.1 → ∀ B : ClosurePlace, IsPlaceOver B v →
      inertiaGroup Gal(Ω/K) B ≤ U) :
    ∃ q : ℕ, NeZero q ∧ m ∣ q ∧ q.Coprime p ∧ (∀ v ∈ S, ↑q ∈ v.1) ∧
      (∀ {v : FinPlace K} {B : ClosurePlace}, ↑q ∉ v.1 → IsPlaceOver B v →
        inertiaGroup Gal(Ω/K) B ≤ U) ∧
      ∀ (F : IntermediateField K Ω) [NumberField F], F ≤ fixedFieldOf U.1.1 →
        (principalIdele (K := F)).range ⊔ idelesUnitOff {w : FinPlace F | ↑q ∈ w.1} = ⊤ := by
  -- Take the product `Q k` of the integers in `[1, k]` that are prime to `p`, with `k` large: it
  -- lies in any finite set of primes, of any number field, that do not divide `p`.
  let Q (k : ℕ) : ℕ := ∏ n ∈ Finset.Icc 1 k with n.Coprime p, n
  have dvd_large {n : ℕ} (hn : n ≠ 0) (hnp : n.Coprime p) : ∀ᶠ k : ℕ in atTop, n ∣ Q k :=
    (eventually_ge_atTop n).mono fun k hk ↦
      Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hn.pos, hk⟩, hnp⟩)
  have mem_large {F : Type} [Field F] [NumberField F] {T : Set (FinPlace F)} (hT : T.Finite)
      (hTp : ∀ v ∈ T, ↑p ∉ v.1) : ∀ᶠ k : ℕ in atTop, ∀ v ∈ T, ↑(Q k) ∈ v.1 := by
    refine hT.eventually_all.2 fun v hv ↦ ?_
    obtain ⟨r, -, -, hr_mem, hr, -⟩ := v.1.exists_prime_and_absNorm_eq_pow
    have hrp : r.Coprime p :=
      hr.coprime_iff_not_dvd.2 fun h ↦ hTp v hv (v.1.mem_of_dvd h.natCast hr_mem)
    exact (dvd_large hr.ne_zero hrp).mono fun k hk ↦ v.1.mem_of_dvd hk.natCast hr_mem
  -- Only finitely many fields lie between `K` and the field of `U`,
  let E : IntermediateField K Ω := fixedFieldOf U.1.1
  have : Finite (IntermediateField K E) :=
    .of_equiv _ IsGalois.intermediateFieldEquivSubgroup.toEquiv.symm
  -- and the class group of each is generated by finitely many primes that do not divide `p`.
  have class_large : ∀ᶠ k : ℕ in atTop, ∀ F ∈ range E.lift, ∀ _ : NumberField F,
      (principalIdele (K := F)).range ⊔ idelesUnitOff {w | ↑(Q k) ∈ w.1} = ⊤ := by
    refine (finite_range _).eventually_all.2 fun F _ ↦ Filter.eventually_all.2 fun _ ↦ ?_
    obtain ⟨T, hT, -, h_off, h_top⟩ :=
      exists_sup_idelesUnitOff_eq_top (K := F) finite_empty _ (finite_natCast_mem p)
    filter_upwards [mem_large hT fun v hv hp ↦ h_off v hp hv] with k hk
    exact eq_top_mono (sup_le_sup_left (idelesUnitOff_mono hk) _) h_top
  -- The finitely many primes with an inertia group outside `U` do not divide `p`.
  let bad : Set (FinPlace K) :=
    {v | ¬ ∀ B : ClosurePlace, IsPlaceOver B v → inertiaGroup Gal(Ω/K) B ≤ U}
  have h_bad : bad.Finite := finite_ramified U.1.2
  have h_bad_p : ∀ v ∈ bad, ↑p ∉ v.1 := fun v hv hp ↦ hv (hU v hp)
  obtain ⟨k, hQ_S, hQ_m, h_ram, h_class⟩ := ((mem_large S.finite_toSet hS).and
    ((dvd_large (NeZero.ne m) hm).and ((mem_large h_bad h_bad_p).and class_large))).exists
  have hQ_ne : Q k ≠ 0 := by grind [Finset.prod_ne_zero_iff]
  have hQ_coprime : (Q k).Coprime p :=
    Nat.Coprime.prod_left fun n hn ↦ (Finset.mem_filter.1 hn).2
  refine ⟨Q k, ⟨hQ_ne⟩, hQ_m, hQ_coprime, hQ_S, ?_, ?_⟩
  · intro v B hv hB
    have h_good : v ∉ bad := fun h ↦ hv (h_ram v h)
    exact not_not.mp h_good B hB
  · exact fun F hF h_le ↦ h_class F ⟨IntermediateField.restrict h_le, F.lift_restrict h_le⟩ hF

/-- There is an open normal subgroup `O` such that the action of `g` on the `m`-th roots of the
`q`-units of the fixed field of `U` (the `y` with `m • y ∈ fixedSUnits q U`) depends only on the
coset of `g` modulo `O`. -/
lemma exists_fix_roots_of_units {m : ℕ} [NeZero m] (U : OpenNormalSubgroup Gal(Ω/K)) (q : ℕ)
    [NeZero q] :
    ∃ O : OpenNormalSubgroup Gal(Ω/K), ∀ g h : Gal(Ω/K),
      (g : Gal(Ω/K) ⧸ O.toOpenSubgroup.toSubgroup) = h →
      ∀ y : DiscreteUnits Ω, m • y ∈ fixedSUnits q U → unitsRep h y = unitsRep g y := by
  -- The roots form a finitely generated group: multiplication by `m` maps it into the finitely
  -- generated group of units, with kernel the `m`-th roots of unity.
  let mul : DiscreteUnits Ω →ₗ[ℤ] DiscreteUnits Ω := m • .id
  let roots : Submodule ℤ (DiscreteUnits Ω) := (fixedSUnits q U).comap mul
  have h_ker : (roots ⊓ LinearMap.ker mul).FG :=
    .of_le (fg_range (rootPowHom Ω m).val.toIntLinearMap) fun y hy ↦
      ((rootPowHom Ω m).prop.2 y).mpr hy.2
  have h_units : (fixedSUnits q U).FG :=
    Module.Finite.iff_fg.mp (dirichlet_fixedSUnits _ q U).1
  have h_image : (roots.map mul).FG := .of_le h_units (map_comap_le mul _)
  obtain ⟨t, ht⟩ : roots.FG := fg_of_fg_map_of_fg_inf_ker mul h_image h_ker
  -- An open normal subgroup `O` fixes the finitely many generators.
  have h_cont : Continuous fun p : Gal(Ω/K) × t ↦ (unitsModule Gal(Ω/K)).ρ p.1 p.2.1 :=
    (unitsModule Gal(Ω/K)).continuous.comp (continuous_id.prodMap continuous_subtype_val)
  obtain ⟨O, hO⟩ := exists_openNormalSubgroup_apply_eq h_cont
  refine ⟨O, fun g h hgh y hy ↦ LinearMap.eqOn_span (fun x hx ↦ ?_) (ht.ge hy)⟩
  have h_fix : unitsRep (g⁻¹ * h) x = x := by
    simpa using hO (g⁻¹ * h) (QuotientGroup.eq.mp hgh : g⁻¹ * h ∈ O) ⟨x, hx⟩
  -- Apply `g` to `(g⁻¹ h) x = x`.
  simpa using congrArg (unitsRep g) h_fix

/-- Let `U` fix the `m`-th roots of unity, that is, the cyclotomic character modulo `m` is trivial
on `U`, and let `p ≠ 0` be prime to `m`, lie in no prime of `S`, and have its primes unramified in
the field of `U`. There is a `q ≠ 0`, prime to `p` and in all primes of `S`, such that for every
open normal subgroup `O` there is a family of split places (`SplitPlaces`: primes of `K` not
dividing `q` with Frobenius elements `s.φ` in `U`) indexed by the cosets of `O`, none dividing
`p`, such that the Frobenius element at the coset of `g ∈ U` lies in that coset. -/
lemma exists_splitPlaces_frob_mem_coset {m : ℕ} [NeZero m] {U : OpenNormalSubgroup Gal(Ω/K)}
    (hU : ∀ g ∈ U, cyclotomicCharMod Ω m g = 1)
    (S : Finset (FinPlace K)) {p : ℕ} [NeZero p] (hmp : m.Coprime p) (hSp : ∀ v ∈ S, ↑p ∉ v.1)
    (hUp : ∀ v : FinPlace K, ↑p ∈ v.1 → ∀ B : ClosurePlace, IsPlaceOver B v →
      inertiaGroup Gal(Ω/K) B ≤ U) :
    ∃ q : ℕ, ∃ _ : NeZero q, q.Coprime p ∧
      (∀ v ∈ S, ↑q ∈ v.asIdeal) ∧
      ∀ O : OpenNormalSubgroup Gal(Ω/K), ∃ I : Set Gal(Ω/K),
        ∃ s : SplitPlaces m q I U (Gal(Ω/K) ⧸ O.toOpenSubgroup.toSubgroup),
        (∀ i : Gal(Ω/K) ⧸ (O.toOpenSubgroup : Subgroup Gal(Ω/K)), ↑p ∉ (s.v i).1) ∧
        ∀ g ∈ U, (s.φ g : Gal(Ω/K) ⧸ O.toOpenSubgroup.toSubgroup) = g := by
  -- Take a large multiple `q` of `m`. Chebotarev gives, outside any finite set, a prime for each
  -- coset; repeating this makes the primes of different cosets distinct.
  obtain ⟨q, hq, hm, hqp, hS, h_unr, h_class⟩ :=
    exists_dvd_coprime_sup_idelesUnitOff_eq_top U S m hmp hSp hUp
  refine ⟨q, hq, hqp, hS, fun O ↦ ?_⟩
  let ι := Gal(Ω/K) ⧸ O.toOpenSubgroup.toSubgroup
  -- `r c ∈ U` represents the coset `c` whenever `c` meets `U`.
  let r : ι → U := invFun fun g : U ↦ ((g : Gal(Ω/K)) : ι)
  have hr (g : U) : (r g : ι) = g := apply_invFun_apply (f := fun g : U ↦ (g : ι)) (a := g)
  -- Chebotarev gives primes outside any finite set with a Frobenius element in `U` and the coset.
  have cheb (c : ι) {T : Set (FinPlace K)} (hT : T.Finite) :
      ∃ v : FinPlace K,
        ((↑q ∉ v.asIdeal ∧ ↑p ∉ v.asIdeal) ∧ v ∉ T) ∧
        ∃ (B : ClosurePlace) (φ : Gal(Ω/K)),
          IsPlaceOver B v ∧ (IsFrob B v.q φ ∧ φ ∈ U) ∧ (φ : ι) = (r c).val := by
    have h_open : IsOpen ((U : Set Gal(Ω/K)) ∩ (↑) ⁻¹' {((r c).val : ι)}) :=
      U.toOpenSubgroup.isOpen'.inter (isOpen_discrete {((r c).val : ι)})
    obtain ⟨v, hv, -, B, hB, φ, ⟨φ_mem, φ_coset⟩, hφ, -⟩ :=
      chebotarev h_open ⟨r c, (r c).prop, rfl⟩
        (((finite_natCast_mem q).union (finite_natCast_mem p)).union hT)
    exact ⟨v, (not_or.mp hv).imp_left not_or.mp, B, φ, hB, ⟨hφ, φ_mem⟩, φ_coset⟩
  -- To get distinct primes, choose a sequence `u n` of families, each avoiding the earlier ones,
  -- and take the prime for `c` from the family number `e c`.
  obtain ⟨e, he⟩ := exists_injective_nat ι
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ι → FinPlace K, ∀ n c,
      ((↑q ∉ (u n c).asIdeal ∧ ↑p ∉ (u n c).asIdeal) ∧ u n c ∉ (u '' Set.Iio n).seq Set.univ) ∧
        ∃ (B : ClosurePlace) (φ : Gal(Ω/K)),
          IsPlaceOver B (u n c) ∧ (IsFrob B (u n c).q φ ∧ φ ∈ U) ∧ (φ : ι) = (r c).val :=
    seq_of_forall_finite_exists fun (t : Set (ι → FinPlace K)) ht ↦
      Classical.skolem.mp fun c ↦ cheb c (ht.seq finite_univ)
  choose hv B φ hB hφ φ_coset using fun c : ι ↦ hu (e c) c
  -- By the choice of `u`, the prime of `c` differs from those of all families with number below
  -- `e c`, so distinct cosets get distinct primes.
  have avoid (c : ι) : ∀ n < e c, ∀ c' : ι, u n c' ≠ u (e c) c := by
    simpa [Set.mem_seq_iff] using (hv c).2
  have u_inj : Injective fun c : ι ↦ u (e c) c := by grind [Injective]
  have hv_off (c : ι) : ↑q ∉ (u (e c) c).asIdeal ∧ ↑p ∉ (u (e c) c).asIdeal := (hv c).1
  let I : Set Gal(Ω/K) := {g | ∃ w : FinPlace K, ↑q ∉ w.asIdeal ∧
    w ∉ Set.range (fun c ↦ u (e c) c) ∧
    ∃ B : ClosurePlace, IsPlaceOver B w ∧ g ∈ inertiaGroup Gal(Ω/K) B}
  let s : SplitPlaces m q I U ι :=
    { cyclotomicCharMod_eq_one := hU
      dvd_level := hm
      v := fun c ↦ u (e c) c
      v_injective := u_inj
      level_notMem := fun c ↦ (hv_off c).left
      valuationSubring := B
      isPlaceOver := hB
      φ := φ
      isFrob := hφ
      mem_inertia_iff := fun _ ↦ Iff.rfl
      inertiaGroup_le := h_unr
      principal_sup_idelesUnitOff := h_class }
  exact ⟨I, s, fun c ↦ (hv_off c).right, fun g hg ↦ (φ_coset g).trans (hr ⟨g, hg⟩)⟩

/-- Let `M` be a `ZMod m`-module fixed by `U`, let `U` contain no complex conjugation, and let `s`
be split places for `U` (`SplitPlaces`) with Frobenius elements `s.φ`; `I` is the union of the
inertia groups above the other primes not dividing `q`. Let each `γ i` be a tame inertia generator
at level `m` (`IsTameGeneratorFor m`) at `s.valuationSubring i`, and let `s.φ j * (g * s.φ k * g⁻¹)`
act like `s.φ i` on the `m`-th roots of `fixedSUnits q U` (the `q`-units fixed by `U`). Then some
trivialised cocycle `P` exists, i.e. a continuous cocycle `P.2` vanishing on `I` and a map `P.1` on
places above `q` and infinity with `g • P.1 x = P.1 (g x) + P.2 g`, such that `P.2` has the values
`a`, `-a`, `-χ(g) g⁻¹ a` at `γ i`, `γ j`, `γ k` (added where these indices agree) and `0` at the
other `γ n`; here `χ` is the cyclotomic character modulo `m`. -/
lemma exists_three_values {m : ℕ} [NeZero m] [Module (ZMod m) M] {q : ℕ}
    {U : OpenNormalSubgroup Gal(Ω/K)} {I : Set Gal(Ω/K)} {J : Type} [NeZero q] [Fintype J]
    [DecidableEq J] (s : SplitPlaces m q I U J)
    {γ : J → Gal(Ω/K)} (hγ : ∀ i : J, IsTameGeneratorFor (K := K) m (s.valuationSubring i) (γ i))
    (hU : M.TrivialOn U.1.1) (hc : ∀ {c : Gal(Ω/K)}, IsComplexConj c → c ∉ U) {i j k : J}
    {g : Gal(Ω/K)} (hφ : ∀ y : DiscreteUnits Ω, m • y ∈ fixedSUnits q U →
      unitsRep (s.φ j * (g * s.φ k * g⁻¹)) y = unitsRep (s.φ i) y) (a : M) :
    ∃ P ∈ M.trivialisedCocycles (PlaceAboveLevel q) I, ∀ n : J, P.2 (γ n) =
      (if n = i then a else 0) - (if n = j then a else 0) -
        if n = k then (cyclotomicCharMod Ω m g).1 • M.ρ g⁻¹ a else 0 := by
  classical
  -- `b y i` is the power residue symbol: by `hb`, the root of unity with exponent `b y i` is
  -- `φ i x - x` whenever `m • x = y`. A linear relation `f` among the symbols of all units gives a
  -- cocycle with values read off from `f`.
  obtain ⟨b, hb, -, exists_cocycle⟩ := s.power_residue_reciprocity γ hγ hU
  -- A real place of the field of `U` would give a complex conjugation in `U`.
  have h_complex : IsTotallyComplex (fixedFieldOf (K := K) U.1.1) :=
    ⟨fun w ↦ not_isReal_iff_isComplex.1 fun hw ↦
      have ⟨⟨_, hc_mem⟩, hc_conj⟩ := exists_isComplexConj U.1.1 hw
      hc hc_conj hc_mem⟩
  -- With `m • x = y`: `φ i x - x = (φ j x - x) + φ j g (φ k g⁻¹ x - g⁻¹ x)`, and `φ j * g` acts on
  -- roots of unity by `cyclotomicCharMod Ω m (φ j * g) = cyclotomicCharMod Ω m g`.
  have symbol (y : fixedSUnits q U) :
      b y i = b y j + cyclotomicCharMod Ω m g * b (fixedSUnitsRep q U (↑g)⁻¹ y) k := by
    obtain ⟨x, hx⟩ : ∃ x : DiscreteUnits Ω, m • x = y := y.1.exists_nsmul (ne m)
    have hgx : m • unitsRep g⁻¹ x = fixedSUnitsRep q U (↑g)⁻¹ y := by rw [← map_nsmul, hx]; rfl
    have h_char : cyclotomicCharMod Ω m (s.φ j * g) = cyclotomicCharMod Ω m g := by
      rw [map_mul, s.cyclotomicCharMod_eq_one (s.φ j) (s.isFrob j).2, one_mul]
    apply (rootPowHom Ω m).2.1
    rw [← h_char, map_add, map_cyclotomicCharMod_mul, hb y x hx, hb y x hx, hb _ _ hgx,
      ← hφ x (by simp [hx])]
    simp
  let χ : ZMod m := cyclotomicCharMod Ω m g
  let f : J × (Gal(Ω/K) ⧸ U.1.1) → ZMod m :=
    Pi.single (i, 1) 1 - Pi.single (j, 1) 1 - Pi.single (k, (g : Gal(Ω/K) ⧸ U.1.1)⁻¹) χ
  -- By `symbol`, `f` is a relation; so `P.2 (γ n) = ∑ δ, δ (f (n, δ) • a)` for some cocycle `P`.
  -- (The finite sum over `J × (Gal(Ω/K) ⧸ U)` in the relation is evaluated by `simp`.)
  obtain ⟨P, hP, P_val⟩ := exists_cocycle h_complex f
    (fun y ↦ by simp [f, χ, mul_comm (b _ _), sub_mul, symbol y, single_apply]) a
  refine ⟨P, hP, fun n ↦ ?_⟩
  -- The representative of the coset of `x` acts on `M` as `x` does.
  have out_act (x : Gal(Ω/K)) (b : M) : M.ρ (x : Gal(Ω/K) ⧸ U.1.1).out b = M.ρ x b := by
    obtain ⟨u, hu⟩ := mk_out_eq_mul U.1.1 x
    simp [hu, hU u u.2]
  -- In the sum over cosets only the coset of `1` and, for `k`, that of `g⁻¹` contribute.
  simp [P_val, f, χ, Pi.single_apply, apply_ite (M.ρ _), ite_and, ← mk_inv, ← mk_one, out_act,
    ZMod.map_smul, sub_smul]

/-- Let `M` be unramified outside `S`, let complex conjugations act trivially on `M`, let `A v` lie
over `v`, and let `L v` contain the local coboundaries for `v ∈ S`. If `q` lies in every prime of
`S`, the part `P.2` of a cocycle `P` trivialised above `q` and infinity and zero on the inertia set
`I` of `s` is a Selmer cocycle (in `L v` at each `v ∈ S`, zero at complex conjugations) that may
ramify at the split primes of `s`. -/
lemma trivialised_mem_selmer (hu : ∀ g ∈ inertiaAbove (S : Set (FinPlace K))ᶜ, M.ρ g = 1)
    (hA : ∀ v : FinPlace K, IsPlaceOver (A v) v)
    (L : ∀ v : FinPlace K, Submodule R (decompGroup Gal(Ω/K) (A v) → M))
    (hL : ∀ v ∈ S, (coboundaryMap (M.restrictTo (decompGroup Gal(Ω/K) (A v))).ρ).range ≤ L v)
    (hcM : ∀ {c : Gal(Ω/K)}, IsComplexConj c → M.ρ c = 1) {m : ℕ} [NeZero m] {q : ℕ}
    {U : OpenNormalSubgroup Gal(Ω/K)} {I : Set Gal(Ω/K)}
    {J : Type} (s : SplitPlaces m q I U J) (hS : ∀ v ∈ S, ↑q ∈ v.1)
    {P : (PlaceAboveLevel q → M) × (Gal(Ω/K) → M)}
    (hP : P ∈ M.trivialisedCocycles (PlaceAboveLevel q) I) :
      P.2 ∈ selmerZ1 M S A L (range s.v) := by
  -- On the stabiliser of a place `x` the cocycle is the coboundary of `P.1 x`.
  have ⟨_, h_triv, h_inertia⟩ := hP
  have cob (x : PlaceAboveLevel q) (g : Gal(Ω/K)) (hg : g • x = x) :
      M.ρ g (P.1 x) - P.1 x = P.2 g := by rw [h_triv g x, hg, add_sub_cancel_left]
  refine ⟨⟨trivialisedCocycles.snd_mem_Z1 hP, fun g ⟨v, hv, B, hB, hg⟩ ↦ ?_⟩, fun v hv ↦ ?_,
    fun c ⟨j, hj⟩ ↦ ?_⟩
  · by_cases hq : ↑q ∈ v.1
    · -- Above `q` and outside `S`, inertia acts trivially, so the coboundary vanishes.
      have h_fix : M.ρ g = 1 := hu g ⟨v, fun h ↦ hv (.inl h), B, hB, hg⟩
      simp [← cob (.inl ⟨B, hB.valuation_natCast_lt_one_iff.2 hq⟩) g
        (congrArg Sum.inl (Subtype.ext hg.1)), h_fix]
    · exact h_inertia g ((s.mem_inertia_iff g).2 ⟨v, hq, fun h ↦ hv (.inr h), B, hB, hg⟩)
  · -- At `v ∈ S` it is a coboundary.
    exact hL v hv ⟨P.1 (.inl ⟨A v, (hA v).valuation_natCast_lt_one_iff.2 (hS v hv)⟩),
      funext fun ⟨g, hg⟩ ↦ cob _ g (congrArg Sum.inl (Subtype.ext hg))⟩
  · -- A complex conjugation fixes an infinite place and acts trivially.
    have c_fix : c • InfinitePlace.mk j = .mk j :=
      (mem_stabilizer_mk_iff ..).2 (.inr (RingHom.ext hj).symm)
    simp [← cob (.inr (.mk j)) c (congrArg Sum.inr c_fix), hcM ⟨j, hj⟩]

/-- Counting relations. Here `s` gives distinct primes `s.v i` of `K` not dividing `q`, each with a
place above it whose Frobenius lies in `U`; `U` fixes the `m`-th roots of unity, `m ∣ q`, and `I` is
the union of inertia groups above the other primes not dividing `q`. Let `M` be unramified outside
`S`, let complex conjugations act trivially on `M`, let `A v` lie over `v`, and let `L v` contain
the local coboundaries for `v ∈ S`. Assume that `q` lies in every prime of `S`, that at most
`#M ^ (#ι + 1)` cocycles zero on `I` are trivialised above `q` and infinity, and that the Selmer
cocycles without extra ramification lie among those that may ramify at the `s.v i` and vanish at all
`γ i`. Then the number of families `n` of maps into `QZ` (ℚ/ℤ) with `∑ i, n i (x (γ i)) = 0` for all
Selmer cocycles `x` that may ramify at the `s.v i`, times `#M` and the orders of the groups of local
cocycles in `L v`, `v ∈ S`, is at least `#M ^ (#S + #(infinite places of K))` times the number of
Selmer cocycles without extra ramification. -/
lemma card_relations_ge (hu : ∀ g ∈ inertiaAbove (S : Set (FinPlace K))ᶜ, M.ρ g = 1)
    (hA : ∀ v : FinPlace K, IsPlaceOver (A v) v)
    (L : ∀ v : FinPlace K, Submodule R (decompGroup Gal(Ω/K) (A v) → M))
    (hL : ∀ v ∈ S, (coboundaryMap (M.restrictTo (decompGroup Gal(Ω/K) (A v))).ρ).range ≤ L v)
    (hcM : ∀ {c : Gal(Ω/K)}, IsComplexConj c → M.ρ c = 1) {m : ℕ} [NeZero m] [Finite M]
    {q : ℕ} {U : OpenNormalSubgroup Gal(Ω/K)} {I : Set Gal(Ω/K)}
    {ι : Type} [NeZero q] [Fintype ι] (s : SplitPlaces m q I U ι) (γ : ι → Gal(Ω/K))
    (hS : ∀ v ∈ S, ↑q ∈ v.1) (h_few : M.HasFewCocycles (PlaceAboveLevel q) I (card ι + 1))
    (h_le : selmerZ1 M S A L ∅ ≤ selmerZ1 M S A L (range s.v))
    (h_zero : ∀ x ∈ selmerZ1 M S A L ∅, ∀ i : ι, x (γ i) = 0) :
    Nat.card (selmerZ1 M S A L ∅) * Nat.card M ^ (#S + card (InfinitePlace K)) ≤
      Nat.card {n : ι → M →+ QZ | ∀ x ∈ selmerZ1 M S A L (range s.v), ∑ i : ι, n i (x (γ i)) = 0} *
        Nat.card M *
        ∏ v ∈ S, Nat.card ↥(L v ⊓ Z1 (M.restrictTo (decompGroup Gal(Ω/K) (A v))).ρ) := by
  -- The relations form the annihilator of `Z` under the pairing `(x, n) ↦ ∑ i, n i (x (γ i))`,
  -- whose left kernel contains `selmerZ1 M S A L ∅`. Counting the annihilator gives `perp`, and
  -- `card_mul_pow_le` bounds `#Z` because there are few trivialised cocycles.
  let pair : (Gal(Ω/K) → M) →+ (ι → M →+ QZ) →+ QZ :=
    ∑ i : ι, (evalAddMonoidHom _ i).flip.comp (evalAddMonoidHom _ (γ i))
  set Z : AddSubgroup (Gal(Ω/K) → M) := (selmerZ1 M S A L (range s.v)).toAddSubgroup
  set ann : ℕ :=
    Nat.card {n : ι → M →+ QZ | ∀ x ∈ selmerZ1 M S A L (range s.v), ∑ i, n i (x (γ i)) = 0}
  set loc : ℕ := ∏ v ∈ S, Nat.card ↥(L v ⊓ Z1 (M.restrictTo (decompGroup Gal(Ω/K) (A v))).ρ)
  have ker_ge : Nat.card (selmerZ1 M S A L ∅) ≤ Nat.card ↥(pair.ker ⊓ Z) := by
    have ker_finite : (↑(pair.ker ⊓ Z) : Set (Gal(Ω/K) → M)).Finite :=
      (finite_unramified_cocycles M (S.finite_toSet.union (finite_range s.v))).subset
        fun _ ⟨_, h_unr, _⟩ ↦ h_unr
    refine Nat.card_mono (s := selmerZ1 M S A L ∅) ker_finite fun x hx ↦ ⟨?_, h_le hx⟩
    ext
    simp [pair, h_zero x hx]
  have perp : ann * Nat.card Z = Nat.card M ^ card ι * Nat.card ↥(pair.ker ⊓ Z) := by
    have ann_eq : ann = Nat.card (pairingAnnihilator pair Z) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun n ↦ by
        simp [pair, Z, pairingAnnihilator, ← SetLike.mem_coe, AddSubgroup.coe_copy])
    rw [ann_eq, card_pairingAnnihilator_mul_card pair (.refl _) Z]
    simp [Nat.card_pi]
  have Z_le : Nat.card Z * Nat.card M ^ (#S + card (InfinitePlace K)) ≤
      Nat.card M ^ (card ι + 1) * loc := card_mul_pow_le hu hA L hL hcM s h_few hS
  refine Nat.le_of_mul_le_mul_left ?_ (pow_pos (Nat.card_pos (α := M)) (card ι))
  calc
    Nat.card M ^ card ι *
          (Nat.card (selmerZ1 M S A L ∅) * Nat.card M ^ (#S + card (InfinitePlace K)))
      ≤ ann * (Nat.card Z * Nat.card M ^ (#S + card (InfinitePlace K))) := by
        rw [← mul_assoc, ← mul_assoc, perp]
        gcongr
    _ ≤ ann * (Nat.card M ^ (card ι + 1) * loc) := by gcongr
    _ = Nat.card M ^ card ι * (ann * Nat.card M * loc) := by ring

end New.selmerZ1
