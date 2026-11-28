import Lib.ClassField.Global.NormTheorems

/-!
# Kummer characters, power indices and the existence theorem for totally complex fields

This file proves the existence theorem of class field theory for a totally complex number field `K`:
a continuous homomorphism from the finite ideles of `K` to a `T₁` group that is trivial on `Kˣ`
factors through the Artin map. The proof uses Kummer theory when `K` contains the `n`-th roots of
unity; otherwise it passes to a cyclic extension of `K` inside `K(μ_n)` and composes with the norm.

`Γ` is the Galois group of `Ω/K`, where `Ω` is the fixed algebraic closure of `ℚ`.
`New.idelesPowAt S n` is the group of finite ideles that are `n`-th powers at the places of `S`.

* `New.exists_comp_artinMap`: the existence theorem.
* `New.exists_kummer_chars`: Kummer characters, and the ideles killed by those of the `S`-units.
* `New.index_pow_local_le`, `New.index_idelesPowAt_ne_zero_and_le`: bounds on the index of local
  `n`-th powers.
* `New.QZChar.eq_zero_of_unramified_off`, `New.sum_ord_smul_frob_eq_zero`: consequences of the
  product formula for `New.artinMap`.
* `New.OddPart.exists_detecting_points_hom`: finitely many points of `Γ` that detect the characters
  killed by `m` and unramified off `S`.

Notions from other files:
* `New.artinMap`: the global Artin map from the finite ideles of `K` to the topological
  abelianisation of `Γ`.
* `New.QZChar.abelianLift`: the homomorphism that a character χ of Γ induces on Γ^ab, with values in
  ℚ/ℤ written multiplicatively.
* `New.idelesUnitOff S`: the finite ideles whose components at the finite places outside `S` are
  units.
* `New.cyclotomicCharMod`: the cyclotomic character Γ → (ℤ/n)^×; it is trivial iff Γ fixes μ_n.

## Relation to the literature

Known; see `Lib.ClassField.Global.AlbertBrauerHasseNoether` for sources.
-/

namespace New

open NumberField QuotientGroup Subgroup Set QZChar Cohomology Function QZ DiscreteUnits NeZero
  Module Nat Pi Fact

attribute [local instance low] Fintype.ofFinite

section

variable {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [NumberField K] (n : ℕ) [NeZero n]
  (S : Set (FinPlace K))
  {L M : Type*} [Field L] [NumberField L] [Algebra K L] [Field M] [NumberField M]

/-- The norm maps of finite adeles compose along a tower `K ⊆ L ⊆ M`: the norm from `M` to `L`
followed by the norm from `L` to `K` is the norm from `M` to `K`. -/
@[simp]
lemma adeleNorm_adeleNorm [Algebra K M] [Algebra L M] [IsScalarTower K L M] :
    ∀ y : 𝔸f M, adeleNorm K L (adeleNorm L M y) = adeleNorm K M y := by
  -- Both sides are continuous and agree on the dense image of `M`, by the tower law for norms.
  exact denseRange_algebraMap_finAdele.eq fun x ↦ by simp [Algebra.norm_norm]

/-- For a set `S` of finite places of `K`, the group of finite ideles of `K` whose components at
all places of `S` are `n`-th powers. -/
noncomputable abbrev idelesPowAt (n : ℕ) : Subgroup (𝔸f K)ˣ :=
  ⨅ v : S, (powMonoidHom n).range.comap (ideleAt v.val)

lemma idelesPowAt_one : idelesPowAt S 1 = ⊤ :=
  eq_top_iff.2 fun x _ ↦ mem_iInf.2 fun v ↦ ⟨ideleAt v.val x, pow_one _⟩

/-- The component at `v` of the principal idele of `x ∈ Kˣ` is the image of `x` in `K_v`. -/
lemma val_ideleAt_principalIdele (v : FinPlace K) (x : Kˣ) :
    ((ideleAt v (principalIdele x) : (LocField v)ˣ) : LocField v) = algebraMap K (LocField v) x :=
  rfl

/-- As a rational number, the index `New.cokerKerIndex` of multiplication by `n` on `Additive Y` is
`[Y : Y ^ n] / #Y[n]`. -/
private lemma cokerKerIndex_natCast_eq_index_range_powMonoidHom_div {Y : Type} [CommGroup Y]
    (n : ℕ) :
    cokerKerIndex (n : End ℤ (Additive Y)) =
      ((powMonoidHom n : Y →* Y).range.index : ℚ) / Nat.card (powMonoidHom n : Y →* Y).ker :=
  rfl

/-- Let `Y` be a commutative group and let `q = #(Y / Y ^ n) / #Y[n]` be the index
(`New.cokerKerIndex`) of multiplication by `n` on `Y` written additively. If `q ≠ 0` and `q = t`,
then the `n`-th powers have finite index `t * #Y[n]` in `Y`. -/
lemma index_range_pow_eq {Y : Type} [CommGroup Y] {n t : ℕ}
    (h_coker :
      let q := cokerKerIndex (n : End ℤ (Additive Y))
      q ≠ 0 ∧ q = t) :
    let f := (powMonoidHom n : Y →* Y)
    f.range.index ≠ 0 ∧ f.range.index = t * Nat.card f.ker := by
  intro f
  obtain ⟨h_coker_ne, h_coker_eq⟩ := h_coker
  rw [cokerKerIndex_natCast_eq_index_range_powMonoidHom_div] at h_coker_ne h_coker_eq
  obtain ⟨h_index_ne, h_ker_ne⟩ := div_ne_zero_iff.1 h_coker_ne
  exact ⟨Nat.cast_ne_zero.1 h_index_ne, mod_cast (div_eq_iff h_ker_ne).1 h_coker_eq⟩

/-! ### Indices of local powers -/

/-- Let `n ≠ 0` and let `v` be a finite place of `K`, with completion `LocField v`. The `n`-th
powers have finite index in `(LocField v)ˣ`, at most `n ^ 2` times the absolute norm of `v ^ a`,
where `a` is the multiplicity of `v` in the ideal `(n)`; that is, at most `n ^ 2 / |n|_v`. -/
lemma index_pow_local_le (v : FinPlace K) :
    let i := (powMonoidHom n : (LocField v)ˣ →* (LocField v)ˣ).range.index
    i ≠ 0 ∧ i ≤ n ^ 2 * (v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {(n : 𝓞 K)})).absNorm := by
  -- View `K_v` as a local field inside `ℚ̄_p`, with integers `O`. The index of the `n`-th powers is
  -- `n * #(O / n)` times the number of `n`-th roots of unity, which is at most `n`
  -- (`cokerKerIndex_local_units`).
  let algebra_K_Ω : Algebra K Ω := (Ω.fieldEmb K).toAlgebra
  obtain ⟨p, hp_prime, h_alg, _j, ⟨hF⟩⟩ : ∃ (p : ℕ) (_ : Fact p.Prime)
      (_ : Algebra (LocField v) (PadicAlgCl p)) (j : Ω →+* PadicAlgCl p),
      Nonempty (IsCompletionEmb v p Gal(Ω/K) (placeOver v) j) :=
    v.isPlaceOver_placeOver.exists_isCompletionEmb Gal(Ω/K)
  set a : ℕ := multiplicity v.asIdeal (Ideal.span {(n : 𝓞 K)})
  -- `n` has the valuation of `π ^ a` for a uniformiser `π`, so `#(O / n) = q ^ a = N(v ^ a)`.
  have h_val :
      (intQpBar p).valuation
          (algebraMap (LocField v) (PadicAlgCl p)
            ((n : valRingBelow (LocField v) (intQpBar p)) : LocField v)) =
        (intQpBar p).valuation
          (algebraMap (LocField v) (PadicAlgCl p) (uniformizer v : LocField v)) ^ a := by
    -- The valuation of `ℚ̄_p` restricts to one on `K_v` with the same valuation ring as `v`.
    have h_equiv : ((intQpBar p).valuation.comap (algebraMap (LocField v) (PadicAlgCl p))).IsEquiv
        (Valued.v : Valuation (LocField v) _) :=
      (Valuation.isEquiv_iff_valuationSubring _ _).mpr hF.valRingBelow_eq
    rw [← map_pow, ← map_pow, ← Valuation.comap_apply, ← Valuation.comap_apply, h_equiv.eq_iff]
    simpa [v.intValuation_eq_exp_neg_multiplicity, NeZero.ne n] using
      v_algebraMap_eq_intValuation (w := v) n
  have h_card :
      (v.asIdeal ^ a).absNorm =
        Nat.card (valRingBelow (LocField v) (intQpBar p) ⧸
          Ideal.span {(n : valRingBelow (LocField v) (intQpBar p))}) := by
    rw [map_pow, ← FinPlace.q, ← hF.residueCard_eq,
      (hF.isUniformiser_iff.2 (v_uniformizer v)).card_quotient_span_eq_pow hF.toIsLocalGalois _
        h_val]
  rw [h_card, sq, mul_right_comm]
  intro i
  -- `[K_v^× : K_v^× ^ n] = n * #(O / n) * #μ_n(K_v)`, and `#μ_n(K_v) ≤ n`.
  obtain ⟨h_index_ne, h_index_eq⟩ :
      i ≠ 0 ∧
        i = n * Nat.card (valRingBelow (LocField v) (intQpBar p) ⧸
            Ideal.span {(n : valRingBelow (LocField v) (intQpBar p))}) *
          Nat.card (powMonoidHom n : (LocField v)ˣ →* (LocField v)ˣ).ker :=
    index_range_pow_eq
      (mod_cast cokerKerIndex_local_units hF.toIsLocalGalois n (AddEquiv.refl _))
  have h_roots_le :
      Nat.card (powMonoidHom n : (LocField v)ˣ →* (LocField v)ˣ).ker ≤ n :=
    card_rootsOfUnity (LocField v) n
  exact ⟨h_index_ne, h_index_eq.trans_le (mul_right_mono h_roots_le)⟩

/-- For `n ≠ 0` and a finite set `S` of finite places of `K`, the ideles that are `n`-th powers at
the places of `S` have finite index, at most `n ^ (2 |S| + [K : ℚ])`. -/
lemma index_idelesPowAt_ne_zero_and_le [Fintype S] :
    (idelesPowAt S n).index ≠ 0 ∧
      (idelesPowAt S n).index ≤ n ^ (2 * S.ncard + finrank ℚ K) := by
  have h_index_comap (v : FinPlace K) (H : Subgroup (LocField v)ˣ) :
      (H.comap (ideleAt v)).index = H.index :=
    index_comap_of_surjective _ fun x ↦ ⟨locIdele v x, ideleAt_locIdele v x⟩
  refine ⟨index_iInf_ne_zero fun v ↦
    (h_index_comap v.val _).trans_ne (index_pow_local_le n v.val).left, ?_⟩
  -- Multiply the bounds `n ^ 2 * N(v-part of (n))` of `index_pow_local_le`. The `v`-parts of
  -- `(n)` are coprime, so their product divides `(n)`, of norm `n ^ [K : ℚ]`.
  have h_dvd : ∏ v : S, v.val.asIdeal ^ multiplicity v.val.asIdeal (Ideal.span {(n : 𝓞 K)}) ∣
      Ideal.span {(n : 𝓞 K)} :=
    Fintype.prod_dvd_of_coprime
      (fun v w h_ne ↦ (v.val.isCoprime_of_ne w.val (Subtype.val_injective.ne h_ne)).pow)
      fun v ↦ pow_multiplicity_dvd v.val.asIdeal _
  have h_norm : (Ideal.span {(n : 𝓞 K)}).absNorm = n ^ finrank ℚ K := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  calc (idelesPowAt S n).index
      ≤ ∏ v : S, n ^ 2 *
          (v.val.asIdeal ^ multiplicity v.val.asIdeal (Ideal.span {(n : 𝓞 K)})).absNorm := by
        grw [index_iInf_le, (h_index_comap _ _).le, (index_pow_local_le n _).right]
    _ = (n ^ 2) ^ S.ncard * (∏ v : S,
          v.val.asIdeal ^ multiplicity v.val.asIdeal (Ideal.span {(n : 𝓞 K)})).absNorm := by
        simp [Finset.prod_mul_distrib]
    _ ≤ (n ^ 2) ^ S.ncard * n ^ finrank ℚ K := by
        grw [Nat.le_of_dvd (by simp [h_norm, pos]) (map_dvd Ideal.absNorm h_dvd), h_norm]
    _ = n ^ (2 * S.ncard + finrank ℚ K) := by rw [pow_add, pow_mul]

variable {n} [Algebra K Ω] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]

/-! ### Characters with prescribed local behaviour -/

/-- Let `Γ` be the Galois group of `Ω/K`, where `Ω` is the fixed algebraic closure of `ℚ`, let `n`
be any natural number (zero is allowed) and let `S` be a set of finite places of `K`. For a finite
place `w`, `placeOver w` is the chosen place of `Ω` over `w`. Let the character `χ` of `Γ` vanish on
the complex conjugations and on the inertia groups at `placeOver w` for `w ∉ S`, and let `n • χ`
vanish on the decomposition groups at `placeOver w` for `w ∈ S`. Then `χ` composed with the Artin
map (through `abelianLift`) kills the principal ideles and the ideles that are `n`-th powers at `S`
and units off `S`. -/
lemma QZChar.sup_le_ker_abelianLift_artinMap (n : ℕ) (χ : QZChar Γ)
    (h_conj : ∀ c : Γ, IsComplexConj c → χ.val c = 0)
    (h_decomp : ∀ w ∈ S, ∀ g ∈ decompGroup Γ (placeOver w), n • χ.val g = 0)
    (h_inertia : ∀ w ∉ S, ∀ g ∈ inertiaGroup Γ (placeOver w), χ.val g = 0) :
    principalIdele.range ⊔ idelesPowAt S n ⊓ idelesUnitOff S ≤
      (abelianLift χ).ker.comap (artinMap Γ) := by
  refine sup_le ?_ ?_
  · -- Principal ideles are killed by Artin reciprocity, as `χ` kills the complex conjugations.
    exact forall_mem_range.2 fun x ↦ abelianLift_artinMap_principalIdele_eq_one χ x h_conj
  · rintro a ⟨h_pow, h_unit⟩
    -- Every local factor of `χ (artinMap a)` is trivial.
    rw [mem_comap, MonoidHom.mem_ker, abelianLift_artinMap_eq_finprod]
    refine finprod_eq_one_of_forall_eq_one fun v ↦ ?_
    by_cases hvS : v ∈ S
    · -- At `S`, `a_v = b ^ n` and the symbol of `b` is a value `χ g` on the decomposition group.
      obtain ⟨b, hb⟩ : ∃ b : (LocField v)ˣ, b ^ n = ideleAt v a := mem_iInf.1 h_pow ⟨v, hvS⟩
      obtain ⟨g, hg_decomp, hgb⟩ : ∃ g ∈ decompGroup Γ (placeOver v),
          toHom χ g = abelianLift χ (artinAt Γ v b) :=
        (v.isPlaceOver_placeOver.range_abelianLift_comp_artinAt χ).le ⟨b, rfl⟩
      calc abelianLift χ (artinAt Γ v (ideleAt v a)) = toHom χ g ^ n := by
            rw [← hb, map_pow, map_pow, hgb]
        _ = 1 := by rw [QZChar.toHom_apply, ← ofAdd_nsmul, h_decomp v hvS g hg_decomp, ofAdd_zero]
    · -- Off `S`, `a_v` is a unit and `χ` is unramified.
      exact (v.isPlaceOver_placeOver.artinAt_units_trivial_iff_inertiaGroup_le χ).2
        (h_inertia v hvS) _
        (mem_idelesUnitOff.1 h_unit v hvS)

/-- Let `S` be a set of finite places of `K` such that `Kˣ` and the ideles that are units outside
`S` generate the finite ideles. Let `z` be a continuous 1-cocycle of `Γ` with values in a discrete
abelian group `V` with trivial action, that is, a continuous homomorphism. If `z` vanishes on the
complex conjugations, on the decomposition groups at `placeOver w` for `w ∈ S` and on the inertia
groups at `placeOver w` for `w ∉ S`, then `z` is zero. -/
lemma QZChar.eq_zero_of_unramified_off (h_gen : principalIdele.range ⊔ idelesUnitOff S = ⊤)
    {V : Type*} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V]
    (z : Z1 (Representation.trivial ℤ Γ V))
    (h_conj : ∀ c : Γ, IsComplexConj c → z.val c = 0)
    (h_decomp : ∀ w ∈ S, ∀ g ∈ decompGroup Γ (placeOver w), z.val g = 0)
    (h_inertia : ∀ w ∉ S, ∀ g ∈ inertiaGroup Γ (placeOver w), z.val g = 0) (g : Γ) :
    z.val g = 0 := by
  -- Test `z g` against every `u : V →+ ℚ/ℤ`. The character `χ = u ∘ z` kills all Artin symbols by
  -- `sup_le_ker_abelianLift_artinMap` with `n = 1`, and `artinMap` is onto.
  refine eq_zero_of_forall_hom_eq_zero fun u ↦ ?_
  obtain ⟨hz_cont, hz_add⟩ := z.property
  let χ : QZChar Γ := ⟨u ∘ z.val, by fun_prop, fun g h ↦ by simp [hz_add]⟩
  have hχ_apply (g : Γ) : χ.val g = u (z.val g) := rfl
  obtain ⟨a, ha⟩ : ∃ a : (𝔸f K)ˣ, artinMap Γ a = g := artinMap_surjective Γ g
  have h_le : principalIdele.range ⊔ idelesPowAt S 1 ⊓ idelesUnitOff S ≤
      (abelianLift χ).ker.comap (artinMap Γ) :=
    sup_le_ker_abelianLift_artinMap S 1 χ (fun c hc ↦ by simp [hχ_apply, h_conj c hc])
      (fun w hw g hg ↦ by simp [hχ_apply, h_decomp w hw g hg])
      (fun w hw g hg ↦ by simp [hχ_apply, h_inertia w hw g hg])
  -- Every idele is a first power at `S`.
  rw [idelesPowAt_one, top_inf_eq, h_gen] at h_le
  simpa [ha, hχ_apply] using h_le (mem_top a)

/-- Artin's law for the symbol `(χ, x)`, read on valuations. Let `χ` be killed by `n` and kill the
Artin symbol of `x ∈ Kˣ`; let the `w j` be distinct, and `s j` a Frobenius at a place `A j` over
`w j` where `χ` is unramified. If at every other finite place `v` either (a) the local symbol of `x`
is trivial, or (b) `x / r ^ n` is a unit at `placeOver v` for some `r ∈ Ωˣ` fixed by inertia there
and `χ` is unramified at `v`, then `∑ j, ord_{w j} x • χ (s j) = 0`, where
`ord_w x = -log (w.valuation K x)`. -/
lemma sum_ord_smul_frob_eq_zero {n : ℕ} {χ : QZChar Γ} (hχ_tors : n • χ = 0) {x : Kˣ}
    (h_art : abelianLift χ (artinMap Γ (principalIdele x)) = 1)
    {J : Type*} [Fintype J] {w : J → FinPlace K} (hw : Injective w)
    {A : J → ClosurePlace} (hA : ∀ j : J, IsPlaceOver (A j) (w j))
    {s : J → Γ} (hs : ∀ j : J, IsFrob (A j) (w j).q (s j))
    (hχ_unram : ∀ j : J, inertiaGroup Γ (A j) ≤ ker χ)
    (h_rest : ∀ v ∉ range w,
      abelianLift χ (artinAt Γ v (ideleAt v (principalIdele x))) = 1 ∨
      (∃ r : DiscreteUnits Ω,
        placeOver v ((ofBase Γ Ω (Additive.ofMul x)).val - n • r).toMul.val = 1 ∧
          ∀ g ∈ inertiaGroup Γ (placeOver v), unitsRep g r = r) ∧
        inertiaGroup Γ (placeOver v) ≤ ker χ) :
    ∑ j : J, -((w j).valuation K x).log • χ.val (s j) = 0 := by
  have h_nχ (g : Γ) : n • χ.val g = 0 := by
    simpa using congr_arg (fun ψ : QZChar Γ ↦ ψ.val g) hχ_tors
  -- In the product formula for `χ (artinMap x)` the factors off the `w j` are trivial.
  have h_off (v : FinPlace K) (hv : v ∉ range w) :
      abelianLift χ (artinAt Γ v (ideleAt v (principalIdele x))) = 1 := by
    rcases h_rest v hv with h_triv | ⟨⟨r, h_unit, hr_fixed⟩, h_unram⟩
    · exact h_triv
    · -- `r` has an integer order `k`, so `ord_v x = n * k`, and `n • χ = 0`.
      have hP : IsPlaceOver (placeOver v) v := v.isPlaceOver_placeOver
      obtain ⟨k, hk⟩ : ∃ k : ℤ, ordRat K (placeOver v) r = k :=
        hP.exists_ordRat_eq_intCast hr_fixed
      obtain ⟨F, hF⟩ : ∃ F : Γ, IsFrob (placeOver v) v.q F := hP.exists_isFrob Γ
      have h_ord : -(v.valuation K x).log = n * k := by
        have h_ord_zero :
            ordRat K (placeOver v) ((ofBase Γ Ω (Additive.ofMul x)).val - n • r) = 0 :=
          hP.ordRat_eq_zero_iff.2 h_unit
        rw [map_sub, map_nsmul, hP.ordRat_ofBase, hk, sub_eq_zero, nsmul_eq_mul] at h_ord_zero
        exact_mod_cast h_ord_zero
      calc abelianLift χ (artinAt Γ v (ideleAt v (principalIdele x)))
          = Multiplicative.ofAdd (-((n * k : ℤ) • χ.val F)) := by
            rw [hP.abelianLift_artinAt_of_inertiaGroup_le_ker χ h_unram hF, ← h_ord, neg_smul,
              neg_neg]
        _ = 1 := by simp [mul_zsmul', h_nχ F]
  have h_support : mulSupport (fun v ↦ abelianLift χ (artinAt Γ v (ideleAt v (principalIdele x))))
      ⊆ ↑(Finset.univ.map ⟨w, hw⟩) :=
    mulSupport_subset_iff'.2 fun v hv ↦ h_off v (by simpa using hv)
  rw [abelianLift_artinMap_eq_finprod, finprod_eq_prod_of_mulSupport_subset _ h_support] at h_art
  -- The factor at `w j` is the inverse of the `j`-th term, as `χ` is unramified there
  -- (uniformisers go to geometric Frobenii).
  have h_factor (j : J) :
      abelianLift χ (artinAt Γ (w j) (ideleAt (w j) (principalIdele x))) =
        Multiplicative.ofAdd (((w j).valuation K x).log • χ.val (s j)) :=
    (hA j).abelianLift_artinAt_of_inertiaGroup_le_ker χ (hχ_unram j) (hs j) x
  have h_prod :
      ∏ j : J, Multiplicative.ofAdd (((w j).valuation K x).log • χ.val (s j)) = 1 := by
    simpa [h_factor] using h_art
  simpa only [neg_smul, Finset.sum_neg_distrib, neg_eq_zero, ← ofAdd_sum, ofAdd_eq_one] using h_prod

/-- Let `x ∈ Kˣ` be an `n`-th power in `K_v`. An element of the decomposition group at a place above
`v` that fixes the `n`-th roots of unity fixes every `n`-th root of `x`. -/
lemma IsPlaceOver.smul_root_eq_of_local_pow {A : ClosurePlace} {v : FinPlace K}
    (h_over : IsPlaceOver A v) {x : Kˣ}
    (hx_pow : ideleAt v (principalIdele x) ∈ (powMonoidHom n).range)
    {r : Ω} (hr : r ^ n = algebraMap K Ω x) (g : Γ) (hg : g ∈ decompGroup Γ A)
    (h_fix : cyclotomicCharMod Ω n g = 1) : g • r = r := by
  -- Embed `Ω` by `j` into `ℚ̄_p`. If `x = z ^ n` in `K_v`, then `j r / z` is an `n`-th root of
  -- unity; `g` fixes it, and fixes `z`.
  obtain ⟨z, hzx⟩ : ∃ z : (LocField v)ˣ, z ^ n = ideleAt v (principalIdele x) := hx_pow
  obtain ⟨p, hp_prime, h_alg, j, ⟨hj⟩⟩ : ∃ (p : ℕ) (_ : Fact p.Prime)
      (_ : Algebra (LocField v) (PadicAlgCl p)) (j : Ω →+* PadicAlgCl p),
      Nonempty (IsCompletionEmb v p Γ A j) :=
    h_over.exists_isCompletionEmb Γ
  have h_cyc : cyclotomicCharMod (PadicAlgCl p) n (⟨g, hg⟩ : decompGroup Γ A) = 1 :=
    (cyclotomicCharMod_eq_of_equivariant (hj.equivariant ⟨g, hg⟩)).symm.trans h_fix
  have h_fix_roots :
      ∀ ζ : PadicAlgCl p, ζ ^ n = 1 → (⟨g, hg⟩ : decompGroup Γ A) • ζ = ζ ^ 1 := by
    rwa [← Units.val_eq_one, ← cast_one, cyclotomicCharMod_eq_iff] at h_cyc
  have hz_val : (z : LocField v) ^ n = algebraMap K (LocField v) x := by
    simp [← val_ideleAt_principalIdele, ← hzx]
  have h_root : (j r / algebraMap (LocField v) (PadicAlgCl p) z) ^ n = 1 := by
    rw [div_pow, ← map_pow j, hr, ← map_pow (algebraMap (LocField v) (PadicAlgCl p)), hz_val,
      ← hj.map_algebraMap]
    exact div_self (by simp)
  have h_jr : j (g • r) = j r := by
    simpa [smul_div₀', ← hj.equivariant] using h_fix_roots _ h_root
  exact j.injective h_jr

omit [Algebra K Ω] in
/-- Let `K` be totally complex and let `S` be a finite set of places such that `Kˣ` and the ideles
that are units outside `S` generate the finite ideles. Let `E` be the group of `S`-units. Suppose
that every element of `E` that is an `n`-th power at each place of `S` lies in `E ^ n`, and that
`n` divides the number of `n`-th roots of unity in `E`. Then the subgroup generated by `Kˣ` and the
ideles that are `n`-th powers at `S` and units elsewhere has finite index, at most `[E : E ^ n]`. -/
lemma index_sup_idelesPowAt_le [IsTotallyComplex K] {S : Set (FinPlace K)} (hS_fin : S.Finite)
    (h_gen : principalIdele.range ⊔ idelesUnitOff S = ⊤)
    (h_loc : ((idelesPowAt S n).comap principalIdele).subgroupOf (S.unit K) ≤
      (powMonoidHom n : S.unit K →* S.unit K).range)
    (h_tors : n ∣ Nat.card (powMonoidHom n : S.unit K →* S.unit K).ker) :
    (principalIdele.range ⊔ idelesPowAt S n ⊓ idelesUnitOff S).index ≠ 0 ∧
      (principalIdele.range ⊔ idelesPowAt S n ⊓ idelesUnitOff S).index ≤
        (powMonoidHom n : S.unit K →* S.unit K).range.index := by
  -- Idea: `G₀.index * [E : E ^ n]` divides `N.index`, which is at most `[E : E ^ n] ^ 2`.
  set N : Subgroup (𝔸f K)ˣ := idelesPowAt S n
  set G₀ : Subgroup (𝔸f K)ˣ := principalIdele.range ⊔ N ⊓ idelesUnitOff S
  set En : Subgroup (S.unit K) := (powMonoidHom n : S.unit K →* S.unit K).range
  let hS_fintype : Fintype S := hS_fin.fintype
  obtain ⟨hN, hN_le⟩ := index_idelesPowAt_ne_zero_and_le n S
  -- `G₀.index` times the index in `E` of the local powers is the index of `N` in `idelesUnitOff S`
  -- (`relIndex_mul_index_sup`); `En.index` divides that index in `E` by `h_loc`.
  have h_dvd : En.index * G₀.index ∣ N.index := calc
    En.index * G₀.index ∣ (N.comap principalIdele).relIndex (S.unit K) * G₀.index :=
      mul_dvd_mul_right (index_dvd_of_le h_loc) _
    _ = N.relIndex (idelesUnitOff S) :=
      relIndex_mul_index_sup h_gen principalIdele_mem_idelesUnitOff
    _ ∣ N.index := relIndex_dvd_index_of_normal N (idelesUnitOff S)
  -- Dirichlet: `E` is finitely generated, and `rank E + 1 = |S| + #(infinite places)`.
  obtain ⟨hE_fg, h_rank⟩ : Module.Finite ℤ (Additive (S.unit K)) ∧
      finrank ℤ (Additive (S.unit K)) + 1 = S.ncard + Fintype.card (InfinitePlace K) :=
    SUnit.dirichlet_unit_theorem hS_fin
  -- `[E : E ^ n] = n ^ rank E * #E[n]`.
  obtain ⟨hEn, hEn_eq⟩ : En.index ≠ 0 ∧ En.index =
      n ^ finrank ℤ (Additive (S.unit K)) * Nat.card (powMonoidHom n : S.unit K →* S.unit K).ker :=
    index_range_pow_eq (Y := S.unit K) (mod_cast cokerKerIndex_eq_pow_finrank)
  -- As `K` is totally complex, `2 |S| + [K : ℚ] = 2 (rank E + 1)`, so `N.index ≤ En.index ^ 2`.
  have h_deg : finrank ℚ K = 2 * Fintype.card (InfinitePlace K) := by
    simp [← InfinitePlace.sum_mult_eq, mul_comm]
  have h_sq : N.index ≤ En.index ^ 2 :=
    calc N.index ≤ n ^ (2 * S.ncard + finrank ℚ K) := hN_le
      _ = (n ^ finrank ℤ (Additive (S.unit K)) * n) ^ 2 := by
        rw [← pow_succ, ← pow_mul, h_deg]
        congr 1
        omega
      _ ≤ (n ^ finrank ℤ (Additive (S.unit K)) *
          Nat.card (powMonoidHom n : S.unit K →* S.unit K).ker) ^ 2 := by
        gcongr
        exact Nat.le_of_dvd (by lia) h_tors
      _ = En.index ^ 2 := by rw [hEn_eq]
  -- Cancel `En.index` in `En.index * G₀.index ≤ N.index ≤ En.index ^ 2`.
  have h_mul_le : En.index * G₀.index ≤ En.index * En.index :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h_dvd).trans (h_sq.trans_eq (sq En.index))
  exact ⟨right_ne_zero_of_mul (ne_zero_of_dvd_ne_zero hN h_dvd),
    Nat.le_of_mul_le_mul_left h_mul_le (Nat.pos_of_ne_zero hEn)⟩

/-- The map `a ↦ ζ ^ a` from `ℤ/n` to `Ωˣ` of `New.rootPowHom`, for the primitive `n`-th root of
unity `ζ` chosen there, is injective. -/
lemma rootPowHom_injective : Injective (rootPowHom Ω n).val := (rootPowHom Ω n).property.left

end

section Kummer

variable {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [NumberField K] {n : ℕ} [NeZero n]
  [Algebra K Ω] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]

variable (K) in
include K in
omit [NumberField K] in
/-- Let `Γ` be the Galois group of `Ω/K`, where `Ω` is the fixed algebraic closure of `ℚ`, and let
`Γ` fix the `n`-th roots of unity. Let `ζ` be the root of unity of order `n` chosen in
`New.rootPowHom`. There is an additive map `κ` from the invariants of `Ωˣ` to the characters
`Γ → ℤ/n` such that `ζ ^ κ x g = g a / a` whenever `a ^ n = x` (written additively in
`New.DiscreteUnits Ω`). -/
lemma exists_kummer_hom (h_fix : ∀ g : Γ, cyclotomicCharMod Ω n g = 1) :
    ∃ κ : (unitsRep : Representation ℤ Γ (DiscreteUnits Ω)).invariants →+
        Z1 (Representation.trivial ℤ Γ (ZMod n)),
      ∀ (x : (unitsRep : Representation ℤ Γ (DiscreteUnits Ω)).invariants) (a : DiscreteUnits Ω),
        n • a = ↑x → ∀ g : Γ, (rootPowHom Ω n).val ((κ x).val g) = unitsRep g a - a := by
  -- For each invariant `x`, choose an `n`-th root `root x` and the Kummer cocycle `κ₀ x`.
  choose root κ₀ h_root_pow h_kummer using exists_kummer_cocycle (K := K) h_fix
  -- `κ₀ x` may be computed from any root of `x`, and `root x + root y` is a root of `x + y`; so
  -- `κ₀` is additive.
  refine ⟨AddMonoidHom.mk' κ₀ fun x y ↦ ?_, h_kummer⟩
  have h_sum : n • (root x + root y) = ↑(x + y) := by simp [h_root_pow]
  ext g
  apply rootPowHom_injective
  calc (rootPowHom Ω n).val ((κ₀ (x + y)).val g)
      = unitsRep g (root x + root y) - (root x + root y) :=
        h_kummer (x + y) (root x + root y) h_sum g
    _ = (rootPowHom Ω n).val ((κ₀ x + κ₀ y).val g) := by
        simp [add_sub_add_comm, h_kummer x _ (h_root_pow x), h_kummer y _ (h_root_pow y)]

variable (K) in
/-- The Kummer map, when `Γ` fixes the `n`-th roots of unity. It sends an invariant `x` of `Ωˣ` to
the character `κ x : Γ → ℤ/n` with `ζ ^ κ x g = g a / a` for every `a` with `a ^ n = x`, where `ζ`
is the root of unity of order `n` chosen in `New.rootPowHom` (`New.rootPowHom_kummerChar`). -/
noncomputable def kummerChar (h_fix : ∀ g : Γ, cyclotomicCharMod Ω n g = 1) :
    (unitsRep : Representation ℤ Γ (DiscreteUnits Ω)).invariants →+
      Z1 (Representation.trivial ℤ Γ (ZMod n)) :=
  (exists_kummer_hom K h_fix).choose

omit [NumberField K] in
/-- The defining property of the Kummer character `κ = kummerChar K h_fix`: if `a ^ n = x`, then
`ζ ^ κ x g = g a / a`, where `ζ` is the root of unity of order `n` chosen in `New.rootPowHom`
(written additively in `New.DiscreteUnits Ω`). -/
lemma rootPowHom_kummerChar (h_fix : ∀ g : Γ, cyclotomicCharMod Ω n g = 1)
    (x : (unitsRep : Representation ℤ Γ (DiscreteUnits Ω)).invariants)
    (a : DiscreteUnits Ω) (ha : n • a = ↑x) (g : Γ) :
    (rootPowHom Ω n).val ((kummerChar K h_fix x).val g) = unitsRep g a - a :=
  (exists_kummer_hom K h_fix).choose_spec x a ha g

omit [NumberField K] in
/-- The Kummer character of `x` vanishes at `g` exactly when `g` fixes an `n`-th root of `x`. -/
lemma kummerChar_apply_eq_zero_iff (h_fix : ∀ g : Γ, cyclotomicCharMod Ω n g = 1)
    (x : (unitsRep : Representation ℤ Γ (DiscreteUnits Ω)).invariants) {a : DiscreteUnits Ω}
    (ha : n • a = ↑x) (g : Γ) : (kummerChar K h_fix x).val g = 0 ↔ unitsRep g a = a := by
  rw [← (rootPowHom_injective (n := n)).eq_iff, rootPowHom_kummerChar h_fix x a ha, map_zero,
    sub_eq_zero]

/-- A point lies in the kernel of a continuous character `χ` with values in `ℚ/ℤ` exactly when `χ`
vanishes there. -/
private lemma QZChar.mem_ker_iff_val_eq_zero {G : Type*} [Group G] [TopologicalSpace G]
    (χ : QZChar G) (g : G) : g ∈ ker χ ↔ χ.val g = 0 :=
  ofAdd_eq_one

omit [NumberField K] [NeZero n] in
/-- Let `x ∈ Kˣ` and let `r` be an `n`-th root of `x` in `Ωˣ` (both written additively). Then
`r ^ n = x` in `Ω`. -/
private lemma val_pow_eq_algebraMap_of_nsmul_eq_ofBase {x : Kˣ} {r : DiscreteUnits Ω}
    (hr : n • r = (ofBase Γ Ω (Additive.ofMul x)).val) :
    (r.toMul : Ω) ^ n = algebraMap K Ω x := by
  simpa [toMul_nsmul] using congrArg (fun z : DiscreteUnits Ω ↦ (z.toMul : Ω)) hr

/-- Let `Γ` fix the `n`-th roots of unity, and let `v` be a finite place of `K` at which `n` is a
unit. If `x ∈ Kˣ` is a unit at `v`, its Kummer character vanishes on the inertia group at the
chosen place `placeOver v` of `Ω` over `v`: inertia fixes an `n`-th root of `x`. -/
private lemma kummerChar_ofBase_apply_eq_zero_of_mem_inertiaGroup
    (h_fix : ∀ g : Γ, cyclotomicCharMod Ω n g = 1) {v : FinPlace K}
    (hn_unit : (n : 𝓞 K) ∉ v.asIdeal) {x : Kˣ} (hx_unit : v.valuation K (x : K) = 1) {g : Γ}
    (hg : g ∈ inertiaGroup Γ (placeOver v)) :
    (kummerChar K h_fix (ofBase Γ Ω (Additive.ofMul x))).val g = 0 := by
  obtain ⟨r, hr⟩ : ∃ r : DiscreteUnits Ω, n • r = (ofBase Γ Ω (Additive.ofMul x)).val :=
    exists_nsmul _ (NeZero.ne n)
  have h_place : IsPlaceOver (placeOver v) v := v.isPlaceOver_placeOver
  rw [kummerChar_apply_eq_zero_iff h_fix _ hr g, DiscreteUnits.ext_iff, val_unitsRep]
  exact inertia_fixes_root_of_unit hg (h_place.valuation_natCast_eq_one_iff.mpr hn_unit)
    (val_pow_eq_algebraMap_of_nsmul_eq_ofBase hr) (h_place.valuationVia_eq_one_iff.mpr hx_unit)
    (smul_algebraMap g (x : K))

/-- Let `S` be a set of finite places of `K` and `u` an `S`-unit (an element of `Kˣ` that is a unit
at each place outside `S`). A `Γ`-invariant `n`-th root `y` of `u` in `Ωˣ` (both written
additively) comes from an `S`-unit `x` with `x ^ n = u`. -/
private lemma exists_unit_pow_eq_of_nsmul_eq_ofBase {S : Set (FinPlace K)} {u : S.unit K}
    {y : (unitsRep : Representation ℤ Γ (DiscreteUnits Ω)).invariants}
    (hy : n • y = ofBase Γ Ω (Additive.ofMul (u : Kˣ))) :
    ∃ x : S.unit K, ofBase Γ Ω (Additive.ofMul (x : Kˣ)) = y ∧ x ^ n = u := by
  -- `y` comes from some `x ∈ Kˣ`, and `x ^ n = u` as `ofBase` is injective.
  obtain ⟨x, rfl⟩ : ∃ x : Additive Kˣ, ofBase Γ Ω x = y :=
    (ofBase_bijective (K := K) Γ).surjective y
  have h_nsmul : n • x = Additive.ofMul (u : Kˣ) :=
    (ofBase_bijective (K := K) Γ).injective ((map_nsmul (ofBase Γ Ω) n x).trans hy)
  have hx_pow : x.toMul ^ n = (u : Kˣ) := by rw [← toMul_nsmul, h_nsmul, toMul_ofMul]
  -- `x` is a unit outside `S`, as its `n`-th power is.
  have hx_unit (v : FinPlace K) (hv : v ∉ S) : v.valuation K (x.toMul : K) = 1 := by
    simpa [← hx_pow, NeZero.ne n] using S.unit_valuation_eq_one K u hv
  exact ⟨⟨x.toMul, hx_unit⟩, rfl, Subtype.ext hx_pow⟩

/-- Let `Γ`, the Galois group of `Ω/K` for the fixed algebraic closure `Ω` of `ℚ`, fix the `n`-th
roots of unity, and let `S` be a set of finite places of `K`. Then `n` divides the number of `n`-th
roots of unity among the `S`-units. -/
private lemma dvd_natCard_ker_powMonoidHom_of_cyclotomicCharMod_eq_one
    (h_fix : ∀ g : Γ, cyclotomicCharMod Ω n g = 1) (S : Set (FinPlace K)) :
    n ∣ Nat.card (powMonoidHom n : S.unit K →* S.unit K).ker := by
  -- The root of unity `ζ` of order `n` chosen in `rootPowHom` is `Γ`-invariant, so it is an
  -- `S`-unit `x` with `x ^ n = 1`. The order of the group of such `x` kills `x`, hence `ζ`.
  set ζ : DiscreteUnits Ω := (rootPowHom Ω n).val 1
  have hζ : IsPrimitiveRoot ζ.toMul n := isPrimitiveRoot_rootPowHom_one Ω n
  have hζ_nsmul : n • ζ = 0 := ((rootPowHom Ω n).property.right ζ).mp ⟨1, rfl⟩
  have hζ_inv : ζ ∈ (unitsRep : Representation ℤ Γ (DiscreteUnits Ω)).invariants :=
    (Representation.mem_invariants _ ζ).mpr fun g ↦
      cyclotomicCharMod_eq_one_iff.mp (h_fix g) ζ hζ_nsmul
  have hζ_root : n • (⟨ζ, hζ_inv⟩ : (unitsRep : Representation ℤ Γ (DiscreteUnits Ω)).invariants) =
      ofBase Γ Ω (Additive.ofMul ((1 : S.unit K) : Kˣ)) :=
    Subtype.ext (by simp [hζ_nsmul])
  obtain ⟨x, hx_eq, hx_pow⟩ := exists_unit_pow_eq_of_nsmul_eq_ofBase hζ_root
  set c : ℕ := Nat.card (powMonoidHom n : S.unit K →* S.unit K).ker
  have hx_ker : x ∈ (powMonoidHom n : S.unit K →* S.unit K).ker := MonoidHom.mem_ker.mpr hx_pow
  have hx_card : ((x : Kˣ) : K) ^ c = 1 := by
    simpa [c] using congrArg (fun z ↦ (((z.val : S.unit K) : Kˣ) : K))
      (pow_card_eq_one' (x := (⟨x, hx_ker⟩ : (powMonoidHom n : S.unit K →* S.unit K).ker)))
  have hζ_val : (ζ.toMul : Ω) = algebraMap K Ω ((x : Kˣ) : K) := by
    simpa using congrArg (fun z ↦ ((Subtype.val z).toMul : Ω)) hx_eq.symm
  refine hζ.dvd_of_pow_eq_one c (Units.ext ?_)
  rw [Units.val_pow_eq_pow_val, hζ_val, ← map_pow, hx_card, map_one, Units.val_one]

/-- Let `Γ`, the Galois group of `Ω/K` for the algebraic closure `Ω` of `ℚ`, fix the `n`-th roots of
unity and let `S` be a set of finite places of `K`. An `S`-unit `u` whose Kummer character vanishes
is the `n`-th power of an `S`-unit: `Γ` fixes an `n`-th root of `u`, which therefore lies in `K`. -/
private lemma mem_range_powMonoidHom_of_kummerChar_eq_zero
    (h_fix : ∀ g : Γ, cyclotomicCharMod Ω n g = 1) {S : Set (FinPlace K)} {u : S.unit K}
    (hu : ∀ g : Γ, (kummerChar K h_fix (ofBase Γ Ω (Additive.ofMul (u : Kˣ)))).val g = 0) :
    u ∈ (powMonoidHom n : S.unit K →* S.unit K).range := by
  obtain ⟨r, hr⟩ : ∃ r : DiscreteUnits Ω, n • r = (ofBase Γ Ω (Additive.ofMul (u : Kˣ))).val :=
    exists_nsmul _ (NeZero.ne n)
  have hr_inv : r ∈ (unitsRep : Representation ℤ Γ (DiscreteUnits Ω)).invariants :=
    (Representation.mem_invariants _ r).mpr fun g ↦
      (kummerChar_apply_eq_zero_iff h_fix _ hr g).mp (hu g)
  obtain ⟨x, -, hx_pow : x ^ n = u⟩ :=
    exists_unit_pow_eq_of_nsmul_eq_ofBase (y := ⟨r, hr_inv⟩) (Subtype.ext hr)
  exact ⟨x, hx_pow⟩

/-- Let `K` be totally complex and let `Γ`, the Galois group of `Ω/K` for the algebraic closure `Ω`
of `ℚ`, fix the `n`-th roots of unity. Let `S` be a set of finite places of `K` that contains the
places above `n`, such that `Kˣ` and the ideles that are units outside `S` generate the finite
ideles. An `S`-unit that is an `n`-th power at each place of `S` is the `n`-th power of an
`S`-unit. -/
private lemma subgroupOf_comap_idelesPowAt_le_range_powMonoidHom
    (h_fix : ∀ g : Γ, cyclotomicCharMod Ω n g = 1) [IsTotallyComplex K] {S : Set (FinPlace K)}
    (h_gen : principalIdele.range ⊔ idelesUnitOff S = ⊤)
    (hS : ∀ v : FinPlace K, ↑n ∈ v.asIdeal → v ∈ S) :
    ((idelesPowAt S n).comap principalIdele).subgroupOf (S.unit K) ≤
      (powMonoidHom n : S.unit K →* S.unit K).range := by
  -- The Kummer character of `u` vanishes on the decomposition groups at `S`, where `u` is an
  -- `n`-th power, on the inertia groups off `S` and on the complex conjugations (there are none).
  intro u hu
  set κu : Z1 (Representation.trivial ℤ Γ (ZMod n)) :=
    kummerChar K h_fix (ofBase Γ Ω (Additive.ofMul (u : Kˣ)))
  obtain ⟨r, hr⟩ : ∃ r : DiscreteUnits Ω, n • r = (ofBase Γ Ω (Additive.ofMul (u : Kˣ))).val :=
    exists_nsmul _ (NeZero.ne n)
  have h_decomp (v : FinPlace K) (hv : v ∈ S) (g : Γ) (hg : g ∈ decompGroup Γ (placeOver v)) :
      κu.val g = 0 := by
    have hu_pow : ideleAt v (principalIdele (u : Kˣ)) ∈ (powMonoidHom n).range :=
      mem_iInf.mp hu ⟨v, hv⟩
    refine (kummerChar_apply_eq_zero_iff h_fix _ hr g).mpr (DiscreteUnits.ext ?_)
    rw [val_unitsRep]
    exact v.isPlaceOver_placeOver.smul_root_eq_of_local_pow hu_pow
      (val_pow_eq_algebraMap_of_nsmul_eq_ofBase hr) g hg (h_fix g)
  have h_conj (c : Γ) (hc : IsComplexConj c) : κu.val c = 0 :=
    (hc.false_of_isTotallyComplex (K := K)).elim
  have h_inertia (v : FinPlace K) (hv : v ∉ S) (g : Γ) (hg : g ∈ inertiaGroup Γ (placeOver v)) :
      κu.val g = 0 :=
    kummerChar_ofBase_apply_eq_zero_of_mem_inertiaGroup h_fix (mt (hS v) hv)
      (S.unit_valuation_eq_one K u hv) hg
  exact mem_range_powMonoidHom_of_kummerChar_eq_zero h_fix
    (eq_zero_of_unramified_off S h_gen κu h_conj h_decomp h_inertia)

/-- Let `K` be totally complex, and let `Γ`, the Galois group of `Ω/K` for the algebraic closure `Ω`
of `ℚ`, fix the `n`-th roots of unity, so that the Kummer map `κ = kummerChar K h_fix` is defined.
Let `S` be a finite set of finite places of `K` that contains the places above `n`, such that `Kˣ`
and the ideles that are units outside `S` generate the finite ideles. Let `a` be a finite idele
whose Artin symbol is killed by `κ u` for every `S`-unit `u` (an element of `Kˣ` that is a unit at
each place outside `S`); here `κ u` is `κ (ofBase Γ Ω u)`, a map `Γ → ℤ/n`, read in `ℚ/ℤ` and lifted
to `Γ^ab`. Then `a` is a principal idele times an idele that is an `n`-th power at each place of `S`
and a unit elsewhere. -/
lemma mem_sup_of_kummerChar_artinMap_eq_one (h_fix : ∀ g : Γ, cyclotomicCharMod Ω n g = 1)
    [IsTotallyComplex K] {S : Set (FinPlace K)}
    (hS_fin : S.Finite) (h_gen : principalIdele.range ⊔ idelesUnitOff S = ⊤)
    (hS : ∀ v : FinPlace K, ↑n ∈ v.asIdeal → v ∈ S) (a : (𝔸f K)ˣ)
    (ha : ∀ u : S.unit K,
      abelianLift (ofZModCocycle n (kummerChar K h_fix (ofBase Γ Ω (Additive.ofMul u.val))))
        (artinMap Γ a) = 1) :
    a ∈ principalIdele.range ⊔ idelesPowAt S n ⊓ idelesUnitOff S := by
  -- Let `E` be the `S`-units and `G₀` the subgroup in the conclusion. The map `u ↦ κ u ∘ artinMap`
  -- embeds `E / E ^ n` into the characters of the quotient by `G₀`; counting shows that it is
  -- onto, so an idele killed by all `κ u` is killed by all characters of the quotient.
  let κ (u : S.unit K) : Z1 (Representation.trivial ℤ Γ (ZMod n)) :=
    kummerChar K h_fix (ofBase Γ Ω (Additive.ofMul (u : Kˣ)))
  set G₀ : Subgroup (𝔸f K)ˣ := principalIdele.range ⊔ idelesPowAt S n ⊓ idelesUnitOff S
  let En : Subgroup (S.unit K) := (powMonoidHom n : S.unit K →* S.unit K).range
  have h_loc : ((idelesPowAt S n).comap principalIdele).subgroupOf (S.unit K) ≤ En :=
    subgroupOf_comap_idelesPowAt_le_range_powMonoidHom h_fix h_gen hS
  obtain ⟨hG₀, h_le⟩ : G₀.index ≠ 0 ∧ G₀.index ≤ En.index :=
    index_sup_idelesPowAt_le hS_fin h_gen h_loc
      (dvd_natCard_ker_powMonoidHom_of_cyclotomicCharMod_eq_one h_fix S)
  have hG₀_fin : G₀.FiniteIndex := ⟨hG₀⟩
  -- `κ u ∘ artinMap` kills `G₀`: there are no complex conjugations, `n` kills `κ u`, and `κ u` is
  -- unramified off `S`, where `n` and `u` are units.
  have h_kills (u : S.unit K) :
      G₀ ≤ (abelianLift (ofZModCocycle n (κ u))).ker.comap (artinMap Γ) := by
    refine sup_le_ker_abelianLift_artinMap S n _ (fun c hc ↦ ?_) (fun v _ g _ ↦ ?_)
      fun v hv g hg ↦ ?_
    · exact (hc.false_of_isTotallyComplex (K := K)).elim
    · simp [← map_nsmul, ZMod.natCast_self]
    · have h_unram : (κ u).val g = 0 := kummerChar_ofBase_apply_eq_zero_of_mem_inertiaGroup h_fix
        (mt (hS v) hv) (S.unit_valuation_eq_one K u hv) hg
      simp [h_unram]
  -- `f` sends the class of `u` to `κ u ∘ artinMap`; it is injective as `artinMap` is onto.
  let f (q : S.unit K ⧸ En) : Additive ((𝔸f K)ˣ ⧸ G₀) →+ QZ :=
    (lift G₀ ((abelianLift (ofZModCocycle n (κ q.out))).comp (artinMap Γ))
      (h_kills q.out)).toAdditiveLeft
  have hf_inj : Injective f := by
    intro p q hpq
    refine Quotient.out_equiv_out.mp
      (leftRel_apply.mpr (mem_range_powMonoidHom_of_kummerChar_eq_zero h_fix fun g ↦ ?_))
    obtain ⟨y, hy⟩ : ∃ y : (𝔸f K)ˣ, artinMap Γ y = g := artinMap_surjective Γ g
    have h_val_eq : (κ p.out).val g = (κ q.out).val g := by
      simpa [f, hy, ofZMod_injective.eq_iff] using DFunLike.congr_fun hpq (.ofMul y)
    calc (κ (p.out⁻¹ * q.out)).val g = -(κ p.out).val g + (κ q.out).val g := by simp [κ]
      _ = 0 := by rw [h_val_eq, neg_add_cancel]
  -- The quotient by `G₀` has `G₀.index ≤ En.index` characters, so `f` is onto.
  have hf_surj : Surjective f :=
    (hf_inj.bijective_of_nat_card_le ((card_hom_QZ _).le.trans h_le)).surjective
  -- So every character of the quotient by `G₀` is some `f q`, and kills the class of `a` by `ha`.
  have h_all : ∀ χ : Additive ((𝔸f K)ˣ ⧸ G₀) →+ QZ, χ (.ofMul (a : (𝔸f K)ˣ ⧸ G₀)) = 0 :=
    hf_surj.forall.mpr fun q ↦ ha q.out
  exact (eq_one_iff a).mp (eq_zero_of_forall_hom_eq_zero h_all)

/-! ### Kummer theory and the existence theorem -/

/-- Let `Γ`, the Galois group of `Ω/K`, fix the `n`-th roots of unity, and let `ζ` be the root of
unity of order `n` chosen in `New.rootPowHom`. There is an additive map `κ` from the `Γ`-invariant
units of `Ω` to the characters `Γ → ℤ/n` such that (a) `ζ ^ κ x g = g a / a` whenever `a ^ n = x`,
and (b) for `K` totally complex and `S` a finite set of finite places such that `Kˣ` and the ideles
that are units outside `S` generate the finite ideles and that contains the places above `n` (the
three unnamed hypotheses, in this order), an idele whose Artin symbol is killed by `κ u` (short for
`κ (ofBase Γ Ω u)`) for every `S`-unit `u` is a principal idele times an idele that is an `n`-th
power at each place of `S` and a unit elsewhere. The map is `New.kummerChar`. -/
lemma exists_kummer_chars (h_fix : ∀ g : Γ, cyclotomicCharMod Ω n g = 1) :
    ∃ κ : (unitsRep : Representation ℤ Γ (DiscreteUnits Ω)).invariants →+
        Z1 (Representation.trivial ℤ Γ (ZMod n)),
      (∀ (x : (unitsRep : Representation ℤ Γ (DiscreteUnits Ω)).invariants) (a : DiscreteUnits Ω),
        n • a = ↑x → ∀ g : Γ, (rootPowHom Ω n).val ((κ x).val g) = unitsRep g a - a) ∧
      ∀ [IsTotallyComplex K] {S : Set (FinPlace K)}, S.Finite →
        principalIdele.range ⊔ idelesUnitOff S = ⊤ →
        (∀ v : FinPlace K, ↑n ∈ v.asIdeal → v ∈ S) →
        ∀ a : (𝔸f K)ˣ,
          (∀ u : S.unit K,
            abelianLift (ofZModCocycle n (κ (ofBase Γ Ω (Additive.ofMul u.val))))
              (artinMap Γ a) = 1) →
          a ∈ principalIdele.range ⊔ idelesPowAt S n ⊓ idelesUnitOff S :=
  ⟨kummerChar K h_fix, rootPowHom_kummerChar h_fix, mem_sup_of_kummerChar_artinMap_eq_one h_fix⟩

/-- Let `K` be totally complex, and let `Γ`, the Galois group of `Ω/K` for the algebraic closure `Ω`
of `ℚ`, fix the `n`-th roots of unity. Let `ψ` be a continuous character of the finite ideles with
values in `ℚ/ℤ` that vanishes on `Kˣ` and is killed by `n` (`toHom ψ` is `ψ` written
multiplicatively). Then `ψ` vanishes on the kernel of the Artin map. -/
lemma QZChar.apply_eq_zero_of_artinMap_eq_one (h_fix : ∀ g : Γ, cyclotomicCharMod Ω n g = 1)
    [IsTotallyComplex K] (ψ : QZChar (𝔸f K)ˣ)
    (hψ_rat : ∀ x : Kˣ, ψ.val (principalIdele x) = 0)
    (hψ_pow : ∀ b : (𝔸f K)ˣ, toHom ψ b ^ n = 1)
    {a : (𝔸f K)ˣ} (ha : artinMap Γ a = 1) : ψ.val a = 0 := by
  -- Take `S` large, containing the places above `n` and those where `ψ` ramifies.
  set R : Set (FinPlace K) := {v | (n : 𝓞 K) ∈ v.asIdeal} ∪
    {v | ¬ ∀ x : (LocField v)ˣ, Valued.v x.val = 1 → toHom ψ (locIdele v x) = 1}
  have hR_fin : R.Finite := (finite_natCast_mem n).union
    (Filter.eventually_cofinite.mp (eventually_unramified (toHom ψ) (isOpen_ker ψ)))
  obtain ⟨S, hS_fin, hS_sub, h_gen⟩ : ∃ S : Set (FinPlace K),
      S.Finite ∧ R ⊆ S ∧ principalIdele.range ⊔ idelesUnitOff S = ⊤ :=
    exists_superset_sup_idelesUnitOff_eq_top hR_fin
  have hS_n (v : FinPlace K) (hv : (n : 𝓞 K) ∈ v.asIdeal) : v ∈ S := hS_sub (Or.inl hv)
  have h_unram (v : FinPlace K) (hv : v ∉ S) :
      ∀ x : (LocField v)ˣ, Valued.v x.val = 1 → toHom ψ (locIdele v x) = 1 :=
    by_contra fun h_ram ↦ hv (hS_sub (Or.inr h_ram))
  -- `ψ` kills the ideles that are `n`-th powers at `S` and units elsewhere, place by place.
  have h_kills : idelesPowAt S n ⊓ idelesUnitOff S ≤ ker ψ := by
    rintro b ⟨hb_pow, hb_unit⟩
    refine mem_of_locIdele_mem ((ker ψ).isClosed_of_isOpen (isOpen_ker ψ)) fun v ↦ ?_
    by_cases hv : v ∈ S
    · obtain ⟨y, hy⟩ : ∃ y : (LocField v)ˣ, y ^ n = ideleAt v b := mem_iInf.mp hb_pow ⟨v, hv⟩
      rw [MonoidHom.mem_ker, ← hy, map_pow, map_pow, hψ_pow]
    · exact h_unram v hv (ideleAt v b) (mem_idelesUnitOff.mp hb_unit v hv)
  have h_principal : principalIdele.range ≤ ker ψ :=
    forall_mem_range.mpr fun x ↦ (QZChar.mem_ker_iff_val_eq_zero ψ _).mpr (hψ_rat x)
  -- `a` is killed by all Kummer characters, so it is such an idele times a principal one.
  have ha_mem : a ∈ principalIdele.range ⊔ idelesPowAt S n ⊓ idelesUnitOff S :=
    mem_sup_of_kummerChar_artinMap_eq_one h_fix hS_fin h_gen hS_n a fun u ↦ by rw [ha, map_one]
  exact (QZChar.mem_ker_iff_val_eq_zero ψ a).mp (sup_le h_principal h_kills ha_mem)

end Kummer

universe u_1 u_2 u_3

section ExistenceTheorem

variable (Γ : Type) {K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [NumberField K] {n : ℕ}
  [NeZero n] (S : Set (FinPlace K)) [Algebra K Ω] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]
  {C : Type u_3} [Group C] [TopologicalSpace C]

/-- Let `Γ` be the Galois group of `Ω/K`, and let `θ` be a continuous homomorphism from the finite
ideles of `K` to a group `C` with a topology whose kernel contains the kernel of the Artin map
`artinMap Γ`, which takes values in the abelianisation `Γ^ab`. Then there is a continuous
homomorphism `μ : Γ → C` with `μ g = θ x` whenever the class of `g` in `Γ^ab` is the Artin symbol of
`x`. -/
lemma exists_comp_artinMap_of_ker_le (θ : (𝔸f K)ˣ →* C) (hθ : Continuous θ)
    (h_ker : (artinMap Γ).ker ≤ θ.ker) :
    ∃ μ : Γ →* C, Continuous μ ∧ ∀ (x : (𝔸f K)ˣ) (g : Γ), artinMap Γ x = g → μ g = θ x := by
  -- `artinMap` is onto, so `θ = μ ∘ artinMap` for a homomorphism `μ` on the abelianisation;
  -- `artinMap` is an open map, hence a quotient map, so `μ` is continuous.
  have h_surj : Surjective (artinMap (K := K) Γ) := artinMap_surjective Γ
  let μ : TopologicalAbelianization Γ →* C := (artinMap Γ).liftOfSurjective h_surj ⟨θ, h_ker⟩
  have hμ_comp (x : (𝔸f K)ˣ) : μ (artinMap Γ x) = θ x :=
    (artinMap Γ).liftOfRightInverse_comp_apply _ _ ⟨θ, h_ker⟩ x
  have h_open : IsOpenMap (artinMap (K := K) Γ) :=
    (artinMap Γ).isOpenMap_of_sigmaCompact h_surj continuous_artinMap
  have hμ : Continuous μ :=
    (h_open.isQuotientMap continuous_artinMap h_surj).continuous_iff.mpr
      (hθ.congr fun x ↦ (hμ_comp x).symm)
  refine ⟨μ.comp (mk' _), hμ.comp continuous_mk, fun x g h_art ↦ ?_⟩
  rw [MonoidHom.comp_apply, mk'_apply, ← h_art, hμ_comp]

/-- Let `χ` be a continuous character of the group `G` with a topology with values in `ℚ/ℤ`, such
that `G ⧸ ker χ` is finite. Then the commutator subgroup of `G` lies in `⁅G, ker χ⁆`. -/
lemma QZChar.commutator_le_commutator_ker {G : Type*} [Group G] [TopologicalSpace G] (χ : QZChar G)
    [Finite (G ⧸ ker χ)] :
    commutator G ≤ ⁅(⊤ : Subgroup G), ker χ⁆ := by
  -- With `U = ker χ`, the group `G / ⁅G, U⁆` is commutative: the image of `U` is central, and the
  -- quotient by it is `G / U`, which `χ` maps by `e` onto a finite, hence cyclic, subgroup of `ℂˣ`.
  set U : Subgroup G := ker χ
  let e : G ⧸ U →* ℂˣ := expUnit.comp (kerLift (toHom χ))
  let f : G ⧸ ⁅(⊤ : Subgroup G), U⁆ →* e.range :=
    e.rangeRestrict.comp (map ⁅(⊤ : Subgroup G), U⁆ U (MonoidHom.id G) (commutator_le_right ⊤ U))
  refine Normal.quotient_commutative_iff_commutator_le.mp
    (f.isMulCommutative_of_isCyclic_of_ker_le_center ?_)
  intro k' hk'
  obtain ⟨k, rfl⟩ := mk_surjective k'
  -- `k` lies in `U`, so its commutators with all of `G` lie in `⁅G, U⁆`, and its class is central.
  have h_exp : expUnit (toHom χ k) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hk')
  have hkU : k ∈ U := MonoidHom.mem_ker.mpr (expUnit_eq_one_iff.mp h_exp)
  refine mem_center_iff.mpr fun q ↦ ?_
  obtain ⟨g, rfl⟩ := mk_surjective q
  have h_comm : g * k * g⁻¹ * k⁻¹ ∈ ⁅(⊤ : Subgroup G), U⁆ :=
    commutator_mem_commutator (mem_top g) hkU
  rwa [← commutatorElement_eq_one_iff_mul_comm, commutatorElement_def, ← mk_inv, ← mk_inv,
    ← mk_mul, ← mk_mul, ← mk_mul, QuotientGroup.eq_one_iff]

omit [NumberField K] in
/-- Let `χ` be a continuous character of `Γ` with values in `ℚ/ℤ` such that `Γ ⧸ ker χ` is finite,
and let `μ` be a continuous homomorphism from `ker χ` to `ℚ/ℤ` (written multiplicatively) that is
invariant under conjugation by `Γ`. Then the closure of the commutator subgroup of `Γ` lies in the
kernel of `μ`, viewed as a subgroup of `Γ`. -/
private lemma QZChar.topologicalClosure_commutator_le_map_ker (χ : QZChar Γ) [Finite (Γ ⧸ ker χ)]
    (μ : ker χ →* Multiplicative QZ) (hμ_cont : Continuous μ)
    (hμ_conj : ∀ (g : Γ) (k : ker χ), μ (MulAut.conjNormal g k) = μ k) :
    (commutator Γ).topologicalClosure ≤ μ.ker.map (ker χ).subtype := by
  -- `μ` kills the commutators of `Γ` with `ker χ`, which contain those of `Γ`; the kernel of `μ`
  -- is closed in `ker χ`, which is closed in `Γ`.
  have h_comm : commutator Γ ≤ μ.ker.map (ker χ).subtype := by
    refine (commutator_le_commutator_ker χ).trans (commutator_le.mpr fun g _ k hk ↦ ?_)
    have h_mem : MulAut.conjNormal g (⟨k, hk⟩ : ker χ) / ⟨k, hk⟩ ∈ μ.ker :=
      μ.div_mem_ker_iff.mpr (hμ_conj g ⟨k, hk⟩)
    exact ⟨_, h_mem, division_def _ _⟩
  have h_ker_closed : IsClosed ((ker χ : Subgroup Γ) : Set Γ) := inferInstance
  exact closure_minimal h_comm
    (h_ker_closed.isClosedMap_subtype_val _ (isClosed_singleton.preimage hμ_cont))

/-- Let `Γ` be the Galois group of `Ω/K` for the algebraic closure `Ω` of `ℚ`. Let `χ` be a
continuous character of `Γ` with values in `ℚ/ℤ` such that `Γ ⧸ ker χ` is finite, let `L` be the
fixed field of `ker χ`, and let `ψ` be a continuous character of the finite ideles of `K`. A
homomorphism `μ` on `ker χ` with `μ k = ψ (N z)` whenever the class of `k` is the Artin symbol over
`L` of `z`, where `N` is the norm from `L` to `K`, is invariant under conjugation by `Γ`: the norm
does not see the action of `Γ` on `L`. -/
private lemma map_conjNormal_eq_of_forall_artinMap_eq (χ : QZChar Γ) [Finite (Γ ⧸ ker χ)]
    (ψ : QZChar (𝔸f K)ˣ) (μ : ker χ →* Multiplicative QZ)
    (hμ : ∀ (z : (𝔸f (fixedFieldOf (K := K) (Ω := Ω) (ker χ)))ˣ) (k : ker χ),
      artinMap (ker χ) z = k →
        μ k = toHom ψ (z.map (adeleNorm K (fixedFieldOf (K := K) (Ω := Ω) (ker χ)))))
    (g : Γ) (k : ker χ) :
    μ (MulAut.conjNormal g k) = μ k := by
  let L : IntermediateField K Ω := fixedFieldOf (ker χ)
  obtain ⟨z, hz⟩ : ∃ z : (𝔸f L)ˣ, artinMap (ker χ) z = k := artinMap_surjective (ker χ) k
  -- Make `L` an `L`-algebra through `σ = g⁻¹` rather than the identity. This extension has degree
  -- one, so its norm `adeleNorm L L` is the inverse of `σ` on ideles, that is, the action of `g`.
  -- All uses of `adeleNorm L L` below refer to this algebra structure.
  let σ : Ω →ₐ[K] Ω := MulSemiringAction.toAlgHom K Ω g⁻¹
  let algebraViaσ : Algebra L L := (σ.restrictNormal L).toAlgebra
  have hσ_conj (t : Ω) : σ (MulAut.conjNormal g k • t) = k • σ t := by
    simp [σ, (ker χ).smul_def, mul_smul]
  have h_art : artinMap (ker χ) (z.map (adeleNorm L L)) = MulAut.conjNormal g k :=
    artinMap_map_adeleNorm hz σ (fun t ↦ (σ.restrictNormal_commutes L t).symm) hσ_conj
  have h_norm : (z.map (adeleNorm L L)).map (adeleNorm K L) = z.map (adeleNorm K L) :=
    Units.ext (by simp)
  calc μ (MulAut.conjNormal g k) = toHom ψ ((z.map (adeleNorm L L)).map (adeleNorm K L)) :=
        hμ _ _ h_art
    _ = toHom ψ (z.map (adeleNorm K L)) := by rw [h_norm]
    _ = μ k := (hμ _ _ hz).symm

/-- Let `K` be totally complex and `Γ` the Galois group of `Ω/K`, and let `ψ` be a continuous
character of the finite ideles with values in `ℚ/ℤ` that vanishes on `Kˣ` and is killed by `n`.
Then `ψ` vanishes on the kernel of the Artin map. -/
private lemma QZChar.apply_eq_zero_of_pow_eq_one_of_artinMap_eq_one [IsTotallyComplex K]
    (ψ : QZChar (𝔸f K)ˣ) (hψ_rat : ∀ x : Kˣ, ψ.val (principalIdele x) = 0)
    (hψ_pow : ∀ b : (𝔸f K)ˣ, toHom ψ b ^ n = 1) {a : (𝔸f K)ˣ} (ha : artinMap Γ a = 1) :
    ψ.val a = 0 := by
  -- Induct on the index `d` of the subgroup of `Γ` that fixes the `n`-th roots of unity. If
  -- `d = 1`, use Kummer theory. Else pass to a cyclic extension `L` of `K` inside `K(μ_n)`, over
  -- which the index is smaller, and compose `ψ` with the norm from `L`.
  induction h_deg : (cyclotomicCharMod Ω n : Γ →* _).ker.index using Nat.strongRec
      generalizing Γ K with
  | _ d ih =>
    rcases forall_or_exists_not (fun g : Γ ↦ cyclotomicCharMod Ω n g = 1) with h_triv | ⟨g₀, hg₀⟩
    · exact apply_eq_zero_of_artinMap_eq_one h_triv ψ hψ_rat hψ_pow ha
    -- Otherwise a character `χ ≠ 0` of `Gal(K(μ_n)/K)` cuts out `L`, and `a` is a norm from `L`
    -- times a principal idele.
    obtain ⟨χ, hχ_ker, hχ_ne⟩ :
        ∃ χ : QZChar Γ, (∀ g ∈ (cyclotomicCharMod Ω n).ker, χ.val g = 0) ∧ χ.val g₀ ≠ 0 :=
      exists_apply_ne_zero_of_notMem_ker (cyclotomicCharMod Ω n) g₀ inferInstance hg₀
    let U : Subgroup Γ := ker χ
    let L : IntermediateField K Ω := fixedFieldOf U
    have hL_cplx : IsTotallyComplex L := isTotallyComplex_of_algebra K L
    have hU_fin : Finite (Γ ⧸ U) := U.quotient_finite_of_isOpen (isOpen_ker χ)
    obtain ⟨x, y, hx_pos, rfl⟩ : ∃ (x : Kˣ) (y : (𝔸f L)ˣ),
        IsTotallyPositive x.val ∧ a = principalIdele x * Units.map (adeleNorm K L) y :=
      (abelianLift_artinMap_eq_one_iff (L := L) χ a).mp (by rw [ha, map_one])
    -- By induction `ρ = ψ ∘ N`, with `N` the norm from `L`, kills the kernel of the Artin map of
    -- `L`, so `ρ = μ ∘ artinMap`.
    let ρ : QZChar (𝔸f L)ˣ :=
      comap ⟨Units.map (adeleNorm K L), (continuous_adeleNorm K L).units_map _⟩ ψ
    have hρ_apply (b : (𝔸f L)ˣ) : toHom ρ b = toHom ψ (b.map (adeleNorm K L)) := rfl
    have h_lt : (cyclotomicCharMod Ω n : U →* _).ker.index < d := by
      have h_ker_le : (cyclotomicCharMod Ω n).ker ≤ U := fun g hg ↦
        (mem_ker_iff_val_eq_zero χ g).mpr (hχ_ker g hg)
      have hU_ne_top : U ≠ ⊤ := fun hU_top ↦
        hχ_ne ((mem_ker_iff_val_eq_zero χ g₀).mp (hU_top.ge (mem_top g₀)))
      calc _ < (cyclotomicCharMod Ω n).ker.relIndex U * U.index :=
          lt_mul_of_one_lt_right card_pos (one_lt_index_of_ne_top hU_ne_top)
        _ = d := (relIndex_mul_index h_ker_le).trans h_deg
    have hρ_rat (z : Lˣ) : ρ.val (principalIdele z) = 0 :=
      calc ρ.val (principalIdele z) = ψ.val ((principalIdele z).map (adeleNorm K L)) := rfl
        _ = ψ.val (principalIdele (z.map (Algebra.norm K))) := by rw [map_adeleNorm_principalIdele]
        _ = 0 := hψ_rat _
    have hρ_pow (b : (𝔸f L)ˣ) : toHom ρ b ^ n = 1 := by rw [hρ_apply, hψ_pow]
    have h_ker_ρ : (artinMap U).ker ≤ (toHom ρ).ker := fun b hb ↦
      (mem_ker_iff_val_eq_zero ρ b).mpr (ih _ h_lt U ρ hρ_rat hρ_pow hb rfl)
    obtain ⟨μ, hμ_cont, hμ⟩ : ∃ μ : U →* Multiplicative QZ, Continuous μ ∧
        ∀ (b : (𝔸f L)ˣ) (k : U), artinMap U b = k → μ k = toHom ρ b :=
      exists_comp_artinMap_of_ker_le U (toHom ρ) ρ.property.left h_ker_ρ
    -- `μ` is invariant under conjugation by `Γ`, so it kills what is trivial in `Γ^ab`.
    have hμ_conj : ∀ (g : Γ) (k : U), μ (MulAut.conjNormal g k) = μ k :=
      map_conjNormal_eq_of_forall_artinMap_eq Γ χ ψ μ hμ
    have h_ker : (commutator Γ).topologicalClosure ≤ μ.ker.map U.subtype :=
      topologicalClosure_commutator_le_map_ker Γ χ μ hμ_cont hμ_conj
    -- If `artinMap y` is the class of `u ∈ U`, then `u` is trivial in `Γ^ab` (norm compatibility
    -- and `ha`), so `ρ y = μ u` is trivial.
    obtain ⟨u, hu⟩ : ∃ u : U, (u : TopologicalAbelianization U) = artinMap U y := mk_surjective _
    have h_norm : artinMap Γ (y.map (adeleNorm K L)) = (u : Γ) :=
      artinMap_map_adeleNorm hu.symm 1 (fun _ ↦ rfl) fun _ ↦ rfl
    have h_art_norm : artinMap Γ (y.map (adeleNorm K L)) = 1 := by
      rwa [map_mul, artinMap_principalIdele_eq_one_of_isTotallyPositive hx_pos, one_mul] at ha
    have hu_comm : (u : Γ) ∈ (commutator Γ).topologicalClosure := by
      rwa [h_norm, QuotientGroup.eq_one_iff] at h_art_norm
    have hu_ker : u ∈ μ.ker := (mem_map_iff_mem U.subtype_injective).mp (h_ker hu_comm)
    have hρy : toHom ρ y = 1 := (hμ y u hu.symm).symm.trans hu_ker
    -- `ψ a = ψ x + ρ y`, and both terms vanish.
    have hψ_a : toHom ψ (principalIdele x * y.map (adeleNorm K L)) = 1 := by
      rw [map_mul, ← hρ_apply, hρy, mul_one]
      exact (mem_ker_iff_val_eq_zero ψ _).mpr (hψ_rat x)
    exact (mem_ker_iff_val_eq_zero ψ _).mp hψ_a

/-- The existence theorem for totally complex `K`. Let `Γ` be the Galois group of `Ω/K`. A
continuous homomorphism `θ` from the finite ideles to a group `C` with a `T₁` topology that is
trivial on `Kˣ` factors through the Artin map: there is a continuous homomorphism `μ : Γ → C` with
`μ g = θ x` whenever the class of `g` in `Γ^ab` is the Artin symbol of `x`. -/
lemma exists_comp_artinMap [IsTotallyComplex K] [T1Space C] (θ : (𝔸f K)ˣ →* C) (hθ : Continuous θ)
    (hθ_rat : ∀ x : Kˣ, θ (principalIdele x) = 1) :
    ∃ μ : Γ →* C, Continuous μ ∧ ∀ (x : (𝔸f K)ˣ) (g : Γ), artinMap Γ x = g → μ g = θ x := by
  -- It is enough that `θ` kills the kernel of `artinMap`. Characters `ψ` with values in `ℚ/ℤ`
  -- separate closed subgroups from points, and each `ψ` that vanishes on `Kˣ` kills the kernel of
  -- `artinMap`, by Kummer theory and an induction on `[K(μ_n) : K]`.
  refine exists_comp_artinMap_of_ker_le Γ θ hθ fun a (ha : artinMap Γ a = 1) ↦ ?_
  suffices key : ∀ ψ : QZChar (𝔸f K)ˣ, (∀ x : Kˣ, ψ.val (principalIdele x) = 0) → ψ.val a = 0 by
    by_contra h_not
    obtain ⟨ψ, hψ, hψa⟩ : ∃ ψ : QZChar (𝔸f K)ˣ, (∀ b ∈ θ.ker, ψ.val b = 0) ∧ ψ.val a ≠ 0 := by
      have h_closed : IsClosed (θ.ker : Set (𝔸f K)ˣ) := isClosed_singleton.preimage hθ
      rw [← ker_mk' θ.ker] at h_closed h_not ⊢
      exact exists_apply_ne_zero_of_notMem_ker (mk' θ.ker) a h_closed h_not
    exact hψa (key ψ fun x ↦ hψ _ (hθ_rat x))
  intro ψ hψ_rat
  -- `ker ψ` is open and contains `Kˣ`, so it has a finite index `n`, and `n` kills `ψ`.
  have hψ_fin : (ker ψ).FiniteIndex := finiteIndex_idele_subgroup_of_isOpen (ker ψ) (isOpen_ker ψ)
    fun x _ ↦ (QZChar.mem_ker_iff_val_eq_zero ψ _).mpr (hψ_rat x)
  have hn : NeZero (ker ψ).index := ⟨hψ_fin.index_ne_zero⟩
  have hψ_pow : ∀ b : (𝔸f K)ˣ, toHom ψ b ^ (ker ψ).index = 1 := by
    simpa using (ker ψ).pow_index_mem
  exact QZChar.apply_eq_zero_of_pow_eq_one_of_artinMap_eq_one Γ ψ hψ_rat hψ_pow ha

variable {Γ} in
/-- Let `Γ` be the Galois group of `Ω/K` and `S` a set of finite places of `K`. The map `x : Γ → B`
is a locally constant homomorphism to the additive group `B`, killed by `m`, and zero on the inertia
groups at the places off `S`. -/
structure OddPart.IsUnramifiedTorsionHom (m : ℕ) {B : Type*} [AddCommGroup B] (x : Γ → B) :
    Prop where
  /-- `x` is locally constant. -/
  isLocallyConstant : IsLocallyConstant x
  /-- `x` is a homomorphism to the additive group `B`. -/
  map_mul (g h : Γ) : x (g * h) = x g + x h
  /-- `m` kills the values of `x`. -/
  nsmul_eq_zero (g : Γ) : m • x g = 0
  /-- `x` vanishes on the inertia group at the chosen place `placeOver v` of `Ω` over each finite
  place `v ∉ S`. -/
  unramified : ∀ v : FinPlace K, v ∉ S → ∀ g : Γ, g ∈ inertiaGroup Γ (placeOver v) → x g = 0

/-- Let `Γ` be the Galois group of `Ω/K` and `S` a set of finite places of `K`. The image under the
Artin map of the group generated by `Kˣ` and the ideles that are `m`-th powers at the places of `S`
and units elsewhere has an index that divides the class number of `K` times the index of the ideles
that are `m`-th powers at `S`. -/
private lemma index_map_artinMap_dvd_classNumber_mul_index (m : ℕ) :
    ((principalIdele.range ⊔ idelesPowAt S m ⊓ idelesUnitOff S).map (artinMap Γ)).index ∣
      classNumber K * (idelesPowAt S m).index := by
  set N : Subgroup (𝔸f K)ˣ := idelesPowAt S m
  set A : Subgroup (𝔸f K)ˣ := principalIdele.range ⊔ N ⊓ idelesUnitOff S
  -- `A ⊔ idelesUnitOff S` contains the kernel of the map `c` to the class group, which is
  -- generated by the principal ideles and the ideles that are units everywhere.
  have h_class : (A ⊔ idelesUnitOff S).index ∣ classNumber K := by
    obtain ⟨c, hc⟩ : ∃ c : (𝔸f K)ˣ →* ClassGroup (𝓞 K),
        c.ker = principalIdele.range ⊔ idelesUnitOff ∅ := exists_idele_classGroup_hom
    have h_ker_le : c.ker ≤ A ⊔ idelesUnitOff S :=
      hc.trans_le (sup_le_sup le_sup_left (idelesUnitOff_mono (Set.empty_subset S)))
    calc (A ⊔ idelesUnitOff S).index ∣ c.ker.index := index_dvd_of_le h_ker_le
      _ = Nat.card c.range := index_ker c
      _ ∣ Nat.card (ClassGroup (𝓞 K)) := card_subgroup_dvd_card c.range
      _ = classNumber K := Nat.card_eq_fintype_card
  have h_rel : A.relIndex (idelesUnitOff S) ∣ N.relIndex (idelesUnitOff S) := by
    rw [← inf_relIndex_right N]
    exact relIndex_dvd_of_le_left _ le_sup_right
  calc (A.map (artinMap Γ)).index ∣ A.index := index_map_dvd _ (artinMap_surjective Γ)
    _ = (A ⊔ idelesUnitOff S).index * A.relIndex (idelesUnitOff S) := by
      rw [← relIndex_mul_index le_sup_left, relIndex_sup_left, mul_comm]
    _ ∣ classNumber K * N.index :=
      mul_dvd_mul h_class (h_rel.trans (relIndex_dvd_index_of_normal N _))

/-- Let `K` be totally complex, `Γ` the Galois group of `Ω/K` and `S` a set of finite places of `K`,
and let the group of finite ideles that are `m`-th powers at the places of `S` have finite index.
There are finitely many points `p i ∈ Γ` and integers `n i ≥ 2`, with `∏ n i` dividing the class
number of `K` times this index, such that every locally constant homomorphism `x` on `Γ` that is
killed by `m` and unramified off `S` (`New.OddPart.IsUnramifiedTorsionHom`) has `n i • x (p i) = 0`,
and is zero if it vanishes at all `p i`. -/
lemma OddPart.exists_detecting_points_hom [IsTotallyComplex K] (m : ℕ)
    (h_finite : (idelesPowAt S m).index ≠ 0) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → Γ) (n : ι → ℕ),
      -- (a) the orders `n i` are at least `2`
      (∀ i : ι, 2 ≤ n i) ∧
      -- (b) their product is bounded
      ∏ i : ι, n i ∣ classNumber K * (idelesPowAt S m).index ∧
      -- (c) a locally constant homomorphism `x`, killed by `m` and unramified off `S`, has
      -- `n i • x (p i) = 0` and is determined by its values at the `p i`
      ∀ {B : Type*} [AddCommGroup B] {x : Γ → B}, IsUnramifiedTorsionHom S m x →
        (∀ i : ι, n i • x (p i) = 0) ∧ ((∀ i : ι, x (p i) = 0) → x = 0) := by
  classical
  -- Let `A` be generated by the principal ideles and the ideles that are `m`-th powers at `S` and
  -- units off `S`, and `H` its image under the Artin map. The quotient of `Γ^ab` by `H` is finite,
  -- so a product of cyclic groups of orders `n i`. For every `f : B →+ ℚ/ℤ` the character `f ∘ x`
  -- factors through the quotient, and these `f` separate the points of `B`.
  set A : Subgroup (𝔸f K)ˣ := principalIdele.range ⊔ idelesPowAt S m ⊓ idelesUnitOff S
  set H : Subgroup (TopologicalAbelianization Γ) := A.map (artinMap Γ)
  have h_index : H.index ∣ classNumber K * (idelesPowAt S m).index :=
    index_map_artinMap_dvd_classNumber_mul_index Γ S m
  have hQ_fin : Finite (TopologicalAbelianization Γ ⧸ H) := finite_of_card_ne_zero
    (ne_zero_of_dvd_ne_zero (mul_ne_zero (classNumber_pos K).ne' h_finite) h_index)
  obtain ⟨ι, hι, n, hn, ⟨ε⟩⟩ : ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ), (∀ i : ι, 1 < n i) ∧
      Nonempty ((TopologicalAbelianization Γ ⧸ H) ≃* ((i : ι) → Multiplicative (ZMod (n i)))) :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite _
  -- `p i` is a representative in `Γ` of a representative in `Γ^ab` of the generator of factor `i`
  let p (i : ι) : Γ := (ε.symm (mulSingle i (.ofAdd 1))).out.out
  have hn_ne (i : ι) : NeZero (n i) := ⟨(Nat.zero_lt_of_lt (hn i)).ne'⟩
  have h_card : H.index = ∏ i : ι, n i :=
    calc H.index = Nat.card ((i : ι) → Multiplicative (ZMod (n i))) := Nat.card_congr ε.toEquiv
      _ = ∏ i : ι, n i := by simp
  refine ⟨ι, hι, p, n, hn, by rwa [← h_card], fun {B} hB x hx ↦ ?_⟩
  -- The character `f ∘ x` kills `H`: by Artin reciprocity, `χ ∘ artinMap` kills `A` as soon as `χ`
  -- kills complex conjugations (`K` has none), is killed by `m` and is unramified off `S`.
  let χ (f : B →+ QZ) : QZChar Γ :=
    ⟨f ∘ x, (hx.isLocallyConstant.comp f).continuous, by simp [hx.map_mul]⟩
  have h_ker (f : B →+ QZ) {a : TopologicalAbelianization Γ} (ha : ε (mk a) = 1) :
      abelianLift (χ f) a = 1 := by
    have h_conj (c : Γ) (hc : IsComplexConj c) : (χ f).val c = 0 :=
      (hc.false_of_isTotallyComplex (K := K)).elim
    have h_decomp (w : FinPlace K) (_hw : w ∈ S) (g : Γ) (_hg : g ∈ decompGroup Γ (placeOver w)) :
        m • (χ f).val g = 0 := by simp [χ, ← map_nsmul, hx.nsmul_eq_zero]
    have h_inertia (w : FinPlace K) (hw : w ∉ S) (g : Γ) (hg : g ∈ inertiaGroup Γ (placeOver w)) :
        (χ f).val g = 0 := by simp [χ, hx.unramified w hw g hg]
    have h_le : H ≤ (abelianLift (χ f)).ker := map_le_iff_le_comap.mpr
      (sup_le_ker_abelianLift_artinMap S m (χ f) h_conj h_decomp h_inertia)
    exact h_le ((QuotientGroup.eq_one_iff a).mp (ε.map_eq_one_iff.mp ha))
  refine ⟨fun i ↦ eq_zero_of_forall_hom_eq_zero fun f ↦ ?_,
    fun h_zero ↦ funext fun g ↦ eq_zero_of_forall_hom_eq_zero fun f ↦ ?_⟩
  · -- `p i ^ n i` lies in `H`
    have h_pow : ε (mk (mk (p i) ^ n i)) = 1 := by
      simp [p, ← mulSingle_pow, ← ofAdd_nsmul, ZMod.natCast_self]
    simpa [χ, ← ofAdd_nsmul, ← map_nsmul] using h_ker f h_pow
  · -- modulo `H`, `g` is a product of powers of the `p i`
    have h_prod : ε (mk (mk g / ∏ i, mk (p i) ^ (ε (mk g) i).toAdd.valMinAbs)) = 1 := by
      ext
      simp [p, mulSingle, update]
    simpa [χ, h_zero] using h_ker f h_prod

end ExistenceTheorem

end New
