import Lib.Base

/-!
# Open subgroups, a tube lemma, and procyclic images of ℓ-adic characters

This file collects auxiliary facts from topology and algebra. It characterises congruence modulo a
principal ideal `(a)` by divisibility of the difference by `a`.

## Main definitions and results

* `IsCompact.eventually_forall_mem`: a form of the tube lemma for a jointly continuous map of two
  variables, with the continuity hypothesis discharged by `fun_prop` by default.
* `New.Selmer.exists_procyclic_generator`: a continuous character of a compact group with values in
  1 + 4ℤ_ℓ has procyclic image.
* `MonoidHom.IsGeneratorModKer`: an element generates a topological group modulo the kernel of a
  homomorphism; `New.Selmer.exists_isGeneratorModKer` gives one for such a character of a profinite
  group.
-/

/-! ## Open subgroups, a tube lemma, and congruence modulo a principal ideal -/

/-- The subgroup U of G is an open subset of G. -/
@[to_additive]
protected abbrev Subgroup.IsOpen {G : Type*} [Group G] [TopologicalSpace G] (U : Subgroup G) :
    Prop := IsOpen (X := G) U

/-- Tube lemma for a jointly continuous f: if W is a neighbourhood of f(x₀, y) for each y in a
compact set K, then f(x, y) ∈ W for all y in K and all x near x₀. -/
lemma IsCompact.eventually_forall_mem {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {K : Set Y} {x₀ : X} (hK : IsCompact K) (f : X → Y → Z) (W : Set Z)
    (h_nhds : ∀ y ∈ K, W ∈ nhds (f x₀ y)) (hf : Continuous f.uncurry := by fun_prop) :
    ∀ᶠ x : X in nhds x₀, ∀ y ∈ K, f x y ∈ W :=
  hK.eventually_forall_of_forall_eventually fun y hy ↦ hf.continuousAt (h_nhds y hy)

/-- Two elements x and y have the same class modulo the principal ideal (a) if and only if a divides
x − y. -/
lemma Ideal.mk_span_eq_iff_dvd_sub {R : Type*} [CommRing R] {a x y : R} :
    Quotient.mk (span {a}) x = Quotient.mk (span {a}) y ↔ a ∣ x - y :=
  Quotient.eq.trans mem_span_singleton

/-! ## Procyclic images of ℓ-adic characters of compact groups -/

section ProcyclicImage

open PadicInt Filter Subgroup ZMod Nat Units

/-- The powers of 5 form a subgroup of index 2 in (ℤ/2^(k+2))ˣ. -/
lemma ZMod.index_zpowers_unitOfCoprime_five (k : ℕ) (h_coprime : Nat.Coprime 5 (2 ^ (k + 2))) :
    (zpowers (unitOfCoprime 5 h_coprime)).index = 2 := by
  have card_units : Nat.card (ZMod (2 ^ (k + 2)))ˣ = 2 * 2 ^ k := by
    simp [card_units_eq_totient, totient_prime_pow_succ Nat.prime_two (k + 1), ← pow_succ']
  have card_powers : Nat.card (zpowers (unitOfCoprime 5 h_coprime)) = 2 ^ k := by
    rw [Nat.card_zpowers, ← orderOf_units, coe_unitOfCoprime, Nat.cast_ofNat, orderOf_five]
  exact Nat.mul_right_cancel card_pos <| by rw [index_mul_card, card_units, card_powers]

/-- A continuous character κ of Γ with values in 1 + 4ℤ_ℓ admits a continuous character μ with
ker μ ≤ ker κ whose image modulo every ℓ^(k+2) is cyclic: κ itself for odd ℓ, κ² for ℓ = 2. -/
lemma New.Selmer.exists_isCyclic_range_toZModPow {ℓ : ℕ} {Γ : Type*} [Fact ℓ.Prime] [Group Γ]
    [TopologicalSpace Γ] (κ : Γ →* ℤ_[ℓ]ˣ) (hκ : Continuous κ)
    (hκ_four : ∀ g : Γ, 4 ∣ (κ g).val - 1) :
    ∃ μ : Γ →* ℤ_[ℓ]ˣ,
      (∀ k : ℕ, IsCyclic ((Units.map
        (toZModPow (k + 2) : ℤ_[ℓ] →+* ZMod (ℓ ^ (k + 2))).toMonoidHom).comp μ).range) ∧
      Continuous μ ∧ μ.ker ≤ κ.ker := by
  obtain hℓ | rfl := em' (ℓ = 2)
  · -- A subgroup of the cyclic group (ℤ/ℓ^(k+2))ˣ is cyclic.
    have (n : ℕ) : IsCyclic (ZMod (ℓ ^ n))ˣ := isCyclic_units_of_prime_pow ℓ Fact.out hℓ n
    exact ⟨κ, fun k ↦ inferInstance, hκ, le_rfl⟩
  refine ⟨κ ^ 2, fun k ↦ ?_, by fun_prop, fun g hg ↦ ?_⟩
  · -- The powers of 5 have index 2 in (ℤ/2^(k+2))ˣ, so they contain all squares.
    have h_five : Nat.Coprime 5 (2 ^ (k + 2)) := by bound
    refine isCyclic_of_le (H' := zpowers (unitOfCoprime 5 h_five)) ?_
    rintro _ ⟨g, rfl⟩
    simp [sq_mem_of_index_two (index_zpowers_unitOfCoprime_five k h_five)]
  · -- κ(g) = ±1, and κ(g) = −1 would give 4 ∣ −2.
    have h_sq : (κ g).val ^ 2 = 1 := by simpa [← Units.val_pow_eq_pow_val] using hg
    have h_not_four : ¬(4 : ℤ_[2]) ∣ -1 - 1 :=
      mod_cast (pow_p_dvd_int_iff (p := 2) 2 (-2)).not.mpr (by norm_num)
    have h_ne : (κ g).val ≠ -1 := fun h ↦ h_not_four (by simpa only [h] using hκ_four g)
    exact Units.val_eq_one.mp ((sq_eq_one_iff.mp h_sq).resolve_right h_ne)

/-- Let ℓ be a prime and κ a continuous homomorphism from a compact group Γ to ℤ_ℓ^× with values in
1 + 4ℤ_ℓ (for odd ℓ this is no condition, as 4 is a unit of ℤ_ℓ; for ℓ = 2 it keeps κ away from
−1). Then κ has procyclic image: for some γ, every open subgroup S that contains γ and ker κ is all
of Γ. -/
lemma New.Selmer.exists_procyclic_generator {ℓ : ℕ} {Γ : Type*} [Fact ℓ.Prime] [Group Γ]
    [TopologicalSpace Γ] [CompactSpace Γ] [ContinuousMul Γ] (κ : Γ →* ℤ_[ℓ]ˣ) (hκ : Continuous κ)
    (hκ_four : ∀ g : Γ, 4 ∣ (κ g).val - 1) :
    ∃ γ : Γ, ∀ S : Subgroup Γ, κ.ker ≤ S → S.IsOpen → γ ∈ S → ∀ g : Γ, g ∈ S := by
  -- Replace κ by a μ with ker μ ≤ ker κ and cyclic image modulo every ℓ^(k+2), generated by
  -- μ(γ k). A cluster point δ of the γ k works: an open S ∋ δ holds γ k for arbitrarily large k,
  -- and an open S ≥ ker κ holds the kernel of μ modulo ℓ^(k+2) for large k.
  let red (k : ℕ) : ℤ_[ℓ]ˣ →* (ZMod (ℓ ^ (k + 2)))ˣ :=
    Units.map (toZModPow (k + 2) : ℤ_[ℓ] →+* ZMod (ℓ ^ (k + 2))).toMonoidHom
  obtain ⟨μ, μ_cyclic, μ_cont, μ_ker⟩ := exists_isCyclic_range_toZModPow κ hκ hκ_four
  have exists_gen (k : ℕ) : ∃ γ : Γ, ∀ g : Γ,
      ∃ n : ℤ, (red k).comp μ γ ^ n = (red k).comp μ g := by
    obtain ⟨⟨_, γ, rfl⟩, hγ⟩ := (μ_cyclic k).exists_generator
    exact ⟨γ, fun g ↦ (mem_zpowers_iff.mp (hγ ⟨_, g, rfl⟩)).imp fun n hn ↦ Subtype.ext_iff.mp hn⟩
  choose γ hγ using exists_gen
  obtain ⟨δ, hδ⟩ : ∃ δ : Γ, ClusterPt δ (atTop.map γ) := exists_clusterPt_of_compactSpace _
  refine ⟨δ, fun S S_ker S_open hδS g ↦ ?_⟩
  -- As Γ is compact, μ is a closed map, so S contains all x with μ(x) close to 1.
  have near_one : ∀ᶠ y : ℤ_[ℓ] in nhds 1, ∀ x ∈ (Units.val ∘ μ) ⁻¹' {y}, x ∈ S :=
    (Units.continuous_val.comp μ_cont).isClosedMap.eventually_nhds_fiber 1 fun x hx ↦
      S_open.mem_nhds (S_ker (μ_ker (Units.ext hx)))
  obtain ⟨ε, ε_pos, hε⟩ := Metric.eventually_nhds_iff.mp near_one
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (ℓ : ℝ) ^ (-(j : ℤ)) < ε := exists_pow_neg_lt ℓ ε_pos
  obtain ⟨k, hjk, hγS⟩ : ∃ k : ℕ, j ≤ k ∧ γ k ∈ S :=
    frequently_atTop.mp (hδ.frequently (S_open.mem_nhds hδS)) j
  -- μ(x) ≡ 1 modulo ℓ^(k+2), with j ≤ k, gives |μ(x) − 1| ≤ ℓ^(−j) < ε.
  have ker_le : ((red k).comp μ).ker ≤ S := fun x hx ↦ by
    have hx_one : toZModPow (k + 2) (μ x : ℤ_[ℓ]) = 1 := by simpa [red, Units.ext_iff] using hx
    have hle : j ≤ k + 2 := le_add_right hjk
    have hx_mem : (μ x : ℤ_[ℓ]) - 1 ∈ RingHom.ker (toZModPow j) := by
      simp [← cast_toZModPow j (k + 2) hle, hx_one]
    rw [ker_toZModPow, ← norm_le_pow_iff_mem_span_pow, ← dist_eq_norm] at hx_mem
    exact hε (hx_mem.trans_lt hj) x rfl
  -- Modulo that kernel, g is a power of γ k.
  obtain ⟨n, hn⟩ := hγ k g
  have h_mem : (γ k ^ n)⁻¹ * g ∈ S := ker_le (by simp [-MonoidHom.coe_comp, hn])
  simpa using S.mul_mem (S.zpow_mem hγS n) h_mem

/-- The element γ generates Γ modulo the kernel of κ: the only closed subgroup that contains γ and
ker κ is Γ. -/
def MonoidHom.IsGeneratorModKer {Γ A : Type*} [Group Γ] [TopologicalSpace Γ] [Group A]
    (κ : Γ →* A) (γ : Γ) : Prop :=
  ∀ S : Subgroup Γ, IsClosed (S : Set Γ) → κ.ker ≤ S → γ ∈ S → S = ⊤

/-- If γ generates Γ modulo the kernel of κ, then so does γ⁻¹. -/
lemma MonoidHom.IsGeneratorModKer.inv {Γ A : Type*} [Group Γ] [TopologicalSpace Γ] [Group A]
    {κ : Γ →* A} {γ : Γ} (hγ : κ.IsGeneratorModKer γ) : κ.IsGeneratorModKer γ⁻¹ :=
  fun S S_closed S_ker h_mem ↦ hγ S S_closed S_ker (inv_mem_iff.1 h_mem)

/-- Let γ generate the compact group Γ modulo the closed kernel of κ. Then every g is a product
h q with h in ker κ and q in the closure of the powers of γ. -/
lemma MonoidHom.IsGeneratorModKer.exists_mul_eq {Γ A : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [Group A] {κ : Γ →* A} {γ : Γ}
    (hγ : κ.IsGeneratorModKer γ) (h_ker : IsClosed (κ.ker : Set Γ)) (g : Γ) :
    ∃ h ∈ κ.ker, ∃ q ∈ (zpowers γ).topologicalClosure, h * q = g := by
  have h_closed : IsClosed (↑(κ.ker ⊔ (zpowers γ).topologicalClosure) : Set Γ) := by
    simpa [normal_mul] using h_ker.mul_right_of_isCompact (isClosed_topologicalClosure _).isCompact
  have h_top : κ.ker ⊔ (zpowers γ).topologicalClosure = ⊤ :=
    hγ _ h_closed le_sup_left (mem_sup_right (le_topologicalClosure _ (mem_zpowers γ)))
  exact mem_sup_of_normal_left.1 (h_top.ge (mem_top g))

/-- If γ generates Γ modulo the kernel of a continuous character κ with values in ℤ_ℓ^×, then
κ(γ)^a − 1 divides κ(g)^a − 1 for every g. -/
lemma MonoidHom.IsGeneratorModKer.pow_sub_one_dvd {ℓ : ℕ} {Γ : Type*} [Fact ℓ.Prime] [Group Γ]
    [TopologicalSpace Γ] {κ : Γ →* ℤ_[ℓ]ˣ} {γ : Γ} (hγ : κ.IsGeneratorModKer γ)
    (hκ : Continuous κ) (a : ℕ) (g : Γ) : (κ γ ^ a).val - 1 ∣ (κ g ^ a).val - 1 := by
  -- The g with this property form the kernel S of κ^a modulo the closed ideal (κ(γ)^a − 1).
  let I : Ideal ℤ_[ℓ] := .span {(κ γ ^ a).val - 1}
  let S : Subgroup Γ := ((Units.map (Ideal.Quotient.mk I).toMonoidHom).comp (κ ^ a)).ker
  have mem_S (x : Γ) : x ∈ S ↔ (κ x ^ a).val - 1 ∈ I := by
    simp [S, Units.ext_iff, ← Ideal.Quotient.eq]
  have S_closed : IsClosed (S : Set Γ) := by
    rw [show (S : Set Γ) = (fun x ↦ (κ x ^ a).val - 1) ⁻¹' I from Set.ext mem_S]
    exact (IsNoetherianRing.isClosed_ideal I).preimage (by fun_prop)
  have ker_le : κ.ker ≤ S := fun x hx ↦ by simp [mem_S, mem_ker.1 hx]
  have h_top : S = ⊤ := hγ S S_closed ker_le ((mem_S γ).2 (Ideal.mem_span_singleton_self _))
  exact Ideal.mem_span_singleton.1 ((mem_S g).1 (h_top.ge (mem_top g)))

/-- A profinite group has a generator modulo the kernel of a continuous character with values in
1 + 4ℤ_ℓ. -/
lemma New.Selmer.exists_isGeneratorModKer {ℓ : ℕ} {Γ : Type*} [Fact ℓ.Prime] [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {κ : Γ →* ℤ_[ℓ]ˣ} (hκ : Continuous κ) (hκ_four : ∀ g : Γ, 4 ∣ (κ g).val - 1) :
    ∃ γ : Γ, κ.IsGeneratorModKer γ := by
  obtain ⟨γ, hγ⟩ := exists_procyclic_generator κ hκ hκ_four
  refine ⟨γ, fun S S_closed S_ker hγS ↦ ?_⟩
  -- A closed subgroup is the intersection of the open subgroups that contain it.
  have h_inf : S = sInf {N : Subgroup Γ | IsOpen (N : Set Γ) ∧ S ≤ N} :=
    ProfiniteGrp.closedSubgroup_eq_sInf_open ⟨S, S_closed⟩
  rw [h_inf, sInf_eq_top]
  exact fun N ⟨N_open, hSN⟩ ↦ (eq_top_iff' N).2 (hγ N (S_ker.trans hSN) N_open (hSN hγS))

end ProcyclicImage
