import Lib.ClassField.Local.ArtinMap

/-!
# The global Artin map: product of local symbols, continuity, splitting and norms

Γ is the Galois group of an algebraic closure Ω of a number field K (`New.IsProGalois`), and
`New.QZChar.abelianLift χ` is a continuous character χ : Γ → ℚ/ℤ seen on Γ^ab, written
multiplicatively. `New.artinAt` and `New.artinMap` are the local and global Artin maps with values
in Γ^ab; `New.decompGroup` and `New.inertiaGroup` are the decomposition and inertia groups of a
valuation subring A.

* `New.IsPlaceOver.range_abelianLift_comp_artinAt`,
  `New.IsPlaceOver.artinAt_units_trivial_iff_inertiaGroup_le`: the local symbols at v give the
  values of χ on the decomposition group; those of units vanish iff χ kills inertia.
* `New.IsPlaceOver.q_eq_and_comap_ne_self_of_decompGroup_le`: v splits completely in a Galois
  extension L of K whose group Gal(Ω/L) contains the decomposition group.
* `New.abelianLift_artinMap_eq_finprod`: the global symbol is the product of the local symbols.
* `New.continuous_artinMap`: the global Artin map is continuous.
* `New.artinMap_map_adeleNorm`: the Artin maps of K and of an extension L are compatible with the
  norm.

Notions from other files:
* `New.IsPlaceOver A v`: the valuation subring A of Ω lies over the finite place v of K.
* `New.ideleAt v a` is the component at v of a finite idele a; `New.locIdele v x` is the finite
  idele with component x at v and 1 elsewhere; `New.idelesUnitOff S` is the group of finite ideles
  that are units at every place outside S.

## Relation to the literature

Known; see `Lib.ClassField.Global.AlbertBrauerHasseNoether` for sources.
-/

namespace New

open Module QZChar Set FinPlace IsGalois

variable {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [EmbeddedNumberField K]

/-- The character χ, as a homomorphism on Γ, takes at g the value of `abelianLift χ` at the class
of g. -/
private lemma QZChar.toHom_eq_abelianLift [IsTopologicalGroup Γ] (χ : QZChar Γ) (g : Γ) :
    toHom χ g = abelianLift χ (g : TopologicalAbelianization Γ) :=
  rfl

/-- g lies in the kernel of χ exactly when `abelianLift χ` kills the class of g. -/
private lemma QZChar.mem_ker_iff_abelianLift_eq_one [IsTopologicalGroup Γ] (χ : QZChar Γ) (g : Γ) :
    g ∈ ker χ ↔ abelianLift χ (g : TopologicalAbelianization Γ) = 1 :=
  Iff.rfl

namespace IsPlaceOver

/- `A` is a place of `Ω` over the finite place `v` of `K` (hypothesis `h`), `χ` a character of
`Γ`, `L ⊂ Ω` a finite Galois extension of `K`, and `U` the subgroup Gal(Ω/L) of `Γ`. -/
variable {A : ClosurePlace} {v : FinPlace K} (χ : QZChar Γ)
  {L : Type*} [Field L] [EmbeddedNumberField L] [Algebra K L]
  (h : IsPlaceOver A v) [MulSemiringAction Γ Ω] [G : IsProGalois Γ K Ω]
  (U : Subgroup Γ) [IsGalois K L] [IsScalarTower K L Ω] [Fact U.IsOpen] [IsProGalois U L Ω]

include h

/-! ### One place: splitting and the local symbol -/

/-- Let `L / K` be Galois with `U = Gal(Ω/L)`, and let `A` be a place of `Ω` over `v`. The number of
places of `L` over `v` times the index of `U ⊓ D` in the decomposition group `D` of `A` is
`[L : K]`. -/
lemma ncard_above_mul_relIndex_eq_finrank :
    {u : FinPlace L | u.below K = v}.ncard * U.relIndex (decompGroup Γ A) = finrank K L := by
  -- For the place `u` of `L` under `A` the index is `e f`, and `e f g = n`.
  obtain ⟨u, hu, rfl⟩ := h.exists_above (L := L)
  obtain ⟨-, -, h_index : U.relIndex (decompGroup Γ A) =
      u.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        u.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)⟩ :=
    h.ramification_in_tower U hu
  rw [h_index, u.ncard_mul_ramificationIdx_mul_inertiaDeg]

variable {U}

/-- Let `L / K` be Galois with `U = Gal(Ω/L)`, and let `A` be a place of `Ω` over `v` whose
decomposition group lies in `U`. Then `v` splits completely: a place `u` of `L` over `v` has the
residue cardinality of `v`, and no nontrivial element of `Gal(L/K)` fixes `u`. -/
lemma q_eq_and_comap_ne_self_of_decompGroup_le (h_dec : decompGroup Γ A ≤ U) (u : FinPlace L)
    (hu : u.below K = v) :
    u.q = v.q ∧ ∀ σ : Gal(L/K), σ ≠ 1 → u.comap σ ≠ u := by
  -- The index in `ncard_above_mul_relIndex_eq_finrank` is `1`, so there are `n = [L : K]` places
  -- over `v`.
  have h_card : {u : FinPlace L | u.below K = v}.ncard = finrank K L := by
    simp [← h.ncard_above_mul_relIndex_eq_finrank (L := L) U, Subgroup.relIndex_eq_one.mpr h_dec]
  refine ⟨?_, fun σ hσ h_fix ↦ hσ ?_⟩
  · -- In `e f g = n` (`ncard_mul_ramificationIdx_mul_inertiaDeg`) we have `g = n`, so the residue
    -- degree `f` is `1`, and the norm of `u` is the norm of `v` to the power `f`.
    have h_efg := u.ncard_mul_ramificationIdx_mul_inertiaDeg (K := K)
    have h_ef : u.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        u.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 := by
      rw [hu, h_card] at h_efg
      simpa [finrank_pos.ne'] using h_efg
    obtain ⟨-, h_f⟩ := mul_eq_one.mp h_ef
    simp [← hu, ← (u.below K).asIdeal.absNorm_pow_inertiaDeg, h_f]
  · -- The orbit of `u` contains all `[L : K]` places over `v`, so the orbit map is injective.
    let orbit (σ : Gal(L/K)) : FinPlace L := u.comap σ
    have h_le : Nat.card Gal(L/K) ≤ (range orbit).ncard := by
      rw [card_aut_eq_finrank, ← h_card]
      exact ncard_le_ncard fun u' hu' ↦ exists_gal_comap_eq (hu.trans hu'.symm)
    have h_inj : Function.Injective (rangeFactorization orbit) :=
      (rangeFactorization_surjective.bijective_of_nat_card_le h_le).injective
    exact h_inj (Subtype.ext h_fix)

/-- Let `A` be a place of `Ω` over `v`. The values of a character `χ` on the local symbols at `v`
are its values on the decomposition group of `A`. -/
lemma range_abelianLift_comp_artinAt :
    ((abelianLift χ).comp (New.artinAt Γ v)).range = (decompGroup Γ A).map (toHom χ) := by
  apply le_antisymm
  · -- The local symbol of `x` is the class of some `g` in the decomposition group.
    rintro _ ⟨x, rfl⟩
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (localArtin Γ A v x)
    have h_art : New.artinAt Γ v x = ((g : Γ) : TopologicalAbelianization Γ) :=
      h.artinAt_eq_of_localArtin_eq hg.symm
    refine ⟨g, g.property, ?_⟩
    rw [MonoidHom.comp_apply, h_art, toHom_eq_abelianLift]
  · -- `localArtin` has dense range, so it meets the open fibre of `χ` through `g`.
    rintro _ ⟨g, hg, rfl⟩
    let ψ : QZChar (decompGroup Γ A) := comap (subgroupIncl (decompGroup Γ A)) χ
    -- Every subset of `ℚ/ℤ` is open.
    have fibre_open : IsOpen (abelianLift ψ ⁻¹' {toHom χ g}) :=
      (continuous_abelianLift ψ).isOpen_preimage _ trivial
    have g_mem : (⟦⟨g, hg⟩⟧ : TopologicalAbelianization (decompGroup Γ A)) ∈
        abelianLift ψ ⁻¹' {toHom χ g} := by
      simp [ψ, QZChar.comap, toHom_eq_abelianLift, subgroupIncl]
    obtain ⟨x, hx : abelianLift ψ (localArtin Γ A v x) = toHom χ g⟩ :=
      h.denseRange_localArtin.exists_mem_open fibre_open ⟨_, g_mem⟩
    exact ⟨x, (h.abelianLift_artinAt χ x).trans hx⟩

/-- Let `A` be a place of `Ω` over `v`. A character `χ` kills all local symbols at `v` exactly when
it is trivial on the decomposition group of `A`. -/
lemma artinAt_trivial_iff_decompGroup_le :
    (∀ x : (LocField v)ˣ, abelianLift χ (New.artinAt Γ v x) = 1) ↔ decompGroup Γ A ≤ ker χ := by
  simp [← Subgroup.map_eq_bot_iff, ← h.range_abelianLift_comp_artinAt, Subgroup.eq_bot_iff_forall]

/-- Let `A` be a place of `Ω` over `v`. A character `χ` kills the local symbols of the units of
`K_v` exactly when it is trivial on the inertia group of `A`.

This is one side of the mutual annihilation of unramified classes (Milne, Arithmetic Duality
Theorems, I.2.6), for global characters. -/
lemma artinAt_units_trivial_iff_inertiaGroup_le :
    (∀ x : (LocField v)ˣ, Valued.v x.val = 1 → abelianLift χ (New.artinAt Γ v x) = 1) ↔
      inertiaGroup Γ A ≤ ker χ := by
  -- The symbols of the units are exactly the classes of the elements of the inertia group.
  refine ⟨fun h_unit g hg ↦ ?_, fun h_ine x hx ↦ ?_⟩
  · -- An element of the inertia group is the symbol of a unit.
    obtain ⟨x, hx_unit, hx_art⟩ := h.exists_localArtin_eq_of_mem_inertiaGroup hg
    rw [mem_ker_iff_abelianLift_eq_one, ← h.artinAt_eq_of_localArtin_eq hx_art]
    exact h_unit x hx_unit
  · -- The symbol of a unit is the class of an element `g` of inertia, which `χ` kills.
    obtain ⟨g, hg_ine, hg_art⟩ := h.exists_mem_inertiaGroup_localArtin_eq (Γ := Γ) hx
    rw [h.artinAt_eq_of_localArtin_eq hg_art, ← mem_ker_iff_abelianLift_eq_one]
    exact h_ine hg_ine

/-- The local symbol of an unramified character. Let `A` be a place of `Ω` over `v`, let `χ` be
trivial on the inertia group of `A`, and let `φ` be a Frobenius element at `A`. Then `χ` takes the
local symbol at `v` of `x ∈ Kˣ` to `(v.valuation K x).log • χ φ`, that is `-(ord_v x • χ φ)` where
`ord_v x = -(v.valuation K x).log`.
This is a form of the local reciprocity map in the unramified case (Serre, Local Fields).
Uniformisers go to geometric Frobenius, hence the minus sign. -/
lemma abelianLift_artinAt_of_inertiaGroup_le_ker (h_unr : inertiaGroup Γ A ≤ ker χ) {φ : Γ}
    (hφ : IsFrob A v.q φ) (x : Kˣ) :
    abelianLift χ (New.artinAt Γ v (ideleAt v (principalIdele x))) =
      Multiplicative.ofAdd ((v.valuation K x).log • χ.val φ) := by
  -- A uniformiser `π` of the completion whose local symbol is the class of `φ⁻¹`.
  obtain ⟨π, hπ_val, hπ_art⟩ := h.exists_localArtin_eq_of_isFrob (by rwa [inv_inv] :
    IsFrob A v.q φ⁻¹⁻¹)
  have h_art_π : New.artinAt Γ v π = ((φ⁻¹ : Γ) : TopologicalAbelianization Γ) :=
    h.artinAt_eq_of_localArtin_eq hπ_art
  -- Multiplying `x` by the power of `π` that cancels its valuation gives a unit, and an
  -- unramified `χ` kills the symbol of a unit.
  let u : (LocField v)ˣ := ideleAt v (principalIdele x) * π ^ (v.valuation K x).log
  have hu : Valued.v u.val = 1 := by
    have h_cancel : v.valuation K x * WithZero.exp (-(v.valuation K x).log) = 1 := by
      rw [WithZero.exp_neg, WithZero.exp_log (by simp), mul_inv_cancel₀ (by simp)]
    simpa [u, ideleAt, hπ_val] using h_cancel
  have h_unit_symbol : abelianLift χ (New.artinAt Γ v u) = 1 :=
    (h.artinAt_units_trivial_iff_inertiaGroup_le χ).mpr h_unr u hu
  simpa [u, h_art_π, mul_inv_eq_one] using h_unit_symbol

end IsPlaceOver

/-! ### The global Artin map -/

/- `χ` is a character of `Γ` and `L` a number field over `K`. -/
variable (χ : QZChar Γ) {L : Type} [Field L] [EmbeddedNumberField L] [Algebra K L]
  [MulSemiringAction Γ Ω] [G : IsProGalois Γ K Ω]

/-- Let `χ` be a character of the Galois group `Γ` of `Ω` over the number field `K`. A finite idele
`a` of `K` close enough to `1` is a unit at every place, and `χ` kills all local symbols of `a`. -/
lemma QZChar.eventually_artinAt_eq_one :
    ∀ᶠ a : (𝔸f K)ˣ in nhds 1,
      a ∈ idelesUnitOff ∅ ∧ ∀ v : FinPlace K, abelianLift χ (artinAt Γ v (ideleAt v a)) = 1 := by
  -- Only finitely many places ramify for `χ`. At these the condition is open; at the others
  -- it holds for every unit idele. (Every homomorphism from the units of a completion to the
  -- abelianisation of `Γ` is continuous: `continuous_hom_locField_units`.)
  let R : Set (FinPlace K) :=
    {v : FinPlace K | ∀ A : ClosurePlace, IsPlaceOver A v → inertiaGroup Γ A ≤ ker χ}ᶜ
  have h_open : IsOpen (⋂ v ∈ R, ideleAt v ⁻¹' ((abelianLift χ).comp (artinAt Γ v)).ker) := by
    refine (finite_ramified (isOpen_ker χ)).isOpen_biInter fun v _ ↦
      IsOpen.preimage (by fun_prop) ?_
    exact continuous_iff_forall_isOpen_ker_comp.mp (continuous_hom_locField_units _) χ
  filter_upwards [((isOpen_idelesUnitOff ∅).inter h_open).mem_nhds (by simp)]
    with a ⟨h_unit, h_ram⟩
  refine ⟨h_unit, fun v ↦ ?_⟩
  by_cases hv : v ∈ R
  · exact mem_iInter₂.1 h_ram v hv
  · have h_unr : inertiaGroup Γ (placeOver v) ≤ ker χ :=
      not_not.1 hv _ v.isPlaceOver_placeOver
    exact (v.isPlaceOver_placeOver.artinAt_units_trivial_iff_inertiaGroup_le χ).2 h_unr _
      (mem_idelesUnitOff.1 h_unit v (notMem_empty v))

/-- A character `χ` of `Γ` takes the global Artin symbol of a finite idele `a` to the product over
the finite places `v` of its values on the local symbols of the components of `a`. -/
@[local simp]
lemma abelianLift_artinMap_eq_finprod (χ : QZChar Γ) (a : (𝔸f K)ˣ) :
    abelianLift χ (artinMap Γ a) =
      ∏ᶠ v : FinPlace K, abelianLift χ (artinAt Γ v (ideleAt v a)) := by
  -- Almost all factors are `1`: those where `χ` is unramified and `a` is a unit.
  have h_fin (χ : QZChar Γ) (a : (𝔸f K)ˣ) :
      ∀ᶠ v : FinPlace K in .cofinite, abelianLift χ (artinAt Γ v (ideleAt v a)) = 1 := by
    filter_upwards [finite_ramified (Ω := Ω) (isOpen_ker χ), finite_setOf_valued_val_ne_one a]
      with v h_unr (hv : Valued.v (a.val v) = 1)
    exact (v.isPlaceOver_placeOver.artinAt_units_trivial_iff_inertiaGroup_le χ).2
      (h_unr _ v.isPlaceOver_placeOver) _ hv
  -- The product is multiplicative in `χ` and in `a`, so by Pontryagin duality
  -- (`exists_hom_abelianLift_eq`) it comes from a homomorphism.
  let F (a : (𝔸f K)ˣ) (χ : QZChar Γ) : Multiplicative QZ :=
    ∏ᶠ v : FinPlace K, abelianLift χ (artinAt Γ v (ideleAt v a))
  have h_add (a : (𝔸f K)ˣ) (χ ξ : QZChar Γ) : F a (χ + ξ) = F a χ * F a ξ := by
    refine (finprod_congr fun v ↦ ?_).trans (finprod_mul_distrib (h_fin χ a) (h_fin ξ a))
    -- On the class of `g` both sides are `χ g + ξ g`, by definition.
    exact (artinAt Γ v _).inductionOn fun _ ↦ rfl
  have h_mul (a b : (𝔸f K)ˣ) (χ : QZChar Γ) : F (a * b) χ = F a χ * F b χ := by
    simpa [F] using finprod_mul_distrib (h_fin χ a) (h_fin χ b)
  have h_hom : ∃ f : (𝔸f K)ˣ →* TopologicalAbelianization Γ,
      ∀ (χ : QZChar Γ) (a : (𝔸f K)ˣ), abelianLift χ (f a) = F a χ :=
    exists_hom_abelianLift_eq
      (.mk' (fun a ↦ .mk' (F a.toMul) (h_add _)) fun a b ↦ AddMonoidHom.ext (h_mul _ _))
  -- `artinMap` is a chosen homomorphism with this property.
  exact abelianLift_artinMap_eq_finprod_of_exists Γ h_hom χ a

/-- The global Artin map on the finite ideles of `K` is continuous. -/
@[fun_prop]
lemma continuous_artinMap : Continuous (artinMap Γ) := by
  -- For each character `χ` the kernel of `χ ∘ artinMap` contains the neighbourhood of `1` given by
  -- `eventually_artinAt_eq_one`.
  refine continuous_iff_forall_isOpen_ker_comp.mpr fun χ ↦ Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [eventually_artinAt_eq_one (K := K) χ] with a ⟨_, h_local⟩
  -- By the product formula `χ (Art a)` is a product of local values that are all `1`.
  simp [h_local]

/-- The global Artin symbol of the idele with component `x` at `v` and `1` elsewhere is the local
symbol of `x` at `v`. -/
@[simp]
lemma artinMap_locIdele (v : FinPlace K) (x : (LocField v)ˣ) :
    artinMap Γ (locIdele v x) = artinAt Γ v x :=
  -- In the product formula only the factor at `v` can differ from `1`.
  abelianization_ext fun χ ↦ by simp_all [finprod_eq_single _ v]

/-- Norm compatibility of the Artin map. Let `L / K` be an extension of number fields embedded in
`Ω`, let `Γ` and `Γ'` be their absolute Galois groups (topological groups acting on `Ω`), let `j` be
an endomorphism of `Ω` that extends `K → L`, and let `j` carry the action of `g ∈ Γ` to that of
`g' ∈ Γ'`. If the Artin symbol of the finite idele `y` of `L` is the class of `g'`, then the Artin
symbol of the norm of `y` to `K` is the class of `g`. -/
lemma artinMap_map_adeleNorm {Γ' : Type} [Group Γ'] [TopologicalSpace Γ'] [MulSemiringAction Γ' Ω]
    [IsProGalois Γ' L Ω] {y : (𝔸f L)ˣ} {g : Γ} {g' : Γ'} (hy : artinMap Γ' y = g') (j : Ω →+* Ω)
    (hj : ∀ x : K, j (algebraMap K Ω x) = algebraMap L Ω (algebraMap K L x))
    (hg : ∀ z : Ω, j (g • z) = g' • j z) :
    artinMap Γ (y.map (adeleNorm K L)) = g := by
  -- Both `a ↦ χ (Art (N a))` and `a ↦ χ (φ (Art a))` are continuous homomorphisms, where `φ` is
  -- the restriction along `j`; they agree on ideles with one component, hence everywhere
  -- (`mem_of_locIdele_mem`).
  obtain ⟨φ, hφ⟩ : ∃ φ : Γ' →ₜ* Γ, ∀ (s : Γ') (z : Ω), j (φ s • z) = s • j z :=
    exists_galois_restrict Γ Γ' j fun s x ↦ by rw [hj, smul_algebraMap]
  -- `φ g'` and `g` act in the same way on `Ω`.
  obtain rfl : φ g' = g := G.faithful.1 fun z ↦ j.injective ((hφ g' z).trans (hg z).symm)
  refine abelianization_ext fun χ ↦ ?_
  let H : Subgroup (𝔸f L)ˣ :=
    ((abelianLift χ).comp ((artinMap Γ).comp (Units.map (adeleNorm K L)))).eqLocus
      ((abelianLift (comap φ χ)).comp (artinMap Γ'))
  -- Both homomorphisms are continuous.
  have H_closed : IsClosed H.carrier := by
    refine isClosed_eq ?_ ?_ <;> simp only [MonoidHom.coe_comp] <;> fun_prop
  have loc_mem (w : FinPlace L) (x : (LocField w)ˣ) : locIdele w x ∈ H := by
    have hw : IsPlaceOver (placeOver w) w := w.isPlaceOver_placeOver
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (localArtin Γ' (placeOver w) w x)
    have hv : IsPlaceOver ((placeOver w).comap j) (w.below K) := by
      simp [IsPlaceOver, hj, comap_apply_lt_one_iff, ← hw _]
    -- Local norm compatibility: the norm of `x` has symbol `φ s` if `x` has symbol `s`.
    have h_norm : artinMap Γ ((locIdele w x).map (adeleNorm K L)) = φ s := by
      rw [adeleNorm_locIdele, artinMap_locIdele]
      exact hv.artinAt_eq_of_localArtin_eq
        ((hw.isNormCompatible φ.toMonoidHom j hφ hj).localArtin_localNorm hs.symm)
    -- So both homomorphisms take the value `χ (φ s)`.
    refine (congrArg (abelianLift χ) h_norm).trans ?_
    simp [hw.artinAt_eq_of_localArtin_eq hs.symm, abelianLift_mk, QZChar.comap]
  have hy_mem : y ∈ H := mem_of_locIdele_mem H_closed fun w ↦ loc_mem w (ideleAt w y)
  calc abelianLift χ (artinMap Γ (y.map (adeleNorm K L)))
      = abelianLift (comap φ χ) (artinMap Γ' y) := hy_mem
    _ = abelianLift χ (φ g') := congrArg (abelianLift (comap φ χ)) hy

end New
