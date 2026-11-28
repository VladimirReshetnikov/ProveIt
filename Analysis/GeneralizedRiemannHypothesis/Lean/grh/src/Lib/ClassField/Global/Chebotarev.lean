import Lib.ClassField.Global.NormTheorems

/-!
# Chebotarev: Frobenii at primes of degree one in every nonempty open set

The qualitative form of Chebotarev's theorem used in the proof: `New.chebotarev`. It is reduced to a
cyclic extension, where it follows from the second inequality `New.second_inequality`.

Notions from other files:
* `New.IsFrob`: `σ` stabilises the valuation subring `A` and `σ • x ≡ x ^ q` modulo the maximal
  ideal for all `x ∈ A`.
* `New.IsPlaceOver`: `IsPlaceOver A v` says that the valuation subring `A` of `Ω` lies over the
  prime `v` of `K`: an integer of `K` is in the maximal ideal of `A` exactly when it lies in `v`.

## Relation to the literature

Known result: Chebotarev's density theorem, existence form. Only existence is proved, namely that
Frobenius elements at primes of degree one outside a finite set are dense in the absolute Galois
group, and no density value is given. Source: J. S. Milne, Class Field Theory, VIII 7.4 (Deuring's
reduction); Stevenhagen–Lenstra, Chebotarëv and his density theorem, Math. Intelligencer 18 (1996).
-/

open QuotientGroup Subgroup New QZChar Nat

/-- Chebotarev's theorem, existence form (no density is given). Let `W` be a nonempty open subset of
the absolute Galois group `Gal(Ω/K)` of the number field `K`, and `S` a finite set of finite places
of `K`. Then (a) some place `v ∉ S` has prime norm `v.q` (the size of its residue field), with a
place `A` of `Ω` over it (a valuation subring, `New.IsPlaceOver`); (b) some arithmetic Frobenius
at `A` for `v.q` lies in `W`; (c) every arithmetic Frobenius at `A` for `v.q` lies in `W`. -/
lemma New.chebotarev {K : Type} [Field K] [NumberField K] [Algebra K Ω] {W : Set Gal(Ω/K)}
    (hW : IsOpen W) (hW_ne : W.Nonempty) {S : Set (FinPlace K)} (hS : S.Finite) :
    -- (a)
    ∃ v : FinPlace K, v ∉ S ∧
      v.q.Prime ∧
      ∃ A : ClosurePlace,
        IsPlaceOver A v ∧
        -- (b)
        ∃ σ ∈ W,
          IsFrob A v.q σ ∧
          -- (c)
          ∀ τ : Gal(Ω/K), IsFrob A v.q τ → τ ∈ W := by
  -- Take `g ∈ W`, an open normal `U` with `g U ⊆ W`, and the fixed field `L` of `H = ⟨g⟩ U`. Over
  -- `L` the extension cut out by `U` is cyclic, and the second inequality gives primes `w` of `L`
  -- of prime norm whose Frobenius is `g` modulo `U`. The prime of `K` below `w` has the same norm.
  obtain ⟨g, hg_mem⟩ : ∃ g : Gal(Ω/K), g ∈ W := hW_ne
  have h_one_mem : (1 : Gal(Ω/K)) ∈ (fun x : Gal(Ω/K) ↦ g * x) ⁻¹' W := by simpa using hg_mem
  obtain ⟨⟨U, hU_normal⟩, hU : ∀ x ∈ U.toSubgroup, g * x ∈ W⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (hW.preimage (continuous_const_mul g)) h_one_mem
  let H : Subgroup Gal(Ω/K) := zpowers g ⊔ U.toSubgroup
  have hH_open : Fact H.IsOpen := ⟨isOpen_mono le_sup_right U.isOpen'⟩
  let L : IntermediateField K Ω := fixedFieldOf H
  let g' : H := ⟨g, mem_sup_left (mem_zpowers g)⟩
  -- `H / U` is a quotient of `⟨g⟩`, so `U` is the kernel of a character `χ` of `H`.
  have h_cyclic : IsCyclic (H ⧸ U.toSubgroup.subgroupOf H) := by
    -- By the second isomorphism theorem, `H / U` is isomorphic to `⟨g⟩ / (⟨g⟩ ∩ U)`.
    have h_quot : IsCyclic (zpowers g ⧸ U.toSubgroup.subgroupOf (zpowers g)) :=
      isCyclic_of_surjective _ (mk'_surjective _)
    exact (quotientInfEquivProdNormalQuotient (zpowers g) U.toSubgroup).isCyclic.mp h_quot
  obtain ⟨χ, hχ⟩ : ∃ χ : QZChar H, ker χ = U.toSubgroup.subgroupOf H :=
    exists_ker_eq_of_isCyclic ⟨_, H.subgroupOf_isOpen _ U.isOpen'⟩ h_cyclic
  obtain ⟨a, ha⟩ : ∃ a : (𝔸f L)ˣ, artinMap H a = mk g' := artinMap_surjective H (mk g')
  -- The kernel of `χ ∘ artinMap` is open and holds the totally positive elements and the norms from
  -- the field cut out by `χ`. By the last part of the second inequality
  -- (`frequently_prime_uniformizer_div_mem_of_adeleNorm_mem`), `ϖ_w a` lies in it for infinitely
  -- many `w` of prime norm (`ϖ_w` is the uniformiser idele at `w`).
  have h_ker_open : ((abelianLift χ).comp (artinMap H)).ker.IsOpen :=
    continuous_iff_forall_isOpen_ker_comp.mp continuous_artinMap χ
  have h_ker_pos (x : Lˣ) (hx : IsTotallyPositive x.val) :
      principalIdele x ∈ ((abelianLift χ).comp (artinMap H)).ker := by
    simp [artinMap_principalIdele_eq_one_of_isTotallyPositive hx]
  have h_often : ∃ᶠ w : FinPlace L in .cofinite, w.q.Prime ∧
      locIdele w (uniformizer w) / a⁻¹ ∈ ((abelianLift χ).comp (artinMap H)).ker :=
    frequently_prime_uniformizer_div_mem_of_adeleNorm_mem _ h_ker_open h_ker_pos
      abelianLift_artinMap_adeleNorm a⁻¹
  -- Almost all `w` lie over a prime of `K` outside `S` at which all inertia groups lie in `U`; take
  -- one of them with `ϖ_w a ∈ ker (χ ∘ artinMap)`.
  have h_almost : ∀ᶠ w : FinPlace L in .cofinite, w.below K ∉ S ∧
      ∀ A : ClosurePlace, IsPlaceOver A (w.below K) → inertiaGroup Gal(Ω/K) A ≤ U.toSubgroup :=
    tendsto_place_comap_cofinite (algebraMap K L)
      (hS.eventually_cofinite_notMem.and (finite_ramified U.isOpen'))
  obtain ⟨w, ⟨hw_prime, hw_ker⟩, hw_notMem, hw_unram⟩ := (h_often.and_eventually h_almost).exists
  have hA : IsPlaceOver (placeOver w) (w.below K) := w.isPlaceOver_placeOver.isPlaceOver_below
  have h_norm : w.q = (w.below K).q := by
    -- `w.q` is a power of the norm below, with the inertia degree as exponent; as `w.q` is a
    -- prime, the exponent is one.
    have h_pow : (w.below K).q ^ w.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = w.q :=
      (w.below K).asIdeal.absNorm_pow_inertiaDeg w.asIdeal
    rw [← h_pow] at hw_prime ⊢
    rw [Nat.Prime.eq_one_of_pow hw_prime, pow_one]
  -- The symbol of `ϖ_w` is the inverse of a Frobenius `σ`, so `χ σ = χ g` and `g⁻¹ σ ∈ U`.
  obtain ⟨σ, hσ, hσ_art⟩ :=
    w.isPlaceOver_placeOver.exists_isFrob_localArtin_eq_inv (Γ := H) (v_uniformizer w)
  have h_symbol : artinAt H w (uniformizer w) = ↑σ⁻¹ :=
    w.isPlaceOver_placeOver.artinAt_eq_of_localArtin_eq hσ_art
  have hσg : (χ : H → QZ) σ = (χ : H → QZ) g' := by
    simpa [h_symbol, inv_mul_eq_one, ha] using hw_ker
  have hσU : g⁻¹ * σ ∈ U.toSubgroup := hχ.le ((toHom χ).eq_iff.mp hσg)
  rw [h_norm] at hσ hw_prime
  have hσ_frob : IsFrob (placeOver w) (w.below K).q ((σ : H) : Gal(Ω/K)) := hσ
  -- Any other Frobenius differs from `σ` by inertia, which lies in `U`.
  have h_all (τ : Gal(Ω/K)) (hτ : IsFrob (placeOver w) (w.below K).q τ) : τ ∈ W := by
    have h_inert : ((σ : H) : Gal(Ω/K))⁻¹ * τ ∈ inertiaGroup Gal(Ω/K) (placeOver w) :=
      hσ_frob.inv_mul_mem_inertiaGroup hτ
    have h_mem : g * (g⁻¹ * σ * (((σ : H) : Gal(Ω/K))⁻¹ * τ)) ∈ W :=
      hU _ (mul_mem hσU (hw_unram _ hA h_inert))
    simpa using h_mem
  exact ⟨w.below K, hw_notMem, hw_prime, placeOver w, hA, ((σ : H) : Gal(Ω/K)), h_all _ hσ_frob,
    hσ_frob, h_all⟩
