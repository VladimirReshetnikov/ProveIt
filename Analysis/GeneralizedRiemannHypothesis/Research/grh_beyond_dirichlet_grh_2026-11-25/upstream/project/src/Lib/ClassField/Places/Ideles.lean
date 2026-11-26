import Lib.Adelic.Adeles.StrongApproximation
import Lib.General.Groups.ProfiniteCharacters
import Lib.General.Measure.HaarModulus

/-!
# Finite ideles, principal ideles and the class group; finite index of open subgroups

The finite ideles of a number field `K` are the units `(𝔸f K)ˣ` of the finite adeles. They embed in
the units of the adeles `New.𝔸 K`, the pairs of a map `NumberField.InfinitePlace K → ℂ` and a finite
adele, with component `1` at the infinite places. `New.FinPlace K` is the set of finite places, and
`New.LocField v` is the completion at `v`. The file defines principal, local and S-unit ideles and
proves their basic properties. It then relates the finite ideles to fractional ideals and the class
group, and deduces that every open subgroup containing the totally positive elements of `Kˣ` has
finite index.

## Main definitions and results

* `New.principalIdele`, `New.locIdele`, `New.ideleAt`: the principal idele of an element of `Kˣ`,
  the idele with one given component and `1` elsewhere, and the component at a place.
* `New.idelesUnitOff`: the ideles that are units outside `S`; open (`New.isOpen_idelesUnitOff`), and
  compact for `S = ∅` (`New.isCompact_idelesUnitOff_empty`).
* `New.exists_idele_divisor_hom`: the divisor map, with kernel the ideles that are units everywhere.
* `New.exists_idele_classGroup_hom`: a map to the class group whose kernel is `Kˣ` times these
  units.
* `New.exists_sup_idelesUnitOff_eq_top`: for a suitable finite `S`, every idele is a principal idele
  times a unit outside `S`.
* `New.finiteIndex_idele_subgroup_of_isOpen`: an open subgroup that contains the totally positive
  elements of `Kˣ` has finite index.

Notions from other files:
* `New.Ô K`: the integral finite adeles, whose component at every place lies in its ring of
  integers; `New.uniformizer w` is a chosen uniformiser of the completion at `w`.
* `S.unit K` (Mathlib): the `S`-units, the `x` in `Kˣ` of valuation `1` at every finite place
  outside `S`.

## Relation to the literature

Known; see `Lib.ClassField.Places.LocalFields` for sources.
-/

noncomputable section

/-!
## Finite ideles: principal and local ideles, S-unit ideles, positivity

`New.mem_of_locIdele_mem` and `New.eventually_unramified` rest on
`New.exists_finset_cover_mulSupport_ideleAt`, which comes from the compactness of
`New.idelesUnitOff ∅`.
-/

section Ideles

open IsDedekindDomain Set Units FiniteAdeleRing

namespace New

variable {K : Type*} [Field K] [NumberField K]

/-! ### Principal ideles, local ideles, components and ideles that are units outside `S` -/

/-- The diagonal homomorphism from K^× to the finite ideles of K. -/
abbrev principalIdele : Kˣ →* (𝔸f K)ˣ := map (algebraMap K (𝔸f K)).toMonoidHom

variable (S : Set (FinPlace K)) (a : (𝔸f K)ˣ) (v : FinPlace K)

/-- The homomorphism sending x ∈ K_v^× to the finite idele with component x at v and 1
elsewhere. -/
def locIdele : (LocField v)ˣ →* (𝔸f K)ˣ := unitsMapNonUnital (singleAdele v)

/-- The homomorphism from the finite ideles of K to the units of `New.𝔸 K` sending a to (1, a), with
component 1 at every infinite place. -/
abbrev finIdeleIncl : (𝔸f K)ˣ →* (𝔸 K)ˣ :=
  map (MonoidHom.inr (NumberField.InfinitePlace K → ℂ) (𝔸f K))

/-- For a finite place v, the homomorphism from K_v^× to the units of `New.𝔸 K` placing the element
at v and 1 at all other places, finite and infinite. -/
def locFullIdele : (LocField v)ˣ →* (𝔸 K)ˣ := finIdeleIncl.comp (unitsMapNonUnital (singleAdele v))

/-- The homomorphism sending a finite idele to its component in K_v^×. -/
def ideleAt : (𝔸f K)ˣ →* (LocField v)ˣ := map (evalAt v).toMonoidHom

/-- The group of finite ideles of K whose components at all places outside S are units. -/
def idelesUnitOff : Subgroup (𝔸f K)ˣ := ⨅ v ∉ S, ((map Valued.v.toMonoidHom).comp (ideleAt v)).ker

@[simp]
lemma locIdele_apply_self (x : (LocField v)ˣ) : (locIdele v x).val v = x := by simp [locIdele]

@[simp]
lemma ideleAt_locIdele (x : (LocField v)ˣ) : ideleAt v (locIdele v x) = x :=
  ext (locIdele_apply_self v x)

@[fun_prop]
lemma continuous_ideleAt : Continuous (ideleAt v) := (continuous_evalAt v).units_map

/-! ### First properties: membership, openness and compactness -/

/-- A finite idele `a` is a unit at all but finitely many places. -/
lemma finite_setOf_valued_val_ne_one : {v : FinPlace K | Valued.v (a.val v) ≠ 1}.Finite :=
  unitsEquiv_finite_valued_eq_one a

/-- The ideles that are units at every place are the units of the ring of integral adeles. -/
lemma idelesUnitOff_empty : idelesUnitOff ∅ = (Ô K).units := by
  -- both sides consist of the ideles whose components are all units of the local integers
  aesop (add simp [idelesUnitOff, val_inj.symm, forall_and, Submonoid.mem_units_iff, Ô,
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.symm])

lemma isOpen_idelesUnitOff : (idelesUnitOff S).IsOpen := by
  -- It contains the open subgroup `idelesUnitOff ∅`, the units of `Ô K`.
  have h_le : idelesUnitOff ∅ ≤ idelesUnitOff S := biInf_mono fun v _ ↦ Set.notMem_empty v
  refine Subgroup.isOpen_mono h_le ?_
  simpa only [idelesUnitOff_empty] using Submonoid.isOpen_units isOpen_Ô

variable {S a v} {w : FinPlace K}

@[simp]
lemma locIdele_apply_of_ne (h_ne : w ≠ v) (x : (LocField v)ˣ) : (locIdele v x).val w = 1 := by
  simp_all [locIdele]

@[simp]
lemma ideleAt_locIdele_of_ne (h_ne : w ≠ v) (x : (LocField v)ˣ) : ideleAt w (locIdele v x) = 1 :=
  ext (locIdele_apply_of_ne h_ne x)

@[simp]
lemma mem_idelesUnitOff :
    a ∈ idelesUnitOff S ↔ ∀ v : FinPlace K, v ∉ S → Valued.v (a.val v) = 1 := by
  simp [idelesUnitOff, ← val_inj, ideleAt]

lemma idelesUnitOff_mono {T : Set (FinPlace K)} (h_sub : S ⊆ T) :
    idelesUnitOff S ≤ idelesUnitOff T :=
  biInf_mono fun _ hv ↦ Set.notMem_subset h_sub hv

lemma isCompact_idelesUnitOff_empty : IsCompact (idelesUnitOff (K := K) ∅ : Set (𝔸f K)ˣ) := by
  rw [idelesUnitOff_empty]
  exact (Ô K).units_isCompact isCompact_Ô

/-- The principal idele of `x` is a unit outside `S` exactly when `x` is an `S`-unit. -/
lemma principalIdele_mem_idelesUnitOff {x : Kˣ} :
    principalIdele x ∈ idelesUnitOff S ↔ x ∈ S.unit K := by
  aesop

/-! ### Approximating an idele by finitely many components -/

/-- For an open neighbourhood `U` of `1` there is a finite set `T` of places such that an idele
that is a unit everywhere and lies outside `U` has a component `≠ 1` at some place of `T`.
Equivalently, the ideles that are units everywhere and `1` on `T` lie in `U`. -/
lemma exists_finset_cover_mulSupport_ideleAt {U : Set (𝔸f K)ˣ} (hU : IsOpen U) (h_one : 1 ∈ U) :
    ∃ T : Finset (FinPlace K),
      (idelesUnitOff ∅).carrier \ U ⊆ ⋃ v ∈ T, (ideleAt v).ker.carrierᶜ := by
  -- the complement of `U` in the units is compact and avoids `1`, so finitely many of the open
  -- sets `{a | ideleAt v a ≠ 1}` cover it
  refine (isCompact_idelesUnitOff_empty.diff hU).elim_finite_subcover _
    (fun v ↦ (continuous_ideleAt v).isOpen_mulSupport) fun a ⟨_, ha_notMem⟩ ↦ ?_
  have ha_ne : a ≠ 1 := (ne_of_mem_of_not_mem h_one ha_notMem).symm
  simpa [ideleAt, ← val_inj, DFunLike.ext_iff] using ha_ne

/-- A closed subgroup H of the finite ideles contains a as soon as it contains, for every place
v, the idele with component a_v at v and 1 elsewhere. -/
lemma mem_of_locIdele_mem {H : Subgroup (𝔸f K)ˣ} (hH : IsClosed H.carrier)
    (ha : ∀ v : FinPlace K, locIdele v (ideleAt v a) ∈ H) : a ∈ H := by
  classical
  -- If `a ∉ H`, the set `a⁻¹ Hᶜ` is an open neighbourhood of `1`. It contains `a⁻¹ b`, where
  -- `b ∈ H` is the product of the components of `a` at enough places; this says `b ∉ H`.
  by_contra ha_notMem
  -- An idele that is a unit everywhere and `1` at the places of `T` lies in `a⁻¹ Hᶜ`.
  obtain ⟨T, hT⟩ : ∃ T : Finset (FinPlace K),
      (idelesUnitOff ∅).carrier \ (fun x ↦ a⁻¹ * x) '' H.carrierᶜ ⊆
        ⋃ v ∈ T, (⇑(ideleAt v)).mulSupport :=
    exists_finset_cover_mulSupport_ideleAt (isOpenMap_mul_left a⁻¹ _ hH.isOpen_compl)
      ⟨a, ha_notMem, inv_mul_cancel a⟩
  -- Enlarge `T` by the places where `a` is not a unit.
  set T' : Finset (FinPlace K) := T ∪ (finite_setOf_valued_val_ne_one a).toFinset with hT'
  set b : (𝔸f K)ˣ := ∏ v ∈ T', locIdele v (ideleAt v a) with hb
  have hb_mem : b ∈ H := prod_mem fun v _ ↦ ha v
  have hb_at (w : FinPlace K) : ideleAt w b = if w ∈ T' then ideleAt w a else 1 := by
    rw [hb, map_prod, Finset.prod_eq_ite _ fun v _ hv ↦ ideleAt_locIdele_of_ne hv.symm _]
    simp
  -- `a⁻¹ b` is `1` on `T'` and equals `a⁻¹`, a unit, elsewhere.
  have h_unit : a⁻¹ * b ∈ idelesUnitOff ∅ := by aesop (add simp [idelesUnitOff, hb_at, hT'])
  have h_notMem : a⁻¹ * b ∉ (fun x ↦ a⁻¹ * x) '' H.carrierᶜ := by simpa using hb_mem
  obtain ⟨v, hv, hv_ne⟩ : ∃ v ∈ T, ideleAt v (a⁻¹ * b) ≠ 1 := by simpa using hT ⟨h_unit, h_notMem⟩
  have h_one : ideleAt v (a⁻¹ * b) = 1 := by simp [hb_at, hT', hv]
  exact hv_ne h_one

/-- The idele with component `x` at `v` and `1` elsewhere is a unit outside any `S` when `x` is a
unit of the integers at `v`. -/
lemma locIdele_mem_idelesUnitOff {x : (LocField v)ˣ} (hx_unit : Valued.v x.val = 1)
    {S : Set (FinPlace K)} : locIdele v x ∈ idelesUnitOff S := by
  simp_all [← and_forall_ne v]

/-- A homomorphism ψ with open kernel from the finite ideles of K to a commutative group is
trivial on the local units at all but finitely many finite places. -/
lemma eventually_unramified {C : Type*} [CommGroup C] (ψ : (𝔸f K)ˣ →* C) (h_open : ψ.ker.IsOpen) :
    ∀ᶠ v : FinPlace K in Filter.cofinite,
      ∀ x : (LocField v)ˣ, Valued.v x.val = 1 → ψ (locIdele v x) = 1 := by
  -- a unit idele outside the kernel has a component `≠ 1` in the finite set `T`; for `v ∉ T` the
  -- idele `locIdele v x` has none
  obtain ⟨T, hT⟩ := exists_finset_cover_mulSupport_ideleAt h_open ψ.map_one
  filter_upwards [T.eventually_cofinite_notMem] with v hv x hx
  by_contra h_ne
  obtain ⟨w, hw, hw_ne⟩ : ∃ w ∈ T, ideleAt w (locIdele v x) ≠ 1 := by
    simpa using hT ⟨locIdele_mem_idelesUnitOff hx, h_ne⟩
  exact hw_ne (ideleAt_locIdele_of_ne (ne_of_mem_of_not_mem hw hv) x)

/-! ### Totally positive elements -/

/-- An element x of K is totally positive if φ(x) > 0 for every ring homomorphism φ : K → ℝ. -/
def IsTotallyPositive (x : K) : Prop := ∀ φ : K →+* ℝ, 0 < φ x

end New

end Ideles

/-!
## Ideles, fractional ideals and the class group

Here `v` is `Valued.v`, the multiplicative valuation of a completion, so the order of an element
at a place is `-log (v _)`.
-/

section IdeleClasses

open NumberField IsDedekindDomain FractionalIdeal WithZero Subgroup ClassGroup HeightOneSpectrum
  Function Units FiniteAdeleRing Valued

namespace New

variable {K : Type*} [Field K] [NumberField K] {R S : Set (FinPlace K)}

attribute [-simp] WithZero.inv_exp
attribute [local simp] WithZero.exp_neg

/-- Two nonzero fractional ideals with the same exponent at every prime are equal. -/
@[ext]
lemma fractionalIdeal_count_ext {I J : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ}
    (h_count : ∀ v : FinPlace K, count K v I.val = count K v J) :
    I = J := by
  -- A nonzero fractional ideal is the product of the primes raised to its exponents.
  rw [Units.ext_iff, ← finprod_heightOneSpectrum_factorization' K I.ne_zero,
    ← finprod_heightOneSpectrum_factorization' K J.ne_zero]
  simp only [h_count]

/-- The divisor map: a homomorphism `d` from the finite ideles to the nonzero fractional ideals such
that (a) an idele `a` is integral at `w` exactly when the exponent of `w` in `d a` is nonnegative,
(b) the kernel is the group of ideles that are units everywhere, (c) the chosen uniformiser at `w`
goes to the prime `w`, and (d) the idele of `x ∈ Kˣ` goes to the principal fractional ideal
`(x)`. -/
lemma exists_idele_divisor_hom :
    ∃ d : (𝔸f K)ˣ →* (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ,
      -- (a)
      (∀ (a : (𝔸f K)ˣ) (w : FinPlace K), v (a.val w) ≤ 1 ↔ 0 ≤ count K w (d a).val) ∧
      -- (b)
      d.ker = idelesUnitOff ∅ ∧
      -- (c)
      (∀ w : FinPlace K, d (locIdele w (uniformizer w)) =
        FractionalIdeal.mk0 K ⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩) ∧
      -- (d)
      ∀ x : Kˣ, d (principalIdele x) = toPrincipalIdeal (𝓞 K) K x := by
  classical
  -- The divisor of an idele `a` is the fractional ideal `∏ w ^ ord_w(a)`. The claims are
  -- checked exponent by exponent, since the exponents determine a nonzero fractional ideal
  -- (`fractionalIdeal_count_ext`).
  have h_exists_divisor (a : (𝔸f K)ˣ) : ∃ I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ,
      ∀ w : FinPlace K, count K w I.val = -log (v (a.val w)) := by
    refine ⟨.mk0 _ ?_, fun w ↦ count_finprod K w _ ?_⟩
    · -- a finite product of powers of nonzero primes is nonzero
      simp [finprod_ne_zero, zpow_ne_zero, ne_bot]
    · -- the exponent is `0` wherever `a` is a unit, so at all but finitely many places
      exact .mono (finite_setOf_valued_val_ne_one a) fun w' (h_unit : v (a.val w') = 1) ↦ by
        simp [h_unit]
  choose d hd using h_exists_divisor
  have hd_eq (a : (𝔸f K)ˣ) (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
      d a = I ↔ ∀ w : FinPlace K, (v (a.val w))⁻¹ = exp (count K w I.val) := by
    simp [New.fractionalIdeal_count_ext_iff, hd, isUnit_iff.mp, ← exp_inj (M := ℤ)]
  have hd_mul (a b : (𝔸f K)ˣ) : d (a * b) = d a * d b := by
    simp [hd_eq, hd, count_mul, isUnit_iff.mp, mul_comm]
  -- For `x = a / b` the order of `x` at `w` is the exponent of `w` in `(x) = (a) / (b)`.
  have h_val_principal (x : K) (hx : x ≠ 0) (w : FinPlace K) :
      (w.valuation K x)⁻¹ = exp (count K w (spanSingleton (nonZeroDivisors (𝓞 K)) x)) := by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (𝓞 K) x
    obtain ⟨ha_ne, hb_ne⟩ : a ≠ 0 ∧ b ≠ 0 := by simpa using hx
    -- `(a / b) = (b)⁻¹ (a)`
    have h_span_eq : spanSingleton (nonZeroDivisors (𝓞 K))
        (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) =
        spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K b)⁻¹ *
          (Ideal.span {a} : Ideal (𝓞 K)) := by
      rw [coeIdeal_span_singleton, ← div_spanSingleton, spanSingleton_div_spanSingleton]
    -- the order of `a / b` is the order of `a` minus the order of `b`
    rw [count_well_defined K w (spanSingleton_ne_zero_iff.2 hx) h_span_eq, map_div₀,
      valuation_of_algebraMap, valuation_of_algebraMap, intValuation_if_neg w ha_ne,
      intValuation_if_neg w hb_ne, ← exp_sub, ← exp_neg, neg_sub_neg, neg_sub]
  -- A uniformiser at `p` gives an idele of order one at `p` and zero elsewhere.
  have h_val_uniformizer (p w : FinPlace K) :
      (v ((locIdele p (uniformizer p)).val w))⁻¹ = exp (if p = w then 1 else 0) := by
    obtain rfl | h_eq := eq_or_ne p w
    · simp [v_uniformizer]
    · simp [locIdele_apply_of_ne h_eq.symm, h_eq]
  refine ⟨.mk' d hd_mul, fun a w ↦ ?_, ext fun a ↦ ?_, fun p ↦ ?_, fun x ↦ ?_⟩
  · -- (a) `v (a w) ≤ 1` exactly when its order `-log (v (a w))` is nonnegative
    simp [hd, isUnit_iff.mp, ← exp_le_exp (G := ℤ)]
  · -- (b) the divisor is trivial exactly when every order is `0`
    simp [hd_eq, count_one, mem_idelesUnitOff]
  · -- (c) the uniformiser at `p` has order `1` at `p` and `0` elsewhere
    simpa [hd_eq, count_maximal] using h_val_uniformizer p
  · -- (d) the orders of `x` are the exponents of the principal ideal `(x)`
    simpa [hd_eq, principalIdele] using h_val_principal x x.ne_zero

/-- There is a homomorphism from the finite ideles to the class group whose kernel is generated by
the principal ideles and the ideles that are units everywhere. -/
lemma exists_idele_classGroup_hom :
    ∃ c : (𝔸f K)ˣ →* ClassGroup (𝓞 K), c.ker = principalIdele.range ⊔ idelesUnitOff ∅ := by
  -- Send an idele to the class of its divisor. The class is trivial iff the divisor is principal,
  -- that is, iff it is the divisor of a principal idele.
  obtain ⟨d, -, hd_ker, -, hd_principal⟩ := exists_idele_divisor_hom (K := K)
  refine ⟨(ClassGroup.mk K).comp d, ext fun a ↦ ?_⟩
  simp [← hd_ker, ← (equiv K).map_eq_one_iff, ← comap_map_eq, hd_principal]

/-- For every finite idele a of K, the power a^h, with h the class number of K, is a principal
idele times an idele that is a unit at every prime. -/
lemma pow_classNumber_mem_principal_sup (a : (𝔸f K)ˣ) :
    a ^ classNumber K ∈ principalIdele.range ⊔ idelesUnitOff ∅ := by
  -- The class of `a` has order dividing the class number.
  obtain ⟨c, hc⟩ := exists_idele_classGroup_hom (K := K)
  rw [← hc, MonoidHom.mem_ker, map_pow]
  exact pow_card_eq_one

/-- A principal idele times a unit outside `S` has, at the places outside `S`, the valuations of an
element of `Kˣ`. -/
lemma exists_valuation_eq_of_mem_sup {a : (𝔸f K)ˣ}
    (ha : a ∈ principalIdele.range ⊔ idelesUnitOff S) :
    ∃ x : Kˣ, ∀ w : FinPlace K, w ∉ S → w.valuation K x.val = v (a.val w) := by
  -- `a` is the principal idele of some `x` times an idele `u` that is a unit outside `S`
  obtain ⟨_, ⟨x, rfl⟩, u, hu, rfl⟩ := mem_sup.mp ha
  exact ⟨x, fun w hw ↦ by simp [mem_idelesUnitOff.mp hu w hw, principalIdele]⟩

/-- For finite sets `R`, `R'` of finite places there is a finite set `T` that contains `R`, meets
`R'` only inside `R`, and is such that every finite idele is a principal idele times an idele
that is a unit outside `T`. -/
lemma exists_sup_idelesUnitOff_eq_top (hR : R.Finite) (R' : Set (FinPlace K)) (hR' : R'.Finite) :
    ∃ T : Set (FinPlace K), T.Finite ∧ R ⊆ T ∧ (∀ v ∈ R', v ∈ T → v ∈ R) ∧
      principalIdele.range ⊔ idelesUnitOff T = ⊤ := by
  -- Take a representative idele `r y` of each of the finitely many ideal classes `y`, divide it
  -- by an element of `K` so that it becomes a unit on `R'`, and let `T` consist of `R` and
  -- the places where one of these quotients is not a unit.
  obtain ⟨c, hc⟩ := exists_idele_classGroup_hom (K := K)
  let r : ClassGroup (𝓞 K) → (𝔸f K)ˣ := invFun c
  -- By density of `K` in the finite adeles, `r y` has the same valuations on `R'` as some `x y`.
  have h_approx (y : ClassGroup (𝓞 K)) :
      ∃ x : Kˣ, ∀ w ∈ R', w.valuation K x.val = v ((r y).val w) := by
    have h_near : ∀ᶠ z in nhds (r y).val, z ≠ 0 ∧ ∀ w ∈ R', v (z w) = v ((r y).val w) := by
      refine (eventually_ne_nhds (r y).ne_zero).and (hR'.eventually_all.mpr fun w _ ↦ ?_)
      -- the valuation at `w` is locally constant away from `0`
      exact (continuous_evalAt w).tendsto _ (locally_const (by simp [isUnit_iff.mp]))
    simpa [exists0] using denseRange_algebraMap_finAdele.mem_nhds h_near
  choose x hx using h_approx
  let q (y : ClassGroup (𝓞 K)) : (𝔸f K)ˣ := (principalIdele (x y))⁻¹ * r y
  let T : Set (FinPlace K) := R ∪ ⋃ y, {w | v ((q y).val w) ≠ 1}
  refine ⟨T, hR.union (Set.finite_iUnion fun y ↦ finite_setOf_valued_val_ne_one (q y)),
    Set.subset_union_left, ?_, top_unique fun a _ ↦ ?_⟩
  · -- On `R'` each quotient is a unit, so `T` meets `R'` only inside `R`.
    simp +contextual [T, q, principalIdele, hx, isUnit_iff.mp]
  -- The subgroup contains the kernel of `c` and the representative of the class of `a`, hence `a`.
  have h_ker_le : c.ker ≤ principalIdele.range ⊔ idelesUnitOff T :=
    hc.trans_le (sup_le_sup_left (idelesUnitOff_mono (Set.empty_subset T)) _)
  have hq_mem : q (c a) ∈ idelesUnitOff T := by simp +contextual [T, mem_idelesUnitOff]
  -- `r (c a)` is the principal idele of `x (c a)` times `q (c a)`.
  have h_rep_mem : r (c a) ∈ principalIdele.range ⊔ idelesUnitOff T :=
    mem_sup.mpr ⟨_, ⟨x (c a), rfl⟩, q (c a), hq_mem, mul_eq_of_eq_inv_mul rfl⟩
  have h_mem_map : c a ∈ (principalIdele.range ⊔ idelesUnitOff T).map c :=
    ⟨r (c a), h_rep_mem, apply_invFun_apply⟩
  -- a subgroup that contains `c.ker` is the preimage of its image
  rw [← comap_map_eq_self h_ker_le]
  exact h_mem_map

/-- Every finite set of places `R` lies in a finite set `S` such that every finite idele is a
principal idele times an idele that is a unit outside `S`. -/
lemma exists_superset_sup_idelesUnitOff_eq_top (hR : R.Finite) :
    ∃ S : Set (FinPlace K), S.Finite ∧ R ⊆ S ∧ principalIdele.range ⊔ idelesUnitOff S = ⊤ := by
  obtain ⟨S, hS, hRS, -, h_sup⟩ := exists_sup_idelesUnitOff_eq_top hR ∅ Set.finite_empty
  exact ⟨S, hS, hRS, h_sup⟩

/-- An open subgroup `H` of the finite ideles that contains the principal ideles of the totally
positive elements of `Kˣ` has finite index. -/
lemma finiteIndex_idele_subgroup_of_isOpen (H : Subgroup (𝔸f K)ˣ) (h_open : H.IsOpen)
    (h_pos : ∀ x : Kˣ, IsTotallyPositive x.val → principalIdele x ∈ H) : H.FiniteIndex := by
  -- Climb from `H` to `H ⊔ P` to `H ⊔ P ⊔ idelesUnitOff ∅` to `⊤`, `P` the principal ideles: each
  -- step has finite (that is, nonzero) index.
  set P : Subgroup (𝔸f K)ˣ := principalIdele.range
  -- The preimage of `H` in `Kˣ` contains the kernel of the signs at the real embeddings,
  -- a map to a finite group.
  have h_index_comap_ne : (H.comap principalIdele).index ≠ 0 := by
    let sgn : Kˣ →* ((K →+* ℝ) → SignType)ˣ :=
      Units.map (.pi fun φ : K →+* ℝ ↦ signHom.toMonoidHom.comp φ.toMonoidHom)
    -- an element with sign `1` at every real embedding is totally positive
    have h_ker_le : sgn.ker ≤ H.comap principalIdele := by
      intro x hx
      have h_sign (φ : K →+* ℝ) : SignType.sign (φ x.val) = 1 :=
        congrFun (congrArg Units.val hx) φ
      exact h_pos x fun φ ↦ sign_eq_one_iff.mp (h_sign φ)
    exact (sgn.ker.finiteIndex_of_le h_ker_le).index_ne_zero
  -- An open subgroup meets the compact group `idelesUnitOff ∅` in a subgroup of finite index.
  have h_relIndex_ne : (H ⊔ P).relIndex (idelesUnitOff ∅) ≠ 0 :=
    isCompact_idelesUnitOff_empty.relIndex_ne_zero (isOpen_mono le_sup_left h_open)
  -- The class group is finite, and `P ⊔ idelesUnitOff ∅` is the kernel of a homomorphism `c` to it.
  obtain ⟨c, hc⟩ : ∃ c : (𝔸f K)ˣ →* ClassGroup (𝓞 K), c.ker = P ⊔ idelesUnitOff ∅ :=
    exists_idele_classGroup_hom
  have h_fin : (H ⊔ P ⊔ idelesUnitOff ∅).FiniteIndex :=
    finiteIndex_of_le (hc.trans_le (sup_le_sup_right le_sup_right _))
  rw [finiteIndex_iff, ← relIndex_mul_index (le_sup_left (b := P)),
    ← relIndex_mul_index (le_sup_left (a := H ⊔ P) (b := idelesUnitOff ∅))]
  -- The first two steps are `[P : H ⊓ P]` and `[idelesUnitOff ∅ : (H ⊔ P) ⊓ idelesUnitOff ∅]`.
  refine mul_ne_zero ?_ (mul_ne_zero ?_ h_fin.index_ne_zero)
  · simpa [P, ← index_comap] using h_index_comap_ne
  · simpa using h_relIndex_ne

/-- The finite ideles form a nonarchimedean group: they have the compact open subgroup
`idelesUnitOff ∅`. -/
instance : NonarchimedeanGroup (𝔸f K)ˣ :=
  -- The open subgroup `idelesUnitOff ∅` is compact and totally disconnected, hence nonarchimedean.
  -- The ideles map continuously and injectively to the product of the completions, which is
  -- totally disconnected.
  have h_inj : Function.Injective fun (a : (𝔸f K)ˣ) (w : FinPlace K) ↦ a.val w := by aesop_cat
  have h_disconnected : TotallyDisconnectedSpace (𝔸f K)ˣ :=
    ⟨fun s _ h ↦
      s.subsingleton_of_image h_inj (h.image (fun a w ↦ a.val w) (by fun_prop)).subsingleton⟩
  have h_compact : CompactSpace (idelesUnitOff (∅ : Set (FinPlace K))) :=
    isCompact_iff_compactSpace.mp isCompact_idelesUnitOff_empty
  .nonarchimedean_of_emb (idelesUnitOff ∅).subtype
    (isOpen_idelesUnitOff ∅).isOpenEmbedding_subtypeVal

end New

end IdeleClasses

end
