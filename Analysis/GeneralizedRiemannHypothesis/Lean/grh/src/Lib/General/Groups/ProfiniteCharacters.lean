import Lib.ClassField.GaloisCohomology.ContinuousCocycles
import Lib.General.Topology

/-!
# ℚ/ℤ, characters of profinite groups, and extension of homomorphisms

`New.QZ` is `ℚ/ℤ` with the discrete topology, and a character of a profinite group `G`
(`New.QZChar G`) is a continuous homomorphism `G → ℚ/ℤ`. The file first proves elementary facts:
the exponential embedding of `ℚ/ℤ` into `ℂˣ`, the embedding of `ZMod n` into `ℚ/ℤ`, extension of
homomorphisms into divisible groups, and equality of the orders of a finite abelian group and its
dual. It then shows that characters separate points of the topological abelianisation of `G`, and
that additive maps from characters to `ℚ/ℤ` are evaluations at its points; these facts are used to
build Artin maps from their values on characters. `New.QZChar.abelianLift χ` denotes the map
induced by `χ` on the abelianisation, with values written multiplicatively.

## Main definitions and results

* `New.QZ.exists_extend`: for abelian groups, homomorphisms to a divisible group extend along any
  homomorphism whose kernel they kill.
* `New.card_hom_QZ`: a finite abelian group and its dual have the same order.
* `New.QZChar.mem_of_forall_abelianLift`, `New.QZChar.abelianization_ext`: characters separate a
  point from a closed subgroup of the abelianisation, and hence separate points.
* `New.QZChar.exists_hom_abelianLift_eq`: every additive map from characters to `ℚ/ℤ` is evaluation
  at a point of the abelianisation, in a form that is multiplicative in a parameter.
* `New.QZChar.continuous_iff_forall_isOpen_ker_comp`: a homomorphism from a commutative topological
  group to the abelianisation is continuous exactly when its composite with each character has open
  kernel.
* `New.exists_monoidHom_extend`, deduced from `New.QZ.exists_extend`: a homomorphism
  `θ` from a commutative group into a divisible commutative group, trivial on the preimage of a
  subgroup `H` under a homomorphism `f` of commutative groups, factors through `f` by a homomorphism
  trivial on `H`.

Notions from other files:
* `New.Z1 ρ`: the continuous 1-cocycles of `ρ`, that is the continuous `f : G → M` with
  `f (g h) = f g + ρ g (f h)`; `New.QZChar G` is the case of the trivial action on `ℚ/ℤ`.
* `New.QZChar.toHom χ`: the character `χ` as a group homomorphism to `ℚ/ℤ` written
  multiplicatively; `New.QZChar.ker χ` is its kernel.
-/

noncomputable section

/-! ## ℚ/ℤ, embeddings of ZMod n and duals of finite abelian groups -/

section RatModInt

open Nat Function QuotientAddGroup AddCircle CharacterModule ZMod NeZero AddMonoidHom AddMonoid

variable {n : ℕ}
  {G H A B W : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Monoid H]
  [TopologicalSpace H] [ContinuousMul H] [AddCommGroup A] [AddCommGroup B] [AddCommGroup W]

/-- A homomorphism from a topological group to a topological monoid is continuous as soon as its
kernel is open. -/
lemma Continuous.of_isOpen_ker (f : G →* H) (h_open : f.ker.IsOpen) : Continuous f :=
  continuous_of_tendsto_nhds_one f (tendsto_nhds_of_eventually_eq (h_open.mem_nhds f.map_one))


namespace New.QZ

/-- Every element of `ℚ/ℤ` has finite order. -/
lemma isAddTorsion : IsAddTorsion QZ := by
  rintro ⟨x⟩
  exact isOfFinAddOrder_iff_exists_rat_eq_div.2 ⟨x, by simp⟩

/-- For `n` positive, the class of `1 / n` in `ℚ/ℤ` has order `n`. -/
lemma addOrderOf_mk_inv (hn : 0 < n) : addOrderOf (mk (n : ℚ)⁻¹) = n := by
  rw [← one_div]
  exact addOrderOf_period_div hn

/-- Every element of `ℚ/ℤ` is the class of a rational number. -/
lemma mk_surjective : Surjective mk := mk'_surjective (AddSubgroup.zmultiples 1)

/-- The class of a rational number in `ℚ/ℤ` is zero exactly when the number is an integer. -/
lemma mk_eq_zero_iff {x : ℚ} : mk x = 0 ↔ ∃ k : ℤ, x = k :=
  (coe_eq_zero_iff 1).trans (by simp [eq_comm])

/-- The group homomorphism from `ℚ/ℤ`, written multiplicatively, to `ℂˣ` sending the class of `x`
to `exp (2 π i x)`. -/
def expUnit : Multiplicative QZ →* ℂˣ :=
  Circle.toUnits.comp
    (toCircle_addChar.compAddMonoidHom
      (map (AddSubgroup.zmultiples 1) (AddSubgroup.zmultiples 1) (Rat.castHom ℝ)
        (by simp))).toMonoidHom

/-- The value of `expUnit` at the class of a rational number `x` is `exp (2 π i x)`. -/
lemma coe_expUnit_ofAdd_mk (x : ℚ) :
    (expUnit (.ofAdd (mk x)) : ℂ) = Complex.exp (x * (2 * Real.pi * Complex.I)) := by
  change Complex.exp ((2 * Real.pi / 1 * (x : ℝ) : ℝ) * Complex.I) = _
  congr 1
  push_cast
  ring

/-- The homomorphism `expUnit : x ↦ exp (2 π i x)` from `ℚ/ℤ` to `ℂˣ` has trivial kernel. -/
lemma expUnit_eq_one_iff {a : Multiplicative QZ} : expUnit a = 1 ↔ a = 1 := by
  obtain ⟨x, rfl⟩ : ∃ x : ℚ, Multiplicative.ofAdd (mk x) = a := mk_surjective a.toAdd
  -- `exp (2 π i x) = 1` exactly when the rational number `x` is an integer.
  rw [Units.ext_iff, coe_expUnit_ofAdd_mk, Units.val_one, Complex.exp_eq_one_iff, ofAdd_eq_one,
    mk_eq_zero_iff]
  simp only [mul_left_inj' Complex.two_pi_I_ne_zero]
  norm_cast

/-- Let `A`, `B` and `W` be abelian groups with `W` divisible and `f : A →+ B` a homomorphism, not
necessarily injective. Every homomorphism `u : A →+ W` that kills the kernel of `f` is equal to
`v ∘ f` for some homomorphism `v : B →+ W`. -/
lemma exists_extend [DivisibleBy W ℤ] (f : A →+ B) (u : A →+ W) (h_ker : f.ker ≤ u.ker) :
    ∃ v : B →+ W, ∀ a : A, v (f a) = u a := by
  -- A divisible group is injective, so the map induced by `u` on `A ⧸ ker f` extends to `B`.
  obtain ⟨v, hv⟩ : ∃ v : B →+ W, v.comp (kerLift f) = QuotientAddGroup.lift f.ker u h_ker :=
    (Module.Baer.of_divisible W).extension_property_addMonoidHom _ (kerLift_injective f) _
  exact ⟨v, fun a ↦ DFunLike.congr_fun hv (a : A ⧸ f.ker)⟩

/-- An element of an abelian group that is killed by every homomorphism to `ℚ/ℤ` is zero. -/
lemma eq_zero_of_forall_hom_eq_zero {a : A} (h_eval : ∀ u : A →+ QZ, u a = 0) : a = 0 :=
  eq_zero_of_character_apply h_eval

/-! ### The embedding of `ZMod n` -/

/-- For `n` nonzero, the additive homomorphism `ℤ/n → ℚ/ℤ` sending the class of `k` to the class
of `k / n`. -/
def ofZMod (n : ℕ) [NeZero n] : ZMod n →+ QZ :=
  ZMod.lift n ⟨zmultiplesHom QZ (mk (n : ℚ)⁻¹), int.divByNat_self n⟩

variable [NeZero n]

/-- The embedding `ofZMod n` sends a residue `b` to the class in `ℚ/ℤ` of `b.val / n`, where
`b.val` is the representative of `b` below `n`. -/
lemma ofZMod_apply (b : ZMod n) : ofZMod n b = mk (b.val / n) := by
  change (b.cast : ℤ) • mk (n : ℚ)⁻¹ = mk (b.val / n)
  simp [← map_zsmul, div_eq_mul_inv]

@[simp]
lemma ofZMod_injective : Injective (ofZMod n) := by
  rw [ofZMod, lift_injective]
  refine fun k hk ↦ (intCast_zmod_eq_zero_iff_dvd k n).2 ?_
  -- An integer `k` kills the class of `1 / n` only if the order `n` of this class divides `k`.
  change k • mk (n : ℚ)⁻¹ = 0 at hk
  rwa [← addOrderOf_dvd_iff_zsmul_eq_zero, addOrderOf_mk_inv (pos n)] at hk

/-- An element of `ℚ/ℤ` killed by `n` is in the image of the embedding `ofZMod n` of `ℤ/n`. -/
lemma exists_ofZMod {a : QZ} (ha : n • a = 0) : ∃ b : ZMod n, ofZMod n b = a := by
  obtain ⟨m, hm, rfl⟩ : ∃ m : ℕ, m < n ∧ mk (m / n * 1) = a :=
    (AddCircle.nsmul_eq_zero_iff (pos n)).1 ha
  exact ⟨m, by simp [ofZMod_apply, mod_eq_of_lt hm]⟩

/-- If `A` is killed by `n`, composing with `New.QZ.ofZMod n` is a bijection from the
homomorphisms `A →+ ZMod n` to the homomorphisms `A →+ ℚ/ℤ`. -/
lemma bijective_ofZMod_comp (h_exp : ∀ a : A, n • a = 0) :
    Bijective ((ofZMod n).comp (M := A)) := by
  refine ⟨fun g g' h ↦ (cancel_left ofZMod_injective).1 h, fun f ↦ ?_⟩
  -- Each value `f a` is killed by `n`, so it is `ofZMod n (g a)` for some `g a`.
  have h_lift (a : A) : ∃ b : ZMod n, ofZMod n b = f a :=
    exists_ofZMod (by rw [← map_nsmul, h_exp, map_zero])
  choose g hg using h_lift
  -- `g` is additive because `ofZMod n` is injective.
  have h_add (a b : A) : g (a + b) = g a + g b := ofZMod_injective (by simp [hg])
  exact ⟨.mk' g h_add, ext hg⟩

end QZ

variable (A) [Finite A]

/-! ### Duals of finite abelian groups -/

/-- A finite abelian group `A` has exactly `#A` homomorphisms to `ℚ/ℤ`: its Pontryagin dual has
the same order as `A`. -/
@[simp]
lemma card_hom_QZ : Nat.card (A →+ QZ) = Nat.card A := by
  -- With `n` the exponent of `A`, homomorphisms to `QZ` are homomorphisms to `ZMod n`; written
  -- multiplicatively, this cyclic group has enough `n`-th roots of unity for the duality theorem.
  let n : ℕ := AddMonoid.exponent A
  let M : Type := Multiplicative (ZMod n)
  let e₁ : (A →+ ZMod n) ≃ (A →+ QZ) :=
    .ofBijective _ (QZ.bijective_ofZMod_comp AddMonoid.exponent_nsmul_eq_zero)
  let e : (A →+ QZ) ≃ (Multiplicative A →* Mˣ) :=
    (e₁.symm.trans toMultiplicative).trans toUnits.monoidHomCongrRightEquiv
  have h_prim : IsPrimitiveRoot (Multiplicative.ofAdd 1 : M) n := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  -- The roots of unity correspond under `toUnits` to a subgroup of the cyclic group `M`.
  have h_roots : HasEnoughRootsOfUnity M (Monoid.exponent (Multiplicative A)) := by
    rw [Monoid.exponent_multiplicative]
    exact { prim := ⟨.ofAdd 1, h_prim⟩,
            cyc := (toUnits.symm.subgroupMap (rootsOfUnity n M)).isCyclic.2 inferInstance }
  exact (card_congr e).trans (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (hM := h_roots))

instance : Finite (A →+ QZ) := finite_of_card_ne_zero (by simp [ne])

end New

end RatModInt

/-! ## Characters of a profinite group and its abelianisation -/

namespace New

open Nat Subgroup Fact QuotientGroup MonoidHom QZ DFunLike

variable {G C : Type*} [Group G] [CommGroup C] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [instance] isClosed_topologicalClosure

namespace QZChar

/-- The additive map sending a continuous 1-cocycle of `G` with values in `ℤ/n` (trivial action)
to the character `G → ℚ/ℤ` obtained by composing with the embedding `ofZMod n`. -/
noncomputable abbrev ofZModCocycle (n : ℕ) [NeZero n] :
    Z1 (Representation.trivial ℤ G (ZMod n)) →+ QZChar G :=
  pairMapZ1 (ContinuousMonoidHom.id G) (ofZMod n).toIntLinearMap

omit [IsTopologicalGroup G] in
lemma continuous_val (χ : QZChar G) : Continuous χ.val :=
  χ.prop.1

instance (χ : QZChar G) : Fact (toHom χ).ker.IsOpen :=
  ⟨(continuous_val χ).isOpen_preimage {0} (isOpen_discrete _)⟩

@[simp]
theorem abelianLift_mk (χ : QZChar G) (g : G) :
    abelianLift χ g = Multiplicative.ofAdd (χ.val g) := rfl

@[fun_prop]
lemma continuous_abelianLift (χ : QZChar G) : Continuous (abelianLift χ) :=
  (continuous_val χ).quotient_lift _

omit [IsTopologicalGroup G] in
/-- The kernel of a character `χ : G → ℚ/ℤ` is open. -/
lemma isOpen_ker (χ : QZChar G) : (ker χ).IsOpen := out

omit [IsTopologicalGroup G] in
/-- Let `G` be a nonarchimedean group and `f : G →* C` a homomorphism to a commutative group
with closed kernel. If `σ` is not in the kernel, some continuous character of `G` vanishes on
the kernel but not at `σ`. -/
lemma exists_apply_ne_zero_of_notMem_ker [NonarchimedeanGroup G] (f : G →* C) (σ : G)
    (hf : IsClosed (f.ker : Set G)) (hσ : σ ∉ f.ker) :
    ∃ χ : QZChar G, (∀ g ∈ f.ker, χ.val g = 0) ∧ χ.val σ ≠ 0 := by
  -- An open subgroup `V` with `σ * V` disjoint from the closed set `f.ker`.
  obtain ⟨V, hV⟩ : ∃ V : OpenSubgroup G, (V : Set G) ⊆ (fun g ↦ σ * g) ⁻¹' (f.ker : Set G)ᶜ :=
    NonarchimedeanGroup.is_nonarchimedean _ ((map_mul_left_nhds_one σ).le (hf.compl_mem_nhds hσ))
  -- So `f σ` is not in `f V`, and a homomorphism `u` from `C ⧸ f V` to `QZ` detects it.
  let π : C →* C ⧸ V.map f := mk' (V.map f)
  have h_ne : Additive.ofMul (π (f σ)) ≠ 0 := by
    intro h_zero
    obtain ⟨g, hg, hfg⟩ : ∃ g ∈ V, f g = f σ := (QuotientGroup.eq_one_iff (f σ)).1 h_zero
    exact hV (V.inv_mem hg) (by simp [hfg] : σ * g⁻¹ ∈ f.ker)
  obtain ⟨u, hu⟩ : ∃ u : Additive (C ⧸ V.map f) →+ QZ, u (.ofMul (π (f σ))) ≠ 0 :=
    not_forall.1 (mt eq_zero_of_forall_hom_eq_zero h_ne)
  -- Pulled back to `G`, the map `u` kills `V`, hence is continuous.
  let ψ : G →* Multiplicative QZ := (u.toMultiplicativeRight.comp π).comp f
  have h_le : V.toSubgroup ≤ ψ.ker := by
    intro g hg
    have h_one : π (f g) = 1 := (QuotientGroup.eq_one_iff (f g)).2 (mem_map_of_mem f hg)
    simp [ψ, h_one]
  have h_cont : Continuous ψ := .of_isOpen_ker ψ (isOpen_mono h_le V.isOpen)
  let χ : QZChar G := ⟨fun g ↦ (ψ g).toAdd, continuous_toAdd.comp h_cont, by simp⟩
  have χ_apply (g : G) : χ.val g = u (.ofMul (π (f g))) := rfl
  exact ⟨χ, fun g hg ↦ by simp [χ_apply, mem_ker.1 hg], by rwa [χ_apply]⟩

variable [CompactSpace G]

/-- A character `χ : G → ℚ/ℤ` of a compact group has finite order: it is killed by the index of
its open kernel. -/
lemma isOfFinAddOrder_of_compactSpace (χ : QZChar G) : IsOfFinAddOrder χ := by
  have h_fin : Finite (G ⧸ ker χ) := quotient_finite_of_isOpen (ker χ) (isOpen_ker χ)
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2
    ⟨(ker χ).index, Nat.pos_of_ne_zero index_ne_zero_of_finite, ?_⟩
  ext g
  change (ker χ).index • (toHom χ g).toAdd = 0
  rw [← _root_.toAdd_pow, ← map_pow, toAdd_eq_zero, ← mem_ker]
  exact (ker χ).pow_index_mem g

/-- Let `G` be a compact group and `t` an additive map from the characters `G → ℚ/ℤ` to `ℚ/ℤ`. On
a finite set `S` of characters, `t` is evaluation at some point of `G`. -/
lemma exists_eval_eq_on_finset (t : QZChar G →+ QZ) (S : Finset (QZChar G)) :
    ∃ g : G, ∀ χ ∈ S, χ.val g = t χ := by
  -- Characters have finite order, so `S` generates a finite group `T`.
  let T : AddSubgroup (QZChar G) := AddSubgroup.closure (S : Set (QZChar G))
  have h_fin : Finite T := AddCommGroup.finite_of_fg_isAddTorsion T fun χ ↦
    T.subtype_injective.isOfFinAddOrder_iff.1 (isOfFinAddOrder_of_compactSpace χ.val)
  -- `E` is the group of the homomorphisms `T →+ QZ` that are evaluation at a point of `G`.
  let pair : QZChar G →+ Additive G →+ QZ := .mk' (fun χ ↦ toAdditiveLeft (toHom χ)) fun _ _ ↦ rfl
  let ev : Additive G →+ T →+ QZ := (pair.domRestrict T).flip
  have ev_apply (g : Additive G) (χ : T) : ev g χ = (χ : QZChar G).val g.toMul := rfl
  let E : AddSubgroup (T →+ QZ) := ev.range
  -- Evaluations separate characters, so `T` embeds in the dual of `E`. As a finite group and
  -- its dual have the same order, `E` is all of the dual of `T`.
  have h_inj : Function.Injective (E.subtype.flip : T →+ E →+ QZ) := by
    intro χ ψ h_eq
    ext g
    change ev (.ofMul g) χ = ev (.ofMul g) ψ
    exact DFunLike.congr_fun h_eq (ev.rangeRestrict (.ofMul g))
  have h_card : Nat.card (T →+ QZ) ≤ Nat.card E :=
    calc Nat.card (T →+ QZ) = Nat.card T := card_hom_QZ T
      _ ≤ Nat.card (E →+ QZ) := card_le_card_of_injective _ h_inj
      _ = Nat.card E := card_hom_QZ E
  obtain ⟨g, hg⟩ : ∃ g : Additive G, ev g = t.domRestrict T :=
    AddMonoidHom.range_eq_top.1 (E.eq_top_of_le_card h_card) _
  exact ⟨g.toMul, fun χ hχ ↦ DFunLike.congr_fun hg ⟨χ, AddSubgroup.subset_closure hχ⟩⟩

/-- For a compact group `G`, an additive map `t` from the characters `G → ℚ/ℤ` to `ℚ/ℤ` is
evaluation at some point of `G`. -/
lemma exists_eval_eq (t : QZChar G →+ QZ) : ∃ g : G, ∀ χ : QZChar G, χ.val g = t χ := by
  -- These are closed conditions on a compact space, and finitely many of them can be met.
  have h_nonempty : (⋂ χ : QZChar G, {g : G | χ.val g = t χ}).Nonempty :=
    CompactSpace.iInter_nonempty (fun χ ↦ isClosed_eq (continuous_val χ) continuous_const)
      fun S ↦ by simpa [Set.Nonempty] using exists_eval_eq_on_finset t S
  simpa [Set.Nonempty] using h_nonempty

variable [TotallyDisconnectedSpace G]

instance : NonarchimedeanGroup G where
  -- The clopen neighbourhoods of `1` form a basis, and each of them contains an open subgroup.
  is_nonarchimedean U hU := by
    obtain ⟨W, ⟨h_clopen, h_one⟩, hWU⟩ := (nhds_basis_isClopen (1 : G)).mem_iff.1 hU
    obtain ⟨V, hVW⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one h_clopen h_one
    exact ⟨V, hVW.trans hWU⟩

/-! ### Duality for profinite groups -/

/-- Let `G` be profinite and `H` a closed subgroup of its topological abelianisation. An element
`σ` of the abelianisation lies in `H` if it is killed by every character `χ : G → ℚ/ℤ` that kills
`H`; here `abelianLift χ` is the map induced by `χ` on the abelianisation. -/
lemma mem_of_forall_abelianLift {H : Subgroup (TopologicalAbelianization G)}
    (hH : IsClosed H.carrier) (σ : TopologicalAbelianization G)
    (hσ : ∀ χ : QZChar G, (∀ g ∈ H, abelianLift χ g = 1) → abelianLift χ σ = 1) :
    σ ∈ H := by
  -- Apply `exists_apply_ne_zero_of_notMem_ker` to the projection of `G` to the quotient of its
  -- abelianisation by `H`.
  let π : G →* TopologicalAbelianization G ⧸ H :=
    (mk' H).comp (mk' (_root_.commutator G).topologicalClosure)
  have mem_ker_π (g : G) : g ∈ π.ker ↔ (g : TopologicalAbelianization G) ∈ H :=
    QuotientGroup.eq_one_iff _
  have h_closed : IsClosed (π.ker : Set G) := by
    convert hH.preimage continuous_mk
    exact Set.ext mem_ker_π
  obtain ⟨τ, rfl⟩ := mk_surjective σ
  by_contra h_notMem
  obtain ⟨χ, hχ, h_ne⟩ : ∃ χ : QZChar G, (∀ g ∈ π.ker, χ.val g = 0) ∧ χ.val τ ≠ 0 :=
    exists_apply_ne_zero_of_notMem_ker π τ h_closed (mt (mem_ker_π τ).1 h_notMem)
  have h_kills : ∀ g ∈ H, abelianLift χ g = 1 := forall_mk.2 fun g hg ↦ by
    rw [abelianLift_mk, hχ g ((mem_ker_π g).2 hg), ofAdd_zero]
  exact h_ne (by simpa using hσ χ h_kills)

/-- For a profinite group `G`, two elements of the topological abelianisation are equal if the
map `abelianLift χ` induced by each character `χ : G → ℚ/ℤ` takes the same value on them. -/
@[ext]
lemma abelianization_ext {g g' : TopologicalAbelianization G}
    (h_lift : ∀ χ : QZChar G, abelianLift χ g = abelianLift χ g') :
    g = g' := by
  -- The abelianisation is the quotient by a closed subgroup, so its trivial subgroup is closed.
  refine eq_of_div_eq_one (mem_bot.1
    (mem_of_forall_abelianLift isClosed_singleton (g / g') fun χ _ ↦ ?_))
  rw [map_div, h_lift χ, div_self']

/-- The existence part of Pontryagin duality for a profinite group `G`: if `s` maps a group `X`
homomorphically to the additive maps from the characters of `G` to `ℚ/ℤ`, then some homomorphism
`f` from `X` to the topological abelianisation of `G` has `χ (f x) = s x χ` for all `χ` and `x`.
Here `abelianLift χ` is the map induced by `χ` on the abelianisation. -/
lemma exists_hom_abelianLift_eq {X : Type*} [Group X] (s : Additive X →+ QZChar G →+ QZ) :
    ∃ f : X →* TopologicalAbelianization G, ∀ (χ : QZChar G) (x : X),
      abelianLift χ (f x) = Multiplicative.ofAdd (s (Additive.ofMul x) χ) := by
  choose g hg using fun x : X ↦ exists_eval_eq (s (.ofMul x))
  have h_ab (χ : QZChar G) (x : X) : abelianLift χ (g x) = .ofAdd (s (.ofMul x) χ) := by
    rw [abelianLift_mk, hg]
  -- The class of `g x` is multiplicative in `x`, because characters separate the points.
  have h_mul (x y : X) : (g (x * y) : TopologicalAbelianization G) = g x * g y :=
    abelianization_ext fun χ ↦ by rw [map_mul, h_ab, h_ab, h_ab, ofMul_mul, map_add,
      AddMonoidHom.add_apply, ofAdd_add]
  exact ⟨.mk' (fun x ↦ g x) h_mul, h_ab⟩

/-- Let `G` be a profinite group and `C` a commutative topological group. A homomorphism `f` from
`C` to the topological abelianisation of `G` is continuous exactly when its composite with the map
`abelianLift χ` induced by each character `χ : G → ℚ/ℤ` has open kernel. -/
lemma continuous_iff_forall_isOpen_ker_comp [TopologicalSpace C] [IsTopologicalGroup C]
    {f : C →* TopologicalAbelianization G} :
    Continuous f ↔ ∀ χ : QZChar G, ((abelianLift χ).comp f).ker.IsOpen := by
  -- Characters separate points, so they embed the compact abelianisation in a product of
  -- discrete groups, and continuity can be checked one character at a time.
  have h_emb : Topology.IsClosedEmbedding
      fun (g : TopologicalAbelianization G) (χ : QZChar G) ↦ abelianLift χ g :=
    (continuous_pi continuous_abelianLift).isClosedEmbedding fun g g' h_eq ↦
      abelianization_ext (congrFun h_eq)
  rw [h_emb.continuous_iff, continuous_pi_iff]
  exact forall_congr' fun χ ↦ ⟨fun h_cont ↦ h_cont.isOpen_preimage {1} (isOpen_discrete _),
    .of_isOpen_ker ((abelianLift χ).comp f)⟩

end QZChar

end New

/-! ## Extension of homomorphisms into a divisible group -/

section ExtendCharacter

open QuotientGroup

/-- Let `A` and `G` be commutative groups, `C` a divisible commutative group, `f : A → G` a
homomorphism and `H` a subgroup of `G`. A homomorphism `θ : A → C` that is trivial at every `a` with
`f a ∈ H` factors as `χ ∘ f` for some homomorphism `χ : G → C` trivial on `H`. -/
lemma New.exists_monoidHom_extend {A G C : Type*} [CommGroup A] [CommGroup G] [CommGroup C]
    [d : DivisibleBy (Additive C) ℤ] (f : A →* G) (θ : A →* C) (H : Subgroup G)
    (h_triv : ∀ a : A, f a ∈ H → θ a = 1) :
    ∃ χ : G →* C, H ≤ χ.ker ∧ ∀ a : A, χ (f a) = θ a := by
  -- Extend `θ` from `A` to the quotient `G ⧸ H`, then pull it back to `G`.
  have h_ker : ((mk' H).comp f).ker ≤ θ.ker := fun a ha ↦ h_triv a ((eq_one_iff (f a)).1 ha)
  obtain ⟨v, hv⟩ : ∃ v : Additive (G ⧸ H) →+ Additive C,
      ∀ a : A, v (.ofMul (f a : G ⧸ H)) = .ofMul (θ a) :=
    QZ.exists_extend ((mk' H).comp f).toAdditive θ.toAdditive h_ker
  refine ⟨v.toMultiplicative.comp (mk' H), fun g hg ↦ ?_, hv⟩
  change v (.ofMul (g : G ⧸ H)) = 0
  rw [(eq_one_iff g).2 hg, ofMul_one, map_zero]

end ExtendCharacter

end
