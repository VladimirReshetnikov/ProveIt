import Lib.ClassField.LocalDuality.KummerFiniteness

/-!
# The local invariant Br(k) ≅ Q/Z and its behaviour under restriction and maps of local fields

The invariant map of local class field theory, for a henselian local field `k` of characteristic `0`
with absolute Galois group `Γ` acting on `Ω` (`New.IsLocalGalois`).

* `New.IsLocalGalois.isClassOfInvariant_classOfInvariant`: the chosen map
  `New.Cohomology.classOfInvariant` from ℚ/ℤ to H²(Γ, Ωˣ) is injective and computes the cyclic
  classes of unramified characters.
* `New.IsLocalGalois.classOfInvariant_bijective`: `New.Cohomology.classOfInvariant` is bijective, so
  it identifies ℚ/ℤ with H²(Γ, Ωˣ).
* `New.Cohomology.resH2_classOfInvariant`, `New.IsLocalGalois.exists_resH2_classOfInvariant_eq`:
  restriction to an open subgroup multiplies the invariant by the index and is onto.
* `New.IsLocalGalois.pairMapH2_classOfInvariant_of_ordRat_eq`,
  `New.IsLocalGalois.pairMapH2_classOfInvariant`: a map of local fields with ramification index `e`
  and residue degree `f` multiplies the invariant by `e * f`.

Notions from other files:
* `New.unitsModule`, `New.unitsRep`: `Ωˣ` written additively (`New.DiscreteUnits`) with the action
  of `Γ`, as a discrete module and as a representation; `H0` are its `Γ`-invariants, the units
  of `k`.
* `New.DiscreteModule.resH2`: restriction of a class in `H²(Γ, M)` to a subgroup of `Γ`; a class is
  split by `V` when its restriction to `V` is zero.
* `New.cyclicClass`: the cyclic class (symbol) `(χ, w) = δχ ∪ w` of a character `χ : Γ → ℚ/ℤ` and
  an invariant `w`.

## Relation to the literature

Known; see `Lib.ClassField.Local.ArtinMap` for sources.
-/

/-- If `R ^ (l - 1) * (l * c ^ l) = (l * c) ^ l` in `ℚ`, with `l` prime and `l * c ≠ 0`, then
`R = l`. -/
private lemma Nat.eq_of_pow_sub_one_mul_eq_mul_pow {R l c : ℕ} (hl : l.Prime)
    (hlc : (l : ℚ) * c ≠ 0) (h : (R : ℚ) ^ (l - 1) * (l * c ^ l) = ((l : ℚ) * c) ^ l) : R = l := by
  -- Cancel `l * c ^ l`, then take `(l - 1)`-th roots, where `l - 1 ≠ 0`.
  have h_pow : (R : ℚ) ^ (l - 1) = (l : ℚ) ^ (l - 1) := by
    refine mul_right_cancel₀ (b := (l * c ^ l : ℚ)) (by simp_all) ?_
    rw [h, mul_pow, ← mul_assoc, pow_sub_one_mul hl.ne_zero]
  exact Nat.pow_left_injective (Nat.sub_ne_zero_of_lt hl.one_lt) (by exact_mod_cast h_pow)

namespace New.IsLocalGalois

open Cohomology Function DiscreteModule Subgroup QZChar QuotientGroup QZ DiscreteUnits AddMonoidHom

variable {Γ k Ω : Type} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω] [Algebra k Ω]
  [MulSemiringAction Γ Ω] (V : OpenSubgroup Γ) {A : ValuationSubring Ω} [L : IsLocalGalois Γ k A]

/-- Let `V` be an open normal subgroup of prime index in `Γ`. If `β ≠ 0` in `H²(Γ, Ωˣ)` is split
by `V` (its restriction to `V` is zero), then every class `x` split by `V` is an integer multiple
of `β`.

This is the case of prime index of `mem_zmultiples_of_resH2_eq_zero`: the classes split by `V` are
the symbols `(ψ, y)` with `ker ψ = V` and `y ∈ kˣ`, and they form a quotient of `kˣ` modulo
norms, a group of prime order `[Γ : V]`. -/
lemma mem_zmultiples_of_index_prime [V.Normal] {β x : (unitsModule Γ).H2} (h_prime : V.index.Prime)
    (hβ : (unitsModule Γ).resH2 V β = 0) (hβ_ne : β ≠ 0) (hx : (unitsModule Γ).resH2 V x = 0) :
    x ∈ AddSubgroup.zmultiples β := by
  -- Write `V = ker ψ`. The symbol map `y ↦ (ψ, y)` sends `kˣ` onto the classes split by `V` and
  -- kills the norms `N`; by Tate's formula `kˣ ⧸ N` has prime order `[Γ : V]`, so the image of
  -- `β ≠ 0` generates.
  have h_fact : Fact V.index.Prime := ⟨h_prime⟩
  -- The fixed field of `V` is local, and `#(O' / n) = #(O / n) ^ [Γ : V]` for the valuation rings.
  have h_ext : IsLocalExtension k A (V : Subgroup Γ) (fixedFieldOf (V : Subgroup Γ)) := of_finite V
  have h_cyclic : IsCyclic (Γ ⧸ (V : Subgroup Γ)) := isCyclic_of_prime_card (p := V.index) rfl
  obtain ⟨ψ, hψ⟩ : ∃ χ : QZChar Γ, QZChar.ker χ = V := exists_ker_eq_of_isCyclic V h_cyclic
  -- From here on `V` is the kernel of the character `ψ`.
  obtain ⟨V, V_open⟩ := V
  obtain rfl : QZChar.ker ψ = V := hψ
  -- The split classes are the symbols `(ψ, y)` with `y ∈ kˣ`.
  have split_iff : ∀ z : (unitsModule Γ).H2, (unitsModule Γ).resH2 (QZChar.ker ψ) z = 0 ↔
      ∃ y : kˣ, z = cyclicClass unitsRep ψ (ofBase Γ Ω (Additive.ofMul y)) :=
    (cyclicClass_spec ψ).left
  obtain ⟨y, rfl⟩ := (split_iff β).mp hβ
  obtain ⟨z, rfl⟩ := (split_iff x).mp hx
  -- The symbol map kills the group `N` of norms.
  let N : Subgroup kˣ := map (Units.map (Algebra.norm k : fixedFieldOf (ker ψ) →* k)) ⊤
  let f : kˣ ⧸ N →* Multiplicative (unitsModule Γ).H2 :=
    lift N ((cyclicClass unitsRep ψ).comp (ofBase Γ Ω)).toMultiplicativeRight fun _ ⟨b, _, hb⟩ ↦
      (cyclicClass_eq_zero_iff_norm _).mpr ⟨b, hb⟩
  have f_mk (a : kˣ) : f (a : kˣ ⧸ N) =
      Multiplicative.ofAdd (cyclicClass unitsRep ψ (ofBase Γ Ω (Additive.ofMul a))) := rfl
  -- Tate's formula for the norm from the fixed field `K` of `ker ψ`: with `l = [Γ : ker ψ]`,
  -- `c = #(O / l)` for the integers `O` of `k`, and `q(Y) = #(Y / Y ^ l) / #Y[l]`, it reads
  -- `[kˣ : N] ^ (l - 1) * q(Kˣ) = q(kˣ) ^ l`, where `q(kˣ) = l * c` and `q(Kˣ) = l * c ^ l`.
  have card_eq : Nat.card (kˣ ⧸ N) = (QZChar.ker ψ).index := by
    set l : ℕ := (QZChar.ker ψ).index
    set c : ℕ := Nat.card (valRingBelow k A ⧸ Ideal.span {(l : valRingBelow k A)})
    have h_ne_l : NeZero l := ⟨h_prime.ne_zero⟩
    let q (Y : Type) [CommGroup Y] : ℚ :=
      cokerKerIndex (l : Module.End ℤ (Additive (⊤ : Subgroup Y)))
    obtain ⟨qk_ne, qk_eq⟩ : q kˣ ≠ 0 ∧ q kˣ = l * c :=
      cokerKerIndex_local_units L l topEquiv.toAdditive
    have qK_eq : q (fixedFieldOf (ker ψ))ˣ = l * c ^ l := by
      rw [← Nat.cast_pow, ← h_ext.card_quotient]
      exact (cokerKerIndex_local_units h_ext.isLocalGalois l topEquiv.toAdditive).right
    have tate : (N.relIndex ⊤ : ℚ) ^ (l - 1) * q (fixedFieldOf (ker ψ))ˣ = q kˣ ^ l :=
      tate_index_formula_norm l (finrank_fixedFieldOf (QZChar.ker ψ)) ⊤ ⊤ (comap_top _).symm
        (fun g y _ ↦ mem_top _) (fun _ _ ↦ ⟨1, mem_top _⟩) qk_ne
    rw [qK_eq, qk_eq, relIndex_top_right] at tate
    exact Nat.eq_of_pow_sub_one_mul_eq_mul_pow h_prime (by rwa [← qk_eq]) tate
  have y_ne : (y : kˣ ⧸ N) ≠ 1 := fun hy ↦ hβ_ne (by rw [← ofAdd_eq_one, ← f_mk, hy, map_one])
  -- So `z` is a power `y ^ m` modulo `N`, and applying `f` gives `(ψ, z) = m • (ψ, y)`.
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (y : kˣ ⧸ N) ^ m = z := mem_zpowers_of_prime_card card_eq y_ne
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨m, Multiplicative.ofAdd.injective ?_⟩
  rw [ofAdd_zsmul, ← f_mk, ← f_mk, ← map_zpow, hm]

/-- If the class `β` in `H²(Γ, Ωˣ)` is split by the open normal subgroup `V` (its restriction to
`V` is zero) and is killed only by multiples of `[Γ : V]`, then every class `x` split by `V` is an
integer multiple of `β`. -/
lemma mem_zmultiples_of_resH2_eq_zero [V.Normal] {β x : (unitsModule Γ).H2}
    (hβ : (unitsModule Γ).resH2 V β = 0) (hβ_order : ∀ n : ℕ, n • β = 0 → V.index ∣ n)
    (hx : (unitsModule Γ).resH2 V x = 0) : x ∈ AddSubgroup.zmultiples β := by
  -- Reduce via `mem_of_prime_step` to a single step `V ≤ W ≤ U` with `W` of prime index in `U`,
  -- done over the fixed field of `U`: given a multiple `s` of `β` with `x - s` split by `W`, find
  -- one with `x - s` split by `U`.
  refine mem_of_prime_step _ hx fun U W hW_normal hVU hVW hW_prime s hs hxs ↦ ?_
  -- `V_U` and `V'` are `V` seen inside `U` and `W`. The class `β'` on `U` dies on `W`, because a
  -- class split by an open subgroup is killed by its index (`index_smul_eq_zero_of_resH2`).
  let V_U : OpenSubgroup (U : Subgroup Γ) := V.comap (Subgroup.subtype _) continuous_subtype_val
  let V' : OpenSubgroup (W : Subgroup U) := V_U.comap (Subgroup.subtype _) continuous_subtype_val
  let β' : ((unitsModule Γ).restrictTo U).H2 := V'.index • (unitsModule Γ).resH2 U β
  -- `β` restricted to `U` is split by `V_U`, and then by `V'` inside `W`.
  have hβ_U : ((unitsModule Γ).restrictTo U).resH2 V_U ((unitsModule Γ).resH2 U β) = 0 :=
    resH2_subgroupOf_eq_zero_symm (by rw [hβ, map_zero])
  have dies : ((unitsModule Γ).restrictTo U).resH2 W β' = 0 := by
    simp only [β', map_nsmul]
    exact index_smul_eq_zero_of_resH2 V' (resH2_subgroupOf_eq_zero_symm (by rw [hβ_U, map_zero]))
  have index_eq : V.index = V'.index * U.index * W.index := by
    -- `V'.index` is by definition the relative index of `V` (inside `U`) in `W`.
    change V.index = ((V : Subgroup Γ).subgroupOf U).relIndex W * U.index * W.index
    rw [mul_right_comm, relIndex_mul_index hVW, ← relIndex_mul_index hVU, relIndex]
  -- If `β' = 0`, the proper divisor `V'.index * U.index` of `V.index` kills `β`, against
  -- `hβ_order`.
  have β'_ne : β' ≠ 0 := by
    intro hβ'_zero
    have h_kill : (V'.index * U.index) • β = 0 := by
      rw [mul_nsmul]
      exact index_smul_eq_zero_of_resH2 U (by rwa [map_nsmul])
    have h_pos : 0 < V'.index * U.index :=
      Nat.pos_of_ne_zero (mul_ne_zero index_ne_zero_of_finite index_ne_zero_of_finite)
    refine Nat.not_dvd_of_pos_of_lt h_pos ?_ (hβ_order _ h_kill)
    exact (lt_mul_of_one_lt_right h_pos hW_prime.one_lt).trans_eq index_eq.symm
  -- So on `U` the class `x - s`, which dies on `W`, is a multiple `j • β'`, and
  -- `s + j • V'.index • β` is the multiple of `β` sought.
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j • β' = (unitsModule Γ).resH2 U (x - s) :=
    mem_zmultiples_of_index_prime W (L := (of_finite U).isLocalGalois) hW_prime dies β'_ne hxs
  refine ⟨s + j • V'.index • β, by aesop, ?_⟩
  rw [← sub_sub, map_sub, ← hj, map_zsmul, map_nsmul, sub_self]

/-! ### The class attached to an element of `ℚ/ℤ` -/

/-- Let `Γ = Gal(Ω/k)` with `Ω` algebraically closed of characteristic 0, and let `A` be stable
under `Γ` with `A ∩ k` a discrete valuation ring with finite residue field (`IsLocalGalois Γ k A`).
Then there is an additive map `b : ℚ/ℤ → H²(Γ, Ωˣ)` satisfying `IsClassOfInvariant`. That is, `b` is
injective, and `b` sends `n • χ(φ)` to the cyclic class of `χ` and `w`, whenever `χ` is a continuous
unramified character `Γ → ℚ/ℤ`, `φ` is a Frobenius element, and `w ∈ Ωˣ` is invariant of normalised
order `n`. -/
lemma exists_isClassOfInvariant :
    ∃ b : QZ →+ H2 (unitsRep (Γ := Γ) (Ω := Ω)), IsClassOfInvariant Γ k A b := by
  -- The class of `r` is the cyclic class `(c r, π)`, where `π` is a uniformiser and `c r` is the
  -- unramified character with value `r` at the Frobenius element.
  obtain ⟨π, hπ⟩ : ∃ π : (unitsModule Γ).H0, ordRat k A π.val = 1 :=
    ⟨_, L.exists_isUniformiser.choose_spec.ordRat_eq_one L⟩
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ : Γ, IsFrob A (residueCard k A) φ := L.frobenius_spec.left
  choose c hc c_unique using existsUnique_unramified_char hφ₀
  -- If `(χ, w) = 0` then `w` is a norm from the fixed field of `χ`. For unramified `χ`, the order
  -- of a norm is a sum of `[Γ : ker χ]` equal integers.
  have index_dvd {χ : QZChar Γ} (hχ : inertiaGroup Γ A ≤ QZChar.ker χ) (w : (unitsModule Γ).H0)
      (n : ℤ) (hn : ordRat k A w.val = n) (h : cyclicClass _ χ w = 0) : ↑(ker χ).index ∣ n := by
    obtain ⟨y, hy⟩ := ((cyclicClass_spec χ).right w).mp h
    -- `y` is fixed by inertia, so its order is an integer.
    obtain ⟨j, hj⟩ : ∃ j : ℤ, ordRat k A y.val = j :=
      exists_ordRat_eq_intCast fun g hg ↦ y.property ⟨g, hχ hg⟩
    refine ⟨j, ?_⟩
    qify
    -- `erw`: `corestrictH0` unfolds to `DiscreteModule.sum`, a sum of maps only after unfolding.
    erw [← hn, ← hy, corestrictH0, LinearMap.sum_apply, map_sum,
        Finset.sum_eq_card_nsmul (b := ↑j)] <;>
      simp [index, Fintype.card_eq_nat_card, ← hj, eq_iff, ↓L.ordRat_eq_zero, decompGroup.val_smul,
        L.mem_decompGroup]
  -- `c` is additive by the uniqueness in `c_unique`.
  have c_add (r s : QZ) : c (r + s) = c r + c s := (c_unique _ _ (by simp_all)).symm
  refine ⟨((cyclicClass _).flip π).comp (.mk' c c_add),
    (injective_iff_map_eq_zero _).mpr fun r h ↦ ?_, fun χ hχ φ hφ w n hn ↦ ?_⟩
  · -- If `(c r, π) = 0`, the kernel of `c r` has index one, so `r = c r φ₀ = 0`.
    have h_index : (ker (c r)).index ∣ 1 := mod_cast index_dvd (hc r).left π 1 hπ h
    have h_frob : φ₀ ∈ ker (c r) := (index_eq_one.mp (Nat.dvd_one.mp h_index)).ge (mem_top φ₀)
    exact (hc r).right.symm.trans h_frob
  -- All classes `(χ, w)` are split by `ker χ`, and `(χ, π)` generates the split classes.
  have h_split (w : (unitsModule Γ).H0) :
      (unitsModule Γ).resH2 (ker χ) (cyclicClass _ χ w) = 0 := by
    obtain ⟨y, rfl⟩ := (ofBase_bijective Γ).surjective w
    exact ((cyclicClass_spec χ).left _).mpr ⟨y.toMul, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j • cyclicClass _ χ π = cyclicClass _ χ w :=
    mem_zmultiples_of_resH2_eq_zero ⟨_, isOpen_ker χ⟩ (h_split π)
      (fun n hn ↦ Int.ofNat_dvd.mp (index_dvd hχ (n • π) _ (by simp [hπ]) (by simpa using hn)))
      (h_split w)
  -- `j ≡ n` modulo the index, which kills `(χ, π)`.
  have h_ord_diff : ordRat k A (j • π - w).val = (j - n : ℤ) := by simp [hπ, hn]
  have h_class_diff : cyclicClass _ χ (j • π - w) = 0 := by simp [hj]
  obtain ⟨i, hi⟩ : ↑(ker χ).index ∣ j - n := index_dvd hχ (j • π - w) _ h_ord_diff h_class_diff
  have χ_eq : χ = c (χ.val φ) := c_unique _ χ
    ⟨hχ, (toHom χ).eq_iff.mpr (hχ _ (hφ.inv_mul_mem_inertiaGroup hφ₀))⟩
  simpa [← χ_eq, mul_zsmul', index_smul_eq_zero_of_resH2 ⟨_, isOpen_ker χ⟩ (h_split π),
    eq_add_of_sub_eq hi, add_zsmul] using hj.symm

/-- The chosen map `classOfInvariant` from `ℚ/ℤ` to `H²(Γ, Ωˣ)` is injective, and the cyclic class
of an unramified character `χ` and an invariant `w` of order `n` is
`n • classOfInvariant Γ k A (χ φ)` for a Frobenius `φ`.

This is the normalisation of the invariant map on the Brauer group of a local field in
characteristic 0, expressed through the inverse map and an arithmetic Frobenius. -/
lemma isClassOfInvariant_classOfInvariant : IsClassOfInvariant Γ k A (classOfInvariant Γ k A) :=
  Cohomology.isClassOfInvariant_classOfInvariant_of_exists Γ k A exists_isClassOfInvariant

variable {Γ' k' Ω' : Type} [Group Γ'] [TopologicalSpace Γ'] [Field k'] [Field Ω'] [Algebra k' Ω']
  [MulSemiringAction Γ' Ω'] {A' : ValuationSubring Ω'} [L' : IsLocalGalois Γ' k' A']

/-- Let `k'` be a second local field, with Galois group `Γ'` acting on `Ω'` and valuation ring `A'`,
and let `j : Ω → Ω'` be a field map compatible with `φ : Γ' → Γ` (`hj`) with `A'` pulling back to
`A` (`hA`). Suppose the `Γ`-fixed unit `w` of `Ωˣ` has normalised order `1` over `k` (`hw_ord`),
`j w` has order `e` over `k'` (`he`, so `e` is the ramification index), and the residue field of
`k'` has `q ^ f` elements, where `q` is that of `k` (`hf`). Then the map `H²(Γ, Ωˣ) → H²(Γ', Ω'ˣ)`
induced by `φ` and `j` sends `classOfInvariant Γ k A r`, the class with invariant `r ∈ ℚ/ℤ`, to the
class with invariant `(e * f) • r`. -/
lemma pairMapH2_classOfInvariant_of_ordRat_eq (φ : Γ' →ₜ* Γ) (j : Ω →+* Ω') (hA : A'.comap j = A)
    (hj : ∀ (g : Γ') (x : Ω), j (φ g • x) = g • j x) {e f : ℕ} {w : (unitsModule Γ).H0}
    (hw_ord : ordRat k A w = 1) (he : ordRat k' A' ((Units.map j).toAdditive w.val) = e)
    (hf : residueCard k' A' = residueCard k A ^ f) (r : QZ) :
    (pairMapH2 φ (Units.map j).toAdditive.toIntLinearMap) (classOfInvariant Γ k A r) =
      classOfInvariant Γ' k' A' ((e * f) • r) := by
  -- Write `r = χ σ` with `χ` unramified and `σ` a Frobenius, so the class is the cyclic class
  -- `(χ, w)`. Its image is the cyclic class of `χ ∘ φ` and `j w`; here `j w` has order `e`, and
  -- `χ ∘ φ` takes the value `f • r` on a Frobenius `τ` of `k'`.
  obtain ⟨σ, hσ⟩ : ∃ σ : Γ, IsFrob A (residueCard k A) σ := L.frobenius_spec.left
  obtain ⟨τ, hτ⟩ : ∃ τ : Γ', IsFrob A' (residueCard k' A') τ := L'.frobenius_spec.left
  obtain ⟨χ, χ_unr, rfl⟩ : ∃ χ : QZChar Γ, (∀ g ∈ inertiaGroup Γ A, χ.val g = 0) ∧ χ.val σ = r :=
    (existsUnique_unramified_char hσ r).exists
  subst hA
  let χ' : QZChar Γ' := comap φ χ
  -- The image of `w` in `Ω'ˣ` is fixed by `Γ'`, as `w` is fixed by `Γ` and `j` is compatible.
  let w' : (unitsModule Γ').H0 := ⟨(Units.map (j : Ω →* Ω')).toAdditive w.val, fun g ↦ by
    have hw : unitsRep (φ g) w.val = w.val := w.property (φ g)
    ext
    simpa [← hj] using congrArg (fun u : DiscreteUnits Ω ↦ j u.toMul.val) hw⟩
  have χ'_unr : ∀ g ∈ inertiaGroup Γ' A', χ'.val g = 0 := fun g hg ↦ χ_unr _ (hg.map hj)
  -- `φ τ` and `σ ^ f` are both Frobenius elements for `residueCard k A ^ f`, so they differ by
  -- inertia.
  have inertia : (σ ^ f)⁻¹ * φ τ ∈ inertiaGroup Γ (A'.comap j) :=
    (hσ.pow f).inv_mul_mem_inertiaGroup (by simpa only [hf] using hτ.map hj)
  have χ'_frob : χ'.val τ = f • χ.val σ :=
    ((toHom χ).eq_iff.mpr (χ_unr _ inertia)).trans (map_pow (toHom χ) σ f)
  have h_cyc : cyclicClass unitsRep χ w = (1 : ℤ) • classOfInvariant Γ k (A'.comap j) (χ.val σ) :=
    isClassOfInvariant_classOfInvariant.right χ χ_unr σ hσ w 1 hw_ord
  have h_cyc' : cyclicClass unitsRep χ' w' = (e : ℤ) • classOfInvariant Γ' k' A' (χ'.val τ) :=
    isClassOfInvariant_classOfInvariant.right χ' χ'_unr τ hτ w' e he
  -- The cocycles of both classes take the values `n • w` and `n • j w` with the same integers.
  have h_map : (pairMapH2 φ (Units.map j).toAdditive.toIntLinearMap) (cyclicClass unitsRep χ w) =
      cyclicClass unitsRep χ' w' :=
    congrArg (Quotient.mk _) (Subtype.ext (funext fun _ ↦ map_zsmul _ _ _))
  rwa [h_cyc, h_cyc', one_zsmul, χ'_frob, natCast_zsmul, ← map_nsmul, ← mul_smul] at h_map

/-- For two local Galois data `Γ, k, A` and `Γ', k', A'`, let `φ : Γ' →ₜ* Γ` be continuous and
`j : Ω →+* Ω'` a ring map with `A'.comap j = A` and `j (φ g • x) = g • j x`. Suppose a `Γ`-invariant
unit `w` of `Ω` has normalised order `1` on `k`, its image under `j` has normalised order `e` on
`k'`, and `residueCard k' A' = residueCard k A ^ f`; then the map `H²(Γ, Ωˣ) → H²(Γ', Ω'ˣ)` induced
by `φ` and `j` sends the class of invariant `r` to the class of invariant `(e * f) • r`. This is the
form of `pairMapH2_classOfInvariant_of_ordRat_eq` with the two conditions on the orders of `w` in
one hypothesis `he`. -/
lemma pairMapH2_classOfInvariant {Γ' k' Ω' : Type} [Group Γ'] [TopologicalSpace Γ'] [Field k']
    [Field Ω'] [Algebra k' Ω'] [MulSemiringAction Γ' Ω'] {A' : ValuationSubring Ω'}
    [L' : IsLocalGalois Γ' k' A'] (φ : Γ' →ₜ* Γ) (j : Ω →+* Ω') (hA : A'.comap j = A)
    (hj : ∀ (g : Γ') (x : Ω), j (φ g • x) = g • j x) {e f : ℕ} {w : (unitsModule Γ).H0}
    (he : ordRat k A w = 1 ∧ ordRat k' A' ((Units.map j).toAdditive w.val) = e)
    (hf : residueCard k' A' = residueCard k A ^ f) (r : QZ) :
    (pairMapH2 φ (Units.map j).toAdditive.toIntLinearMap) (classOfInvariant Γ k A r) =
      classOfInvariant Γ' k' A' ((e * f) • r) :=
  pairMapH2_classOfInvariant_of_ordRat_eq φ j hA hj he.left he.right hf r

/-- Restriction to an open subgroup `V`, the Galois group of `Ω` over the fixed field
`fixedFieldOf V`, sends the class of `r` to the class of `[Γ : V] • r`.

Part of the functoriality of the local invariant: in characteristic 0, restriction to an open
subgroup multiplies the invariant by the degree, expressed through the inverse map ℚ/ℤ → H². -/
lemma _root_.New.Cohomology.resH2_classOfInvariant {r : QZ} :
    (unitsModule Γ).resH2 V (classOfInvariant Γ k A r) =
      classOfInvariant V.toSubgroup (fixedFieldOf V.toSubgroup) A (V.index • r) := by
  -- The degree `[Γ : V]` is `e * f`, so this is `pairMapH2_classOfInvariant_of_ordRat_eq` for the
  -- inclusion of `V`, with a uniformiser `π` of `k` as the invariant of order `1`.
  obtain ⟨e, f, h_ram, -⟩ := (of_finite V).exists_isRamificationData
  obtain ⟨π, hπ_unif⟩ : ∃ π : kˣ, IsUniformiser A π.val := L.exists_isUniformiser
  have hπ : ordRat k A (ofBase Γ Ω (Additive.ofMul π)) = 1 := hπ_unif.ordRat_eq_one L
  have hπ_V : ordRat (fixedFieldOf (V : Subgroup Γ)) A
      ((Units.map (RingHom.id Ω)).toAdditive (ofBase Γ Ω (Additive.ofMul π)).val) = e := by
    simp [h_ram.ordRat_eq, hπ]
  rw [← h_ram.mul_eq]
  exact pairMapH2_classOfInvariant_of_ordRat_eq (L' := (of_finite V).isLocalGalois) _ (.id Ω) rfl
    (fun _ _ ↦ rfl) hπ hπ_V h_ram.residueCard_eq r

lemma resH2_classOfInvariant_eq_zero {r : QZ} (h_kill : V.index • r = 0) :
    (unitsModule Γ).resH2 V (classOfInvariant Γ k A r) = 0 := by
  rw [resH2_classOfInvariant V, h_kill]
  exact map_zero _

/-! ### The invariant -/

/-- For a henselian local field `k` of characteristic `0` with absolute Galois group `Γ`, the map
`New.Cohomology.classOfInvariant` from `ℚ/ℤ` to `H²(Γ, Ωˣ)` is bijective. So the Brauer group of `k`
is `ℚ/ℤ`.

This is the invariant isomorphism, stated for the inverse map ℚ/ℤ → H²(Γ, Ωˣ) and for `k` henselian
and discretely valued with finite residue field, complete or not. -/
lemma classOfInvariant_bijective : Bijective (classOfInvariant Γ k A) := by
  -- Injectivity is part of `isClassOfInvariant_classOfInvariant`. For surjectivity, a cocycle `x`
  -- is split by an open normal subgroup `W`, and the class of `1 / [Γ : W]` generates the classes
  -- split by `W`.
  refine ⟨isClassOfInvariant_classOfInvariant.left, Quot.ind fun ⟨x, x_cont, x_cocycle⟩ ↦ ?_⟩
  obtain ⟨W, hW⟩ : ∃ W : OpenNormalSubgroup Γ, ∀ h ∈ W, ∀ g : Γ, x (g, h) = x (g, 1) :=
    exists_openNormalSubgroup_apply_eq (x_cont.comp continuous_swap)
  have hW_index : NeZero W.index := ⟨index_ne_zero_of_finite⟩
  let r : QZ := ofZMod W.index 1
  have r_split : (unitsModule Γ).resH2 W.toOpenSubgroup (classOfInvariant Γ k A r) = 0 :=
    resH2_classOfInvariant_eq_zero _ (by simp [r, ← map_nsmul, ZMod.natCast_self])
  -- `classOfInvariant` is injective, and `n • r` is the image of `n` in `ZMod W.index`.
  have r_order (n : ℕ) (h : n • classOfInvariant Γ k A r = 0) : W.index ∣ n := by
    rw [← map_nsmul, map_eq_zero_iff _ isClassOfInvariant_classOfInvariant.left] at h
    simpa [r, ← map_nsmul, map_eq_zero_iff, ZMod.natCast_eq_zero_iff] using h
  -- On `W`, `x (g, h) = x (g, 1) = g • x (1, 1)` is the coboundary of the constant `x (1, 1)`.
  have x_g_one (g : Γ) : x (g, 1) = unitsRep g (x (1, 1)) - x (1, 1) + x (1, 1) := by
    simpa using x_cocycle g 1 1
  have x_split : (unitsModule Γ).resH2 W.toOpenSubgroup ⟦⟨x, x_cont, x_cocycle⟩⟧ = 0 :=
    (Submodule.ker_mkQ _).ge ⟨fun _ ↦ x (1, 1), continuous_const, fun g h ↦
      (hW h h.property g).trans (x_g_one g)⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n • classOfInvariant Γ k A r = ⟦⟨x, x_cont, x_cocycle⟩⟧ :=
    mem_zmultiples_of_resH2_eq_zero W.toOpenSubgroup r_split r_order x_split
  exact ⟨n • r, (map_zsmul _ n r).trans hn⟩

/-- Restriction to the open subgroup `V` (a finite extension of `k`) is onto on the classes of
`ℚ/ℤ`: every class `y` in `H²(V, Ωˣ)` is the restriction of the class of some `r`. -/
lemma exists_resH2_classOfInvariant_eq (y : ((unitsModule Γ).restrictTo V).H2) :
    ∃ r : QZ, (unitsModule Γ).resH2 V (classOfInvariant Γ k A r) = y := by
  -- `y` has an invariant `s` over the fixed field of `V`; divide `s` by the index in `ℚ/ℤ`.
  obtain ⟨s, rfl⟩ : ∃ s : QZ, classOfInvariant V.toSubgroup (fixedFieldOf V.toSubgroup) A s = y :=
    (of_finite V).isLocalGalois.classOfInvariant_bijective.surjective y
  obtain ⟨r, rfl⟩ : ∃ r : QZ, V.index • r = s :=
    DivisibleBy.surjective_smul _ ℤ (Int.natCast_ne_zero.mpr index_ne_zero_of_finite) s
  exact ⟨r, resH2_classOfInvariant V⟩

end New.IsLocalGalois
