import Lib.ClassField.Places.DecompositionCyclotomic
import Lib.ClassField.Places.ValuationSubrings
import Lib.General.Groups.ProfiniteCharacters

/-!
# Local fields: Frobenius, uniformisers, normalised valuation, extensions, unramified characters

A local field is a field `k` whose absolute Galois group `Γ` acts on an algebraic closure `Ω` and
stabilises a valuation subring `A` of `Ω` (`New.IsLocalGalois`). The trace `O = A ∩ k`
(`New.valRingBelow k A`) must be a discrete valuation ring whose residue field has finite order `q`
(`New.residueCard k A`); completeness is not assumed. `A.valuation` is multiplicative (at most 1 on
`A`). For a uniformiser `π` of `k`, the additive valuation `New.ordRat k A : Ωˣ → ℚ` is normalised
so that `π` has order `1`; it is defined on `DiscreteUnits Ω`, which is `Ωˣ` written additively
(`x.toMul` is the unit). `valuationVia k A c` is `A.valuation` of the image of `c : k` in `Ω`.

## Main definitions and results

* `New.IsLocalGalois.frobenius_spec`: for a henselian local field `k`, `Γ` contains an arithmetic
  Frobenius `φ`. The products of a power `φ ^ n` (`n ≥ 0`) with an element of inertia are dense in
  `Γ`, and `A` is integral over `A ∩ k`. The three parts are `New.IsLocalGalois.exists_isFrob`,
  `New.IsLocalGalois.denseRange_frob_pow_mul_inertia` and
  `New.IsLocalGalois.isIntegral_valRingBelow`.
* `New.IsLocalGalois.of_finite`: a finite extension `k'` of `k` is local, and its ramification index
  `e` and residue degree `f` satisfy `e * f = [k' : k]`. Moreover `e = 1` if the group of `k'`
  contains inertia.
* `New.existsUnique_unramified_char`: for a local field `k` and `r ∈ ℚ/ℤ` there is exactly one
  continuous character of its absolute Galois group that is trivial on inertia and sends a given
  Frobenius to `r`. It comes from the action on roots of unity of order dividing `q ^ m - 1`, `m`
  the order of `r`.

Notions from other files:
* `New.IsFrob`: `σ` stabilises the valuation subring `A` and `σ • x ≡ x ^ q` modulo the maximal
  ideal for all `x ∈ A`.
* `New.IsUniformiser`: `π` is a uniformiser of `K` for `A`: an element of `K` lies in the maximal
  ideal of `A` exactly when its valuation is at most that of `π`.
* `New.residueCard k A`: the order of the residue field of A ∩ k (zero if infinite).
* `New.ordRat k A`: the order on Ωˣ normalised on k, chosen so that `n * ordRat k A x = a` exactly
  when `x ^ n` and `π ^ a` have the same valuation, for uniformisers `π` of `k`.
* `New.QZ`: the group ℚ/ℤ; it is given the discrete topology.

## Relation to the literature

Known result: Hilbert ramification theory for infinite Galois extensions, here for local fields.
Places are valuation rings of an algebraic closure acted on by an abstract profinite group, and
local fields are only henselian with finite residue field. Source: J. Neukirch, Algebraic Number
Theory, 1999, I §9, II §§7–9, VI §1; J.-P. Serre, Local Fields, 1979, I §7, IV §2; Stacks Project,
tag 09EE.
-/

/-! ## Existence of Frobenius; Frobenius and inertia are topological generators -/

section LocalFrobenius

open IsLocalRing FiniteField Polynomial Ideal.Quotient MulSemiringAction Subgroup

/-- If every element of `Γ` maps the valuation subring `A` of `Ω` to itself, then `A`, as the
subring `New.valRingBelow Ω A` of `Ω`, is stable under `Γ`. -/
private lemma New.isInvariantSubring_valRingBelow_of_forall_mem_decompGroup {Γ Ω : Type*}
    [Group Γ] [Field Ω] [MulSemiringAction Γ Ω] {A : ValuationSubring Ω}
    (h_decomp : ∀ g : Γ, g ∈ decompGroup Γ A) :
    IsInvariantSubring Γ (valRingBelow Ω A).toSubring := by
  constructor
  intro g x hx
  simpa [mem_decompGroup_iff.mp (h_decomp g) x] using hx

/-- Let every element of `Γ` map the valuation subring `A` of `Ω` to itself, so that `Γ` acts on
`A` (as the subring `New.valRingBelow Ω A`) and on its residue field. Then `g` is a Frobenius
element for `q` at `A` (`New.IsFrob`) exactly when it acts on the residue field as `y ↦ y ^ q`. -/
private lemma New.isFrob_iff_forall_smul_residue_eq_pow {Γ Ω : Type*} [Group Γ] [Field Ω]
    [MulSemiringAction Γ Ω] {A : ValuationSubring Ω} (h_decomp : ∀ g : Γ, g ∈ decompGroup Γ A)
    (g : Γ) (q : ℕ) :
    letI := (New.isInvariantSubring_valRingBelow_of_forall_mem_decompGroup
      h_decomp).toMulSemiringAction
    IsFrob A q g ↔ ∀ y : ResidueField (valRingBelow Ω A), g • y = y ^ q := by
  let action_B : MulSemiringAction Γ (valRingBelow Ω A).toSubring :=
    (New.isInvariantSubring_valRingBelow_of_forall_mem_decompGroup h_decomp).toMulSemiringAction
  let B : ValuationSubring Ω := valRingBelow Ω A
  -- `g` acts on the residue of `y` through its action on `B`; two residues are equal when the
  -- difference has valuation below `1`.
  have h_smul_residue (y : B) : g • residue B y = residue B (g • y) := rfl
  have h_residue_eq_iff (y z : B) : residue B y = residue B z ↔ A.valuation ((y : Ω) - z) < 1 :=
    Iff.trans (mk_eq_mk_iff_sub_mem y z)
      (Valuation.mem_maximalIdeal_iff Ω (A.valuation.comap (algebraMap Ω Ω)))
  unfold IsFrob
  rw [and_iff_right (h_decomp g), residue_surjective.forall]
  constructor
  · intro h_close y
    rw [h_smul_residue, ← map_pow, h_residue_eq_iff]
    exact h_close y y.property
  · intro h_res x hx
    have h_y : g • residue B ⟨x, hx⟩ = residue B ⟨x, hx⟩ ^ q := h_res ⟨x, hx⟩
    rw [h_smul_residue, ← map_pow, h_residue_eq_iff] at h_y
    exact h_y

/-- Let `Γ` be the absolute Galois group of a henselian local field `K`, `A` the valuation ring of
the algebraic closure `Ω`, and `q` the order of the residue field of `A ∩ K`.
(a) There is an arithmetic Frobenius: `φ ∈ Γ` with `φ • x ≡ x ^ q` modulo the maximal ideal.
(b) For every such `φ`, the products `φ ^ n * i` (`n ≥ 0`, `i` in inertia) are dense in `Γ`.
(c) Every element of `A` (here `New.valRingBelow Ω A`) is integral over `A ∩ K`
(`New.valRingBelow K A`). -/
lemma New.IsLocalGalois.frobenius_spec {Γ K Ω : Type*} [Group Γ] [TopologicalSpace Γ] [Field K]
    [Field Ω] [Algebra K Ω] [MulSemiringAction Γ Ω] {A : ValuationSubring Ω}
    [L : IsLocalGalois Γ K A] :
    -- (a) an arithmetic Frobenius exists
    (∃ φ : Γ, IsFrob A (residueCard K A) φ) ∧
    -- (b) the products of a power of a Frobenius and an inertia element are dense
    (∀ {φ : Γ}, IsFrob A (residueCard K A) φ →
      DenseRange fun p : ℕ × inertiaGroup Γ A ↦ φ ^ p.1 * (p.2 : Γ)) ∧
    -- (c) the valuation ring of `Ω` is integral over that of `K`
    ∀ x : valRingBelow Ω A, IsIntegral (valRingBelow K A) (x : Ω) := by
  -- `Γ` acts on `B = A` with invariants `A ∩ K`, so `B` is integral and `Γ` surjects onto the
  -- automorphisms of the residue field `R` over that of `A ∩ K`; a lift of `y ↦ y ^ q` is a
  -- Frobenius. For density apply the same surjectivity to the closed subgroup generated by `φ`.
  have h_proGalois : IsProGalois Γ K Ω := L.toIsProGalois
  have h_algClosed : IsAlgClosed Ω := L.toIsAlgClosed
  let B : ValuationSubring Ω := valRingBelow Ω A
  let R : Type _ := ResidueField B
  -- with the discrete topology on `B` the action is continuous, since stabilisers are open
  let uniformSpace_B : UniformSpace B := ⊥
  let action_B : MulSemiringAction Γ B.toSubring :=
    (New.isInvariantSubring_valRingBelow_of_forall_mem_decompGroup
      L.mem_decompGroup).toMulSemiringAction
  have smulCommClass_B : SMulCommClass Γ (valRingBelow K A) B :=
    ⟨fun g x y ↦ Subtype.ext (smul_comm g x (y : Ω))⟩
  have continuousSMul_B : ContinuousSMul Γ B := continuousSMul_iff_stabilizer_isOpen.mpr fun x ↦
    Subgroup.isOpen_mono (fun g hg ↦ Subtype.ext hg) (L.isOpen_stabilizer (x : Ω))
  have h_inv : Algebra.IsInvariant (valRingBelow K A) B Γ := by
    refine ⟨fun ⟨x, hx⟩ h_fix ↦ ?_⟩
    obtain ⟨y, rfl⟩ : ∃ y : K, algebraMap K Ω y = x :=
      L.isInvariant.isInvariant x fun g ↦ congrArg Subtype.val (h_fix g)
    exact ⟨⟨y, hx⟩, rfl⟩
  have h_int : Algebra.IsIntegral (valRingBelow K A) B := h_inv.isIntegral_of_profinite
  -- Every `g` stabilises `A`, so `IsFrob` is a condition on the action on the residue field.
  have isFrob_iff {g : Γ} {q : ℕ} : IsFrob A q g ↔ ∀ y : R, g • y = y ^ q :=
    New.isFrob_iff_forall_smul_residue_eq_pow L.mem_decompGroup g q
  let k : Type _ := ResidueField (valRingBelow K A)
  have finite_k : Finite k := L.finite_residue
  refine ⟨?_, fun {φ} hφ g ↦ ?_, fun x ↦ (h_int.isIntegral x).algebraMap⟩
  · let fintype_k : Fintype k := .ofFinite k
    have isAlgebraic_R : Algebra.IsAlgebraic k R := (algebra_isIntegral_of_liesOver _ _).isAlgebraic
    -- lift the Frobenius automorphism of `R` over `k` to `Γ`
    -- `φ` is untyped: it lies in the stabiliser of the maximal ideal, whose action instance is
    -- found only through `stabilizerHom`
    obtain ⟨φ, hφ⟩ : ∃ φ,
        stabilizerHom (maximalIdeal B) (maximalIdeal (valRingBelow K A)) Γ φ =
          frobeniusAlgEquivOfAlgebraic k R :=
      stabilizerHom_surjective_of_profinite (maximalIdeal (valRingBelow K A)) _ _
    have hq : residueCard K A = Fintype.card k := Fintype.card_eq_nat_card.symm
    refine ⟨φ, isFrob_iff.mpr fun y ↦ ?_⟩
    rw [hq]
    exact AlgEquiv.congr_fun hφ y
  · -- `G` is the closed subgroup generated by `φ`, with invariants `B₀` in `B`.
    let G : Subgroup Γ := (Subgroup.zpowers φ).topologicalClosure
    let B₀ : Subring B := FixedPoints.subring B G
    let P : Ideal B₀ := (maximalIdeal B).under B₀
    have compactSpace_G : CompactSpace G :=
      isCompact_iff_compactSpace.mp isClosed_closure.isCompact
    -- the elements of `B` fixed by `G` are those of `B₀`
    have isInvariant_B₀ : Algebra.IsInvariant B₀ B G := ⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩
    -- The residue `y` of an element fixed by `φ` has `y ^ q = y`, so it lies in the residue field
    -- of `A ∩ K`, which `g` fixes.
    have h_fix (a : B₀) : g • residue B a = residue B a := by
      have h_pow : residue B a ^ residueCard K A = residue B a := by
        have hφ_mem : φ ∈ G := subset_closure ⟨1, zpow_one φ⟩
        have h_fixed : (⟨φ, hφ_mem⟩ : G) • (a : B) = (a : B) := a.property ⟨φ, hφ_mem⟩
        simpa [Subgroup.smul_def, isFrob_iff.mp hφ] using congrArg (residue B) h_fixed
      -- `residue B a` is a root of `X ^ q - X`, which splits over the residue field `k`
      obtain ⟨⟨b⟩, hb⟩ : residue B a ∈ (algebraMap k R).range :=
        splits_X_pow_nat_card_sub_X.mem_range_of_isRoot
          (X_pow_card_sub_X_ne_zero _ Finite.one_lt_card) (by simpa [sub_eq_zero] using h_pow)
      rw [← hb]
      exact congrArg (residue B) (smul_algebraMap g b)
    -- Hence some `s ∈ G` acts on `R` as `g` does, and `s⁻¹ * g` is in the inertia group.
    obtain ⟨s, hs⟩ : ∃ s, -- untyped for the same reason as `φ` above
        stabilizerHom (maximalIdeal B) P G s =
          { toRingAut Γ R g with commutes' := Quot.ind h_fix } :=
      stabilizerHom_surjective_of_profinite (G := G) P (maximalIdeal B) _
    -- the action of `s` on `R` is the map in `hs`
    have h_act (y : R) : (s : Γ) • y = g • y := DFunLike.congr_fun hs y
    have h_ine : (s : Γ)⁻¹ * g ∈ inertiaGroup Γ A := by
      refine New.mem_inertiaGroup_iff.mpr (isFrob_iff.mpr fun y ↦ ?_)
      rw [pow_one, mul_smul, inv_smul_eq_iff, h_act]
    -- In a compact group `s` is a limit of nonnegative powers of `φ`; multiply by `s⁻¹ * g`.
    have hs_mem : (s : Γ) ∈ _root_.closure (Set.range fun n : ℕ ↦ φ ^ n) :=
      (closure_range_zpow_eq_pow φ).le (s : G).property
    let i : inertiaGroup Γ A := ⟨(s : Γ)⁻¹ * g, h_ine⟩
    simpa using map_mem_closure (continuous_mul_const ((s : Γ)⁻¹ * g)) hs_mem
      (Set.forall_mem_range.mpr fun n ↦ Set.mem_range_self (n, i))

variable {Γ K Ω : Type*} [Group Γ] [TopologicalSpace Γ] [Field K] [Field Ω] [Algebra K Ω]
  [MulSemiringAction Γ Ω] {A : ValuationSubring Ω}

lemma New.IsLocalGalois.exists_isFrob [L : IsLocalGalois Γ K A] :
    ∃ φ : Γ, IsFrob A (residueCard K A) φ :=
  L.frobenius_spec.left

/-- For an arithmetic Frobenius `φ`, the products `φ ^ n * i` (`n : ℕ`, `i` in the inertia group
of `A`) are dense in `Γ`. -/
lemma New.IsLocalGalois.denseRange_frob_pow_mul_inertia [L : IsLocalGalois Γ K A] {φ : Γ}
    (hφ : IsFrob A (residueCard K A) φ) :
    DenseRange fun p : ℕ × inertiaGroup Γ A ↦ φ ^ p.1 * (p.2 : Γ) := by
  obtain ⟨-, h_dense, -⟩ := L.frobenius_spec
  exact h_dense hφ

/-- Every element of `A` (as `New.valRingBelow Ω A`) is integral over `New.valRingBelow K A`. -/
lemma New.IsLocalGalois.isIntegral_valRingBelow [L : IsLocalGalois Γ K A] (x : valRingBelow Ω A) :
    IsIntegral (valRingBelow K A) (x : Ω) := by
  obtain ⟨-, -, h_int⟩ := L.frobenius_spec
  exact h_int x

end LocalFrobenius

namespace New

/-!
## Uniformisers and the normalised additive valuation

The idea: the product of the conjugates of x ∈ Ω lies in k and has the valuation of a power of x
(`New.Cohomology.exists_val_eq_pow_index`), so the order of x is a rational number.
-/

section LocalValuation

open IsDiscreteValuationRing Subgroup MulAction Ideal Cohomology Finset Valuation

variable {Γ k Ω : Type*} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω] [Algebra k Ω]
  [MulSemiringAction Γ Ω] {A : ValuationSubring Ω}

/-- A uniformiser `π` of `k` lies in the maximal ideal of `A`: its valuation is below `1`. -/
lemma IsUniformiser.valuationVia_lt_one {π : k} (h : IsUniformiser A π) : valuationVia k A π < 1 :=
  (h π).mpr le_rfl

lemma dvd_iff_valuationVia_le {x y : valRingBelow k A} :
    x ∣ y ↔ valuationVia k A y ≤ valuationVia k A x :=
  (integer.integers _).dvd_iff_le

/-- If A ∩ k is a discrete valuation ring, then π ∈ k is a uniformiser for A if and only if π
lies in A ∩ k and is irreducible there. -/
lemma isUniformiser_iff_irreducible [IsDiscreteValuationRing (valRingBelow k A)] {π : k} :
    IsUniformiser A π ↔ ∃ h : π ∈ valRingBelow k A, Irreducible (⟨π, h⟩ : valRingBelow k A) := by
  -- Unfold both sides to inequalities of the valuation `v` of `A` read on `k`: the maximal ideal of
  -- `A ∩ k` is `(π)` when `v a < 1 ↔ v a ≤ v π` for all `a` with `v a ≤ 1`.
  -- `↓`: the plain `mem_maximalIdeal_iff` is too late, simp first turns membership into `¬IsUnit`
  simp [irreducible_iff_uniformizer, Ideal.ext_iff, ↓mem_maximalIdeal_iff, mem_span_singleton,
    dvd_iff_valuationVia_le, ← comap_apply, IsUniformiser]
  set v : Valuation k A.ValueGroup := A.valuation.comap (algebraMap k Ω)
  show (∀ x : k, v x < 1 ↔ v x ≤ v π) ↔ v π ≤ 1 ∧ ∀ a : k, v a ≤ 1 → (v a < 1 ↔ v a ≤ v π)
  refine ⟨fun h_unif ↦ ⟨((h_unif π).mpr le_rfl).le, fun a _ ↦ h_unif a⟩,
    fun ⟨hπ_le, h_unif⟩ x ↦ ?_⟩
  -- for `v x > 1 ≥ v π` both sides are false
  exact if hx : v x ≤ 1 then h_unif x hx
    else iff_of_false (fun h_lt ↦ hx h_lt.le) (fun h_le ↦ hx (h_le.trans hπ_le))

/-- If all of Γ = Gal(Ω / k) maps the valuation subring A to itself, then for x ∈ Ω the power
x ^ m, with m the number of conjugates of x (the index of its stabiliser), has the valuation of an
element of k. -/
lemma Cohomology.exists_val_eq_pow_index [h_galois : IsProGalois Γ k Ω]
    (h_decomp : ∀ g : Γ, g ∈ decompGroup Γ A) (x : Ω) :
    ∃ c : k, valuationVia k A c = A.valuation x ^ (stabilizer Γ x).index := by
  -- The product of the finitely many conjugates of `x` is fixed by `Γ`, so it comes from `k`.
  have fintype_orbit : Fintype (orbit Γ x) := (isLocallyConstant_smul x).range_finite.fintype
  have h_fixed (g : Γ) : g • ∏ y : orbit Γ x, (y : Ω) = ∏ y : orbit Γ x, (y : Ω) :=
    smul_prod'.trans (Equiv.prod_comp (toPerm g) fun y : orbit Γ x ↦ (y : Ω))
  obtain ⟨c, hc⟩ : ∃ c : k, algebraMap k Ω c = ∏ y : orbit Γ x, (y : Ω) :=
    h_galois.isInvariant.isInvariant _ h_fixed
  -- All of `Γ` is the decomposition group, so every conjugate has the valuation of `x`.
  have h_val : ∀ y : orbit Γ x, A y = A x := by
    rintro ⟨_, g, rfl⟩
    exact decompGroup.val_smul (h_decomp g) x
  refine ⟨c, ?_⟩
  calc valuationVia k A c = ∏ y : orbit Γ x, A y := by simp [valuationVia, hc]
    _ = A x ^ (stabilizer Γ x).index := by simp [h_val, index_stabilizer]

/-- If π is a uniformiser of k for A and x in the valuation ring 𝒪 of k has the valuation of
π^a, then #(𝒪/x) = q^a, with q the order of the residue field. -/
lemma IsUniformiser.card_quotient_span_eq_pow (L : IsLocalGalois Γ k A) {π : kˣ}
    (h : IsUniformiser A π.val) {x : valRingBelow k A} (a : ℕ)
    (hx : valuationVia k A x = valuationVia k A π ^ a) :
    Nat.card (valRingBelow k A ⧸ span {x}) = residueCard k A ^ a := by
  -- `x` generates the `a`-th power of the maximal ideal, which `π` generates.
  have h_dvr : IsDiscreteValuationRing (valRingBelow k A) := L.isDiscreteValuationRing
  obtain ⟨hπ_mem, hπ_irr⟩ := isUniformiser_iff_irreducible.mp h
  have h_span : span {x} = IsLocalRing.maximalIdeal (valRingBelow k A) ^ a := by
    rw [hπ_irr.maximalIdeal_eq, span_singleton_pow]
    -- `x` and `π ^ a` have the same valuation, so each divides the other
    refine le_antisymm ?_ ?_
    · rw [span_singleton_le_span_singleton, dvd_iff_valuationVia_le]
      simp [hx, valuationVia]
    · rw [span_singleton_le_span_singleton, dvd_iff_valuationVia_le]
      simp [hx, valuationVia]
  have h_card : Submodule.cardQuot (IsLocalRing.maximalIdeal (valRingBelow k A) ^ a) =
      Submodule.cardQuot (IsLocalRing.maximalIdeal (valRingBelow k A)) ^ a :=
    cardQuot_pow_of_prime h_dvr.not_a_field'
  -- the residue field is the quotient by the maximal ideal
  change Nat.card (valRingBelow k A ⧸ span {x}) =
    Nat.card (valRingBelow k A ⧸ IsLocalRing.maximalIdeal (valRingBelow k A)) ^ a
  rw [h_span, ← Submodule.cardQuot_apply, h_card, Submodule.cardQuot_apply]

/-- A non-zero element of the local field k has the valuation of an integral power of the
uniformiser π. -/
lemma IsUniformiser.exists_valuationVia_eq_zpow (L : IsLocalGalois Γ k A) {π : kˣ}
    (h : IsUniformiser A π.val) (x : k) (hx : x ≠ 0) :
    ∃ a : ℤ, valuationVia k A x = valuationVia k A π ^ a := by
  -- In the discrete valuation ring, `x = u • π ^ a` with a unit `u`, of valuation `1`.
  have h_dvr : IsDiscreteValuationRing (valRingBelow k A) := L.isDiscreteValuationRing
  obtain ⟨hπ_mem, hπ_irr⟩ := isUniformiser_iff_irreducible.mp h
  obtain ⟨a, u, rfl⟩ := exists_units_eq_smul_zpow_of_irreducible hπ_irr hx
  have hu : valuationVia k A (u : valRingBelow k A) = 1 :=
    (valuationSubring.integers _).valuation_unit u
  exact ⟨a, by simp [Units.smul_def, Algebra.smul_def, valuationVia, hu]⟩

/-- Let `Γ` be the Galois group of `Ω / k`, where `Ω` is algebraically closed of characteristic 0,
`Γ` stabilises the valuation subring `A`, and `A ∩ k` is a discrete valuation ring with finite
residue field (`IsLocalGalois`). If `k` has a uniformiser `π`, then there is an additive map `f`
from `Ωˣ` (written additively as `DiscreteUnits Ω`) to `ℚ` with the following property, which
defines `New.ordRat`: for every uniformiser `p` of `k`, every `x`, every `n : ℕ` and every `a : ℤ`,
the `A`-valuation of `x` raised to the power `n` equals `valuationVia k A p ^ a` exactly when
`n * f x = a`. -/
lemma IsUniformiser.exists_addMonoidHom_valuation_pow_eq_iff (L : IsLocalGalois Γ k A) {π : kˣ}
    (h : IsUniformiser A π.val) :
    ∃ f : DiscreteUnits Ω →+ ℚ, ∀ p : kˣ, IsUniformiser A p.val →
      ∀ (x : DiscreteUnits Ω) (n : ℕ) (a : ℤ),
        A.valuation x.toMul ^ n = valuationVia k A p ^ a ↔ n * f x = a := by
  -- The product of the `m x` conjugates of `x` has the valuation of `x ^ m x`, and that of some
  -- `π ^ b x`; put `f x = b x / m x`.
  let m (x : DiscreteUnits Ω) : ℕ := (stabilizer Γ (x.toMul : Ω)).index
  have hm (x : DiscreteUnits Ω) : m x ≠ 0 :=
    index_ne_zero_iff_finite.mpr (quotient_finite_of_isOpen _ (L.isOpen_stabilizer _))
  have hm_ne (x : DiscreteUnits Ω) : (m x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hm x)
  have h_norm (x : DiscreteUnits Ω) :
      ∃ b : ℤ, A.valuation x.toMul ^ m x = valuationVia k A π ^ b := by
    obtain ⟨c, hc⟩ := exists_val_eq_pow_index L.mem_decompGroup (x.toMul : Ω)
    have hc_ne : c ≠ 0 := by
      rintro rfl
      simpa [valuationVia] using hc.ge
    rw [← hc]
    exact h.exists_valuationVia_eq_zpow L c hc_ne
  choose b hb using h_norm
  -- In both steps clear denominators and use that `a ↦ v(π) ^ a` is injective, as `0 < v(π) < 1`.
  have hπ_pos : 0 < valuationVia k A π := by simp [pos_iff]
  have h_inj : Function.Injective fun a : ℤ ↦ valuationVia k A π ^ a :=
    zpow_right_injective₀ hπ_pos h.valuationVia_lt_one.ne
  have h_add (x y : DiscreteUnits Ω) : (b (x + y) / m (x + y) : ℚ) = b x / m x + b y / m y := by
    suffices h_int : b (x + y) * m x * m y = m (x + y) * (m y * b x + m x * b y) by
      have h_int_ℚ : (b (x + y) : ℚ) * m x * m y = m (x + y) * (m y * b x + m x * b y) := by
        exact_mod_cast h_int
      field_simp [hm_ne]
      linear_combination h_int_ℚ
    -- both sides give the valuation of `(x y) ^ (m (x + y) * m x * m y)`
    apply h_inj
    show valuationVia k A π ^ (b (x + y) * m x * m y) =
      valuationVia k A π ^ (m (x + y) * (m y * b x + m x * b y) : ℤ)
    simp [zpow_add₀ hπ_pos.ne', zpow_mul, ← hb, mul_comm, pow_right_comm, ← mul_pow]
  let f : DiscreteUnits Ω →+ ℚ := .mk' (fun x ↦ b x / m x) h_add
  have hf (x : DiscreteUnits Ω) (n : ℕ) (a : ℤ) :
      A.valuation x.toMul ^ n = valuationVia k A π ^ a ↔ n * f x = a := by
    have h_iff_ℚ : (n : ℚ) * f x = a ↔ n * b x = m x * a := by
      rw [show f x = b x / m x from rfl, ← mul_div_assoc, div_eq_iff (hm_ne x), mul_comm (a : ℚ)]
      exact_mod_cast Iff.rfl
    rw [h_iff_ℚ, ← h_inj.eq_iff, ← pow_left_inj₀ zero_le zero_le (hm x), pow_right_comm, hb x]
    -- both sides now compare powers of `v(π)`
    simp [zpow_mul, mul_comm]
  -- Any two uniformisers have the same valuation, so `f` has the property for every uniformiser.
  have h_unif (p : kˣ) (hp : IsUniformiser A p.val) : valuationVia k A π = valuationVia k A p :=
    ((hp π).mp h.valuationVia_lt_one).antisymm ((h p).mp hp.valuationVia_lt_one)
  exact ⟨f, fun p hp ↦ by simpa only [← h_unif p hp] using hf⟩

/-- Let k be a henselian local field with uniformiser π. For x ∈ Ω^×, n ∈ ℕ and a ∈ ℤ, x^n and π^a
have equal A-valuation if and only if n·ord(x) = a, where ord is the order normalised on k. -/
lemma IsUniformiser.valuation_pow_eq_zpow_iff_mul_ordRat_eq (L : IsLocalGalois Γ k A) {π : kˣ}
    (h : IsUniformiser A π.val) {x : DiscreteUnits Ω} (n : ℕ) (a : ℤ) :
    A.valuation x.toMul ^ n = valuationVia k A π ^ a ↔ n * ordRat k A x = a :=
  valuation_pow_eq_iff_mul_ordRat_eq_of_exists k A (h.exists_addMonoidHom_valuation_pow_eq_iff L) π
    h x n a

/-- A uniformiser `π` of `k` has order `1` for the order `New.ordRat k A` normalised on `k`. -/
lemma IsUniformiser.ordRat_eq_one (L : IsLocalGalois Γ k A) {π : kˣ} (h : IsUniformiser A π.val) :
    ordRat k A (DiscreteUnits.ofBase Γ Ω (Additive.ofMul π)) = 1 := by
  -- `ofBase` sends `π` to its image in `Ω`
  have h_val : A ((DiscreteUnits.ofBase Γ Ω (Additive.ofMul π) : DiscreteUnits Ω).toMul : Ω) =
      valuationVia k A π := rfl
  simpa using (h.valuation_pow_eq_zpow_iff_mul_ordRat_eq L 1 1).mp (by simpa using h_val)

lemma IsLocalGalois.exists_isUniformiser (L : IsLocalGalois Γ k A) :
    ∃ π : kˣ, IsUniformiser A π.val := by
  have h_dvr : IsDiscreteValuationRing (valRingBelow k A) := L.isDiscreteValuationRing
  obtain ⟨π, hπ⟩ := h_dvr.exists_irreducible
  exact ⟨.mk0 (π : k) (by simpa using hπ.ne_zero),
    isUniformiser_iff_irreducible.mpr ⟨π.property, hπ⟩⟩

lemma IsLocalGalois.ordRat_eq_zero (L : IsLocalGalois Γ k A) {x : DiscreteUnits Ω} :
    ordRat k A x = 0 ↔ A x.toMul = 1 := by
  simpa using (L.exists_isUniformiser.choose_spec.valuation_pow_eq_zpow_iff_mul_ordRat_eq L 1
    0).symm

end LocalValuation

/-! ## Finite extensions, ramification index and residue degree -/

section LocalExtension

open Nat IsLocalRing Module Algebra.TensorProduct Ideal Subtype Rat IsIntegralClosure ResidueField

universe w

variable {Γ k : Type*} {Ω : Type w} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω]
  [Algebra k Ω] [MulSemiringAction Γ Ω] {A : ValuationSubring Ω} [G : IsLocalGalois Γ k A]

/-- The order `q = residueCard k A` of the residue field of `O = A ∩ k` lies in the maximal ideal
of `A`: its valuation `A q` is less than `1`. -/
lemma valuation_residueCard_lt_one : A (residueCard k A) < 1 := by
  -- The order of the residue field is the index of the maximal ideal, and kills `1` modulo it.
  -- `residueCard k A` is the order of `O ⧸ maximalIdeal O`, which is this index by definition.
  have h_index : (maximalIdeal (valRingBelow k A)).toAddSubgroup.index = residueCard k A := rfl
  have h_mem : (residueCard k A : valRingBelow k A) ∈ maximalIdeal (valRingBelow k A) := by
    simpa [h_index] using (maximalIdeal (valRingBelow k A)).toAddSubgroup.nsmul_index_mem 1
  simpa using (Valuation.mem_maximalIdeal_iff k (A.valuation.comap (algebraMap k Ω))).mp h_mem

variable (k A) in
/-- For fields `k` and `k'` inside `Ω`, at the valuation subring `A`: the number `e` is the
ramification index and `f` the residue degree of `k'` over `k`, and their product is `n`. -/
structure IsRamificationData (k' : Type*) [Field k'] [Algebra k' Ω] (n e f : ℕ) : Prop where
  /-- The product of `e` and `f` is `n`. -/
  mul_eq : e * f = n
  /-- The orders of the residue fields satisfy `q' = q ^ f`. -/
  residueCard_eq : residueCard k' A = residueCard k A ^ f
  /-- The normalised additive valuations satisfy `ord' = e • ord`. -/
  ordRat_eq : ordRat k' A = e • ordRat k A

variable (k A) in
/-- The field `k'` inside `Ω` is local with group `V ≤ Γ`, and its ramification index, residue
degree and valuation ring are those of an extension of `k` of degree `V.index`. -/
structure IsLocalExtension (V : Subgroup Γ) (k' : Type*) [Field k'] [Algebra k' Ω] : Prop where
  /-- The field `k'` is local with group `V`. -/
  isLocalGalois : IsLocalGalois V k' A
  /-- There are `e` and `f` with `e * f = V.index`, and `e = 1` if `V` contains inertia. -/
  exists_isRamificationData :
    ∃ e f : ℕ, IsRamificationData k A k' V.index e f ∧ (inertiaGroup Γ A ≤ V → e = 1)
  /-- For the valuation rings, `#(O' / n) = #(O / n) ^ V.index`; an infinite order is `0`. -/
  card_quotient (n : ℕ) :
    Nat.card (valRingBelow k' A ⧸ span {(n : valRingBelow k' A)}) =
      Nat.card (valRingBelow k A ⧸ span {(n : valRingBelow k A)}) ^ V.index

/-- Let `k` be local (the instance `G`) and `k'` local with group `V`, over `k` inside `Ω`, with
uniformisers `π` of `k` and `π'` of `k'`. If `π` has the valuation of `π' ^ e`, then the orders
normalised on `k'` and on `k` satisfy `ordRat k' A = e • ordRat k A`. -/
private lemma ordRat_eq_nsmul_ordRat_of_valuationVia_eq_zpow {V : Subgroup Γ} {k' : Type*}
    [Field k'] [Algebra k' Ω] [Algebra k k'] [IsScalarTower k k' Ω] (L : IsLocalGalois V k' A)
    {π : kˣ} (hπ : IsUniformiser A π.val) {π' : k'ˣ} (hπ' : IsUniformiser A π'.val) {e : ℕ}
    (hπ_val : valuationVia k' A (algebraMap k k' π) = valuationVia k' A π'.val ^ (e : ℤ)) :
    ordRat k' A = e • ordRat k A := by
  refine AddMonoidHom.ext fun x ↦ ?_
  -- `n * ord x = a` means that `x ^ n` has the valuation of the `a`-th power of a uniformiser.
  -- With `ordRat k A x = a / d`, `x ^ d` has the valuation of `π ^ a`, that is of `π' ^ (e * a)`,
  -- so `d * ordRat k' A x = e * a`.
  set r : ℚ := ordRat k A x
  have h_π : valuationVia k A π.val = valuationVia k' A π'.val ^ (e : ℤ) := by
    simpa [valuationVia, IsScalarTower.algebraMap_apply k k' Ω] using hπ_val
  have h_k' : A.valuation x.toMul ^ r.den = valuationVia k' A π'.val ^ ((e : ℤ) * r.num) := by
    rw [zpow_mul, ← h_π]
    exact (hπ.valuation_pow_eq_zpow_iff_mul_ordRat_eq G r.den r.num).mpr (den_mul_eq_num r)
  have h_mul : (r.den : ℚ) * ordRat k' A x = ((e : ℤ) * r.num : ℤ) :=
    (hπ'.valuation_pow_eq_zpow_iff_mul_ordRat_eq L r.den _).mp h_k'
  show ordRat k' A x = e • r
  refine mul_left_cancel₀ (a := (r.den : ℚ)) (by positivity) ?_
  rw [h_mul, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, ← den_mul_eq_num r]
  ring

/-- If an open subgroup `V` of `Γ` contains inertia and the power `σ ^ f` (`f ≠ 0`) of an
arithmetic Frobenius `σ`, then `V` has index at most `f`. -/
private lemma index_le_of_isFrob_pow_mem {V : OpenSubgroup Γ} {σ : Γ}
    (hσ : IsFrob A (residueCard k A) σ) {f : ℕ} [NeZero f]
    (h_ine : inertiaGroup Γ A ≤ (V : Subgroup Γ)) (h_pow : σ ^ f ∈ (V : Subgroup Γ)) :
    V.index ≤ f := by
  -- The elements `σ ^ m * g` with `g` in inertia are dense, and lie in the coset of `σ ^ (m % f)`.
  have h_cover (γ : Γ) :
      (γ : Γ ⧸ (V : Subgroup Γ)) ∈
        Set.range fun i : Fin f ↦ ((σ ^ i.val : Γ) : Γ ⧸ (V : Subgroup Γ)) := by
    refine isClosed_property (G.denseRange_frob_pow_mul_inertia hσ)
      ((Set.finite_range _).isClosed.preimage (by fun_prop))
      (fun ⟨m, g⟩ ↦ ⟨.ofNat f m, ?_⟩) γ
    -- `σ ^ (m % f)` and `σ ^ m * g` lie in the same coset, as `σ ^ f ∈ V` and `g ∈ V`.
    have h_coset : ((σ ^ (m % f) : Γ) : Γ ⧸ (V : Subgroup Γ)) =
        ((σ ^ m * (g : Γ) : Γ) : Γ ⧸ (V : Subgroup Γ)) := by
      simp [mod_def, h_ine g.property, h_pow, pow_sub, mul_div_le, pow_mul, pow_mem]
    simpa using h_coset
  simpa [Subgroup.index] using card_le_card_of_surjective
    (fun i : Fin f ↦ ((σ ^ i.val : Γ) : Γ ⧸ (V : Subgroup Γ))) (Quotient.ind h_cover)

/-- A finite extension of a local field is local. Here `Γ` is the Galois group of an algebraically
closed field `Ω` of characteristic 0 over `k`, stabilising the valuation subring `A`, with `A ∩ k` a
discrete valuation ring with finite residue field. Given an open subgroup `V` of `Γ` and a finite
extension `k'` of `k` inside `Ω` with Galois group `V`, the claim is that `k'` is local in the same
sense with group `V` and ring `A`, and that its ramification index, residue degree and valuation
ring are those of an extension of `k` of degree `V.index`. -/
lemma IsLocalGalois.isLocalExtension (V : OpenSubgroup Γ) (k' : Type*) [Field k'] [Algebra k' Ω]
    [IsProGalois (V : Subgroup Γ) k' Ω] [Algebra k k'] [IsScalarTower k k' Ω]
    [FiniteDimensional k k'] :
    IsLocalExtension k A (V : Subgroup Γ) k' := by
  -- The valuation ring `P` of `k'` is the integral closure of the ring `O` of `k`, hence free of
  -- rank `[k' : k]` over `O`. Counting `O / π` and `P / π` gives `e * f = [k' : k]`; if `V`
  -- contains inertia, then `Γ / V` has at most `f` elements, since the powers of a Frobenius `σ`
  -- meet every coset and `σ ^ f ∈ V`.
  have h_dvr : IsDiscreteValuationRing (valRingBelow k A) := G.isDiscreteValuationRing
  have h_fin : Finite (ResidueField (valRingBelow k A)) := G.finite_residue
  obtain ⟨π, hπ⟩ : ∃ π : kˣ, IsUniformiser A π.val := G.exists_isUniformiser
  obtain ⟨σ, hσ⟩ : ∃ σ : Γ, IsFrob A (residueCard k A) σ := G.exists_isFrob
  have h_index : V.index = finrank k k' :=
    (eq_fixingSubgroup_of_isProGalois (V := (V : Subgroup Γ))).right
  let O : ValuationSubring k := valRingBelow k A
  let P : ValuationSubring k' := valRingBelow k' A
  have charZero_k : CharZero k := (algebraMap k Ω).charZero
  -- each `x : P` is integral over `O` in `Ω`, hence in `k'`, hence in `P`
  have isIntegral_OP : Algebra.IsIntegral O P :=
    ⟨fun x ↦ (G.isIntegral_valRingBelow ⟨algebraMap k' Ω x, x.property⟩).tower_bot_of_field
      |>.tower_bot val_injective⟩
  have isNoetherian_OP : IsNoetherian O P := isNoetherian O k k' P
  have isNoetherianRing_P : IsNoetherianRing P := isNoetherianRing O k k' P
  have faithfulSMul_OP : FaithfulSMul O P := .tower_bot O P k'
  -- `P` is a noetherian valuation ring, not a field, with residue field finite over that of `O`.
  have L : IsLocalGalois (V : Subgroup Γ) k' A :=
    { mem_decompGroup := fun g ↦ G.mem_decompGroup g
      isDiscreteValuationRing :=
        { not_a_field' := ne_bot_of_liesOver_of_ne_bot h_dvr.not_a_field' _ }
      finite_residue := finite_of_finite h_fin }
  obtain ⟨π', hπ'⟩ := L.exists_isUniformiser
  -- `P / x = (O / x) ⊗ P` is free of rank `[k' : k]` over `O / x`.
  have h_card (x : O) :
      Nat.card (P ⧸ span {algebraMap O P x}) = Nat.card (O ⧸ span {x}) ^ V.index := by
    have h_equiv : Nat.card (P ⧸ (span {x}).map (algebraMap O P)) =
        Nat.card (Fin (finrank O P) → O ⧸ span {x}) :=
      card_congr ((quotIdealMapEquivQuotTensor P (span {x})).toEquiv.trans
        (basis (O ⧸ span {x}) (finBasis O P)).equivFun.toEquiv)
    simpa [map_span, card_fun, h_index, IsFractionRing.finrank_eq O k P k'] using h_equiv
  -- The ramification index `e`: `π` has the valuation of `π' ^ e`, and `e ≥ 0` as `π` is integral.
  obtain ⟨e, he⟩ : ∃ e : ℤ, valuationVia k' A (algebraMap k k' π) = valuationVia k' A π' ^ e :=
    hπ'.exists_valuationVia_eq_zpow L _ (by simp)
  -- `v(π') ^ e = v(π) ≤ 1` and `v(π') < 1`.
  have he_nonneg : 0 ≤ e := by
    simpa [zero_lt_iff, hπ'.valuationVia_lt_one, valuationVia, he,
      IsScalarTower.algebraMap_apply k k' Ω]
      using hπ.valuationVia_lt_one.le
  lift e to ℕ using he_nonneg
  let f : ℕ := finrank (ResidueField O) (ResidueField P)
  have hq : residueCard k' A = residueCard k A ^ f := natCard_eq_pow_finrank
  -- Put `q = residueCard k A`. By `IsUniformiser.card_quotient_span_eq_pow`, `O / π` has `q`
  -- elements and `P / π` has `(q ^ f) ^ e`; by `h_card` the latter has `q ^ V.index`.
  have h_ef : e * f = V.index := by
    let π₀ : O := ⟨π, hπ.valuationVia_lt_one.le⟩
    have h_count : residueCard k' A ^ e = Nat.card (O ⧸ span {π₀}) ^ V.index := by
      rw [← h_card π₀, hπ'.card_quotient_span_eq_pow L e he]
    refine Nat.pow_right_injective h_fin.one_lt_card ?_
    simpa [O, π₀, pow_mul', hq, hπ.card_quotient_span_eq_pow G 1] using h_count
  refine ⟨L, ⟨e, f, ⟨h_ef, hq, ordRat_eq_nsmul_ordRat_of_valuationVia_eq_zpow L hπ hπ' he⟩,
    fun (h_ine : inertiaGroup Γ A ≤ (V : Subgroup Γ)) ↦ ?_⟩, fun n ↦ mod_cast h_card n⟩
  -- `σ ^ f` and a Frobenius `τ ∈ V` of `k'` differ by an element of inertia.
  obtain ⟨τ, hτ⟩ : ∃ τ : (V : Subgroup Γ), IsFrob A (residueCard k' A) τ := L.exists_isFrob
  have h_pow : σ ^ f ∈ (V : Subgroup Γ) := by
    have h_frob : IsFrob A (residueCard k' A) (σ ^ f) := by simpa only [hq] using hσ.pow f
    simpa [mul_mem_cancel_right τ.property] using h_ine (h_frob.inv_mul_mem_inertiaGroup hτ)
  have h_pos : 0 < V.index := h_index.trans_gt finrank_pos
  have neZero_f : NeZero f := ⟨by lia⟩
  have h_le : V.index ≤ f := index_le_of_isFrob_pow_mem hσ h_ine h_pow
  -- `0 < e * f = V.index ≤ f` forces `e = 1`.
  nlinarith

/-- A finite extension of a local field is local: `New.IsLocalGalois.isLocalExtension`, with `k'` by
default the fixed field in `Ω` of the open subgroup `V` of `Γ`. -/
lemma IsLocalGalois.of_finite (V : OpenSubgroup Γ)
    (k' : Type w := fixedFieldOf (V : Subgroup Γ)) [Field k'] [Algebra k' Ω]
    [IsProGalois (V : Subgroup Γ) k' Ω] [Algebra k k'] [IsScalarTower k k' Ω]
    [FiniteDimensional k k'] :
    IsLocalExtension k A (V : Subgroup Γ) k' :=
  G.isLocalExtension V k'

/-- The fixed field of an open subgroup `V` of `Γ` is local, a finite extension of `k`
(`New.IsLocalExtension`). -/
lemma IsLocalGalois.isLocalExtension_fixedFieldOf (V : OpenSubgroup Γ) :
    IsLocalExtension k A (V : Subgroup Γ) (fixedFieldOf (V : Subgroup Γ)) :=
  G.isLocalExtension V (fixedFieldOf (V : Subgroup Γ))

/-- Over a local field `k`, an element of `Ωˣ` fixed by the inertia group has integral order,
for the order normalised on `k`. -/
lemma IsLocalGalois.exists_ordRat_eq_intCast {x : DiscreteUnits Ω}
    (h_fixed : ∀ g ∈ inertiaGroup Γ A, unitsRep g x = x) :
    ∃ n : ℤ, ordRat k A x = n := by
  -- The field fixed by the stabiliser `V` of `x` contains `x` and is unramified over `k`, so its
  -- normalised order agrees with that of `k`.
  obtain ⟨V, hV⟩ :
      ∃ V : OpenSubgroup Γ, ∀ g : Γ, g ∈ (V : Subgroup Γ) ↔ g • (x.toMul : Ω) = x.toMul :=
    ⟨⟨MulAction.stabilizer Γ _, G.isOpen_stabilizer _⟩, fun _ ↦ .rfl⟩
  have h_ext : IsLocalExtension k A (V : Subgroup Γ) (fixedFieldOf (V : Subgroup Γ)) :=
    G.isLocalExtension_fixedFieldOf V
  have h_local : IsLocalGalois (V : Subgroup Γ) (fixedFieldOf (V : Subgroup Γ)) A :=
    h_ext.isLocalGalois
  obtain ⟨e, f, h_data, h_unram⟩ : ∃ e f : ℕ,
      IsRamificationData k A (fixedFieldOf (V : Subgroup Γ)) (V : Subgroup Γ).index e f ∧
        (inertiaGroup Γ A ≤ (V : Subgroup Γ) → e = 1) :=
    h_ext.exists_isRamificationData
  -- The inertia group fixes `x`, so it lies in `V`, and the extension is unramified.
  have h_inertia_le : inertiaGroup Γ A ≤ (V : Subgroup Γ) := fun g hg ↦
    (hV g).mpr (congrArg (fun y : DiscreteUnits Ω ↦ y.toMul.val) (h_fixed g hg))
  obtain rfl : e = 1 := h_unram h_inertia_le
  have h_ord : ordRat (fixedFieldOf (V : Subgroup Γ)) A = ordRat k A :=
    h_data.ordRat_eq.trans (one_smul _ _)
  obtain ⟨π, hπ⟩ : ∃ π : (fixedFieldOf (V : Subgroup Γ))ˣ, IsUniformiser A π.val :=
    h_local.exists_isUniformiser
  -- In that field `x` has the valuation of an integral power `π ^ n`.
  let y : fixedFieldOf (V : Subgroup Γ) := ⟨x.toMul, fun g ↦ (hV g).mp g.property⟩
  have hy_ne : y ≠ 0 := fun h_zero ↦ x.toMul.ne_zero (congrArg Subtype.val h_zero)
  obtain ⟨n, hn⟩ : ∃ n : ℤ, A.valuation (x.toMul : Ω) =
      valuationVia (fixedFieldOf (V : Subgroup Γ)) A π.val ^ n :=
    hπ.exists_valuationVia_eq_zpow h_local y hy_ne
  have h_eq : (1 : ℕ) * ordRat (fixedFieldOf (V : Subgroup Γ)) A x = n :=
    (hπ.valuation_pow_eq_zpow_iff_mul_ordRat_eq h_local 1 n).mp ((pow_one _).trans hn)
  exact ⟨n, by simpa [h_ord] using h_eq⟩

end LocalExtension

/-!
## Unramified characters with a given value at Frobenius

* `New.exists_openNormalSubgroup_apply_eq`: a continuous map from `Γ × Y` (`Γ` a Galois group as in
  `New.IsProGalois`, `Y` compact) to a discrete space satisfies `f (u, y) = f (1, y)` on an open
  normal subgroup.
-/

section UnramifiedCharacters

variable {Γ Ω k : Type*} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω] [Algebra k Ω]
  [MulSemiringAction Γ Ω] {A : ValuationSubring Ω} [L : IsLocalGalois Γ k A]

/-- For the Galois group `Γ` of `Ω` over `k` (`New.IsProGalois`), a compact space `Y`, a discrete
space `X` and a continuous `f : Γ × Y → X`, there is an open normal subgroup `U` of `Γ` with
`f (u, y) = f (1, y)` for all `u ∈ U` and all `y`. -/
lemma exists_openNormalSubgroup_apply_eq {Y X : Type*} [IsProGalois Γ k Ω] [TopologicalSpace Y]
    [CompactSpace Y] [TopologicalSpace X] [DiscreteTopology X] {f : Γ × Y → X} (hf : Continuous f) :
    ∃ U : OpenNormalSubgroup Γ, ∀ u ∈ U, ∀ y : Y, f (u, y) = f (1, y) := by
  -- The set of `(u, y)` with `f (u, y) ≠ f (1, y)` is closed, and so is its projection to `Γ`, as
  -- `Y` is compact. The complement is an open neighbourhood of `1`.
  have h_closed : IsClosed {p : Γ × Y | f p ≠ f (1, p.snd)} :=
    (isClosed_discrete {x : X × X | x.fst ≠ x.snd}).preimage (hf.prodMk (by fun_prop))
  simpa [Set.subset_def] using ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isClosedMap_fst_of_compactSpace _ h_closed).isOpen_compl

/-- Let `Γ` be the absolute Galois group of a local field `k` and `φ` an arithmetic Frobenius
(`New.IsFrob` for `q = residueCard k A`). For every `r` in `QZ = ℚ/ℤ` there is exactly one
continuous character `χ : Γ → ℚ/ℤ` (an element of `New.QZChar Γ`, applied as `χ.val`) that is
trivial on inertia and has `χ φ = r`. -/
lemma existsUnique_unramified_char {φ : Γ} (hφ : IsFrob A (residueCard k A) φ) (r : QZ) :
    ∃! χ : QZChar Γ, (∀ g ∈ inertiaGroup Γ A, χ.val g = 0) ∧ χ.val φ = r := by
  -- Let `m` be the order of `r` and `N = q ^ m - 1`. The action on the `N`-th roots of unity is
  -- unramified, and a character of `(ℤ/N)ˣ` takes the image of `φ` to `r`.
  have h_fin : Finite (IsLocalRing.ResidueField (valRingBelow k A)) := L.finite_residue
  have hq : 1 < residueCard k A := Finite.one_lt_card
  have hN_pos : 0 < residueCard k A ^ addOrderOf r - 1 := by simp [hq, r.isAddTorsion]
  let N : ℕ+ := ⟨residueCard k A ^ addOrderOf r - 1, hN_pos⟩
  -- `N` is a unit of `A`, as `q` lies in the maximal ideal.
  have hN : A N = 1 := by
    simp [N, Valuation.map_sub_eq_of_lt_right, pow_lt_one', r.isAddTorsion,
      valuation_residueCard_lt_one]
  -- Let `n` be the order of the image of `φ`. Then `φ ^ n`, a `q ^ n`-Frobenius, fixes the `N`-th
  -- roots of unity, so `q ^ m - 1 ∣ q ^ n - 1`, and `m ∣ n`.
  have order_dvd : addOrderOf r ∣ orderOf (cyclotomicCharMod Ω N φ) := by
    have h_mod : residueCard k A ^ orderOf (cyclotomicCharMod Ω N φ) ≡ 1 [MOD N] :=
      ((hφ.pow _).mem_ker_cyclotomicCharMod_iff hN).mp (by simp)
    simpa [Nat.dvd_iff_mod_eq_zero, Nat.sub_eq_iff_eq_add, NeZero.one_le, N, hq.ne'] using
      h_mod.symm.dvd'
  -- So `i ↦ i • r` factors through the powers of the image of `φ`, and it extends to `(ℤ/N)ˣ`
  -- because `ℚ/ℤ` is divisible.
  have h_ker : (zmultiplesHom (Additive (ZMod N)ˣ) (.ofMul (cyclotomicCharMod Ω N φ))).ker ≤
      (zmultiplesHom QZ r).ker := by
    simpa [zmultiplesHom_ker_eq, Int.mem_zmultiples_iff, Int.ofNat_dvd] using order_dvd
  obtain ⟨e, he⟩ :
      ∃ e : Additive (ZMod N)ˣ →+ QZ, ∀ i : ℤ, e (i • .ofMul (cyclotomicCharMod Ω N φ)) = i • r :=
    QZ.exists_extend _ _ h_ker
  let χ : QZChar Γ :=
    ⟨(e ∘ .ofMul) ∘ cyclotomicCharMod Ω N, .comp (by fun_prop) (.of_isOpen_ker _ Fact.out), by simp⟩
  refine existsUnique_of_exists_of_unique ⟨χ, fun g hg ↦ ?_, ?_⟩ fun a b ha hb ↦ ?_
  · simp [χ, cyclotomicCharMod_eq_one_of_mem_inertiaGroup hg hN]
  · simpa [χ] using he 1
  · -- The elements `φ ^ n * g` with `g` in inertia are dense, and `a`, `b` agree on them.
    have h_dense : DenseRange fun p : ℕ × inertiaGroup Γ A ↦ φ ^ p.1 * (p.2 : Γ) :=
      L.denseRange_frob_pow_mul_inertia hφ
    obtain ⟨ha_cont, ha_add⟩ : (a : Γ → QZ) ∈ QZChar Γ := a.property
    obtain ⟨hb_cont, hb_add⟩ : (b : Γ → QZ) ∈ QZChar Γ := b.property
    refine Subtype.ext (h_dense.equalizer ha_cont hb_cont ?_)
    ext ⟨n, g⟩
    induction n with
    | zero => simp_all
    | succ n ih => simp_all [pow_succ]

end UnramifiedCharacters

end New
