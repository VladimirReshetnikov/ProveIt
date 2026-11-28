import Lib.ClassField.GaloisCohomology.ContinuousCocycles

/-!
# Profinite Galois groups: continuity, restriction maps and the Galois correspondence

Infinite Galois theory for an abstract group. `New.IsProGalois Γ K Ω` says that the profinite group
`Γ` acts on the Galois extension `Ω / K` as its Galois group, with open stabilisers. This covers
`Gal(Ω/K)` and its closed subgroups `H` (acting over the fixed field `New.fixedFieldOf H`) at once.
`Fact (IsOpen U)` and `IsClosed H` are used as instances on subgroups.

* `New.continuous_of_equivariant_emb`: a map between such groups that is compatible with a ring
  homomorphism of the top fields is continuous.
* `New.exists_galois_restrict`, `New.isClosedEmbedding_galois_restrict`,
  `New.isOpenEmbedding_galois_restrict`: restriction maps between Galois groups, along a map of the
  top fields or to a smaller base field. The parts of the second one are
  `New.isClosedEmbedding_of_smul_eq_smul`, `New.range_eq_fixingSubgroup_of_smul_eq_smul` and
  `New.index_range_eq_finrank_of_smul_eq_smul`.
* `New.fixedFieldOf_fixingSubgroup`, `New.fixingSubgroup_fixedFieldOf`, `New.finrank_fixedFieldOf`:
  the Galois correspondence between intermediate fields and closed subgroups, with degree equal to
  index.

Notions from other files:
* `New.DiscreteUnits.ofBase`: the homomorphism from K^× to the Γ-invariants of Ω^× (both written
  additively) induced by K → Ω.

## Relation to the literature

Known; see `Lib.ClassField.Places.LocalFields` for sources.
-/

open Function MulSemiringAction InfiniteGalois Subgroup Units IntermediateField IsScalarTower Module
  Fact Subtype DFunLike MulAction Topology algebraMap

namespace New

/-- `Ω` is an algebraic closure of every field `K` of characteristic zero of which it is an
algebra. -/
instance {K : Type*} [Field K] [CharZero K] [Algebra K Ω] : IsAlgClosure K Ω where
  isAlgClosed := inferInstance
  isAlgebraic := .tower_top (K := ℚ) K

/-- A chosen embedding of the number field K into the fixed algebraic closure `Ω` of ℚ (the constant
of the instance above, not the section variable `Ω`). -/
noncomputable def Ω.fieldEmb (K : Type*) [Field K] [NumberField K] : K →+* Ω := Classical.ofNonempty

section

variable {Γ K Ω : Type*} [Group Γ] [TopologicalSpace Γ] [Field K] [Field Ω] [Algebra K Ω]
  (H U : Subgroup Γ) [h : IsClosed (X := Γ) H] [Fact (IsOpen (X := Γ) U)]

instance (U : OpenSubgroup Γ) : Fact (IsOpen (X := Γ) U.toSubgroup) := ⟨U.isOpen⟩

/-- The Galois group of a Galois extension `Ω / K`, with its Krull topology, acts on `Ω` as its
profinite Galois group. -/
instance [IsGalois K Ω] : IsProGalois Gal(Ω/K) K Ω := ⟨stabilizer_isOpen_of_isIntegral⟩

/-- An open subgroup `U` of a topological group is closed. -/
instance [ContinuousMul Γ] : IsClosed (X := Γ) U := U.isClosed_of_isOpen out

/-- A closed subgroup `H` of a compact group is compact. -/
instance [CompactSpace Γ] : CompactSpace H := isCompact_iff_compactSpace.mp h.isCompact

end

variable {Γ K Ω : Type*} [Group Γ] [TopologicalSpace Γ] [Field K] [Field Ω] [Algebra K Ω]
  [MulSemiringAction Γ Ω] [G : IsProGalois Γ K Ω]
  (H U : Subgroup Γ) [h : IsClosed (X := Γ) H] [Fact (IsOpen (X := Γ) U)]
  {Γ' L Ω' : Type*} [Group Γ'] [TopologicalSpace Γ'] [Field L] [Field Ω'] [Algebra L Ω']
  [MulSemiringAction Γ' Ω'] (j : Ω →+* Ω')

/-- A closed subgroup is the Galois group over its fixed field. -/
instance : @IsProGalois H (fixedFieldOf H) Ω _ _ _ inferInstance _ _ :=
  ⟨fun x ↦ (G.isOpen_stabilizer x).preimage_val⟩

include G

/-! ### The topology of `Γ` and its action on `Ω` -/

/-- For each `x : Ω`, the orbit map `g ↦ g • x` on the profinite Galois group `Γ` is locally
constant. -/
lemma isLocallyConstant_smul (x : Ω) : IsLocallyConstant fun g : Γ ↦ g • x := by
  -- The map factors through the quotient by the open stabilizer of `x`, which is discrete.
  have h_discrete : DiscreteTopology (Γ ⧸ stabilizer Γ x) :=
    QuotientGroup.discreteTopology (G.isOpen_stabilizer x)
  exact .of_discrete (ofQuotientStabilizer Γ x)

/-- The elements `g` of the profinite Galois group `Γ` such that `g • x` satisfies a given predicate
form a closed set. -/
lemma isClosed_setOf_smul (x : Ω) (P : Ω → Prop) : IsClosed {g : Γ | P (g • x)} :=
  -- Its complement is the preimage of `{y | ¬ P y}` under the locally constant orbit map.
  isOpen_compl_iff.mp (isLocallyConstant_smul x {y : Ω | ¬P y})

/-- Let `Γ` act as the Galois group of `Ω / K`, `Γ'` as that of `Ω' / L`, and let `j : Ω → Ω'` be a
ring homomorphism. A map `φ : Γ' → Γ` with `j (φ g • x) = g • j x` for all `g` and `x` is
continuous. -/
lemma continuous_of_equivariant_emb [IsProGalois Γ' L Ω'] {φ : Γ' → Γ}
    (hφ : ∀ (g : Γ') (x : Ω), j (φ g • x) = g • j x) : Continuous φ := by
  -- With `Ω` discrete, `g ↦ (g • ·)` embeds the compact group `Γ` in the space of maps `Ω → Ω`.
  let uniformSpace_discrete : UniformSpace Ω := ⊥
  have h_emb : IsClosedEmbedding fun (g : Γ) (x : Ω) ↦ g • x :=
    (continuous_pi fun x ↦ (isLocallyConstant_smul x).continuous).isClosedEmbedding
      fun g g' h_eq ↦ G.faithful.eq_of_smul_eq_smul (congrFun h_eq)
  refine h_emb.continuous_iff.mpr (continuous_pi fun x ↦ IsLocallyConstant.continuous ?_)
  -- `g ↦ φ g • x` is locally constant because its composite with the injection `j` is.
  have h_const : IsLocallyConstant fun g ↦ j (φ g • x) := by
    simpa only [hφ] using isLocallyConstant_smul (j x)
  exact h_const.desc _ j j.injective

variable (Γ Γ')

/-- Every `K`-automorphism of `Ω` is given by an element of `Γ`. -/
lemma toAlgAut_surjective : Surjective (toAlgAut Γ K Ω) := by
  -- The image is a closed subgroup whose fixed field is `K`; by Galois theory it is everything.
  have h_cont : Continuous (toAlgAut Γ K Ω) := continuous_of_equivariant_emb 1 fun _ _ ↦ rfl
  let S : ClosedSubgroup Gal(Ω/K) := ⟨(toAlgAut Γ K Ω).range, (isCompact_range h_cont).isClosed⟩
  refine fun σ ↦ (fixingSubgroup_fixedField S).le fun ⟨x, hx⟩ ↦ ?_
  -- `x` is fixed by the image of `Γ`, so it lies in `K`.
  have h_fixed (g : Γ) : g • x = x := (mem_fixedField_iff _ _).mp hx (toAlgAut Γ K Ω g) ⟨g, rfl⟩
  obtain ⟨y, rfl⟩ : ∃ y : K, algebraMap K Ω y = x := G.isInvariant.isInvariant x h_fixed
  exact σ.commutes y

/-- The units of `K` are exactly the `Γ`-invariant units of `Ω`. -/
lemma DiscreteUnits.ofBase_bijective : Bijective (ofBase Γ Ω (K := K)) := by
  refine ⟨coind_injective _ (map_injective (algebraMap K Ω).injective), fun x ↦ ?_⟩
  -- An invariant unit of `Ω` comes from a nonzero element of `K`.
  have h_fixed (g : Γ) : g • ((x.val.toMul : Ωˣ) : Ω) = (x.val.toMul : Ωˣ) :=
    congrArg (fun v : DiscreteUnits Ω ↦ (v.toMul : Ω)) (x.property g)
  obtain ⟨y, hy⟩ : ∃ y : K, algebraMap K Ω y = (x.val.toMul : Ωˣ) :=
    G.isInvariant.isInvariant _ h_fixed
  exact ⟨mk0 y (by grind [ne_zero]), val_injective (ext hy)⟩

/-- Two ring homomorphisms `j, j' : Ω → Ω'` that agree on `K` differ by an element of `Γ`:
`j (g • x) = j' x` for some `g` and all `x`. -/
lemma exists_apply_smul_eq_of_comp_algebraMap_eq (j' : Ω →+* Ω')
    (h_agree : j.comp (algebraMap K Ω) = j'.comp (algebraMap K Ω)) :
    ∃ g : Γ, ∀ x : Ω, j (g • x) = j' x := by
  -- Through `j`, the field `Ω'` is an `Ω`-algebra and `j'` is a `K`-algebra map. As `Ω / K` is
  -- normal, every such map is `j` composed with a `K`-automorphism of `Ω`.
  algebraize [j, j.comp (algebraMap K Ω)]
  obtain ⟨σ, hσ⟩ := (Normal.algHomEquivAut K Ω' Ω).symm.surjective ⟨j', ext_iff.mp h_agree.symm⟩
  obtain ⟨g, rfl⟩ := toAlgAut_surjective Γ σ
  exact ⟨g, fun x ↦ DFunLike.congr_fun hσ x⟩

/-! ### Restriction maps -/

/-- Let `Γ` act as the Galois group of `Ω / K`, `Γ'` as that of `Ω' / L`, and let `j : Ω → Ω'` be a
ring homomorphism such that every element of `Γ'` fixes the image under `j` of each element of `K`.
Then there is a continuous homomorphism `φ : Γ' → Γ` with `j (φ g • x) = g • j x` for all `g` and
`x`. -/
lemma exists_galois_restrict [IsProGalois Γ' L Ω']
    (h_fix : ∀ (g : Γ') (x : K), g • j (algebraMap K Ω x) = j (algebraMap K Ω x)) :
    ∃ φ : Γ' →ₜ* Γ, ∀ (g : Γ') (x : Ω), j (φ g • x) = g • j x := by
  -- The embeddings `j` and `g • j` agree on `K`, so they differ by an element of `Γ`.
  have h_exists (g : Γ') : ∃ σ : Γ, ∀ x : Ω, j (σ • x) = g • j x :=
    exists_apply_smul_eq_of_comp_algebraMap_eq Γ j ((toRingHom Γ' Ω' g).comp j)
      (RingHom.ext (h_fix g)).symm
  choose f hf using h_exists
  have h_mul (g g' : Γ') : f (g * g') = f g * f g' :=
    G.faithful.eq_of_smul_eq_smul fun x ↦ j.injective (by simp [hf, mul_smul])
  exact ⟨⟨.mk' f h_mul, continuous_of_equivariant_emb j hf⟩, hf⟩

variable {Γ Γ'} [Algebra K L] [Algebra L Ω] [MulSemiringAction Γ' Ω] [IsScalarTower K L Ω]
  [J : IsProGalois Γ' L Ω] (φ : Γ' →* Γ)

include J in
omit [Algebra K L] [IsScalarTower K L Ω] in
/-- For `K ⊆ Ω`, `L ⊆ Ω` with profinite Galois groups `Γ` of `Ω / K` (`G`) and `Γ'` of `Ω / L`
(`J`), a homomorphism `φ: Γ' →* Γ` with `φ g • x = g • x` for all `g` and `x` (such as
`AlgEquiv.restrictScalarsHom`) is a closed embedding. -/
lemma isClosedEmbedding_of_smul_eq_smul (hφ : ∀ (g : Γ') (x : Ω), φ g • x = g • x) :
    IsClosedEmbedding φ := by
  -- `φ` is injective because `Γ'` acts faithfully on `Ω`.
  have h_inj : Injective φ := fun g g' h_eq ↦
    J.faithful.eq_of_smul_eq_smul fun x ↦ by rw [← hφ, h_eq, hφ]
  -- A continuous injection of a compact space into a Hausdorff one is a closed embedding.
  exact (continuous_of_equivariant_emb (RingHom.id Ω) hφ).isClosedEmbedding h_inj

omit [Algebra K L] [IsScalarTower K L Ω] in
/-- For `K ⊆ Ω`, `L ⊆ Ω` with Galois groups `Γ` of `Ω / K` and `Γ'` of `Ω / L`, the range of a
homomorphism `φ: Γ' →* Γ` with `φ g • x = g • x` for all `g` and `x` is the subgroup of `Γ` fixing
`L` pointwise. -/
lemma range_eq_fixingSubgroup_of_smul_eq_smul (hφ : ∀ (g : Γ') (x : Ω), φ g • x = g • x) :
    φ.range = fixingSubgroup Γ (Set.range (algebraMap L Ω)) := by
  refine le_antisymm ?_ fun g hg ↦ ?_
  · -- The image of `φ` fixes `L`, since `Γ'` does.
    simp [IsConcreteLE.le_iff, mem_fixingSubgroup_iff, hφ]
  -- An element `g` fixing `L` acts on `Ω` as some `g' : Γ'`.
  have h_agree_L (y : L) : algebraMap L Ω y = g • algebraMap L Ω y :=
    ((mem_fixingSubgroup_iff Γ).mp hg _ ⟨y, rfl⟩).symm
  obtain ⟨g', hg'⟩ : ∃ g' : Γ', ∀ x : Ω, g' • x = g • x :=
    exists_apply_smul_eq_of_comp_algebraMap_eq Γ' (RingHom.id Ω) (toRingHom Γ Ω g)
      (RingHom.ext h_agree_L)
  exact ⟨g', G.faithful.eq_of_smul_eq_smul fun x ↦ (hφ g' x).trans (hg' x)⟩

/-- For `K ⊆ L ⊆ Ω` with Galois groups `Γ` of `Ω / K` and `Γ'` of `Ω / L`, the range of a
homomorphism `φ : Γ' →* Γ` with `φ g • x = g • x` for all `g` and `x` has index `[L : K]` in `Γ`
(both sides are `0` if the degree is infinite). -/
lemma index_range_eq_finrank_of_smul_eq_smul (hφ : ∀ (g : Γ') (x : Ω), φ g • x = g • x) :
    φ.range.index = finrank K L := by
  -- The index is that of the group fixing the image of `L`, pulled back along `Γ → Gal(Ω/K)`.
  rw [range_eq_fixingSubgroup_of_smul_eq_smul φ hφ,
    (toAlgHom K L Ω).equivFieldRange.toLinearEquiv.finrank_eq, finrank_eq_fixingSubgroup_index,
    ← index_comap_of_surjective _ (toAlgAut_surjective Γ)]
  -- The subgroup of `Γ` fixing `L` is, by definition, the preimage of the one in `Gal(Ω/K)`.
  rfl

/-- Restriction to a smaller base field. For `K ⊆ L ⊆ Ω` with Galois groups `Γ` of `Ω / K` and `Γ'`
of `Ω / L`, a homomorphism `φ : Γ' →* Γ` compatible with the actions on `Ω` is (a) a closed
embedding, (b) onto the subgroup fixing `L`, (c) whose index is `[L : K]` (both sides are `0` if the
degree is infinite). -/
lemma isClosedEmbedding_galois_restrict (hφ : ∀ (g : Γ') (x : Ω), φ g • x = g • x := by tauto) :
    IsClosedEmbedding φ ∧
    φ.range = fixingSubgroup Γ (Set.range (algebraMap L Ω)) ∧
    φ.range.index = finrank K L :=
  ⟨isClosedEmbedding_of_smul_eq_smul φ hφ, range_eq_fixingSubgroup_of_smul_eq_smul φ hφ,
    index_range_eq_finrank_of_smul_eq_smul φ hφ⟩

/-- For `K ⊆ L ⊆ Ω` with `L / K` finite and Galois groups `Γ` of `Ω / K` and `Γ'` of `Ω / L`, a
homomorphism `φ : Γ' →* Γ` with `φ g • x = g • x` for all `g` and `x` is an open embedding. -/
lemma isOpenEmbedding_galois_restrict (hφ : ∀ (g : Γ') (x : Ω), φ g • x = g • x)
    [Module.Finite K L] : IsOpenEmbedding φ := by
  -- The image is a closed subgroup of finite index.
  have h_closedEmb := isClosedEmbedding_of_smul_eq_smul φ hφ
  have h_finiteIndex : φ.range.FiniteIndex :=
    ⟨(index_range_eq_finrank_of_smul_eq_smul φ hφ).trans_ne finrank_pos.ne'⟩
  exact ⟨h_closedEmb.isEmbedding,
    isOpen_of_isClosed_of_finiteIndex φ.range h_closedEmb.isClosed_range⟩

/-! ### The Galois correspondence -/

/-- Galois correspondence: the fixed field of the subgroup of `Γ` fixing an intermediate field `L`
of `Ω / K` pointwise is `L`. -/
lemma fixedFieldOf_fixingSubgroup (L : IntermediateField K Ω) :
    fixedFieldOf (fixingSubgroup Γ (L : Set Ω)) = L := by
  -- Transfer the statement for `Gal(Ω/K)` along the surjection `Γ → Gal(Ω/K)`.
  refine .trans (ext fun x ↦ ?_) (fixedField_fixingSubgroup L)
  simp [(toAlgAut_surjective Γ).forall, mem_fixingSubgroup_iff]

/-- Let Γ act as the Galois group of Ω/K, and K ⊆ L ⊆ Ω. A subgroup V of Γ that acts as the
Galois group of Ω/L is the subgroup fixing L pointwise, and its index is [L : K] (both read as 0 if
infinite). -/
lemma eq_fixingSubgroup_of_isProGalois {V : Subgroup Γ} [J : IsProGalois V L Ω] :
    V = fixingSubgroup Γ (Set.range (algebraMap L Ω)) ∧ V.index = finrank K L := by
  obtain ⟨-, h_range, h_index⟩ :=
    isClosedEmbedding_galois_restrict (K := K) (L := L) V.subtype fun _ _ ↦ rfl
  rw [V.range_subtype] at h_range h_index
  exact ⟨h_range, h_index⟩

/-- Galois correspondence: the subgroup of `Γ` fixing the fixed field of a closed subgroup `H`
pointwise is `H`. -/
lemma fixingSubgroup_fixedFieldOf : fixingSubgroup Γ (fixedFieldOf H : Set Ω) = H := by
  -- `H` acts as the Galois group of `Ω` over its fixed field.
  obtain ⟨h_eq, -⟩ := eq_fixingSubgroup_of_isProGalois (K := K) (L := fixedFieldOf H) (V := H)
  have h_range : Set.range (algebraMap (fixedFieldOf H) Ω) = (fixedFieldOf H : Set Ω) :=
    congrArg SetLike.coe (fieldRange_val (fixedFieldOf H))
  rwa [h_range, eq_comm] at h_eq

/-- The fixed field of a closed subgroup `H` has degree the index of `H` (`0` if infinite). -/
lemma finrank_fixedFieldOf : finrank K (fixedFieldOf H) = H.index := by
  obtain ⟨-, h_index⟩ := eq_fixingSubgroup_of_isProGalois (K := K) (L := fixedFieldOf H) (V := H)
  exact h_index.symm

/-- The fixed field of an open subgroup is finite over `K`. -/
instance finiteDimensional_fixedFieldOf : FiniteDimensional K (fixedFieldOf U) := by
  -- The degree is the index of `U`, which is finite and positive since `U` is open.
  have h_index_pos : 0 < U.index := (U.quotient_finite_of_isOpen out).card_pos
  exact .of_finrank_pos <| by rwa [finrank_fixedFieldOf U]

/-- The fixed field of an open subgroup, over a number field `K`, is a number field. -/
instance [NumberField K] : NumberField (fixedFieldOf U) := .of_module_finite K _

end New
