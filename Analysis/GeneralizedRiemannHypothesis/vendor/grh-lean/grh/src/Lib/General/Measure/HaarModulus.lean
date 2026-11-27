import Lib.General.LinearAlgebra.IntegralLattices

/-!
# Pushforward of Haar measures, the modulus of GL_n and the generalised index

This file compares Haar measures under pushforward and computes the factors by which maps scale
them. Mathlib's `distribHaarChar A g` is the factor by which `g` scales Haar measure on the additive
group `A`. For a unit `a`, `New.genIndex a` is the inverse of this factor for multiplication by `a`.
For a pair `R ⊆ A` with `New.IsAdelic R`, the indices of column lattices are expressed through
`genIndex` of determinants.

## Main definitions and results

* `New.measure_smul_map_restrict_eq_smul_inv`: the pushforward under a homomorphism of a
  bi-invariant measure restricted to a set `O`, compared with a left invariant measure on the
  target. The condition on `O` is `New.HasStableLifts`.
* `New.inv_distribHaarChar_eq_relIndex_div`: the inverse of the scaling factor is a ratio of
  relative indices of compact open subgroups.
* `New.genIndex`: the generalised index of `a : R`, for a unit the inverse of the factor by which
  `a` scales Haar measure on `R`, and `0` otherwise. Let `O` be a compact open subring and `a ∈ O`
  a unit of `R`. Then it is the cardinality of `O / a O` (`New.genIndex_eq_card`).
* `New.inv_distribHaarChar_GL_eq_genIndex_det`: `g : GL n R` scales Haar measure on `n → R` as
  `det g` does on `R`, if `R` has a compact open subring with the property `New.IsValuationPair`.
* `New.submoduleIndex_colLattice_div`: the ratio of the two indices between the column lattice of
  an invertible matrix and the standard lattice is `genIndex` of the determinant.
* `New.submoduleIndex_colLattice_intVectors`: if the matrix has entries in `R`, the index of its
  column lattice in the standard lattice is `genIndex` of the determinant.

Notions from other files:
* `New.IsValuationPair O`: any two elements `a`, `b` of the ambient ring are `O`-multiples of
  `(1 - e) a + e b` for some idempotent `e` of the subring `O`.
* `New.IsAdelic R`: the subring `R` of `A` is open, compact, stable under `star` and satisfies
  `New.IsValuationPair`, with further properties that are not used here.
-/

/-!
## Units along non-unital ring maps and invertible matrices from spanning sets

`New.unitsMapNonUnital` maps units along a ring map that need not preserve 1.
`New.exists_GL_col_mem_of_span` picks the columns of an invertible matrix from a spanning set.
-/

section NonUnitalUnits

/-- For a ring homomorphism `f : K → R` that need not preserve `1`, the homomorphism of unit groups
`x ↦ 1 + f (x - 1)`. -/
@[simps! apply_val]
def New.unitsMapNonUnital {K R : Type*} [Ring K] [Ring R] (f : K →ₙ+* R) : Kˣ →* Rˣ :=
  Units.map
    { toFun (x : K) := 1 + f (x - 1)
      map_one' := by simp
      -- with `a = x - 1` and `b = y - 1`: `(1 + f a) (1 + f b) = 1 + f (a + b + a b)`
      map_mul' := by noncomm_ring [← map_mul, ← map_add, implies_true] }

open Matrix Module Basis Submodule

/-- If a set `s` spans `n → K` over a field `K`, then some invertible matrix has all its columns
in `s`. -/
lemma New.exists_GL_col_mem_of_span {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (s : Set (n → K)) (h_span : ⊤ ≤ span K s) :
    ∃ U : GL n K, ∀ i : n, U.val.col i ∈ s := by
  -- take a basis chosen from `s`, reindexed by `n`, as the columns
  let b : Basis n K (n → K) :=
    (ofSpan h_span).reindex (indexEquiv (ofSpan h_span) (Pi.basisFun K n))
  have h_unit : IsUnit (Matrix.of b)ᵀ := linearIndependent_col_iff_isUnit.1 b.linearIndependent
  exact ⟨h_unit.unit, fun i ↦ ofSpan_subset h_span (by simp [b])⟩

end NonUnitalUnits

/-! ## Haar pushforwards and the modulus of a matrix -/

section HaarModulus

open MeasureTheory Measure Set Pointwise ENNReal Function AddSubgroup

namespace New

section Invariant

variable {Z G : Type _} [Group Z] [MeasurableSpace Z] [MeasurableMul Z]

/-- Let `ζ` be a right invariant measure on a group `Z`. If `E` is empty or some right translate of
`E` lies in `K`, then `ζ E ≤ ζ K`. -/
@[to_additive]
lemma measure_le_of_div_mem {ζ : Measure Z} [IsMulRightInvariant ζ] {E K : Set Z}
    (h_transl : ∀ y ∈ E, ∃ g : Z, ∀ z ∈ E, z / g ∈ K) : ζ E ≤ ζ K := by
  obtain rfl | ⟨y, hy⟩ := E.eq_empty_or_nonempty
  · simp
  obtain ⟨g, hg⟩ := h_transl y hy
  calc ζ E ≤ ζ ((fun z : Z ↦ z / g) ⁻¹' K) := measure_mono hg
    _ ≤ ζ K := (measurePreserving_div_right ζ g).measure_preimage_le K

variable [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

/-- Every `h : G` has a preimage `g` under `π` whose left and right translations preserve the
set `O`. -/
@[to_additive HasAddStableLifts /-- Every `h : G` has a preimage `g` under `π` whose left and right
translations preserve the set `O`. -/]
def HasStableLifts (π : Z →* G) (O : Set Z) : Prop :=
  ∀ h : G, ∃ g : Z, π g = h ∧ (∀ x : Z, g * x ∈ O ↔ x ∈ O) ∧ ∀ x : Z, x * g ∈ O ↔ x ∈ O

/-- Let `μ` be a bi-invariant measure on `Z`, `π : Z →* G` measurable, and `O` a measurable set
preserved by the translations by suitable lifts of the elements of `G` (`New.HasStableLifts`). Then
the pushforward of `μ.restrict O` gives every two-sided translate of a measurable set `S` the
measure `μ (π ⁻¹' S ∩ O)`. -/
@[to_additive]
lemma map_restrict_apply_preimage_mul_mul (μ : Measure Z) [μ.IsMulLeftInvariant]
    [μ.IsMulRightInvariant] {π : Z →* G} (hπ : Measurable π) {O : Set Z} (hO : MeasurableSet O)
    (h_lift : HasStableLifts π O) (a b : G) {S : Set G} (hS : MeasurableSet S) :
    (μ.restrict O).map π ((fun x : G ↦ a * x * b) ⁻¹' S) = μ (π ⁻¹' S ∩ O) := by
  -- Translate by lifts `g` of `a` and `g'` of `b`, which preserve `O` and `μ`.
  obtain ⟨g, rfl, hg_left, -⟩ := h_lift a
  obtain ⟨g', rfl, -, hg'_right⟩ := h_lift b
  have h_set : π ⁻¹' ((fun x : G ↦ π g * x * π g') ⁻¹' S) ∩ O =
      (fun z : Z ↦ g * z) ⁻¹' ((fun z : Z ↦ z * g') ⁻¹' (π ⁻¹' S ∩ O)) := by
    ext z
    simp [hg_left, hg'_right]
  rw [map_apply hπ (by measurability), restrict_apply' hO, h_set, measure_preimage_mul,
    measure_preimage_mul_right]

/-- Let `μ` be a bi-invariant measure on `Z`, `π : Z →* G` measurable, and `O` a measurable set
with `New.HasStableLifts π O`. Then the pushforward of `μ.restrict O` is left invariant. -/
@[to_additive]
lemma isMulLeftInvariant_map_restrict (μ : Measure Z) [μ.IsMulLeftInvariant]
    [μ.IsMulRightInvariant] {π : Z →* G} (hπ : Measurable π) {O : Set Z} (hO : MeasurableSet O)
    (h_lift : HasStableLifts π O) : ((μ.restrict O).map π).IsMulLeftInvariant := by
  refine (forall_measure_preimage_mul_iff _).1 fun a S hS ↦ ?_
  rw [map_apply hπ hS, restrict_apply' hO]
  simpa using map_restrict_apply_preimage_mul_mul μ hπ hO h_lift a 1 hS

variable [MeasurableInv G]

/-- Let `μ` be an s-finite bi-invariant measure on `Z`, `η` an s-finite left invariant measure on
`G`, `π : Z →* G` measurable, `O` a measurable set with `New.HasStableLifts π O`, and `K`
measurable in `G`. Then `η K` times the pushforward of `μ.restrict O` equals `μ (π ⁻¹' K ∩ O)`
times `η.inv`, the image of `η` under inversion. -/
@[to_additive measure_smul_map_restrict_eq_smul_neg]
lemma measure_smul_map_restrict_eq_smul_inv (μ : Measure Z) [SFinite μ] [μ.IsMulLeftInvariant]
    [μ.IsMulRightInvariant] (η : Measure G) [SFinite η] [η.IsMulLeftInvariant] {π : Z →* G}
    (hπ : Measurable π) {O : Set Z} (hO : MeasurableSet O) (h_lift : HasStableLifts π O)
    {K : Set G} (hK : MeasurableSet K) :
    η K • (μ.restrict O).map π = μ (π ⁻¹' K ∩ O) • η.inv := by
  -- The pushforward `ν` is left invariant and gives all right translates of `K` the same measure.
  set ν : Measure G := (μ.restrict O).map π
  have h_left : ν.IsMulLeftInvariant := isMulLeftInvariant_map_restrict μ hπ hO h_lift
  have h_right (x : G) : ν ((fun z : G ↦ z * x) ⁻¹' K) = μ (π ⁻¹' K ∩ O) := by
    simpa using map_restrict_apply_preimage_mul_mul μ hπ hO h_lift 1 x hK
  refine ext_of_lintegral _ fun f hf ↦ ?_
  have h_int : η K * ∫⁻ y, f y ∂ν = ∫⁻ x, ν ((fun z : G ↦ z * x) ⁻¹' K) * f x⁻¹ ∂η :=
    measure_mul_lintegral_eq η ν hK f hf
  simpa (disch := fun_prop) [Measure.inv, lintegral_map, h_right] using h_int

/-- Let `μ` be an s-finite bi-invariant measure on `Z`, `η` an s-finite left invariant measure on
`G`, `π : Z →* G` measurable, `O` a measurable set with `New.HasStableLifts π O`, and `K`
measurable in `G`. Then `μ (π ⁻¹' K ∩ O)` times `η.inv`, the image of `η` under inversion, is left
invariant. -/
@[to_additive isAddLeftInvariant_measure_smul_neg]
lemma isMulLeftInvariant_measure_smul_inv (μ : Measure Z) [SFinite μ] [μ.IsMulLeftInvariant]
    [μ.IsMulRightInvariant] (η : Measure G) [SFinite η] [η.IsMulLeftInvariant] {π : Z →* G}
    (hπ : Measurable π) {O : Set Z} (hO : MeasurableSet O) (h_lift : HasStableLifts π O)
    {K : Set G} (hK : MeasurableSet K) :
    (μ (π ⁻¹' K ∩ O) • η.inv).IsMulLeftInvariant := by
  rw [← measure_smul_map_restrict_eq_smul_inv μ η hπ hO h_lift hK]
  have := isMulLeftInvariant_map_restrict μ hπ hO h_lift
  infer_instance

/-- Let `μ` be an s-finite bi-invariant measure on `Z`, `η` an s-finite left invariant measure on
`G`, `π : Z →* G` measurable, `K` measurable in `G`, and `O` a measurable set such that every
element of `G` has a preimage under `π` whose translations preserve `O` (`New.HasStableLifts`).
Then `η K` times the pushforward of `μ.restrict O` equals `μ (π ⁻¹' K ∩ O)` times `η.inv`, the
image of `η` under inversion, and this measure is left invariant. -/
@[to_additive]
lemma map_restrict_haar_eq (μ : Measure Z) [SFinite μ] [μ.IsMulLeftInvariant]
    [μ.IsMulRightInvariant] (η : Measure G) [SFinite η] [η.IsMulLeftInvariant] {π : Z →* G}
    (hπ : Measurable π) {O : Set Z} (hO : MeasurableSet O) (h_lift : HasStableLifts π O)
    {K : Set G} (hK : MeasurableSet K) :
    η K • (μ.restrict O).map π = μ (π ⁻¹' K ∩ O) • η.inv ∧
      (μ (π ⁻¹' K ∩ O) • η.inv).IsMulLeftInvariant :=
  ⟨measure_smul_map_restrict_eq_smul_inv μ η hπ hO h_lift hK,
    isMulLeftInvariant_measure_smul_inv μ η hπ hO h_lift hK⟩

end Invariant

section ScalingFactor

variable {A B G : Type _} [Group G] [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [LocallyCompactSpace A] [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DistribMulAction G A] [ContinuousConstSMul G A] [PolishSpace A]

/-- Let `G` act by continuous additive automorphisms on a locally compact Polish abelian group `A`,
and let `L` be a compact open subgroup. Then the inverse of `distribHaarChar A g`, the factor by
which `g` scales Haar measure, is `[L : gL ∩ L] / [gL : gL ∩ L]`. -/
lemma inv_distribHaarChar_eq_relIndex_div (L : AddSubgroup A) (hL_open : IsOpen (L : Set A))
    (hL_compact : IsCompact (L : Set A)) (g : G) :
    (distribHaarChar A g : ℝ)⁻¹ = ((g • L).relIndex L : ℝ) / (L.relIndex (g • L) : ℝ) := by
  borelize A
  -- The measure of `g • L ∩ L`, times its index in `L` or in `g • L`, is the measure of that
  -- group, and `g • L` has `distribHaarChar A g` times the measure of `L`.
  have h_index {H K : AddSubgroup A} (hK : IsCompact (K : Set A)) (hH : IsOpen (H : Set A)) :
      H.relIndex K * (addHaar ((H : Set A) ∩ K)).toReal = (addHaar (K : Set A)).toReal := by
    simpa using congrArg ENNReal.toReal (relIndex_add_measure_inf hK hH addHaar)
  have h_L : (g • L).relIndex L * (addHaar (g • (L : Set A) ∩ L)).toReal =
      (addHaar (L : Set A)).toReal := h_index hL_compact (hL_open.smul g)
  have h_gL : L.relIndex (g • L) * (addHaar (g • (L : Set A) ∩ L)).toReal =
      distribHaarChar A g * (addHaar (L : Set A)).toReal := by
    simpa [← distribHaarChar_mul, inter_comm] using h_index (K := g • L) (hL_compact.smul g) hL_open
  have h_pos : 0 < (addHaar (L : Set A)).toReal :=
    toReal_pos (hL_open.measure_ne_zero addHaar ⟨0, L.zero_mem⟩) hL_compact.measure_ne_top
  -- Divide `h_L` by `h_gL`: the measures cancel.
  rw [← mul_div_mul_right _ _ (right_ne_zero_of_mul (h_L.trans_ne h_pos.ne')), h_L, h_gL, mul_comm,
    div_mul_cancel_left₀ h_pos.ne']

variable [MeasurableSpace B] [BorelSpace B] [MeasurableSpace A] [BorelSpace A]

/-- Let `e : B → A` be an isomorphism of topological groups, with `A` Polish, locally compact and
abelian, and let `e ∘ φ = ψ ∘ e` with `ψ` measurable. If `ψ` pushes a Haar measure `ν` on `A` to
`c • ν`, then `φ` pushes every Haar measure `μ` on `B` to `c • μ`. -/
lemma map_addHaar_eq_smul_of_semiconj (μ : Measure B) [μ.IsAddHaarMeasure] {ν : Measure A}
    [ν.IsAddHaarMeasure] (e : B ≃ₜ+ A) {ψ : A → A} {φ : B → B}
    (h_semiconj : ∀ x : B, e (φ x) = ψ (e x)) (hψ : Measurable ψ) {c : ℝ≥0∞}
    (hν : ν.map ψ = c • ν) : μ.map φ = c • μ := by
  -- By uniqueness of Haar measure `μ.map e` is a multiple of `ν`; transport along `e.symm`.
  have h_unique : μ.map e = (μ.map e).addHaarScalarFactor ν • ν := isAddLeftInvariant_eq_smul _ _
  have h_map : (μ.map e).map ψ = c • μ.map e := by
    rw [h_unique, smul_comm c, ← hν]
    simp (disch := fun_prop) only [Measure.map_smul]
  have hφ : φ = e.symm ∘ ψ ∘ e := funext fun x ↦ by simp [← h_semiconj]
  calc μ.map φ = ((μ.map e).map ψ).map e.symm := by
        rw [hφ, Measure.map_map hψ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    _ = c • (μ.map e).map e.symm := by simp (disch := fun_prop) only [h_map, Measure.map_smul]
    _ = c • μ := by simp (disch := fun_prop) [Measure.map_map, comp_def]

/-- The action of `a : G` pushes a Haar measure `ν` on `A` forward to `ν` divided by
`distribHaarChar A a`, the factor by which `a` scales Haar measure. -/
lemma map_const_smul_eq_inv_distribHaarChar_smul {ν : Measure A} [ν.IsAddHaarMeasure] (a : G) :
    ν.map (fun x : A ↦ a • x) = (distribHaarChar A a)⁻¹ • ν := by
  ext S hS
  rw [map_apply (measurable_const_smul a) hS, preimage_smul, ← distribHaarChar_mul]
  simp

/-- `map_const_smul_eq_inv_distribHaarChar_smul` with the scalar written as `ENNReal.ofReal` of a
real number: `a : G` pushes a Haar measure `ν` on `A` forward to `ν` divided by
`distribHaarChar A a`, the factor by which `a` scales Haar measure. -/
lemma map_smul_eq_inv_distribHaarChar_smul {ν : Measure A} [ν.IsAddHaarMeasure] (a : G) :
    ν.map (fun x : A ↦ a • x) = ENNReal.ofReal (distribHaarChar A a : ℝ)⁻¹ • ν := by
  rw [map_const_smul_eq_inv_distribHaarChar_smul, ← NNReal.coe_inv, ofReal_coe_nnreal,
    ENNReal.smul_def]

end ScalingFactor

variable {n R : Type _} [Fintype n] [DecidableEq n] [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R] [LocallyCompactSpace R]

/-- The action of invertible matrices on vectors is jointly continuous. -/
instance : ContinuousSMul (GL n R) (n → R) where
  continuous_smul := by
    -- unfold the action to multiplication of a matrix by a vector
    unfold_projs
    fun_prop

/-- Each invertible matrix acts continuously on vectors. -/
instance : ContinuousConstSMul (GL n R) (n → R) := inferInstance

/-- The generalised index of `a : R`, as a real number. For a unit `a` it is the inverse of the
factor by which multiplication by `a` scales Haar measure on `R`; for a non-unit it is `0`. -/
noncomputable def genIndex : MulChar R ℝ :=
  MulChar.ofUnitHom (NNReal.toRealHom.toMonoidHom.comp (distribHaarChar R)).toHomUnits⁻¹

lemma genIndex_eq_inv_distribHaarChar (a : Rˣ) :
    genIndex (a : R) = (distribHaarChar R a : ℝ)⁻¹ := by simp [genIndex]

lemma genIndex_pos (a : Rˣ) : 0 < genIndex (a : R) := by simp [genIndex, distribHaarChar_pos]

/-- Let `L` be a compact open additive subgroup of `R` and `u` a unit. The generalised index
`genIndex u` is the quotient of indices `[L : uL ∩ L] / [uL : uL ∩ L]`. -/
lemma genIndex_eq_relIndex_div [PolishSpace R] (L : AddSubgroup R) (hL_open : IsOpen (L : Set R))
    (hL_compact : IsCompact (L : Set R)) (u : Rˣ) :
    genIndex (u : R) = ((u • L).relIndex L : ℝ) / (L.relIndex (u • L) : ℝ) := by
  exact (genIndex_eq_inv_distribHaarChar u).trans
    (inv_distribHaarChar_eq_relIndex_div L hL_open hL_compact u)

/-! ### The generalised index for a compact open subring -/

variable [PolishSpace R] {O : Subring R}

/-- Let `O` be a compact open subring of `R`. For `a ∈ O` that is a unit of `R`, the generalised
index `genIndex a` (the inverse of the factor by which `a` scales Haar measure on `R`) equals the
cardinality of the quotient ring of `O` by `a O`. -/
lemma genIndex_eq_card (hO_open : IsOpen (O : Set R)) (hO_compact : IsCompact (O : Set R))
    {a : R} (ha : a ∈ O) (h_unit : IsUnit a) :
    genIndex a = Nat.card (O ⧸ Ideal.span {(⟨a, ha⟩ : O)}) := by
  -- By `genIndex_eq_relIndex_div` the left side is `[O : a O ∩ O] / [a O : a O ∩ O]`.
  -- Since `a O ⊆ O`, the denominator is `1` and the numerator is the index of the ideal `(a)`.
  obtain ⟨u, rfl⟩ : ∃ u : Rˣ, u = a := h_unit
  let L : AddSubgroup R := O.toAddSubgroup
  have h_le : u • L ≤ L := by
    rintro _ ⟨r, hr, rfl⟩
    exact O.mul_mem ha hr
  have h_span : (Ideal.span {(⟨u, ha⟩ : O)}).toAddSubgroup = (u • L).addSubgroupOf L := by
    ext ⟨x, hx⟩
    suffices (∃ r ∈ O, r * u = x) ↔ ∃ r ∈ O, u * r = x by
      simpa [L, Ideal.mem_span_singleton', mem_addSubgroupOf, mem_smul_pointwise_iff_exists,
        Subtype.ext_iff, Units.smul_def]
    simp only [mul_comm]
  rw [genIndex_eq_relIndex_div L hO_open hO_compact u, relIndex_eq_one.2 h_le, Nat.cast_one,
    div_one, relIndex, ← h_span]
  exact congrArg _ (index_eq_card _)

/-- Let `O` be a compact open subring of `R`. If `V` lies in `intGL n O`, that is, `V` and its
inverse have entries in `O`, then the generalised index `genIndex (det V)` (the inverse of the
factor by which `det V` scales Haar measure on `R`) is `1`. -/
lemma genIndex_det_eq_one (hO_open : IsOpen (O : Set R)) (hO_compact : IsCompact (O : Set R))
    {V : GL n R} (hV : V ∈ intGL n O) : genIndex V.val.det = 1 := by
  obtain ⟨U, rfl⟩ := hV
  -- the determinant is the image of the unit `det U` of `O`, which generates the unit ideal
  have h_det : (Matrix.GeneralLinearGroup.map O.subtype U).val.det = (U.val.det : O) :=
    (O.subtype.map_det U.val).symm
  rw [h_det, genIndex_eq_card hO_open hO_compact U.val.det.prop (U.det.isUnit.map O.subtype)]
  simp [Nat.card_unique]

/-- Let `O` be a compact open subring of `R`. A matrix `k` that has, like its inverse, entries in
`O` preserves Haar measure on `n → R`. -/
lemma distribHaarChar_eq_one_of_mem_intGL (hO_open : IsOpen (O : Set R))
    (hO_compact : IsCompact (O : Set R)) {k : GL n R} (hk : k ∈ intGL n O) :
    distribHaarChar (n → R) k = 1 := by
  -- `k` preserves the compact open subgroup `L` of vectors with entries in `O`, so both indices
  -- in `inv_distribHaarChar_eq_relIndex_div` are `1`.
  let L : AddSubgroup (n → R) := (intVectors O n).toAddSubgroup
  have h_stab : k⁻¹ • L = L :=
    AddSubgroup.ext fun v ↦ mem_inv_pointwise_smul_iff.trans (mulVec_mem_intVectors_iff hk)
  have h_div : (distribHaarChar (n → R) k⁻¹ : ℝ)⁻¹ = (k⁻¹ • L).relIndex L / L.relIndex (k⁻¹ • L) :=
    inv_distribHaarChar_eq_relIndex_div L (isOpen_intVectors hO_open)
      (isCompact_pi_infinite fun _ ↦ hO_compact) k⁻¹
  simpa [h_stab] using h_div

/-- The diagonal matrix `diagGL d` with unit entries `d i` scales Haar measure on `n → R` by the
product of the factors by which the `d i` scale Haar measure on `R`. -/
lemma distribHaarChar_diagGL (d : n → Rˣ) :
    distribHaarChar (n → R) (diagGL d) = ∏ i : n, distribHaarChar R (d i) := by
  borelize R
  obtain ⟨C⟩ : Nonempty (TopologicalSpace.PositiveCompacts R) := inferInstance
  -- A diagonal matrix maps the box `B = C ^ n` to the product of the `d i • C`.
  let B : Set (n → R) := univ.pi fun _ : n ↦ (C : Set R)
  have h_box : diagGL d • B = univ.pi fun i : n ↦ d i • (C : Set R) :=
    (image_congr' fun x ↦ funext (Matrix.mulVec_diagonal _ x)).trans (piMap_image_univ_pi _ _)
  -- Compare measures, for the product of the Haar measures that give `C` measure `1`.
  let μ : Measure (n → R) := Measure.pi fun _ : n ↦ addHaarMeasure C
  have h_left : μ (diagGL d • B) = distribHaarChar (n → R) (diagGL d) := by
    simp [μ, B, ← distribHaarChar_mul, addHaarMeasure_self]
  have h_right : μ (univ.pi fun i : n ↦ d i • (C : Set R)) =
      (∏ i : n, distribHaarChar R (d i) : NNReal) := by
    simp [μ, ← distribHaarChar_mul, addHaarMeasure_self]
  rw [← coe_inj, ← h_left, h_box, h_right]

/-- Let `R` be a locally compact Polish commutative ring with a compact open subring `O` satisfying
`New.IsValuationPair` (any `a b : R` are `O`-multiples of `(1 - e) a + e b` for an idempotent `e`
of `O`). Then `g : GL n R` scales Haar measure on `n → R` by the same factor as
`det g` scales Haar measure on `R`; the inverse of the latter factor is `genIndex (det g)`. -/
lemma inv_distribHaarChar_GL_eq_genIndex_det (hO_open : IsOpen (O : Set R))
    (hO_compact : IsCompact (O : Set R)) (hO_val : IsValuationPair O) (g : GL n R) :
    (distribHaarChar (n → R) g : ℝ)⁻¹ = genIndex g.val.det := by
  -- By Smith normal form `g = k * diagonal d * k'` with `k`, `k'` in `intGL n O`; both sides
  -- are multiplicative, trivial on `intGL n O`, and equal on diagonal matrices.
  obtain ⟨k, hk, k', hk', d, hg⟩ := hO_val.smith_normal_form g.val
  lift d to n → Rˣ using by simpa [hg] using g.det.isUnit
  obtain rfl : g = k * diagGL d * k' := Units.ext hg
  have h_left : distribHaarChar (n → R) (k * diagGL d * k') = ∏ i : n, distribHaarChar R (d i) := by
    simp [distribHaarChar_eq_one_of_mem_intGL hO_open hO_compact, hk, hk', distribHaarChar_diagGL]
  have h_right : genIndex (k * diagGL d * k').val.det = ∏ i : n, genIndex (d i : R) := by
    simp [hg, genIndex_det_eq_one hO_open hO_compact, hk, hk']
  rw [h_left, h_right]
  simp [genIndex_eq_inv_distribHaarChar]

end New

end HaarModulus

/-!
## Integral matrices, the generalised index and indices of lattices

`New.genIndex a = [R : R ∩ a R] / [a R : R ∩ a R]` for a unit `a` of `A` and a pair `R ⊆ A` with
`New.IsAdelic R`.
`New.colLattice R M` is the `R`-span of the columns of `M`. `New.submoduleIndex L L'` is the index
of `L ⊓ L'` in `L'` (`0` if infinite). `New.IsIntMatrix R M` says that `M` has entries in `R`.

* `New.one_le_genIndex`, `New.genIndex_star`: the index is at least `1` on elements of `R` that are
  units of `A`, and it is invariant under `star`.
-/

section GeneralisedIndex

open Units AddSubgroup
open scoped Pointwise

namespace New

variable {A : Type*} [CommRing A] {R : Subring A} {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Integral matrices -/

lemma IsIntMatrix.det_mem {M : Matrix n n A} (hM : IsIntMatrix R M) : M.det ∈ R := by
  let N : Matrix n n R := fun i j ↦ ⟨M i j, hM i j⟩
  have h_det : N.det = M.det := R.subtype.map_det N
  simp [← h_det]

lemma IsIntMatrix.adjugate {M : Matrix n n A} (hM : IsIntMatrix R M) :
    IsIntMatrix R M.adjugate := by
  let N : Matrix n n R := fun i j ↦ ⟨M i j, hM i j⟩
  have h_adj : N.adjugate.map R.subtype = M.adjugate := R.subtype.map_adjugate N
  simp [← h_adj, IsIntMatrix]

/-! ### The generalised index for an adelic pair -/

variable [StarRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
  [PolishSpace A]

/-- Let `R ⊆ A` satisfy `New.IsAdelic`, so that `R` is compact and open. The generalised index
`genIndex u` (the inverse of the factor by which `u` scales Haar measure on `A`) is at least `1` if
`u ∈ R` is a unit of `A`. -/
lemma one_le_genIndex [hR : IsAdelic R] {u : A} (hu : u ∈ R) (h_unit : IsUnit u) :
    1 ≤ genIndex u := by
  obtain ⟨h_open, h_compact⟩ := hR.isOpen_isCompact
  have h_pos : 0 < genIndex u := genIndex_pos h_unit.unit
  -- `genIndex u` is the cardinality of `R ⧸ u R`, so it is a positive natural number
  rw [genIndex_eq_card h_open h_compact hu h_unit] at h_pos ⊢
  exact_mod_cast h_pos

/-- Let `R ⊆ A` satisfy `New.IsAdelic`, so that `R` is compact, open and stable under `star`. Then
the generalised index `genIndex a` (the inverse of the factor by which `a` scales Haar measure on
`A`, and `0` for a non-unit) is invariant under `star`. -/
@[simp]
lemma genIndex_star [hR : IsAdelic R] (a : A) : genIndex (star a) = genIndex a := by
  obtain h_nonunit | ⟨a, rfl⟩ := em' (IsUnit a)
  · simp [genIndex.map_nonunit, h_nonunit]
  obtain ⟨h_open, h_compact⟩ := hR.isOpen_isCompact
  let L : AddSubgroup A := R.toAddSubgroup
  -- conjugation maps `star b • R` to `b • R`, and in particular fixes `R`
  let σ : RingAut A := starRingAut
  have h_map (b : Aˣ) : σ • star b • L = b • L := by
    ext x
    suffices (∃ r ∈ R, b * star r = x) ↔ ∃ r ∈ R, b * r = x by
      simpa [L, σ, mem_smul_pointwise_iff_exists, Units.smul_def]
    exact ⟨fun ⟨r, hr, h_eq⟩ ↦ ⟨star r, hR.star_mem hr, h_eq⟩,
      fun ⟨r, hr, h_eq⟩ ↦ ⟨star r, hR.star_mem hr, by rwa [star_star]⟩⟩
  have h_fix : σ • L = L := by simpa using h_map 1
  -- on units `genIndex` is a quotient of two indices, which conjugation preserves
  have h_num : (star a • L).relIndex L = (a • L).relIndex L := by
    rw [← relIndex_pointwise_smul σ, h_map, h_fix]
  have h_den : L.relIndex (star a • L) = L.relIndex (a • L) := by
    rw [← relIndex_pointwise_smul σ, h_map, h_fix]
  simp only [← coe_star, genIndex_eq_relIndex_div L h_open h_compact, h_num, h_den]

/-! ### Indices of lattices -/

omit [StarRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
  [PolishSpace A] in
/-- The lattice `colLattice R M` spanned by the columns of an invertible matrix `M` is the image
under `M` of the lattice `intVectors R n` of vectors with entries in `R`. -/
lemma toAddSubgroup_colLattice (M : GL n A) :
    (colLattice R M.val).toAddSubgroup = M • (intVectors R n).toAddSubgroup := rfl

/-- Let `R ⊆ A` satisfy `New.IsAdelic`, so that `R` is compact and open, and let `M` be invertible
over `A`. Let `L = colLattice R M` be the `R`-span of the columns of `M` and `L₀ = intVectors R n`
the lattice of vectors with entries in `R`. Then the quotient of the indices
`submoduleIndex L L₀ = [L₀ : L ∩ L₀]` and `submoduleIndex L₀ L = [L : L ∩ L₀]` is
`genIndex (det M)`, the inverse of the factor by which `det M` scales Haar measure on `A`. -/
lemma submoduleIndex_colLattice_div [hR : IsAdelic R] {M : GL n A} :
    (submoduleIndex (colLattice R M.val) (intVectors R n) : ℝ) /
        (submoduleIndex (intVectors R n) (colLattice R M.val) : ℝ) =
      genIndex M.val.det := by
  obtain ⟨h_open, h_compact⟩ := hR.isOpen_isCompact
  rw [submoduleIndex, submoduleIndex, toAddSubgroup_colLattice,
    ← inv_distribHaarChar_GL_eq_genIndex_det h_open h_compact hR.isValuationPair]
  exact (inv_distribHaarChar_eq_relIndex_div (intVectors R n).toAddSubgroup
    (isOpen_intVectors h_open) (isCompact_pi_infinite fun _ ↦ h_compact) M).symm

/-- Let `R ⊆ A` satisfy `New.IsAdelic`, so that `R` is compact and open. The `R`-span
`colLattice R M` of the columns of an invertible matrix `M` with entries in `R` has index
`genIndex (det M)` (the inverse of the factor by which `det M` scales Haar measure on `A`) in the
lattice `intVectors R n` of vectors with entries in `R`. -/
lemma submoduleIndex_colLattice_intVectors [hR : IsAdelic R] {M : GL n A}
    (hM : IsIntMatrix R M.val) :
    submoduleIndex (colLattice R M.val) (intVectors R n) = genIndex M.val.det := by
  -- the columns are integral, so `colLattice R M ≤ intVectors R n` and the denominator is `1`
  have h_one : submoduleIndex (intVectors R n) (colLattice R M.val) = 1 :=
    relIndex_eq_one.mpr (colLattice_le fun j i ↦ hM i j)
  rw [← submoduleIndex_colLattice_div, h_one, Nat.cast_one, div_one]

end New

end GeneralisedIndex
