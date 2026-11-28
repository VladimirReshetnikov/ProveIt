import Lib.Shimura.CongruenceRelation.KernelReduction
import Lib.Shimura.IntegralModel.UniversalFamily

/-!
# Hecke elements on adelic torsion and reductions of Frobenius twists of Hecke neighbours

Fix a split place `w` of the CM field `E` and a subspace `C` of `(𝓞 / w)ⁿ`, and let `q` be the order
of the residue field. This file describes how the Hecke element `New.Variety.invHeckeIsogeny w C`
acts on the torsion module `New.AdelicTorsion E n`, which is `(𝔸_f / Ô)ⁿ`. These computations are
combined with Frobenius-twisted reductions of linear maps to prove
`New.Variety.UniversalFamily.exists_ne_bot_factorsThrough_sup`. This result is the geometric step
behind the congruence relation at `w`.

## Main definitions and results

* `New.Variety.exists_residue_torsion_emb`: the `w`-torsion is `(𝓞 / w)ⁿ`, compatibly with integral
  matrices.
* `New.Variety.frobeniusTwist`: the absolute Frobenius of a `k`-scheme, as a map between its two
  structures over `V`.
* `New.Variety.IsTwistedReduction`: a map between reductions is the reduction of a map `ψ` twisted
  by a Frobenius.
* `New.Variety.IsTwistedReduction.exists_comp_eq_smul`: a multiple of one twisted reduction factors
  through another.

Notions from other files:
* `New.Variety.invHeckeIsogeny`: For a subspace U of k_wⁿ of dimension r, the product of a central
  factor, the conjugate of N(ϖ_w)^(−r) with N the norm from E to ℚ(√−d₀), and a unitary local
  factor, which is (`New.basicCosetRep` U)⁻¹ at w and 1 away from w and w̄.
* `New.basicCosetRep`: For a subspace U of k_wⁿ of dimension r, a matrix in the double coset of
  diag(ϖ 1_r, 1) in GL_n(E_w) whose reduction modulo w has kernel U.
* `New.Variety.SplitFinPlace`: The finite places w of E with w̄ ≠ w, that is, those split over the
  maximal real subfield.
* `New.Variety.IsSafe`: The place u of ℚ(√−d₀) below w contains some (1 + √−d₀)/2 − b coprime to its
  conjugate (so u is split), and the level 𝔑 lies neither in w nor in a place above ū.

## Relation to the literature

Known result: Pointwise step of the Eichler–Shimura congruence relation for GU(1,n−1) at a split
place. Only the geometric step is treated here, and it uses no ordinary locus. At each geometric
point of the special fibre, the Frobenius-twisted Hecke neighbour of a subspace depends only on its
sum with one fixed non-zero subspace. Source: Wedhorn, Congruence relations on some Shimura
varieties, J. reine angew. Math. 524 (2000) 43–71; the method follows Katz–Mazur 1985 ch. 13 and
Harris–Taylor 2001 III.4.
-/

/-! ## The w-torsion and the action of Hecke elements on adelic torsion -/

namespace New.Variety

open NumberField Matrix IsDedekindDomain HeightOneSpectrum Submodule Nat Set QuadField
  GeneralLinearGroup

section

variable {E n : Type} [Field E] [NumberField E] [Fintype n]

/-- The `w`-torsion of `(𝔸_f / Ô)ⁿ` is a copy of `(𝓞 / w)ⁿ`, and an integral matrix kills a
torsion point exactly when its reduction modulo `w` kills the corresponding vector. -/
lemma exists_residue_torsion_emb (w : HeightOneSpectrum (𝓞 E)) :
    ∃ ρ : (n → ResField w) →ₗ[𝓞 E] AdelicTorsion E n,
      -- (a) `ρ` is injective with image the `w`-torsion
      (⇑ρ).Injective ∧
      ρ.range = Submodule.torsionBySet (𝓞 E) (AdelicTorsion E n) w.asIdeal ∧
      -- (b) integral matrices kill `ρ x` exactly when their reduction kills `x`
      ∀ x : n → ResField w, ∃ v : n → 𝔸f E,
        ρ x = torsionClass v ∧
        ∀ g : Matrix n n (Ô E),
          torsionClass (g.map (fun a : Ô E ↦ a.val) *ᵥ v) = 0 ↔
            x ∈ residueKer (g.map (fun a : Ô E ↦ a.val w)) := by
  -- Let `ϖ` be the uniformiser at `w`. The map `f : c ↦ torsionClass (ϖ⁻¹ c)` on `𝓞ⁿ` (component
  -- at `w` only) has the same kernel as reduction `p` modulo `w`, so it factors through an
  -- injection `ρ` of `(𝓞 / w)ⁿ`.
  have h_class_eq_zero_iff (x : n → Ô E) :
      torsionClass (fun i ↦ singleAdele w (uniformizer w).val⁻¹ * (x i).val) = 0 ↔
        (fun i ↦ reduceAt w (x i)) = 0 := by
    simp_all [funext_iff, mem_Ô, ← and_forall_ne w, ← v_uniformizer_inv_mul_le_one_iff]
  let p : (n → 𝓞 E) →ₗ[𝓞 E] n → ResField w := (Algebra.linearMap (𝓞 E) (ResField w)).compLeft n
  let f : (n → 𝓞 E) →ₗ[𝓞 E] AdelicTorsion E n :=
    torsionClass ∘ₗ (singleAdele w (uniformizer w)⁻¹ • (Algebra.linearMap (𝓞 E) (𝔸f E)).compLeft n)
  have h_ker : f.ker = p.ker := ext fun c ↦ h_class_eq_zero_iff (algebraMap _ _ ∘ c)
  have hp : (⇑p).Surjective := (algebraMap_ResField_surjective w).comp_left
  let ρ : (n → ResField w) →ₗ[𝓞 E] AdelicTorsion E n :=
    p.ker.liftQ f h_ker.ge ∘ₗ (p.quotKerEquivOfSurjective hp).symm.toLinearMap
  have h_inj : (⇑ρ).Injective :=
    ρ.ker_eq_bot.mp (by simp [ρ, LinearMap.ker_comp, ker_liftQ, h_ker])
  have hρ (c : n → 𝓞 E) : ρ (p c) = f c := by simp [ρ]
  refine ⟨ρ, h_inj, ?_, hp.forall.mpr fun c ↦
    ⟨(singleAdele w (uniformizer w)⁻¹ • (Algebra.linearMap (𝓞 E) (𝔸f E)).compLeft n) c, hρ c,
      fun g ↦ ?_⟩⟩
  · -- The image is killed by `w` and has as many elements as the `w`-torsion.
    have h_card : Nat.card (torsionBySet (𝓞 E) (AdelicTorsion E n) w.asIdeal) =
        Nat.card (n → ResField w) := by
      rw [card_torsionBySet_adelicTorsion w.ne_bot, card_fun, card_ResField, card_eq_fintype_card]
    have h_le : ρ.range ≤ torsionBySet (𝓞 E) (AdelicTorsion E n) w.asIdeal := by
      simp +contextual [IsConcreteLE.le_iff, ← map_smul, funext_iff, Algebra.smul_def, h_inj,
        algebraMap_ResField_eq_zero]
    exact SetLike.ext' (Finite.eq_of_subset_of_card_le
      (finite_of_card_ne_zero (h_card.trans_gt card_pos).ne') h_le
      (h_card.trans (card_range_of_injective h_inj).symm).le)
  · -- `using!`: after simp the two sides differ only by unfolding `algebraMap` through `E` and
    -- `reduceAt`, which plain `using` does not do.
    simpa [mulVec_smul, funext_iff, mulVec_apply_eq_sum, residueOrZero, mem_Ô.1] using!
      h_class_eq_zero_iff (g *ᵥ algebraMap _ _ ∘ c)

end

variable {E n : Type} [Field E] [CMBase E] [Fintype n] [DecidableEq n] {D : PEL E} {d₀ : ℕ}
  [HasQuadSubfield d₀ E] {v : n → 𝔸f E} {w : SplitFinPlace E}
  {C : Submodule (ResField w.val) (n → ResField w.val)}

omit [Fintype n] [DecidableEq n] in
/-- An integer `a` of `E` kills the class of `v` in `(𝔸_f / Ô)ⁿ` exactly when
`|a|_u · |v i|_u ≤ 1` for every coordinate `i` and every finite place `u`. -/
lemma smul_torsionClass_eq_zero_iff {a : 𝓞 E} :
    a • torsionClass v = 0 ↔
      ∀ (i : n) (u : HeightOneSpectrum (𝓞 E)), u.intValuation a * Valued.v (v i u) ≤ 1 := by
  rw [← map_smul, torsionClass_eq_zero]
  have h_component (u : HeightOneSpectrum (𝓞 E)) :
      (algebraMap (𝓞 E) (𝔸f E) a) u = algebraMap E (LocField u) (a : E) := rfl
  simp [mem_Ô, Algebra.smul_def, ← v_algebraMap_eq_intValuation, h_component]

/-- If `w` is safe for `I`, then at `w` the inverse of the Hecke element `invHeckeIsogeny w C` is
the matrix `basicCosetRep C`. -/
lemma invHeckeIsogeny_inv_at_eq_basicCosetRep {I : 𝓞 E} (hw : IsSafe I w.val) :
    (invHeckeIsogeny w C)⁻¹.val.map (evalAt w.val) = (basicCosetRep C).val := by
  -- The place below `w` is split, so the central factor is trivial at `w`; the local factor at
  -- `w` is the inverse transpose of the transpose of `basicCosetRep C`, that is its inverse.
  obtain ⟨h_split_disc, -, -⟩ := hw
  obtain ⟨h_isSplit, -⟩ := h_split_disc.isSplit_and_prime_q
  rw [← val_map_apply, invHeckeIsogeny, map_inv, map_mul, map_inv, map_pow, map_inv, map_pow,
    evalAt_centralScalar_of_ne h_isSplit.symm]
  simp [invTransposeGL, transposeGL]

/-- The inverse Hecke element acts trivially at the places other than `w` that do not lie above the
conjugate of the place below `w`. -/
lemma invHeckeIsogeny_inv_mulVec_of_ne {u : FinPlace E} (hu : u ≠ w.val)
    (h_below : u.below (QuadField d₀) ≠ star (w.val.below (QuadField d₀))) (i : n) :
    ((invHeckeIsogeny w C)⁻¹.val *ᵥ v) i u = v i u := by
  -- Both factors of `invHeckeIsogeny` have component `1` at `u`: the central one lives above the
  -- conjugate of the place below `w`, the local one at `w` and its conjugate.
  refine ((evalAt u).map_mulVec (invHeckeIsogeny w C)⁻¹.val v i).trans ?_
  have h_star_ne : star u ≠ w.val := by grind [below_star, star_star]
  rw [← val_map_apply, invHeckeIsogeny, map_inv, map_mul, map_inv, map_pow, map_inv, map_pow,
    evalAt_centralScalar_of_ne h_below, evalAt_conjAtSplit_of_ne _ hu h_star_ne]
  simp

/-- The Hecke element `g = invHeckeIsogeny w C` is a frame for the scalar form `q ^ dim C`: the
matrix `q ^ dim C • gᴴ g` is a scalar unit of the profinite integers. -/
lemma isScalarFrame_invHeckeIsogeny :
    IsScalarFrame (invHeckeIsogeny w C) (w.val.q ^ Module.finrank (ResField w.val) C : ℕ) := by
  set r : ℕ := Module.finrank (ResField w.val) C
  -- `uniformizerNorm w` is the norm to `QuadField d₀` of the uniformiser at `w` and norms keep the
  -- idelic absolute value, so `(uniformizerNorm w ^ r)⁻¹` has absolute value `q ^ r` and
  -- `centralScalar_mem_GU` applies.
  have h_abs : ((w.val.q ^ r : ℕ) : ℚ) =
      finIdeleAbs (((uniformizerNorm w ^ r)⁻¹).map (adeleNorm ℚ (QuadField d₀))) := by
    simp [finIdeleAbs_adeleNorm, norm_locField_eq_q_zpow]
  obtain ⟨h_pos, h_centre_frame⟩ :
      IsScalarFrame (centralScalar (uniformizerNorm w ^ r)⁻¹ : GL n (𝔸f E)) (w.val.q ^ r : ℕ) :=
    (centralScalar_mem_GU (uniformizerNorm w ^ r)⁻¹).2 ((w.val.q ^ r : ℕ) : ℚ) h_abs
  -- The local factor is unitary, so the product is still a frame for `q ^ r • 1`.
  have h_local :
      IsFrameFor ((1 : E) • 1 : Matrix n n E) (conjAtSplit w (transposeGL (basicCosetRep C))) :=
    ⟨1, by simp⟩
  have h_frame : IsFrameFor ((((w.val.q ^ r : ℕ) : ℚ) : E) • 1)
      (centralScalar (uniformizerNorm w ^ r)⁻¹ * conjAtSplit w
        (transposeGL (basicCosetRep C))) := by
    simpa only [one_smul] using (IsFrameFor.mul_iff _ _ h_centre_frame).2 h_local
  exact ⟨h_pos, h_frame⟩

/-- If `w` is safe for the level `𝔑` and the class of `v` is killed by `𝔑`, then the inverse of
the Hecke element `New.Variety.invHeckeIsogeny w C` fixes the class of `v`. -/
lemma torsionClass_inv_mulVec_eq_of_mem_levelTorsion
    (C : Submodule (ResField w.val) (D.Index → ResField w.val)) (v : D.Index → 𝔸f E)
    (hw : IsSafe D.level w) (hv : torsionClass v ∈ D.levelTorsion) :
    torsionClass ((invHeckeIsogeny w C)⁻¹.val *ᵥ v) = torsionClass v := by
  -- At every place `u`, the two vectors differ by an integral vector: the matrix is integral and
  -- acts trivially at the places dividing the level.
  simp only [PEL.levelTorsion, mem_torsionBy_iff, smul_torsionClass_eq_zero_iff] at hv
  refine torsionClass_eq_iff.mpr fun i ↦ Subring.mem_iInf.mpr fun u ↦ ?_
  by_cases h𝔑 : D.level ∈ u.asIdeal
  · -- At a place dividing the level the matrix acts trivially, since `w` is safe.
    have hu_ne : u ≠ w.val := by grind [IsSafe]
    obtain ⟨-, -, h_level_conj⟩ := hw
    have h_below : u.below (QuadField d₀) ≠ star (w.val.below (QuadField d₀)) :=
      fun h_eq ↦ h_level_conj u h_eq h𝔑
    simp [-coe_units_inv, invHeckeIsogeny_inv_mulVec_of_ne hu_ne h_below]
  · -- Elsewhere `v` is integral, and so is its image under the integral matrix.
    have hv_int (j : D.Index) : Valued.v (v j u) ≤ 1 := by
      simpa [intValuation_eq_one_iff.mpr h𝔑] using hv j u
    refine ((LocInt u).toSubring.comap (evalAt u)).sub_mem ?_ (hv_int i)
    rw [mulVec_apply_eq_sum]
    obtain ⟨-, h_inv_int⟩ := invHeckeIsogeny_mem_GUPlus w C
    exact sum_mem fun j _ ↦ mul_mem (mem_Ô.mp (h_inv_int i j) u) (hv_int j)

/-- Let `E` be a CM field containing `ℚ(√-d₀)`, with `D.β` the image of `betaK d₀ = (1 + √-d₀)/2`.
Let `w` be a split finite place of `E` that is safe for the level `D.level` (`IsSafe`: the place of
`ℚ(√-d₀)` below `w` is split and prime to the discriminant, and `𝔑` lies neither in `w` nor in any
place above the conjugate place), and let `b` be an integer with `β - b ∈ w` coprime to
`star β - b`. For a vector `v` of finite adeles and a subspace `C` of `k_wⁿ` (`k_w` the residue
field at `w`), suppose `(β - b) ^ N` kills the class `torsionClass v` in `(𝔸f E / Ô E)ⁿ`, and the
inverse of the Hecke matrix `invHeckeIsogeny w C` attached to `C` sends `v` to a vector of class
`0`; then the ideal `w` kills `torsionClass v`. -/
lemma mem_torsionBySet_of_pow_smul_eq_zero_of_torsionClass_inv_mulVec_eq_zero
    (C : Submodule (ResField w.val) (D.Index → ResField w.val)) (v : D.Index → 𝔸f E)
    (hβ : D.β = (algebraMap (𝓞 (QuadField d₀)) (𝓞 E)) (betaK d₀)) (hw : IsSafe D.level w) {b : ℤ}
    (h_coprime : IsCoprime (D.β - b) (star D.β - b)) (hb : D.β - b ∈ w.val.asIdeal) (N : ℕ)
    (hN : (D.β - b) ^ N • torsionClass v = 0)
    (h_zero : torsionClass ((invHeckeIsogeny w C)⁻¹.val *ᵥ v) = 0) :
    torsionClass v ∈ torsionBySet (𝓞 E) (AdelicTorsion E D.Index) w.val.asIdeal := by
  -- An integrality statement, checked place by place: `a • v` is integral at every place `u`.
  simp only [smul_torsionClass_eq_zero_iff, map_pow, torsionClass_eq_zero, mem_Ô,
    mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall] at hN h_zero ⊢
  intro a ha i u
  rcases eq_or_ne u w with rfl | hu
  · -- At `w`, `v` is `(basicCosetRep C)⁻¹` applied to an integral vector; the simple pole of
    -- this matrix is cancelled by `a ∈ w`.
    have hv_eq : v i w = ((basicCosetRep C)⁻¹.val *ᵥ
        fun j ↦ evalAt _ (((invHeckeIsogeny w C)⁻¹.val *ᵥ v) j)) i := by
      simp [-coe_units_inv, RingHom.map_mulVec, invHeckeIsogeny_inv_at_eq_basicCosetRep hw]
    obtain ⟨⟨-, h_inv_entries, -⟩, -⟩ := basicCosetRep_mem_and_residueKer_eq C
    rw [hv_eq]
    exact mul_le_mul' ((intValuation_le_pow_iff_mem w.val a 1).mpr (by simpa using ha))
      (v_matrix_mul_le h_inv_entries (fun j _ ↦ h_zero j w.val) i i)
  -- At the other places `v` itself is integral.
  refine mul_le_one' (u.intValuation_le_one a) ?_
  by_cases hu_mem : D.β - b ∈ u.asIdeal
  · -- The matrix acts trivially at `u`: if `u` lay above the conjugate place, `w` would contain
    -- both `β - b` and its conjugate, which are coprime.
    have h_below : FinPlace.below (QuadField d₀) u ≠ star (w.val.below (QuadField d₀)) := by
      refine fun h_eq ↦ w.val.isPrime.notMem_of_isCoprime_of_mem h_coprime hb ?_
      have h_mem_iff : betaK d₀ - b ∈ (FinPlace.below (QuadField d₀) u).asIdeal ↔
          betaK d₀ - b ∈ (star (FinPlace.below (QuadField d₀) w.val)).asIdeal := by
        rw [h_eq]
      -- `using!`: simp leaves `RingOfIntegers.mapRingHom` where the goal has `algebraMap` between
      -- the rings of integers, which agree only by unfolding
      have h_iff : D.β - b ∈ u.asIdeal ↔ star D.β - b ∈ w.val.asIdeal := by
        simpa [hβ, ↓D.star_beta] using! h_mem_iff
      exact h_iff.mp hu_mem
    simpa only [invHeckeIsogeny_inv_mulVec_of_ne hu h_below] using h_zero i u
  · -- `β - b` is a unit at `u`, so `v` is integral there by `hN`.
    simpa [intValuation_eq_one_iff.mpr hu_mem] using hN i u

end New.Variety

/-!
## Reductions of Frobenius twists of Hecke neighbours

Take a point of level one over a valuation subring of ℂ. Let w be the split place below its
reduction to an algebraically closed residue field, good for `D` and safe. The point has one Hecke
neighbour for each subspace A of k_wⁿ. Reduce it to that field and twist by the Frobenius of
exponent q ^ (n - dim A). Under a further condition on `D.β`, for some nonzero subspace W, the
result depends only on A + W.
-/

section CongruenceStep

open Module Matrix CategoryTheory FiniteField NumberField Over New CartesianMonoidalCategory
  ThetaObject Obj Pic QuadField IsGroupBaseChange Category AddSubgroup AlgebraicGeometry

namespace New.Variety

/-! ### Counting fibres, torsion bounds and Frobenius on residue fields -/

/-- For a homomorphism `Φ` from a finite group `G`, `n` times the number of elements of the fibre
of `Φ` over `a` is `n * |G| / |Φ.range|` if `a` is in the range of `Φ`, and `0` otherwise. -/
lemma mul_card_preimage_singleton {G H : Type} [AddCommGroup G] [AddCommGroup H] [Finite G]
    (Φ : G →+ H) (n : ℕ) (a : H) [Decidable (a ∈ Φ.range)] :
    n * Nat.card (Φ ⁻¹' {a}) = if a ∈ Φ.range then n * Nat.card G / Nat.card Φ.range else 0 := by
  split_ifs with ha
  · obtain ⟨v, rfl⟩ := ha
    rw [Nat.card_congr (Φ.fiberEquivKer v), ← index_ker, ← Φ.ker.card_mul_index]
    simp [← mul_assoc, index_ne_zero_of_finite]
  · simp [Set.preimage_singleton_eq_empty.2 ha]

variable {E k : Type} [Field E] [CMBase E] [Field k] {D : PEL E}

/-- A torsion class killed by `(invHeckeIsogeny w C)⁻¹` is killed by `q ^ dim C`, where `q` is the
norm of `w`. -/
lemma q_pow_smul_torsionClass_eq_zero {d₀ : ℕ} [HasQuadSubfield d₀ E] {w : SplitFinPlace E}
    {C : Submodule (ResField w.val) (D.Index → ResField w.val)} {v : D.Index → 𝔸f E}
    (hv : torsionClass ((invHeckeIsogeny w C)⁻¹.val *ᵥ v) = 0) :
    w.val.q ^ finrank (ResField w.val) C • torsionClass v = 0 := by
  -- With `γ = (invHeckeIsogeny w C)⁻¹`, the scalar `q ^ dim C` is an integral matrix times `γ`.
  obtain ⟨-, ε, hε⟩ :
      IsScalarFrame (invHeckeIsogeny w C) (w.val.q ^ finrank (ResField w.val) C : ℕ) :=
    isScalarFrame_invHeckeIsogeny
  obtain ⟨-, h_inv_int⟩ := invHeckeIsogeny_mem_GUPlus w C
  set A : Matrix D.Index D.Index (𝔸f E) :=
    (invHeckeIsogeny w C)⁻¹.valᴴ * finAdeleIncl ℚ E ε • 1 with hA
  have h_int (i j : D.Index) : A i j ∈ Ô E := by
    simp [A, mul_mem, star_mem_Ô, h_inv_int, -coe_units_inv]
  have h_zero : torsionClass (A *ᵥ (invHeckeIsogeny w C)⁻¹.val *ᵥ v) = 0 :=
    torsionClass_mulVec_eq_zero h_int hv
  rw [mulVec_mulVec, hA, gram_inv_of_gram_eq hε] at h_zero
  simpa [map_smul', ← map_nsmul, smul_mulVec] using h_zero

/-- If `D.β - b` vanishes in a field of characteristic `l`, then `l ^ n` divides the `n`-th power
of its norm `(D.β - b) * (star D.β - b)`, so that power kills the `l ^ n`-torsion. -/
lemma pow_smul_conj_pow_smul_eq_zero {d₀ : ℕ} [HasQuadSubfield d₀ E]
    (hβ : D.β = algebraMap (𝓞 (QuadField d₀)) (𝓞 E) (betaK d₀)) {l : ℕ} [CharP k l]
    {ρ : 𝓞 E →+* k} {b : ℤ} (hb : D.β - b ∈ RingHom.ker ρ) {N : Type} [AddCommGroup N]
    [Module (𝓞 E) N] {n : ℕ} {s : N} (hs : l ^ n • s = 0) :
    (D.β - b) ^ n • (star D.β - b) ^ n • s = 0 := by
  have h_norm : ((|Algebra.norm ℤ (betaK d₀ - b)| : ℤ) : 𝓞 E) = (D.β - b) * (star D.β - b) := by
    simpa [← hβ, ← D.star_beta] using
      congrArg (algebraMap (𝓞 (QuadField d₀)) (𝓞 E)) (absNorm_span_eq_mul_star d₀ (betaK d₀ - b))
  obtain ⟨i, hi⟩ : (l : ℤ) ∣ Algebra.norm ℤ (betaK d₀ - b) := by
    simpa [CharP.intCast_eq_zero_iff] using
      Ideal.mem_of_dvd (RingHom.ker ρ) ⟨star D.β - b, h_norm⟩ hb
  have hl : (l : 𝓞 E) ^ n • s = 0 := mod_cast hs
  rw [← mul_smul, ← mul_pow, ← h_norm]
  simp [hi, mul_pow, ← mul_comm i, mul_smul, hl]

/-- Raising to a power of the norm `q` of `w` fixes the residue field of `w`, so it does not
change a ring map with kernel `w`. -/
lemma iterateFrobenius_comp_eq_of_ker_eq {w : FinPlace E} {ρ : 𝓞 E →+* k}
    (h_ker : w.asIdeal = RingHom.ker ρ) {l f r : ℕ} [Fact l.Prime] [CharP k l]
    (h_pow : l ^ f = w.q ^ r) : (iterateFrobenius k l f).comp ρ = ρ := by
  ext c
  have := Fintype.ofFinite (ResField w)
  have h_mem : c ^ w.q ^ r - c ∈ w.asIdeal := by
    simp [← card_ResField, ← algebraMap_ResField_eq_zero, pow_card_pow]
  simpa [h_ker, iterateFrobenius, h_pow, sub_eq_zero] using h_mem

variable {Z : Scheme} {τ : Z ⟶ Spec (CommRingCat.of (𝓞 E))} {X : ThetaFamily D Z τ}

/-- The torsion sections are dense in the kernel of an isogeny `ψ`, so a number `μ` that kills the
torsion sections of the kernel kills all its points. -/
lemma comp_nsmul_id_eq_zero_of_torsionPoint {V : ValuationSubring ℂ}
    {y y' : ThetaObject X (Spec (CommRingCat.of V))} (e : y.FullLevelStructure)
    (ψ : y.groupScheme ⟶ y'.groupScheme) [IsIsogeny ψ] {μ : ℕ}
    (h_tor : ∀ s : AdelicTorsion E D.Index, e.torsionPoint s ≫ ψ = 0 → μ • s = 0)
    {T : Over (Spec (CommRingCat.of V))} (a : T ⟶ y.groupScheme) (ha : a ≫ ψ = 0) :
    a ≫ (μ • 𝟙 y.groupScheme) = 0 := by
  refine eq_zero_iff_factors_zero_section.2
    (ker_factors_of_torsionPoint e ψ (μ • 𝟙 y.groupScheme) (fun s hs ↦ ?_) a ha)
  refine ⟨𝟙 _, ?_⟩
  -- `μ` kills the torsion class `s`, so `μ` times its torsion point is zero
  simp [← map_nsmul, Hom.zero_def, h_tor s hs, comp_nsmul]

section HeckeIsogenyTorsion

variable {d₀ : ℕ} [HasQuadSubfield d₀ E] {V : Type} [CommRing V]
  {y y' : ThetaObject X (Spec (CommRingCat.of V))} {e : y.FullLevelStructure}
  {e' : y'.FullLevelStructure} {ψ : y.groupScheme ⟶ y'.groupScheme} {w : SplitFinPlace E}
  {C : Submodule (ResField w.val) (D.Index → ResField w.val)}

/-- If `ψ` acts on torsion sections by `(invHeckeIsogeny w C)⁻¹` and `w` is safe for the level,
then `ψ` respects the level points. -/
lemma torsionPoint_comp_eq_of_mem_levelTorsion
    (hψ : ∀ v : D.Index → 𝔸f E, e.torsionPoint (torsionClass v) ≫ ψ =
      e'.torsionPoint (torsionClass ((invHeckeIsogeny w C)⁻¹.val *ᵥ v)))
    (h_safe : IsSafe D.level w.val) {s : AdelicTorsion E D.Index} (hs : s ∈ D.levelTorsion) :
    e.torsionPoint s ≫ ψ = e'.torsionPoint s := by
  induction s using torsionClass_induction with | _ v => ?_
  rw [hψ, torsionClass_inv_mulVec_eq_of_mem_levelTorsion C v h_safe hs]

/-- If `ψ` acts on torsion sections by `(invHeckeIsogeny w C)⁻¹`, then `q ^ dim C` kills each
torsion class whose section `ψ` kills, where `q` is the norm of `w`. -/
lemma nsmul_eq_zero_of_torsionPoint_comp_eq_zero
    (hψ : ∀ v : D.Index → 𝔸f E, e.torsionPoint (torsionClass v) ≫ ψ =
      e'.torsionPoint (torsionClass ((invHeckeIsogeny w C)⁻¹.val *ᵥ v)))
    {s : AdelicTorsion E D.Index} (hs : e.torsionPoint s ≫ ψ = 0) :
    w.val.q ^ finrank (ResField w.val) C • s = 0 := by
  induction s using torsionClass_induction with | _ v => ?_
  have h_inv_zero : torsionClass ((invHeckeIsogeny w C)⁻¹.val *ᵥ v) = 0 := by
    rwa [hψ, map_eq_zero_iff _ e'.injective] at hs
  exact q_pow_smul_torsionClass_eq_zero h_inv_zero

/-- Let `ψ` act on torsion sections by `(invHeckeIsogeny w C)⁻¹`, with `w` safe for the level and
`D.β - b ∈ w` coprime to its conjugate. A torsion class killed by a power of `D.β - b` whose
section `ψ` kills is `w`-torsion. -/
lemma mem_torsionBySet_of_pow_smul_eq_zero_of_torsionPoint_comp_eq_zero
    (hψ : ∀ v : D.Index → 𝔸f E, e.torsionPoint (torsionClass v) ≫ ψ =
      e'.torsionPoint (torsionClass ((invHeckeIsogeny w C)⁻¹.val *ᵥ v)))
    (hβ : D.β = algebraMap (𝓞 (QuadField d₀)) (𝓞 E) (betaK d₀)) (h_safe : IsSafe D.level w.val)
    {b : ℤ} (h_cop : IsCoprime (D.β - b) (star D.β - b)) (hb : D.β - b ∈ w.val.asIdeal)
    {s : AdelicTorsion E D.Index} {N : ℕ} (hN : (D.β - b) ^ N • s = 0)
    (hs : e.torsionPoint s ≫ ψ = 0) :
    s ∈ Submodule.torsionBySet (𝓞 E) (AdelicTorsion E D.Index) w.val.asIdeal := by
  induction s using torsionClass_induction with | _ v => ?_
  have h_inv_zero : torsionClass ((invHeckeIsogeny w C)⁻¹.val *ᵥ v) = 0 := by
    rwa [hψ, map_eq_zero_iff _ e'.injective] at hs
  exact mem_torsionBySet_of_pow_smul_eq_zero_of_torsionClass_inv_mulVec_eq_zero C v hβ h_safe
    h_cop hb N hN h_inv_zero

/-- Let `ψ` act on torsion sections by `(invHeckeIsogeny w C)⁻¹`, with `w` safe of norm `q` and
`D.β - b ∈ w` coprime to its conjugate. Then `ψ` respects the level points, `q ^ dim C` kills the
torsion of its kernel, and the part of that torsion killed by a power of `D.β - b` is
`w`-torsion. -/
lemma torsionPoint_comp_of_heckeIsogeny {d₀ : ℕ} [HasQuadSubfield d₀ E] {V : Type} [CommRing V]
    {y y' : ThetaObject X (Spec (CommRingCat.of V))} {e : y.FullLevelStructure}
    {e' : y'.FullLevelStructure} {ψ : y.groupScheme ⟶ y'.groupScheme} {w : SplitFinPlace E}
    {C : Submodule (ResField w.val) (D.Index → ResField w.val)}
    (hψ : ∀ v : D.Index → 𝔸f E, e.torsionPoint (torsionClass v) ≫ ψ =
      e'.torsionPoint (torsionClass ((invHeckeIsogeny w C)⁻¹.val *ᵥ v)))
    (hβ : D.β = algebraMap (𝓞 (QuadField d₀)) (𝓞 E) (betaK d₀)) (h_safe : IsSafe D.level w.val)
    {b : ℤ} (h_cop : IsCoprime (D.β - b) (star D.β - b)) (hb : D.β - b ∈ w.val.asIdeal)
    (s : AdelicTorsion E D.Index) :
    (s ∈ D.levelTorsion → e.torsionPoint s ≫ ψ = e'.torsionPoint s) ∧
    (e.torsionPoint s ≫ ψ = 0 → w.val.q ^ finrank (ResField w.val) C • s = 0) ∧
    (∀ N : ℕ, (D.β - b) ^ N • s = 0 → e.torsionPoint s ≫ ψ = 0 →
      s ∈ Submodule.torsionBySet (𝓞 E) (AdelicTorsion E D.Index) w.val.asIdeal) :=
  ⟨fun hs ↦ torsionPoint_comp_eq_of_mem_levelTorsion hψ h_safe hs,
    fun hs ↦ nsmul_eq_zero_of_torsionPoint_comp_eq_zero hψ hs,
    fun _ hN hs ↦ mem_torsionBySet_of_pow_smul_eq_zero_of_torsionPoint_comp_eq_zero hψ hβ h_safe
      h_cop hb hN hs⟩

/-- Let `σ : k_wⁿ → (𝔸_f / Ô)ⁿ` be `𝓞 E`-linear, with `σ v` the class of the adelic vector
`rep v`, such that an integral matrix kills `σ v` exactly when its reduction at `w` kills `v`. If
`ψ` acts on torsion sections by `(invHeckeIsogeny w C)⁻¹` and `w` is safe, then `ψ` kills the
torsion section of `σ v` exactly when `v ∈ C`. -/
lemma torsionPoint_comp_eq_zero_iff_mem {d₀ : ℕ} [HasQuadSubfield d₀ E] {V : Type} [CommRing V]
    {y y' : ThetaObject X (Spec (CommRingCat.of V))} {e : y.FullLevelStructure}
    {e' : y'.FullLevelStructure} {ψ : y.groupScheme ⟶ y'.groupScheme} {w : SplitFinPlace E}
    {C : Submodule (ResField w.val) (D.Index → ResField w.val)}
    (hψ : ∀ v : D.Index → 𝔸f E, e.torsionPoint (torsionClass v) ≫ ψ =
      e'.torsionPoint (torsionClass ((invHeckeIsogeny w C)⁻¹.val *ᵥ v)))
    (h_safe : IsSafe D.level w.val) {σ : (D.Index → ResField w.val) →ₗ[𝓞 E] AdelicTorsion E D.Index}
    {rep : (D.Index → ResField w.val) → D.Index → 𝔸f E}
    (hσ_rep : ∀ v : D.Index → ResField w.val, σ v = torsionClass (rep v))
    (hσ_ker : ∀ (v : D.Index → ResField w.val) (g : Matrix D.Index D.Index (Ô E)),
      torsionClass (g.map (fun a : Ô E ↦ a.val) *ᵥ rep v) = 0 ↔
        v ∈ residueKer (g.map (fun a : Ô E ↦ a.val w.val)))
    (v : D.Index → ResField w.val) :
    e.torsionPoint (σ v) ≫ ψ = 0 ↔ v ∈ C := by
  -- `M` is the integral matrix `(invHeckeIsogeny w C)⁻¹`. At `w` it is `basicCosetRep C`, whose
  -- reduction has kernel `C`.
  obtain ⟨-, h_inv_int⟩ := invHeckeIsogeny_mem_GUPlus w C
  obtain ⟨-, h_residueKer⟩ := basicCosetRep_mem_and_residueKer_eq C
  let M : Matrix D.Index D.Index (Ô E) := fun i j ↦ ⟨(invHeckeIsogeny w C)⁻¹.val i j, h_inv_int i j⟩
  have hM_val : M.map (fun a ↦ a.val) = (invHeckeIsogeny w C)⁻¹.val := rfl
  have hM_at : M.map (fun a ↦ a.val w.val) = (invHeckeIsogeny w C)⁻¹.val.map (evalAt w.val) := rfl
  rw [hσ_rep, hψ, map_eq_zero_iff _ e'.injective, ← hM_val, hσ_ker, hM_at,
    invHeckeIsogeny_inv_at_eq_basicCosetRep h_safe, h_residueKer]

end HeckeIsogenyTorsion

section Multiplier

variable [IsAlgClosed k] {x₀ x x' : ThetaObject X (Spec (CommRingCat.of k))} {μ : ℕ}
  {g : x₀.groupScheme ⟶ x.groupScheme} {g' : x₀.groupScheme ⟶ x'.groupScheme}
  [IsIsogeny g] [IsIsogeny g'] [IsLinear g] [IsLinear g']

omit [IsIsogeny g'] in
/-- Let `g` and `g'` be linear isogenies with the same source and the same multiplier `μ`. A map `j`
with `g ≫ j = c • g'` satisfies `⟨c • u, g v⟩ = ⟨j u, g' v⟩`, where `⟨·,·⟩` is the pairing
`picClass.pairing` of the line bundle class of `x`, resp. `x'`. -/
lemma pairing_smul_eq_of_comp_eq_smul
    (hg : pull g.left x.lineBundle.picClass = μ • x₀.lineBundle.picClass)
    (hg' : pull g'.left x'.lineBundle.picClass = μ • x₀.lineBundle.picClass)
    {j : x.groupScheme ⟶ x'.groupScheme} (c : 𝓞 E) (hj : g ≫ j = c • g')
    ⦃T : Over (Spec (CommRingCat.of k))⦄ (u : T ⟶ x.groupScheme) (v : T ⟶ x₀.groupScheme) :
    x.lineBundle.picClass.pairing (u ≫ (c • 𝟙 x.groupScheme)) (v ≫ g) =
      x'.lineBundle.picClass.pairing (u ≫ j) (v ≫ g') := by
  -- For `u` in the image of `g` both sides are `μ` times one pairing on `x₀.groupScheme`, and the
  -- identity descends along `g`.
  refine pairing_eq_of_fpqc_cover (.id_horiz _) g (c • 𝟙 x.groupScheme) g j g' ?_ u v
  simp [hj, hg, hg', ← IsLinear.smul_comp, ← pairing_comp]

/-- Let `g : x₀ ⟶ x` and `g' : x₀ ⟶ x'` be linear isogenies of objects over an algebraically closed
field `k` with multiplier `μ` (`E` is the CM field of the datum `D`), `x` rigid, and let `l ^ n`
kill the kernel of `g'`. If `(star D.β - b) ^ n` times each of `g`, `g'` factors through the other,
and `D.β - b` is coprime to its conjugate, then `g` itself factors through `g'`. -/
lemma exists_factor_of_conj_pow_smul_factors {l n : ℕ} [Fact l.Prime] [CharP k l] {b : ℤ}
    (h_cop : IsCoprime (D.β - b) (star D.β - b)) (h_rigid : x.HasSpanningCoords)
    (hg : pull g.left x.lineBundle.picClass = μ • x₀.lineBundle.picClass)
    (hg' : pull g'.left x'.lineBundle.picClass = μ • x₀.lineBundle.picClass)
    (h_killed : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra k B]
      (u : specOver k B ⟶ x₀.groupScheme), u ≫ g' = 0 → u ≫ (l ^ n • 𝟙 x₀.groupScheme) = 0)
    {ν : x.groupScheme ⟶ x'.groupScheme} (hν : g ≫ ν = (star D.β - b) ^ n • g')
    {ν' : x'.groupScheme ⟶ x.groupScheme} [IsAdditive ν']
    (hν' : g' ≫ ν' = (star D.β - b) ^ n • g) :
    ∃ j : x'.groupScheme ⟶ x.groupScheme, IsAdditive j ∧ g' ≫ j = g := by
  -- `g` kills the kernel of `g'`, since its multiples by the coprime elements `(D.β - b) ^ n` and
  -- `(star D.β - b) ^ n` do.
  refine exists_isAdditive_comp_eq_of_isIsogeny g' g
    fun B hB_ring hB_local hB_alg hB_finite hB_noeth u hu ↦ ?_
  have h_conj : u ≫ ((star D.β - b) ^ n • g) = 0 := by simp [← hν', reassoc_of% hu]
  have h_self : u ≫ ((D.β - b) ^ n • g) = 0 := by
    refine h_rigid.eq_zero_of_pairing_eq_zero (id_comp x) (u ≫ ((D.β - b) ^ n • g)) n (𝟙 _) ?_
      fun T a c ↦ ?_
    · -- `l ^ n` kills `u`, since `u ≫ g' = 0`
      have h_l_pow : l ^ n • u = 0 := by simpa [comp_nsmul] using h_killed B u hu
      rw [← comp_nsmul, ← nsmul_comp, h_l_pow]
      simp
    · -- Move the scalar across the pairing, then use the identity for `ν` and `u ≫ g' = 0`.
      have h_ν : x.lineBundle.picClass.pairing
            (c ≫ ((star D.β - b) ^ n • 𝟙 x.groupScheme)) ((a ≫ u) ≫ g) =
          x'.lineBundle.picClass.pairing (c ≫ ν) ((a ≫ u) ≫ g') :=
        pairing_smul_eq_of_comp_eq_smul hg hg' _ hν c (a ≫ u)
      simpa [pairing_comm _ (a ≫ _), pairing.eq_1 _ _ 0, hu, pairing_pow_smul_adjoint] using h_ν
  obtain ⟨c₁, c₂, h_bezout⟩ :
      ∃ c₁ c₂ : 𝓞 E, c₁ * (D.β - b) ^ n + c₂ * (star D.β - b) ^ n = 1 := h_cop.pow
  -- Bézout: `u ≫ g` is a combination of `u ≫ (D.β - b) ^ n • g` and `u ≫ (star D.β - b) ^ n • g`
  have h_comb :
      u ≫ ((c₁ * (D.β - b) ^ n + c₂ * (star D.β - b) ^ n) • g) = u ≫ ((1 : 𝓞 E) • g) := by
    rw [h_bezout]
  simpa [add_smul, mul_smul, h_conj, h_self, comp_add] using h_comb.symm

omit [IsIsogeny g] in
/-- Let `g : x₀ ⟶ x`, `g' : x₀ ⟶ x'` be linear isogenies of objects over an algebraically closed
field `k` with the same multiplier (`E` is the CM field of the datum `D`), `x'` rigid, and
`g' ≫ j = g`. If `x` and `x'` have the same map `𝓞 E → k` and `j` respects the level points, then
`x' = x` and `j` respects the maps to the family. -/
lemma eq_of_comp_eq_of_pull_picClass_eq (h_rigid : x'.HasSpanningCoords)
    (hg : pull g.left x.lineBundle.picClass = μ • x₀.lineBundle.picClass)
    (hg' : pull g'.left x'.lineBundle.picClass = μ • x₀.lineBundle.picClass)
    (h_base : x'.baseHom = x.baseHom) {j : x'.groupScheme ⟶ x.groupScheme} [IsAdditive j]
    (hj : g' ≫ j = g) (h_level : ∀ s : D.levelTorsion, x'.levelPoints s ≫ j = x.levelPoints s) :
    x' = x ∧ j.left ≫ x.toFamily.left = x'.toFamily.left := by
  have hj_lin : IsLinear j := by
    refine ⟨fun c ↦ (epi_of_epi_left g').left_cancellation _ _ ?_⟩
    -- after `g'`, both sides are `c • g`, by `hj` and the linearity of `g`
    simpa [← assoc, ← hj] using IsLinear.smul_id_comp (f := g) c
  have hj_one : g' ≫ j = (1 : 𝓞 E) • g := by rw [one_smul, hj]
  -- by descent along `g'`, it is enough to compare the pairings on the image of `g'`
  have hj_pair : ∀ ⦃T : Over (Spec (CommRingCat.of k))⦄ (u v : T ⟶ x'.groupScheme),
      x'.lineBundle.picClass.pairing u v = x.lineBundle.picClass.pairing (u ≫ j) (v ≫ j) :=
    pairing_eq_of_fpqc_cover (.id_horiz _) g' (𝟙 _) (𝟙 _) j j fun T a v ↦ by
      simpa [pairing_comm, hj] using
        pairing_smul_eq_of_comp_eq_smul hg' hg 1 hj_one v a
  exact h_rigid.eq_and_comp_toFamily_eq_of_hom (id_comp x') h_base j hj_pair h_level

end Multiplier

section TwistedReduction

variable {V : Type} [CommRing V]

/-- The absolute Frobenius `t ↦ t ^ l ^ f` of a `k`-scheme, as a map over `V` between its two
structures given by `π` followed by the Frobenius of `k` and by `π`. -/
noncomputable def frobeniusTwist (π : V →+* k) (l : ℕ) [Fact l.Prime] [CharP k l] (f : ℕ) :
    Over.map (specMap ((iterateFrobenius k l f).comp π)) ⟶ Over.map (specMap π) where
  app T := homMk (absFrobenius f T) (by
    have h_frob : absFrobenius f T ≫ T.hom = T.hom ≫ specMap (iterateFrobenius k l f) :=
      (absFrobenius_comm ..).trans
        (T.hom ≫= by simpa using! comp_absFrobenius f (.mk (𝟙 _)) (𝟙 _))
    simpa [specMap] using! h_frob =≫ specMap π)
  naturality := by simp [absFrobenius_comm, OverMorphism.ext_iff]

variable {π : V →+* k} {l f : ℕ} [Fact l.Prime] [CharP k l]
  {y y' : ThetaObject X (Spec (CommRingCat.of V))} {x₀ x : ThetaObject X (Spec (CommRingCat.of k))}

open scoped MonoidalCategory in
/-- Let `x₀` be the reduction of `y` along `π`, and `x` that of `y'` along `π` followed by the
Frobenius `t ↦ t ^ l ^ f`. The map `g : x₀ → x` is the reduction of `ψ : y → y'` twisted by that
Frobenius. -/
structure IsTwistedReduction (hx₀ : x₀.IsPullbackAlong (specMap π) y)
    (hx : x.IsPullbackAlong (specMap ((iterateFrobenius k l f).comp π)) y')
    (ψ : y.groupScheme ⟶ y'.groupScheme) (g : x₀.groupScheme ⟶ x.groupScheme) : Prop where
  /-- On points, `g` is the Frobenius followed by `ψ`. -/
  pointEquiv_comp {T : Over (Spec (CommRingCat.of k))} (u : T ⟶ x₀.groupScheme) :
    hx.isGroupBaseChange.pointEquiv (u ≫ g) =
      (frobeniusTwist π l f).app T ≫ hx₀.isGroupBaseChange.pointEquiv u ≫ ψ
  /-- The map `g` is `𝓞 E`-linear. -/
  isLinear : IsLinear g
  /-- The map `g` sends the reduction of a section `a` to the reduction of `ψ a`. -/
  pullSection_comp (a : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ y.groupScheme) :
    hx₀.isGroupBaseChange.pullSection a ≫ g = hx.isGroupBaseChange.pullSection (a ≫ ψ)

variable {hx₀ : x₀.IsPullbackAlong (specMap π) y}
  {hx : x.IsPullbackAlong (specMap ((iterateFrobenius k l f).comp π)) y'}
  {ψ : y.groupScheme ⟶ y'.groupScheme} {g : x₀.groupScheme ⟶ x.groupScheme}

variable (hx₀ hx ψ) in
/-- A linear map `ψ : y ⟶ y'` over `V` has a twisted reduction: a map `g : x₀ ⟶ x` between the
reductions of `y` and `y'` that is the reduction of `ψ` twisted by the Frobenius `t ↦ t ^ l ^ f`
(`New.Variety.IsTwistedReduction`). -/
lemma exists_isTwistedReduction [IsLinear ψ] :
    ∃ g : x₀.groupScheme ⟶ x.groupScheme, IsTwistedReduction hx₀ hx ψ g :=
  -- `x` is a base change of `y'`, so maps into it are given by their points
  (hx₀.isGroupBaseChange.exists_hom_baseChange hx.isGroupBaseChange (frobeniusTwist π l f) ψ).imp
    fun _ ⟨h_point, h_lin, h_section⟩ ↦ ⟨h_point, h_lin, h_section⟩

/-- The multiplier of the twisted reduction is that of `ψ` times `l ^ f`. Here `X` is a theta family
of the PEL datum `D`, and `x₀`, `x` are its objects over the field `k` of characteristic `l`. -/
lemma IsTwistedReduction.pull_picClass_eq_nsmul (hg : IsTwistedReduction hx₀ hx ψ g) {r : ℕ}
    (hψ : pull ψ.left y'.lineBundle.picClass = r • y.lineBundle.picClass) :
    pull g.left x.lineBundle.picClass = (l ^ f * r) • x₀.lineBundle.picClass := by
  rw [mul_nsmul, picClass_pull_absFrobenius _ _ x₀.isProjEmbedding.isLinearSystem,
    hx.lineBundle_eq_pull, hx₀.lineBundle_eq_pull]
  -- on underlying schemes, `g` followed by the map to `y'` is the Frobenius followed by `ψ`
  have h_pull : pull (hx.isGroupBaseChange.pointEquiv (𝟙 x₀.groupScheme ≫ g)).left
      y'.lineBundle.picClass = pull ((frobeniusTwist π l f).app x₀.groupScheme ≫
        hx₀.isGroupBaseChange.pointEquiv (𝟙 x₀.groupScheme) ≫ ψ).left y'.lineBundle.picClass := by
    rw [hg.pointEquiv_comp]
  simpa [← pull_picClass, pull_comp, hψ, pointEquiv_apply, frobeniusTwist] using h_pull

/-- If `π` and `ψ` are surjective, then so is a twisted reduction `g` of `ψ`, on underlying
schemes. -/
lemma IsTwistedReduction.surjective [IsAlgClosed k] (hg : IsTwistedReduction hx₀ hx ψ g)
    (hπ : Function.Surjective π) [Surjective ψ.left] : Surjective g.left := by
  have h_closed : IsClosedImmersion hx.schemeMap.left :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback hx.isGroupBaseChange.isPullback.flip
      (.spec_of_surjective _ ((bijective_iterateFrobenius k l f).surjective.comp hπ))
  refine ⟨fun c' ↦ ?_⟩
  -- A preimage under `ψ` of the image of `c'` lies in the special fibre, so it comes from a
  -- point `c` of `x₀.groupScheme`; Frobenius does not move points.
  obtain ⟨a, ha⟩ := ψ.left.surjective (hx.schemeMap.left c')
  -- `a` lies over the image of `c'` in `Spec k`, moved by the Frobenius of `k`
  have h_over : y.groupScheme.hom.base a =
      (specMap π).base ((specMap (iterateFrobenius k l f)).base (x.groupScheme.hom.base c')) := by
    simpa [specMap, ← ψ.w, ha, -Over.w] using congrArg (fun φ ↦ φ.base c') hx.schemeMap.w
  obtain ⟨c, hc, -⟩ :=
    Scheme.exists_preimage_of_isPullback hx₀.isGroupBaseChange.isPullback a _ h_over
  refine ⟨c, hx.schemeMap.left.isClosedEmbedding.injective ?_⟩
  have h_point_left : (hx.isGroupBaseChange.pointEquiv (𝟙 x₀.groupScheme ≫ g)).left c =
      ((frobeniusTwist π l f).app x₀.groupScheme ≫
        hx₀.isGroupBaseChange.pointEquiv (𝟙 x₀.groupScheme) ≫ ψ).left c := by
    rw [hg.pointEquiv_comp]
  simpa [ha, hc, frobeniusTwist, absFrobenius_apply, pointEquiv_apply] using h_point_left

/-- If `x₀` is rigid, `g` has multiplier `μ` and `μ` kills the kernel of `ψ`, then `μ` kills the
points of the kernel of `g` with values in local Noetherian rings. -/
lemma IsTwistedReduction.comp_nsmul_id_eq_zero (hg : IsTwistedReduction hx₀ hx ψ g)
    (h_rigid : x₀.HasSpanningCoords) {μ : ℕ}
    (h_cls : pull g.left x.lineBundle.picClass = μ • x₀.lineBundle.picClass)
    (h_ker : ∀ {T : Over (Spec (CommRingCat.of V))} (a : T ⟶ y.groupScheme),
      a ≫ ψ = 0 → a ≫ (μ • 𝟙 y.groupScheme) = 0)
    (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra k B]
    (u : specOver k B ⟶ x₀.groupScheme) (hu : u ≫ g = 0) : u ≫ (μ • 𝟙 x₀.groupScheme) = 0 := by
  -- The point `μ • u` vanishes after Frobenius and is in the kernel of the polarisation, hence
  -- vanishes by rigidity.
  have hg_lin : IsLinear g := hg.isLinear
  refine h_rigid.eq_zero_of_pairing_eq_zero (id_comp x₀) (u ≫ (μ • 𝟙 x₀.groupScheme)) 0
    ((frobeniusTwist π l f).app (specOver k B)).left ?_ ?_
  · refine hx₀.isGroupBaseChange.pointEquiv.map_eq_zero_iff.mp ?_
    -- after Frobenius, `u` gives a point of `y` that `ψ` kills, hence that `μ` kills
    have h_frob_ψ : ((frobeniusTwist π l f).app (specOver k B) ≫
        hx₀.isGroupBaseChange.pointEquiv u) ≫ ψ = 0 := by
      simp [← hg.pointEquiv_comp, hu]
    simpa [eq_zero_iff_factors_zero_section, pointEquiv_apply,
      hx₀.isGroupBaseChange.nsmul_id_comp] using h_ker _ h_frob_ψ
  · -- `μ` times the pairing of `u` and `a` is the pairing of `g u` and `g a`, which is `0`
    -- because `g u = 0`.
    obtain ⟨h_parallelogram, -⟩ := x₀.hasClassLaws
    have h_pair {T : Over (Spec (CommRingCat.of k))} (a c : T ⟶ x₀.groupScheme) :
        (μ • x₀.lineBundle.picClass).pairing a c =
          x.lineBundle.picClass.pairing (a ≫ g) (c ≫ g) := by
      rw [← h_cls, pairing_comp]
    simp [← h_parallelogram.nsmul_pairing_eq_pairing_nsmul, h_pair, hu, pairing.eq_1, comp_nsmul]

/-- Let `y`, `y'` be objects of the theta family `X` over `V`, `k` an algebraically closed field of
characteristic `l`, `ψ : y ⟶ y'` a linear isogeny with multiplier `r`, and `l ^ f * r = M` with
`M ≠ 0`. Then the reduction `x` of `y'` along `π` followed by the Frobenius `t ↦ t ^ l ^ f` has a
twisted reduction `g : x₀ ⟶ x` of `ψ`, and `g` is an isogeny with multiplier `M`. -/
lemma exists_isTwistedReduction_isIsogeny [IsAlgClosed k] (hπ : Function.Surjective π)
    (hx₀ : x₀.IsPullbackAlong (specMap π) y) (ψ : y.groupScheme ⟶ y'.groupScheme) [IsIsogeny ψ]
    [IsLinear ψ] {r M : ℕ} [NeZero M]
    (hψ_cls : pull ψ.left y'.lineBundle.picClass = r • y.lineBundle.picClass)
    (h_mul : l ^ f * r = M) :
    ∃ (x : ThetaObject X (Spec (CommRingCat.of k)))
      (hx : x.IsPullbackAlong (specMap ((iterateFrobenius k l f).comp π)) y')
      (g : x₀.groupScheme ⟶ x.groupScheme), IsTwistedReduction hx₀ hx ψ g ∧
        pull g.left x.lineBundle.picClass = M • x₀.lineBundle.picClass ∧ IsIsogeny g := by
  obtain ⟨x, hx⟩ : ∃ x : ThetaObject X (Spec (CommRingCat.of k)),
      x.IsPullbackAlong (specMap ((iterateFrobenius k l f).comp π)) y' :=
    y'.exists_isPullbackAlong _
  obtain ⟨g, hg⟩ : ∃ g : x₀.groupScheme ⟶ x.groupScheme, IsTwistedReduction hx₀ hx ψ g :=
    exists_isTwistedReduction hx₀ hx ψ
  have hg_lin : IsLinear g := hg.isLinear
  have hg_cls : pull g.left x.lineBundle.picClass = M • x₀.lineBundle.picClass := by
    rw [hg.pull_picClass_eq_nsmul hψ_cls, h_mul]
  -- `g` is quasi-finite, since its multiplier is not zero, and surjective, hence an isogeny
  have hg_isog : IsIsogeny g :=
    isIsogeny_of_locallyQuasiFinite g
      (locallyQuasiFinite_of_pull_picClass x₀.isProjEmbedding NeZero.out hg_cls) (hg.surjective hπ)
  exact ⟨x, hx, g, hg, hg_cls, hg_isog⟩

end TwistedReduction

/-- Let `X` be a theta family of the PEL datum `D` of the CM field `E`, and `k` an algebraically
closed field. Let `g`, `g'` be twisted reductions of `ψ`, `ψ'` (`hg`, `hg'`), with `D.β - b` in the
kernel of `𝓞 E → k` and coprime to its conjugate (`hb`, `h_cop`), and `c`, `c'` injective families
of torsion vectors killed by that kernel. If `υ` moves the torsion of the kernel of `ψ` into `c`,
`ψ'` kills `c'`, `(D.β - b) ^ n • υ` kills the kernel of the isogeny `g`, and `c`, `c'` have equal
numbers of sections through each `k`-point (weights `l ^ f`, `l ^ f'`), then `υ • g'` factors
through `g`. -/
lemma IsTwistedReduction.exists_comp_eq_smul [IsAlgClosed k] {V : ValuationSubring ℂ}
    {π : V →+* k} {l f f' : ℕ} [Fact l.Prime] [CharP k l]
    {y y₁ y₂ : ThetaObject X (Spec (CommRingCat.of V))}
    {x₀ x₁ x₂ : ThetaObject X (Spec (CommRingCat.of k))} {hx₀ : x₀.IsPullbackAlong (specMap π) y}
    {hx₁ : x₁.IsPullbackAlong (specMap ((iterateFrobenius k l f).comp π)) y₁}
    {hx₂ : x₂.IsPullbackAlong (specMap ((iterateFrobenius k l f').comp π)) y₂}
    {ψ : y.groupScheme ⟶ y₁.groupScheme} {ψ' : y.groupScheme ⟶ y₂.groupScheme}
    {g : x₀.groupScheme ⟶ x₁.groupScheme} {g' : x₀.groupScheme ⟶ x₂.groupScheme}
    [IsIsogeny ψ] [IsIsogeny ψ'] [IsIsogeny g] (hg : IsTwistedReduction hx₀ hx₁ ψ g)
    (hg' : IsTwistedReduction hx₀ hx₂ ψ' g') (e : y.FullLevelStructure) {b : ℤ}
    (hb : D.β - b ∈ RingHom.ker x₀.baseHom) (h_cop : IsCoprime (D.β - b) (star D.β - b))
    {ι ι' : Type} {c : ι → AdelicTorsion E D.Index} {c' : ι' → AdelicTorsion E D.Index}
    (hc_inj : Function.Injective c) (hc'_inj : Function.Injective c')
    (hc_mem : ∀ i : ι, c i ∈
      Submodule.torsionBySet (𝓞 E) (AdelicTorsion E D.Index) (RingHom.ker x₀.baseHom))
    (hc'_mem : ∀ i : ι', c' i ∈
      Submodule.torsionBySet (𝓞 E) (AdelicTorsion E D.Index) (RingHom.ker x₀.baseHom))
    {υ : 𝓞 E} {n : ℕ}
    (h_into : ∀ s : AdelicTorsion E D.Index, e.torsionPoint s ≫ ψ = 0 → υ • s ∈ Set.range c)
    (h_kills : ∀ i : ι', e.torsionPoint (c' i) ≫ ψ' = 0)
    (h_killed : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra k B]
      (u : specOver k B ⟶ x₀.groupScheme), u ≫ g = 0 → (D.β - b) ^ n • υ • u = 0)
    (h_count : ∀ a : (Over.map (specMap π)).obj (specOver k k) ⟶ y.groupScheme,
      l ^ f * sectionCount e c a = l ^ f' * sectionCount e c' a) :
    ∃ ν : x₁.groupScheme ⟶ x₂.groupScheme, IsAdditive ν ∧ g ≫ ν = υ • g' := by
  have hg'_lin : IsLinear g' := hg'.isLinear
  refine exists_isAdditive_comp_eq_of_isIsogeny g (υ • g') ?_
  intro B inst_ring inst_local inst_alg inst_finite inst_noetherian u hu
  set a : (Over.map (specMap π)).obj (specOver k B) ⟶ y.groupScheme :=
    υ • hx₀.isGroupBaseChange.pointEquiv u with ha
  have ha_killed : (D.β - b) ^ n • a = 0 := by
    simpa [ha] using congrArg hx₀.isGroupBaseChange.pointEquiv (h_killed B u hu)
  obtain ⟨res, -⟩ : ∃ res : B →ₐ[k] k, ⊥ ≤ RingHom.ker res :=
    nullstellensatz_exists_le_ker bot_ne_top
  -- For each family, a power of `θ` is a local equation at `a` for its sections; the exponent is
  -- the number of them through the closed point `a₀` of `a`.
  obtain ⟨θ, -, hθ⟩ : ∃ θ : B, res θ = 0 ∧ ∀ ⦃J : Type⦄ (c : J → AdelicTorsion E D.Index),
      Function.Injective c →
      (∀ i : J, c i ∈ Submodule.torsionBySet (𝓞 E) (AdelicTorsion E D.Index)
        (RingHom.ker x₀.baseHom)) →
      IsLocalEquation e c a
        (θ ^ sectionCount e c ((Over.map (specMap π)).map (specOver.map res) ≫ a)) :=
    exists_isLocalEquation_pow_sectionCount e hx₀ hb h_cop n a ha_killed res
  let a₀ : (Over.map (specMap π)).obj (specOver k k) ⟶ y.groupScheme :=
    (Over.map (specMap π)).map (specOver.map res) ≫ a
  -- Vanishing along the Frobenius of `B` is vanishing after the twist.
  have hl : (l : B) = 0 := natCast_eq_zero_of_over_charP (B := .of B) (specOver k B).hom
  have h_along (r : ℕ) {A : Over (Spec (CommRingCat.of V))} [AddObj A]
      (p : (Over.map (specMap π)).obj (specOver k B) ⟶ A) :
      VanishesAlong p (frobPow hl r) ↔ (frobeniusTwist π l r).app (specOver k B) ≫ p = 0 :=
    vanishesAlong_iff _ (comp_absFrobenius r (.mk _) (𝟙 _))
  -- The equation for `c` vanishes after Frobenius, since `g` kills `u`; by `h_count` so does the
  -- equation for `c'`, and then `ψ'` kills `a` after Frobenius.
  have h_frob_zero :
      (frobeniusTwist π l f).app (specOver k B) ≫ hx₀.isGroupBaseChange.pointEquiv u ≫ ψ = 0 := by
    simp [← hg.pointEquiv_comp, hu]
  have h_pow : (θ ^ sectionCount e c a₀) ^ l ^ f = 0 :=
    (hθ c hc_inj hc_mem).map_eq_zero ψ rfl h_into
      ((h_along f (hx₀.isGroupBaseChange.pointEquiv u ≫ ψ)).2 h_frob_zero)
  have h_pow' : (θ ^ sectionCount e c' a₀) ^ l ^ f' = 0 := by
    rwa [← pow_mul, mul_comm, ← h_count, mul_comm, pow_mul]
  have h_frob : (frobeniusTwist π l f').app (specOver k B) ≫ a ≫ ψ' = 0 :=
    (h_along f' _).1 ((hθ c' hc'_inj hc'_mem).vanishesAlong ψ' h_kills h_pow')
  simpa [ha, ← hg'.pointEquiv_comp, ← map_smul, ← ModuleObj.comp_smul] using h_frob

/-- Rigidity for two twisted reductions `g₁ : x₀ ⟶ x₁` and `g₂ : x₀ ⟶ x₂` of maps from `y` that
respect the level points: if they are linear isogenies with multiplier `l ^ n`, `l ^ n` kills the
kernel of `g₂`, `x₁`, `x₂` are rigid with the same map `𝓞 E → k`, `D.β - b` is coprime to its
conjugate (`h_cop`), and `(star D.β - b) ^ n` times each of `g₁`, `g₂` factors through the other,
then `x₂ = x₁`, and some `j : x₂ ⟶ x₁` with `g₂ ≫ j = g₁` respects the maps to the family. -/
lemma IsTwistedReduction.eq_of_conj_pow_smul_factors [IsAlgClosed k] {V : ValuationSubring ℂ}
    {π : V →+* k} {l f₁ f₂ n : ℕ} [Fact l.Prime] [CharP k l]
    {y y₁ y₂ : ThetaObject X (Spec (CommRingCat.of V))}
    {x₀ x₁ x₂ : ThetaObject X (Spec (CommRingCat.of k))} {hx₀ : x₀.IsPullbackAlong (specMap π) y}
    {hx₁ : x₁.IsPullbackAlong (specMap ((iterateFrobenius k l f₁).comp π)) y₁}
    {hx₂ : x₂.IsPullbackAlong (specMap ((iterateFrobenius k l f₂).comp π)) y₂}
    {ψ₁ : y.groupScheme ⟶ y₁.groupScheme} {ψ₂ : y.groupScheme ⟶ y₂.groupScheme}
    {g₁ : x₀.groupScheme ⟶ x₁.groupScheme} {g₂ : x₀.groupScheme ⟶ x₂.groupScheme}
    [IsIsogeny g₁] [IsIsogeny g₂] [IsLinear g₁] [IsLinear g₂]
    (hg₁ : IsTwistedReduction hx₀ hx₁ ψ₁ g₁) (hg₂ : IsTwistedReduction hx₀ hx₂ ψ₂ g₂)
    (e : y.FullLevelStructure) (e₁ : y₁.FullLevelStructure) (e₂ : y₂.FullLevelStructure)
    (h_level₁ : ∀ s ∈ D.levelTorsion, e.torsionPoint s ≫ ψ₁ = e₁.torsionPoint s)
    (h_level₂ : ∀ s ∈ D.levelTorsion, e.torsionPoint s ≫ ψ₂ = e₂.torsionPoint s)
    (h_rigid₁ : x₁.HasSpanningCoords) (h_rigid₂ : x₂.HasSpanningCoords)
    (hg₁_cls : pull g₁.left x₁.lineBundle.picClass = l ^ n • x₀.lineBundle.picClass)
    (hg₂_cls : pull g₂.left x₂.lineBundle.picClass = l ^ n • x₀.lineBundle.picClass)
    (h_killed₂ : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra k B]
      (u : specOver k B ⟶ x₀.groupScheme), u ≫ g₂ = 0 → u ≫ (l ^ n • 𝟙 x₀.groupScheme) = 0)
    (h_base : x₂.baseHom = x₁.baseHom) {b : ℤ} (h_cop : IsCoprime (D.β - b) (star D.β - b))
    {ν : x₁.groupScheme ⟶ x₂.groupScheme} (hν : g₁ ≫ ν = (star D.β - b) ^ n • g₂)
    {ν' : x₂.groupScheme ⟶ x₁.groupScheme} [IsAdditive ν']
    (hν' : g₂ ≫ ν' = (star D.β - b) ^ n • g₁) :
    ∃ j : x₂.groupScheme ⟶ x₁.groupScheme,
      g₂ ≫ j = g₁ ∧ x₂ = x₁ ∧ j.left ≫ x₁.toFamily.left = x₂.toFamily.left := by
  obtain ⟨j, hj_add, hj⟩ :=
    exists_factor_of_conj_pow_smul_factors h_cop h_rigid₁ hg₁_cls hg₂_cls h_killed₂ hν hν'
  -- `j` respects the level points, so rigidity applies
  have hj_level (s : D.levelTorsion) : x₂.levelPoints s ≫ j = x₁.levelPoints s := by
    simp [hx₁.levelPoints_eq_pullSection, hx₂.levelPoints_eq_pullSection, e₁.levelPoints_eq,
      e₂.levelPoints_eq, ← hg₁.pullSection_comp, ← hg₂.pullSection_comp, hj, ← h_level₁,
      ← h_level₂]
  exact ⟨j, hj, eq_of_comp_eq_of_pull_picClass_eq h_rigid₂ hg₁_cls hg₂_cls h_base hj hj_level⟩

/-- Let `X` be a theta family of the PEL datum `D` of the CM field `E`, and `k` a field of
characteristic `l`. Let `D.β` be the image of `betaK d₀ = (1 + √-d₀)/2` (`hβ`), and let `D.β - b`
vanish under `ρ : 𝓞 E → k`. Suppose that `l ^ M` kills the torsion classes whose sections `ψ` kills,
that such a class killed by a power of `D.β - b` lies in the image of `σ`, and that `ψ` kills the
section of `σ v` exactly when `v ∈ C`. Then `(star D.β - b) ^ M` maps each torsion class whose
section `ψ` kills into `σ C`. -/
lemma exists_apply_eq_conj_pow_smul_of_comp_eq_zero {d₀ : ℕ} [HasQuadSubfield d₀ E]
    (hβ : D.β = algebraMap (𝓞 (QuadField d₀)) (𝓞 E) (betaK d₀)) {l : ℕ} [CharP k l]
    {ρ : 𝓞 E →+* k} {b : ℤ} (hb : D.β - b ∈ RingHom.ker ρ) {V : Type} [CommRing V]
    {y y' : ThetaObject X (Spec (CommRingCat.of V))} {e : y.FullLevelStructure}
    {ψ : y.groupScheme ⟶ y'.groupScheme} [IsLinear ψ] {w : SplitFinPlace E}
    {C : Submodule (ResField w.val) (D.Index → ResField w.val)}
    {σ : (D.Index → ResField w.val) →ₗ[𝓞 E] AdelicTorsion E D.Index} {M : ℕ}
    (h_range : ∀ (s : AdelicTorsion E D.Index) (N : ℕ), (D.β - b) ^ N • s = 0 →
      e.torsionPoint s ≫ ψ = 0 → s ∈ σ.range)
    (h_tor_killed : ∀ s : AdelicTorsion E D.Index, e.torsionPoint s ≫ ψ = 0 → l ^ M • s = 0)
    (h_ker_res : ∀ v : D.Index → ResField w.val, e.torsionPoint (σ v) ≫ ψ = 0 ↔ v ∈ C)
    (s : AdelicTorsion E D.Index) (hs : e.torsionPoint s ≫ ψ = 0) :
    ∃ v : C, σ v = (star D.β - b) ^ M • s := by
  have h_zero : e.torsionPoint ((star D.β - b) ^ M • s) ≫ ψ = 0 := by simp [hs]
  obtain ⟨v, hv⟩ :=
    h_range _ M (pow_smul_conj_pow_smul_eq_zero hβ hb (h_tor_killed s hs)) h_zero
  exact ⟨⟨v, by rwa [← h_ker_res, hv]⟩, hv⟩

/-- A place `w` good for `D` contains `D.β - b` for an integer `b` with `D.β - b` coprime to its
conjugate. -/
lemma _root_.New.PEL.IsGoodAt.exists_coprime {w : Ideal (𝓞 E)} (h_good : D.IsGoodAt w) :
    ∃ b : ℤ, D.β - b ∈ w ∧ IsCoprime (D.β - b) (star D.β - b) := by
  obtain ⟨-, p, b, -, -, hb, h_cop, -⟩ := h_good
  exact ⟨b, hb, h_cop⟩

/-- Let the torsion section of `σ t` reduce to zero at the closed point, and let
`l ^ m B * q ^ dim B` be the same for all subspaces `B` of `k_wⁿ`. If `A' ⊔ span t = A ⊔ span t`,
then the number of `v ∈ A` whose section `σ v` reduces to a given `k`-point `a`, weighted by
`l ^ m A`, equals the same number for `A'`, weighted by `l ^ m A'`. -/
private lemma pow_mul_sectionCount_eq_of_sup_span_eq {V : ValuationSubring ℂ} {π : V →+* k}
    {y : ThetaObject X (Spec (CommRingCat.of V))} (e : y.FullLevelStructure) {w : SplitFinPlace E}
    (σ : (D.Index → ResField w.val) →ₗ[𝓞 E] AdelicTorsion E D.Index) {t : D.Index → ResField w.val}
    (ht_red : toUnit ((Over.map (specMap π)).obj (specOver k k)) ≫ e.torsionPoint (σ t) = 0)
    {l : ℕ} {m : Submodule (ResField w.val) (D.Index → ResField w.val) → ℕ}
    (h_split : ∀ B : Submodule (ResField w.val) (D.Index → ResField w.val),
      l ^ m B * w.val.q ^ finrank (ResField w.val) B = l ^ m ⊥)
    {A A' : Submodule (ResField w.val) (D.Index → ResField w.val)}
    (h_sup : A' ⊔ (ResField w.val ∙ t) = A ⊔ (ResField w.val ∙ t))
    (a : (Over.map (specMap π)).obj (specOver k k) ⟶ y.groupScheme) :
    l ^ m A * sectionCount e (fun v : A ↦ σ v) a =
      l ^ m A' * sectionCount e (fun v : A' ↦ σ v) a := by
  classical
  -- `Φ B` reduces the sections in `B` to `k`-points. The sizes of its fibres, weighted by
  -- `l ^ m B`, depend only on its image, and adding `t` does not change that image.
  let Φ (B : Submodule (ResField w.val) (D.Index → ResField w.val)) :
      B →+ ((Over.map (specMap π)).obj (specOver k k) ⟶ y.groupScheme) :=
    .mk' (fun v ↦ toUnit _ ≫ e.torsionPoint (σ v)) (by simp [comp_add])
  have h_fibre (B : Submodule (ResField w.val) (D.Index → ResField w.val)) :
      l ^ m B * sectionCount e (fun v : B ↦ σ v) a =
        if a ∈ (Φ B).range then l ^ m ⊥ / Nat.card (Φ B).range else 0 := by
    rw [← h_split B, ← card_ResField, ← natCard_eq_pow_finrank]
    exact mul_card_preimage_singleton (Φ B) (l ^ m B) a
  have h_range : (Φ A').range = (Φ A).range := by
    simpa [Φ, SetLike.ext_iff, ht_red, Submodule.mem_span_singleton,
      (algebraMap_ResField_surjective _).exists, comp_add] using
      congrArg (fun B : Submodule (ResField w.val) (D.Index → ResField w.val) ↦ (Φ B).range) h_sup
  rw [h_fibre A, h_fibre A', h_range]

/-- The kernel and rigidity steps of `New.Variety.UniversalFamily.exists_ne_bot_factorsThrough_sup`.
Here `X` is a theta family of the PEL datum `D` of the CM field `E`, `k` is a field,
`ψ B : y ⟶ y' B` are linear isogenies respecting the level points, `g B` their twisted reductions,
isogenies with multiplier `l ^ M` onto rigid `x B`, and `σ` embeds `k_wⁿ` onto the torsion killed by
the kernel of `x₀.baseHom`, which holds `D.β - b` (`hb`, `h_cop`). Suppose `ψ B` kills the section
of `σ v` exactly when `v ∈ B`, `l ^ M` kills the torsion classes whose sections `ψ B` kills, those
among them killed by a power of `D.β - b` lie in the range of `σ`, `x₀` is rigid, and each `x B` has
the map `𝓞 E → k` of `x₀`. If `A`, `A'` have equal weighted section counts, then `x A' = x A`, and
some `j` with `g A' ≫ j = g A` respects the maps to the family. -/
private lemma exists_comp_eq_and_eq_of_sectionCount_eq [IsAlgClosed k] {d₀ : ℕ}
    [HasQuadSubfield d₀ E] (hβ : D.β = algebraMap (𝓞 (QuadField d₀)) (𝓞 E) (betaK d₀))
    {w : SplitFinPlace E} {V : ValuationSubring ℂ} {π : V →+* k} {l : ℕ} [Fact l.Prime] [CharP k l]
    {y : ThetaObject X (Spec (CommRingCat.of V))} (e : y.FullLevelStructure)
    {x₀ : ThetaObject X (Spec (CommRingCat.of k))} {hx₀ : x₀.IsPullbackAlong (specMap π) y}
    (h_rigid₀ : x₀.HasSpanningCoords) {b : ℤ} (hb : D.β - b ∈ RingHom.ker x₀.baseHom)
    (h_cop : IsCoprime (D.β - b) (star D.β - b))
    {σ : (D.Index → ResField w.val) →ₗ[𝓞 E] AdelicTorsion E D.Index}
    (hσ_inj : Function.Injective σ)
    (hσ_range : σ.range =
      Submodule.torsionBySet (𝓞 E) (AdelicTorsion E D.Index) (RingHom.ker x₀.baseHom))
    {m : Submodule (ResField w.val) (D.Index → ResField w.val) → ℕ} {M : ℕ}
    {y' : Submodule (ResField w.val) (D.Index → ResField w.val) →
      ThetaObject X (Spec (CommRingCat.of V))}
    (e' : ∀ B : Submodule (ResField w.val) (D.Index → ResField w.val), (y' B).FullLevelStructure)
    {ψ : ∀ B : Submodule (ResField w.val) (D.Index → ResField w.val),
      y.groupScheme ⟶ (y' B).groupScheme}
    [∀ B : Submodule (ResField w.val) (D.Index → ResField w.val), IsIsogeny (ψ B)]
    [∀ B : Submodule (ResField w.val) (D.Index → ResField w.val), IsLinear (ψ B)]
    (h_level : ∀ B : Submodule (ResField w.val) (D.Index → ResField w.val), ∀ s ∈ D.levelTorsion,
      e.torsionPoint s ≫ ψ B = (e' B).torsionPoint s)
    (h_tor_killed : ∀ (B : Submodule (ResField w.val) (D.Index → ResField w.val))
      (s : AdelicTorsion E D.Index), e.torsionPoint s ≫ ψ B = 0 → l ^ M • s = 0)
    (h_place : ∀ (B : Submodule (ResField w.val) (D.Index → ResField w.val))
      (s : AdelicTorsion E D.Index) (N : ℕ),
      (D.β - b) ^ N • s = 0 → e.torsionPoint s ≫ ψ B = 0 → s ∈ σ.range)
    (h_ker_res : ∀ (B : Submodule (ResField w.val) (D.Index → ResField w.val))
      (v : D.Index → ResField w.val),
      e.torsionPoint (σ v) ≫ ψ B = 0 ↔ v ∈ B)
    {x : Submodule (ResField w.val) (D.Index → ResField w.val) →
      ThetaObject X (Spec (CommRingCat.of k))}
    {hx : ∀ B : Submodule (ResField w.val) (D.Index → ResField w.val),
      (x B).IsPullbackAlong (specMap ((iterateFrobenius k l (m B)).comp π)) (y' B)}
    {g : ∀ B : Submodule (ResField w.val) (D.Index → ResField w.val),
      x₀.groupScheme ⟶ (x B).groupScheme}
    [∀ B : Submodule (ResField w.val) (D.Index → ResField w.val), IsIsogeny (g B)]
    [∀ B : Submodule (ResField w.val) (D.Index → ResField w.val), IsLinear (g B)]
    (hg : ∀ B : Submodule (ResField w.val) (D.Index → ResField w.val),
      IsTwistedReduction hx₀ (hx B) (ψ B) (g B))
    (hg_cls : ∀ B : Submodule (ResField w.val) (D.Index → ResField w.val),
      pull (g B).left (x B).lineBundle.picClass = l ^ M • x₀.lineBundle.picClass)
    (h_rigid : ∀ B : Submodule (ResField w.val) (D.Index → ResField w.val), (x B).HasSpanningCoords)
    (h_baseHom : ∀ B : Submodule (ResField w.val) (D.Index → ResField w.val),
      (x B).baseHom = x₀.baseHom)
    {A A' : Submodule (ResField w.val) (D.Index → ResField w.val)}
    (h_count : ∀ a : (Over.map (specMap π)).obj (specOver k k) ⟶ y.groupScheme,
      l ^ m A * sectionCount e (fun v : A ↦ σ v) a =
        l ^ m A' * sectionCount e (fun v : A' ↦ σ v) a) :
    ∃ j : (x A').groupScheme ⟶ (x A).groupScheme,
      g A' ≫ j = g A ∧ x A' = x A ∧ j.left ≫ (x A).toFamily.left = (x A').toFamily.left := by
  -- `l ^ M` kills the torsion sections in the kernel of `ψ C`, hence the kernel of `g C`.
  have h_killed (C : Submodule (ResField w.val) (D.Index → ResField w.val)) (B : Type)
      [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra k B]
      (u : specOver k B ⟶ x₀.groupScheme) (hu : u ≫ g C = 0) :
      u ≫ (l ^ M • 𝟙 x₀.groupScheme) = 0 :=
    (hg C).comp_nsmul_id_eq_zero h_rigid₀ (hg_cls C)
      (comp_nsmul_id_eq_zero_of_torsionPoint e (ψ C) (h_tor_killed C)) B u hu
  have h_conj_killed (C : Submodule (ResField w.val) (D.Index → ResField w.val)) (B : Type)
      [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra k B]
      (u : specOver k B ⟶ x₀.groupScheme) (hu : u ≫ g C = 0) :
      (D.β - b) ^ M • (star D.β - b) ^ M • u = 0 := by
    have h_nsmul : l ^ M • u = 0 := by simpa [comp_nsmul] using h_killed C B u hu
    exact pow_smul_conj_pow_smul_eq_zero hβ hb h_nsmul
  -- `(star D.β - b) ^ M` maps the torsion sections of the kernel of `ψ C` into `σ C`; so
  -- `(star D.β - b) ^ M • g C'` factors through `g C` when the counts agree.
  have h_factor (C C' : Submodule (ResField w.val) (D.Index → ResField w.val))
      (h_count_eq : ∀ a : (Over.map (specMap π)).obj (specOver k k) ⟶ y.groupScheme,
        l ^ m C * sectionCount e (fun v : C ↦ σ v) a =
          l ^ m C' * sectionCount e (fun v : C' ↦ σ v) a) :
      ∃ ν : (x C).groupScheme ⟶ (x C').groupScheme,
        IsAdditive ν ∧ g C ≫ ν = (star D.β - b) ^ M • g C' :=
    (hg C).exists_comp_eq_smul (hg C') e hb h_cop
      (c := fun v : C ↦ σ v) (c' := fun v : C' ↦ σ v) hσ_inj.injOn.injective
      hσ_inj.injOn.injective (fun v ↦ hσ_range.le ⟨v, rfl⟩) (fun v ↦ hσ_range.le ⟨v, rfl⟩)
      (exists_apply_eq_conj_pow_smul_of_comp_eq_zero hβ hb (h_place C) (h_tor_killed C)
        (h_ker_res C))
      (fun v ↦ (h_ker_res C' v).2 v.property) (h_conj_killed C) h_count_eq
  obtain ⟨ν, -, hν⟩ := h_factor A A' h_count
  obtain ⟨ν', hν'_add, hν'⟩ := h_factor A' A fun a ↦ (h_count a).symm
  -- By rigidity, the two factorizations make the objects `x A'` and `x A` equal.
  exact (hg A).eq_of_conj_pow_smul_factors (hg A') e (e' A) (e' A') (h_level A) (h_level A')
    (h_rigid A) (h_rigid A') (hg_cls A) (hg_cls A') (h_killed A')
    ((h_baseHom A').trans (h_baseHom A).symm) h_cop hν hν'

end New.Variety

/-- The pointwise step of the congruence relation at the split place `w` below `π`, good for `D` and
safe, of norm `q`, where `π : V → k` is onto an algebraically closed field of characteristic `l`.
Here `E` contains the imaginary quadratic field ℚ(√−d₀), and `D.β` is its integer
`betaK d₀ = (1 + √−d₀)/2`. Let `x₀` reduce the object under the level-one point `s` with moduli
point `z`, and let `α A` be the Hecke neighbour of `z` given by `A ≤ k_wⁿ`, with
`l ^ m A = q ^ (n - dim A)` with `n = D.rank`. Then for some `W ≠ ⊥`, the reduction of `α A` twisted
by `t ↦ t ^ l ^ m A` depends only on `A ⊔ W`. -/
lemma New.Variety.UniversalFamily.exists_ne_bot_factorsThrough_sup {E k : Type} {d d₀ : ℕ} [Field E]
  [CMBase E]
    {D : PEL E} {R : Subalgebra (𝓞 E) E} [HasQuadSubfield d₀ E] (U : UniversalFamily D R)
    (hβ : D.β = algebraMap (𝓞 (QuadField d₀)) (𝓞 E) (betaK d₀))
    -- a point of level one over a valuation subring of `ℂ`
    {V : ValuationSubring ℂ} {z : ModuliPoint E D.Index d}
    {s : Spec (CommRingCat.of V) ⟶ (U.family.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin d)).left}
    (h_point : U.family.IsPointOf 1 z s)
    -- the reduction `x₀` of the object under `s` to an algebraically closed field
    {w : SplitFinPlace E} [Field k] [IsAlgClosed k] {π : V →+* k} (hπ : Function.Surjective π)
    {x₀ : ThetaObject U.family (Spec (CommRingCat.of k))}
    (hx₀ : x₀.IsPullbackAlong (specMap π)
      (s ≫ (U.family.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin d)).hom))
    -- the place lies below the reduction map, and is good and safe
    (h_ker : w.val.asIdeal = RingHom.ker x₀.baseHom) (h_good : D.IsGoodAt w.val.asIdeal)
    (h_safe : IsSafe D.level w.val)
    -- for each subspace, a Frobenius exponent and the point of the Hecke neighbour
    {l : ℕ} [Fact l.Prime] [CharP k l]
    {m : Submodule (ResField w.val) (D.Index → ResField w.val) → ℕ}
    {α : Submodule (ResField w.val) (D.Index → ResField w.val) →
      (Spec (CommRingCat.of V) ⟶ (U.family.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin d)).left)}
    (h_exp : ∀ A : Submodule (ResField w.val) (D.Index → ResField w.val),
      l ^ m A = w.val.q ^ (D.rank - finrank (ResField w.val) A))
    (h_nbr : ∀ A : Submodule (ResField w.val) (D.Index → ResField w.val),
      U.family.IsPointOf 1 (z.act ⟨invHeckeIsogeny w A, invHeckeIsogeny_mem_GUPlus w A⟩) (α A)) :
    ∃ W : Submodule (ResField w.val) (D.Index → ResField w.val), W ≠ ⊥ ∧
      Function.FactorsThrough
        (fun A : Submodule (ResField w.val) (D.Index → ResField w.val) ↦
          specMap ((iterateFrobenius k l (m A)).comp π) ≫ α A)
        (fun A : Submodule (ResField w.val) (D.Index → ResField w.val) ↦ A ⊔ W) := by
  classical
  -- Let `y` and `y' B` be the objects over `V` behind the points `s` and `α B`; `x₀` and `x B` are
  -- their reductions to `k`, the latter twisted by Frobenius. The isogeny `ψ B` from `y` to `y' B`
  -- reduces to an isogeny `g B` from `x₀` to `x B`. Its kernel depends only on the reduction of the
  -- sections in `B`, which does not change when a vector `t` whose section reduces to zero is
  -- added; then rigidity identifies the targets.
  obtain @⟨y, V_torus, inst_torus, Y_period, e, rfl⟩ := h_point
  choose y' V_tori inst_tori Y_periods e' hα_eq using fun A ↦
    (ThetaFamily.isPointOf_iff ..).mp (h_nbr A)
  -- `ψ A` has multiplier `q ^ dim A` and acts on torsion by `(invHeckeIsogeny w A)⁻¹`.
  choose hψ_ρ ψ hψ_isog hψ_lin hψ_cls hψ_ev hψ_π using fun A ↦
    e.exists_isogeny 1 (by simp [ratConj, ModuliPoint.act]) (e' A) (by simp [ModuliPoint.act])
      (invHeckeIsogeny_mem_GUPlus w A).2 isScalarFrame_invHeckeIsogeny
  -- Goodness gives an integer `b` with `D.β - b ∈ w` coprime to its conjugate.
  obtain ⟨b, hb, h_cop⟩ := h_good.exists_coprime
  -- `σ` identifies `k_wⁿ` with the `w`-torsion of `(𝔸_f / Ô)ⁿ`; an integral matrix kills `σ v`
  -- exactly when its reduction modulo `w` kills `v` (`hσ_ker`).
  choose σ hσ_inj hσ_range rep hσ_rep hσ_ker using exists_residue_torsion_emb (n := D.Index) w.val
  -- `ψ C` respects level points, `q ^ dim C` kills the torsion of its kernel, and the part of that
  -- torsion killed by a power of `D.β - b` is `w`-torsion.
  choose h_level h_q_kills h_place using fun C ↦
    torsionPoint_comp_of_heckeIsogeny (hψ_ev C) hβ h_safe h_cop hb
  rw [← hσ_range] at h_place
  simp_rw [h_ker, pointOf_hom] at h_good hb hσ_range hx₀
  -- A nonzero `w`-torsion section `σ t` reduces to zero.
  obtain ⟨_, ⟨t, rfl⟩, ht_ne, ht_red⟩ : ∃ s ∈ σ.range, s ≠ 0 ∧
      toUnit (map (specMap π) (specOver k k)) ≫ e.fullStructure.torsionPoint s = 0 := by
    rw [hσ_range]
    obtain ⟨-, h_exists_zero, -⟩ := exists_param_pow_card_eq_zero h_good e.fullStructure hx₀
    exact h_exists_zero
  -- The reduced isogenies `g B` all have multiplier `l ^ m ⊥ = q ^ n`: a factor `q ^ dim B` from
  -- `ψ B` and `l ^ m B = q ^ (n - dim B)` from Frobenius.
  have h_split (B : Submodule (ResField w.val) (D.Index → ResField w.val)) :
      l ^ m B * w.val.q ^ finrank (ResField w.val) B = l ^ m ⊥ := by
    simpa [h_exp] using pow_sub_mul_pow _ B.finrank_le
  choose x hx g hg hg_cls hg_isog using fun B ↦
    exists_isTwistedReduction_isIsogeny hπ hx₀ (ψ B) (hψ_cls B) (h_split B)
  have hg_lin (B : Submodule (ResField w.val) (D.Index → ResField w.val)) : IsLinear (g B) :=
    (hg B).isLinear
  -- The torsion sections in the kernel of `ψ C`: the `w`-part is `C`, and `l ^ m ⊥` kills them all.
  have h_ker_res (C : Submodule (ResField w.val) (D.Index → ResField w.val))
      (v : D.Index → ResField w.val) : e.fullStructure.torsionPoint (σ v) ≫ ψ C = 0 ↔ v ∈ C :=
    torsionPoint_comp_eq_zero_iff_mem (hψ_ev C) h_safe hσ_rep hσ_ker v
  have h_tor_killed (C : Submodule (ResField w.val) (D.Index → ResField w.val))
      (s : AdelicTorsion E D.Index)
      (hs : e.fullStructure.torsionPoint s ≫ ψ C = 0) : l ^ m ⊥ • s = 0 := by
    rw [← h_split C, mul_smul, h_q_kills C s hs, smul_zero]
  -- The line `W` is spanned by `t`; adding it does not change the weighted counts of sections.
  refine ⟨ResField w.val ∙ t, by simpa using ne_zero_of_map ht_ne, fun A' A h_sup ↦ ?_⟩
  have h_count (a : (Over.map (specMap π)).obj (specOver k k) ⟶ y.groupScheme) :
      l ^ m A * sectionCount e.fullStructure (fun v : A ↦ σ v) a =
        l ^ m A' * sectionCount e.fullStructure (fun v : A' ↦ σ v) a :=
    pow_mul_sectionCount_eq_of_sup_span_eq e.fullStructure σ ht_red h_split h_sup a
  -- The twist by `l ^ m B`, a power of `q`, does not change the map `𝓞 E → k`.
  have h_baseHom (B : Submodule (ResField w.val) (D.Index → ResField w.val)) :
      (x B).baseHom = x₀.baseHom := by
    rw [(hx B).baseHom_eq_comp, hψ_ρ, RingHom.comp_assoc, ← hx₀.baseHom_eq_comp,
      iterateFrobenius_comp_eq_of_ker_eq h_ker (h_exp B)]
  -- By rigidity the objects `x A'` and `x A` are equal, and some `j` with `g A' ≫ j = g A`
  -- respects the maps to the family.
  obtain ⟨j, hj, h_base, h_proj⟩ :=
    exists_comp_eq_and_eq_of_sectionCount_eq hβ e.fullStructure
      (e.hasSpanningCoords_of_specMap_comp_eq π hx₀)
      hb h_cop hσ_inj hσ_range (fun B ↦ (e' B).fullStructure) h_level h_tor_killed h_place h_ker_res
      hg hg_cls (fun B ↦ (e' B).hasSpanningCoords_of_specMap_comp_eq _ (hx B)) h_baseHom h_count
  -- The two points agree on the base by `h_base`, and on each section by `h_proj` and `hj`.
  have hψ_π_one : ∀ (B : Submodule (ResField w.val) (D.Index → ResField w.val))
      (r : RealVectors E D.Index), e.π r ≫ ψ B = (e' B).π r := by simpa using hψ_π
  -- `↓`: `hψ_π_one` must rewrite the sections before `simp` splits the composites
  simp [fibrePower_ext_iff, hα_eq, ModuliPoint.act, ↓← hψ_π_one, -comp_left,
    ← comp_left_assoc, ← (hx _).isGroupBaseChange.pullSection_comp_assoc,
    ← (hg _).pullSection_comp, (hx _).comp_toFamily, ← h_proj, hj, hx, h_base]

end CongruenceStep
