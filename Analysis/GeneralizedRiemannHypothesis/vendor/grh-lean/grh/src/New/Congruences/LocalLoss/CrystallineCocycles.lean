import New.Congruences.Lifting.CupOrthogonalityBounds
import New.Congruences.LocalLoss.Basic

/-!
# Crystalline cocycles and the defect of a crystalline lattice at a place above ℓ

This file gives local estimates at a place above ℓ for the module `New.Period.crysCocycles` of
crystalline cocycles of a Galois lattice `L` over a coefficient ring `O`. Throughout, the instance
`OverGp Γ ℓ` gives a homomorphism j from `Γ` to G_ℓ = Gal(ℚ̄_ℓ / ℚ_ℓ) with open image.
`New.CoeffRing.normLength` normalises lengths so that `O / ℓ` has length `1`. For a crystalline
lattice, the defect `New.Lift.dualDefect` for a class of lattices is the length of the cocycles
modulo those in the annihilator `New.Lift.cupOrthogonal` of the lattices in the class. This file
computes the rank of the crystalline cocycles and bounds the normalised defect of a lattice whose
jumps lie in windows, under the size conditions `New.Selmer.CrystallineSizes`.

## Main definitions and results

* `New.Selmer.finrank_crysCocycles_eq_add_neg_jumps`: the rank is `rank L` plus the number of
  negative Hodge–Tate jumps at the embeddings that belong to the place.
* `New.Selmer.normLength_dualDefect_le_of_hasCupExponent`: if a power ℓ^k carries the cocycles into
  the annihilator of a class of lattices, as `New.Lift.HasCupExponent` says, then the defect is
  bounded in terms of k.
* `New.Selmer.normLength_dualDefect_le_of_crystallineSizes`: the defect is bounded in terms of the
  crystalline loss `New.Selmer.crystallineLoss`, uniformly in `ℓ`.

Notions from other files:
* `New.Lift.GalLattice`: A finite free O-module with a compatible ℤ_ℓ-module structure, together
  with an O-linear representation of the group Γ on it.
* `New.Period.IsPotentiallyCrystalline`: for a representation on T and the crystalline period ring
  B, the elements of B⊗T fixed by all g with j(g) near 1 span B⊗T over B.
* `New.Period.crysCocycles`: Z_f(T), the module, over the coefficient ring, of maps c: Γ → T such
  that some y in B⊗T has 1⊗c(g) = gy − y for all g.
* `New.Period.jump`: The multiplicity of the Hodge–Tate jump u at γ: the dimension over ℚ̄_ℓ (zero
  if infinite) of the space `New.Period.hodgeTateMaps`.

## Relation to the literature

See `New.Congruences.LocalLoss.CrystallineDefect` for related work.
-/

/-!
## Rank of crystalline cocycles and a length bound

`New.Period.HasJumps ρ γ J` says that `J` is the multiset of jumps at the coefficient embedding `γ`.
-/

namespace New.Selmer

export Lift (InClass)

open Lift Period crysCocycles Module Set Multiset Finset DFunLike Submodule Finite TensorProduct

variable {ℓ : ℕ} [ThePrime ℓ] {O : CoeffRing ℓ} {Γ : Type} {n : Type} [Group Γ] [Fintype n]
  [DecidableEq n] [𝒥 : OverGp Γ ℓ] {R : Type} [CommRing R] [Algebra ℤ_[ℓ] R] [TopologicalSpace Γ]
  {L : GalLattice O Γ}

/-- The Γ-lattice over R given by the module R^n with Γ acting through the matrix representation
ρ. -/
noncomputable abbrev matrixLattice (ρ : Γ →* Matrix n n R) : GalLattice R Γ where
  Carrier := n → R
  ρ := actionRep R (n → R) ρ

open scoped Classical in
/-- Let `E` be a CM field containing a primitive `5040`-th root of unity, `e` an embedding of `E`
into `ℚ̄_ℓ`, and let `𝒥.toGp : Γ → G_ℓ` be an open embedding onto the elements of
`G_ℓ = Gal(ℚ̄_ℓ / ℚ_ℓ)` that fix `e E` (`h_group`). Let `O` be the ring of integers of a finite
Galois extension of `ℚ_ℓ` and `L` a potentially crystalline `O`-lattice with action of `Γ`. For `g`
in `G_ℓ`, `coefficientEmbedding O g` is the embedding `x ↦ g x` of `O` into `ℂ_ℓ`, and
`complexEmbeddingOf e g` is the complex embedding `ι⁻¹ ∘ g⁻¹ ∘ e` of `E`, with `ι : ℂ ≃ ℚ̄_ℓ` the
isomorphism fixed by `PadicIso ℓ`. Suppose that for each `g` the Hodge–Tate jumps of `L` at the
first are the multiset `J` at the second. Then the rank of the module of crystalline cocycles of `L`
is `rank L` plus the number of negative jumps, summed over the distinct embeddings `ι⁻¹ ∘ g⁻¹ ∘ e`
of `E`.

A case of the Bloch–Kato rank formula for crystalline cocycles. -/
lemma finrank_crysCocycles_eq_add_neg_jumps {E : Type*} [Field E] [CMFieldWithRoot5040 E]
    {e : E →+* PadicAlgCl ℓ} [PadicIso ℓ] (h_group : IsCompletionGroup e 𝒥.toGp)
    (h_crys : IsPotentiallyCrystalline L.ρ) {J : (E →+* ℂ) → Multiset ℤ}
    (hJ : ∀ g : Gp ℓ, HasJumps L.ρ (coefficientEmbedding O g) (J (complexEmbeddingOf e g))) :
    finrank O (crysCocycles L.ρ) =
      finrank O L + ∑ σ : E →+* ℂ with ∃ g : Gp ℓ, complexEmbeddingOf e g = σ,
        (J σ).countP (· < 0) := by
  -- Apply the rank formula over `ℤ_ℓ`, count the jumps in two ways, and divide by `[O : ℤ_ℓ]`.
  have : Module.Finite O (crysCocycles L.ρ) := fg h_crys
  -- Every embedding `φ` of `O` is `coefficientEmbedding O (s φ)`; `K φ` are the jumps at `φ`.
  choose s hs using coefficientEmbedding_surjective (O := O)
  choose K hK using fun φ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ] ↦
    (h_crys.exists_hasJumps φ).imp fun _ h_jumps ↦ h_jumps.2
  -- `r σ` is an element of the Galois group with `complexEmbeddingOf e (r σ) = σ`.
  let r : range (complexEmbeddingOf e) → Gp ℓ := rangeSplitting (complexEmbeddingOf e)
  -- Over `ℤ_ℓ` the jumps are those at all the embeddings of `O` together.
  have jumps_sum : HasJumps (overZp L.ρ) (Algebra.ofId ℤ_[ℓ] ℂ_[ℓ]) (∑ φ, K φ) := fun u ↦ by
    simpa [← h_crys.sum_jump_eq_jump_overZp.1 u, count_sum'] using
      sum_congr rfl fun φ _ ↦ hK φ u
  have K_eq (g : Gp ℓ) : K (coefficientEmbedding O g) = J (complexEmbeddingOf e g) :=
    ext' fun u ↦ (hK (coefficientEmbedding O g) u).symm.trans (hJ g u)
  -- `φ ↦ coefficientEmbedding O (g * s φ)` permutes the embeddings of `O`.
  have sum_K (g : Gp ℓ) : ∑ φ, K (coefficientEmbedding O (g * s φ)) = ∑ φ, K φ := by
    refine (Function.Injective.bijective_of_finite fun φ ψ h_eq ↦ ?_).sum_comp K
    -- Both sides are `g` applied to the values of `s φ` and `s ψ`, and `g` is injective.
    rw [← hs φ, ← hs ψ]
    simpa [coefficientEmbedding, ext_iff] using h_eq
  -- `σ ↦ complexEmbeddingOf e (r σ * g)` permutes the embeddings of the place.
  have sum_J (g : Gp ℓ) :
      ∑ σ, J (complexEmbeddingOf e (r σ * g)) = ∑ σ : range (complexEmbeddingOf e), J σ := by
    let perm (σ : range (complexEmbeddingOf e)) : range (complexEmbeddingOf e) :=
      ⟨complexEmbeddingOf e (r σ * g), r σ * g, rfl⟩
    refine (Function.Injective.bijective_of_finite (f := perm) fun σ τ ↦ ?_).sum_comp (J ·)
    simp [perm, r, Subtype.ext_iff, ← apply_rangeSplitting, h_group.complexEmbeddingOf_eq_iff]
  -- Sum the jumps at `coefficientEmbedding O (r σ * s φ)` first over `φ`, then over `σ`; there are
  -- `𝒥.toGp.range.index` embeddings `σ` and `finrank ℤ_[ℓ] O` embeddings `φ`.
  have double_count :
      𝒥.toGp.range.index • ∑ φ, K φ = finrank ℤ_[ℓ] O • ∑ σ : range (complexEmbeddingOf e), J σ :=
    calc _ = ∑ σ, ∑ φ, K (coefficientEmbedding O (r σ * s φ)) := by
          simp [sum_K, h_group.index_eq_card_range]
      _ = ∑ φ, ∑ σ, K (coefficientEmbedding O (r σ * s φ)) := sum_comm
      _ = _ := by simp [K_eq, sum_J, card_algHom_eq_finrank]
  -- Multiplied by `[O : ℤ_ℓ]`, the ranks become ranks over `ℤ_ℓ`. There `crysCocycles.finrank_eq`
  -- gives the rank of `L` plus the index times the number of negative jumps, which `double_count`
  -- evaluates.
  have h_neg : 𝒥.toGp.range.index * (∑ φ, K φ).countP (· < 0) =
      finrank ℤ_[ℓ] O *
        ∑ σ : E →+* ℂ with ∃ g : Gp ℓ, complexEmbeddingOf e g = σ, (J σ).countP (· < 0) := by
    simpa [← coe_countPAddMonoidHom, sum_set_coe, ← filter_mem_univ_eq_toFinset] using
      congrArg (countP (· < 0)) double_count
  refine Nat.mul_left_cancel (finrank_pos (R := ℤ_[ℓ]) (M := O)) ?_
  rw [mul_add, finrank_mul_finrank, finrank_mul_finrank, (finrank_eq h_crys jumps_sum).2, h_neg]

/-- From an exponent to the defect. Let `L` be potentially crystalline, and let `ℓ ^ k` carry the
crystalline cocycles of `L` into `cupOrthogonal 𝒬 L`, the functions orthogonal to the lattices in
`𝒬` under the cup product (this is `HasCupExponent 𝒬 L k`). The defect `dualDefect 𝒬 L` is the
length of the crystalline cocycles modulo `cupOrthogonal 𝒬 L`. Then this defect, normalised so that
`O / ℓ` has length `1` (`normLength`), is at most `y` times the index of the image of `Γ` under
`𝒥.toGp` in `G_ℓ`, for any `y ≥ 2 k · rank L`. -/
lemma normLength_dualDefect_le_of_hasCupExponent {k : ℕ} (hL : IsPotentiallyCrystalline L.ρ)
    {𝒬 : GalLattice O Γ → Prop} {y : NNReal}
    (hy : finrank O L * (2 * k) ≤ y) (h_exp : HasCupExponent 𝒬 L k) :
    O.normLength (dualDefect 𝒬 L) ≤ 𝒥.toGp.range.index * y := by
  -- The defect is the length of a quotient of `crysCocycles / ℓ ^ k`, that is of `(O / ℓ ^ k) ^ r`,
  -- with `r` the `O`-rank of `crysCocycles`; this has normalised length `r * k`. Bloch–Kato bounds
  -- `r` by `2 * index * rank L`.
  have : Module.Finite O (crysCocycles L.ρ) := fg hL
  obtain ⟨K, hK_card, hK⟩ := hL.exists_hasJumps (ρ := overZp L.ρ) (Algebra.ofId ℤ_[ℓ] ℂ_[ℓ])
  set m : ℕ := 𝒥.toGp.range.index
  have hm : 0 < m := (𝒥.toGp.range.quotient_finite_of_isOpen 𝒥.isOpen_range.out).card_pos
  -- The rank over `ℤ_ℓ`: at most `rank L` of the jumps `K` are negative.
  have h_rankZ : finrank ℤ_[ℓ] (crysCocycles L.ρ) ≤ 2 * (m * finrank ℤ_[ℓ] L) :=
    calc _ = finrank ℤ_[ℓ] L + m * K.countP (· < 0) := (finrank_eq hL hK).2
      _ ≤ finrank ℤ_[ℓ] L + m * finrank ℤ_[ℓ] L := by grw [countP_le_card, hK_card]
      _ ≤ _ := by linarith [Nat.le_mul_of_pos_left (finrank ℤ_[ℓ] L) hm]
  -- The rank over `O`: divide by the degree of `O` over `ℤ_ℓ`.
  have h_rank : finrank O (crysCocycles L.ρ) ≤ 2 * (m * finrank O L) := by
    rw [← finrank_mul_finrank ℤ_[ℓ] O, ← finrank_mul_finrank ℤ_[ℓ] O L] at h_rankZ
    exact le_of_mul_le_mul_left (by linarith) (finrank_pos (R := ℤ_[ℓ]) (M := O))
  let I : Ideal O := Ideal.span {(ℓ : ↑O) ^ k}
  have h_sub : I • ⊤ ≤ (cupOrthogonal 𝒬 L).submoduleOf (crysCocycles L.ρ) := by
    rw [ideal_span_singleton_smul]
    rintro _ ⟨c, -, rfl⟩
    exact h_exp _ c.2
  calc _ ≤ O.normLength (length O (crysCocycles L.ρ ⧸ I • (⊤ : Submodule O _))) := by
        grw [dualDefect, relLength, length_le_of_surjective _ (factor_surjective h_sub)]
    _ = finrank O (crysCocycles L.ρ) * k := by
      rw [← (quotTensorEquivQuotSMul (crysCocycles L.ρ) I).length_eq,
        (equivFinsuppOfBasisRight (M := O ⧸ I) (finBasis O (crysCocycles L.ρ))).length_eq]
      simp [I]
    _ ≤ m * (finrank O L * (2 * k)) := mod_cast by linarith [Nat.mul_le_mul_right k h_rank]
    _ ≤ m * y := mul_le_mul_right (mod_cast hy) _

end New.Selmer

/-!
## The defect of a crystalline lattice with jumps in a window

`New.Lift.FitsWindows η ε b W U` says that the jump set `U` lies in the union of the low window
`[-η, η]` and the far window `ε [b, b + W]`.
-/

section CrystallineBound

open New Lift Nat Module Finset Period Real

/-- The crystalline loss `crystallineLoss h b ℓ` is the `ℓ`-adic valuation of `(2 b)!` times the
`h³`-th power of the product of the positive integers in `(b - 30 h³, b + 30 h³]`. If `ℓ ^ n`
divides this number, then `n ≤ crystallineLoss h b ℓ`. -/
lemma New.Selmer.le_crystallineLoss_of_pow_dvd {ℓ h b n : ℕ} [ThePrime ℓ]
    (hn : ℓ ^ n ∣ (2 * b)! * (∏ k ∈ Ioc (b - 30 * h ^ 3) (b + 30 * h ^ 3), k) ^ h ^ 3) :
    n ≤ crystallineLoss h b ℓ := by
  rwa [crystallineLoss, ← padicValNat_dvd_iff_le (by simp [factorial_ne_zero, prod_eq_zero_iff])]

/-- The bound `2 b < ℓ (crystallineLoss h b ℓ + 1)` on the crystalline loss `crystallineLoss h b ℓ`,
the `ℓ`-adic valuation of `(2 b)! (∏ k) ^ h³`, where `k` runs over the positive integers in
`(b - 30 h³, b + 30 h³]`. The factor `(2 b)!` alone gives it. -/
lemma New.Selmer.two_mul_lt_mul_crystallineLoss_succ {ℓ : ℕ} [hp : ThePrime ℓ] (h b : ℕ) :
    2 * b < ℓ * (crystallineLoss h b ℓ + 1) := by
  have h_val : padicValNat ℓ (2 * b)! ≤ crystallineLoss h b ℓ :=
    le_crystallineLoss_of_pow_dvd (pow_padicValNat_dvd.mul_right _)
  have h_div : 2 * b / ℓ ≤ padicValNat ℓ (2 * b)! := by
    rw [← padicValNat_mul_div_factorial, padicValNat_factorial_mul]
    exact Nat.le_add_left _ _
  calc 2 * b < ℓ * (2 * b / ℓ + 1) := lt_mul_div_succ _ hp.out.pos
    _ ≤ ℓ * (crystallineLoss h b ℓ + 1) := by grw [h_div, h_val]

/-- If `ℓ` divides some positive integer in `(b - 30 h³, b + 30 h³]`, then the crystalline loss
`crystallineLoss h b ℓ` is at least `h³`. -/
lemma New.Selmer.cube_le_crystallineLoss_of_dvd {ℓ h b n : ℕ} [ThePrime ℓ]
    (hn : n ∈ Ioc (b - 30 * h ^ 3) (b + 30 * h ^ 3)) (hℓ : ℓ ∣ n) : h ^ 3 ≤ crystallineLoss h b ℓ :=
  le_crystallineLoss_of_pow_dvd
    ((pow_dvd_pow_of_dvd (hℓ.trans (dvd_prod_of_mem _ hn)) _).mul_left _)

/-- If `H ≤ 4 b` and `2 log (4 b) < m`, then `⌊log_ℓ H⌋ < m`, because `log ℓ ≥ 1 / 2`. -/
lemma New.Selmer.natLog_lt_of_two_mul_log_lt {ℓ H b m : ℕ} [hp : ThePrime ℓ]
    (hm : 2 * Real.log (4 * b : ℝ) < m) (hH : H ≤ 4 * b) : ℓ.log H < m := by
  have h_half : (2 : ℝ)⁻¹ ≤ Real.log ℓ := by
    grw [← hp.out.two_le, cast_two, ← one_sub_inv_le_log_of_pos two_pos]
    norm_num
  have h_nonneg : 0 ≤ Real.log (4 * b : ℝ) := by exact_mod_cast log_natCast_nonneg (4 * b)
  rw [← Nat.cast_lt (α := ℝ)]
  calc (ℓ.log H : ℝ) ≤ ℓ.log (4 * b) := by grw [hH]
    _ ≤ logb ℓ (4 * b : ℕ) := natLog_le_logb _ _
    _ = Real.log (4 * b : ℝ) / Real.log ℓ := by simp [logb]
    _ ≤ Real.log (4 * b : ℝ) / 2⁻¹ := by gcongr
    _ = 2 * Real.log (4 * b : ℝ) := by ring
    _ < m := hm

/-- Suppose that `ℓ > G + δ + n` divides no integer in `(b - c, b + c]` and that `δ + n < c`. Then
`NoMultipleNear ℓ n a` holds for `a = b + δ` and for `a = G + δ`: `ℓ` divides no nonzero integer
within `n` of `0` or `± a`. -/
lemma New.Selmer.noMultipleNear_of_forall_not_dvd {ℓ n G b c δ a : ℕ} (h_large : G + δ + n < ℓ)
    (hc : δ + n < c) (h_not : ∀ u ∈ Ioc (b - c) (b + c), ¬ℓ ∣ u) (ha : a = b + δ ∨ a = G + δ) :
    Lift.NoMultipleNear ℓ n a := by
  intro u hu₀ hu h_dvd
  -- a nonzero multiple of `ℓ` is too large for the windows at `0` and `± (G + δ)`
  have h_le : ℓ ≤ u.natAbs := Int.natAbs_le_of_dvd_ne_zero h_dvd hu₀
  refine h_not u.natAbs ?_ (Int.natCast_dvd.mp h_dvd)
  simp only [abs_le, mem_Ioc] at hu ⊢
  omega

/-- The size conditions of the crystalline bound: `Q² ≪ h`, `h³ ≪ G`, `h³ G ≪ b`, `log b ≪ m` and
`Q η ≪ h³`, with `δ < η`. Here `A ≪ B` stands for `99 A ≤ B`, except in the logarithmic one. -/
structure New.Selmer.CrystallineSizes (Q m h G b δ η W : ℕ) : Prop where
  /-- The bound `Q` for small primes is positive. -/
  bound_pos : 0 < Q
  /-- `Q² ≪ h`, with room for the width `W` of the far windows and for `m`. -/
  sq_le : 99 * (Q * Q + (W + 1) * Q + Q + W + m) ≤ h
  /-- `h³ ≪ G`. -/
  cube_le : 99 * h ^ 3 ≤ G
  /-- `h³ G ≪ b`. -/
  mul_cube_le : 99 * (G * h ^ 3 + G) ≤ b
  /-- `2 log (4 b) < m`. -/
  log_lt : 2 * Real.log (4 * b : ℝ) < m
  /-- The shift `δ` of the far windows is less than the radius `η` of the low window. -/
  shift_lt : δ < η
  /-- `Q η ≪ h³`, with room for `W Q` and `h`. -/
  low_le : 99 * ((η + W) * Q + η + h) ≤ h ^ 3

/-- The lattice `L` has few low jumps: at each embedding the negative members of `U` and `U'` are
at most `-h / 2`, and at most `μ` jumps of `L` lie in `[-η, η]`. -/
structure New.Selmer.HasFewLowJumps {ℓ : ℕ} [ThePrime ℓ] {Γ : Type} [Group Γ] [OverGp Γ ℓ]
    {O : CoeffRing ℓ} (L : GalLattice O Γ) (h μ η : ℕ) (U U' : (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ) :
    Prop where
  /-- The negative members of `U g` and `U' g` are at most `-h / 2`. -/
  two_mul_le (g : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) (u : ℤ) (hu : u < 0) (h_mem : u ∈ U g ∨ u ∈ U' g) :
    2 * u ≤ -h
  /-- At most `μ` jumps of `L` at `g`, counted with multiplicity, lie in `[-η, η]`. -/
  sum_jump_le (g : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) : ∑ u ∈ Icc (-η : ℤ) η, jump L.ρ g u ≤ μ

/-- `LettersReadThick k letter th ε Q h T s`: for embeddings `g` indexed by `ι`, with thickness
`th g` and sign `ε g`, the value `letter g` in `ℂ_ℓ` determines both by the functions `T` and `s`,
at thick `g` and, if `Q < ℓ`, at every `g`. Here `k` is a Kummer chart, the prime `ℓ` is small if
`ℓ ≤ Q`, and `h` bounds the ramification. The degree of `k` is the index of `Γ`, the chart is
unramified with `ℓ ≥ 7`, or `ℓ ≤ Q` and all signs agree; for `ℓ ≤ Q` thick letters are sparse. -/
structure New.Selmer.LettersReadThick {ℓ : ℕ} [ThePrime ℓ] {Γ : GroupOverGp ℓ}
    (k : KummerChart Γ) {ι : Type} (letter : ι → ℂ_[ℓ]) (th : ι → Prop) (ε : ι → ℤˣ) (Q h : ℕ)
    (T : ℂ_[ℓ] → Prop) (s : ℂ_[ℓ] → ℤˣ) : Prop where
  /-- The degree `e f` of the chart is the index of the image of `Γ` in `G_ℓ`. -/
  e_mul_f_eq_index : k.e * k.f = Γ.overGp.toGp.range.index
  /-- The ramification `e` of the chart is at most `h`. -/
  e_le : k.e ≤ h
  /-- The letter reads thickness at thick embeddings, and at all embeddings if `Q < ℓ`. -/
  thick_iff (g : ι) (hg : th g ∨ Q < ℓ) : th g ↔ T (letter g)
  /-- The letter reads the sign at thick embeddings, and at all embeddings if `Q < ℓ`. -/
  sign_eq (g : ι) (hg : th g ∨ Q < ℓ) : ε g = s (letter g)
  /-- The chart is unramified with `ℓ ≥ 7`, or `ℓ ≤ Q` and all letters have the same sign. -/
  isUnramified_or_sign_eq : k.IsUnramified ∧ 7 ≤ ℓ ∨ ℓ ≤ Q ∧ ∀ z z' : ℂ_[ℓ], s z = s z'
  /-- For `ℓ ≤ Q` no three thick letters, that is letters with `T`, follow one another at
  distances `≤ log_ℓ h³` in an orbit of `z ↦ z ^ ℓ`. -/
  not_thick_pow (hℓ : ℓ ≤ Q) (z : ℂ_[ℓ]) (a : ℕ) (ha : a ∈ Icc 1 (ℓ.log (h ^ 3))) (a' : ℕ)
    (ha' : a' ∈ Icc 1 (ℓ.log (h ^ 3))) (hz : T z) (hz' : T (z ^ ℓ ^ a)) : ¬T (z ^ ℓ ^ (a + a'))

open scoped Classical in
/-- Let `k` be a Kummer chart of `Γ`. Its letters `i` are the units of `𝔽_{ℓ^f}`, and
`ω = theta (k.letterTeich i)` is the root of unity in `ℂ_ℓ` that Fontaine's map `θ` gives to the
Teichmüller lift of `i`; `ζ` in `O` has `ζ ^ (ℓ ^ f - 1) = 1`. `FitsWindows η ε a W V` says
`V ⊆ [-η, η] ∪ ε · [a, a + W]`. Let the jump sets `U g` fit the windows with sign `ε g`, with
`a = b + δ` at thick `g` (`th g`) and `a = G + δ` at thin ones, and let `g ζ` determine thickness
and sign through `T` and `s` at thick `g`, and at all `g` if `Q < ℓ`. Then `k.letterJumps ζ U i`,
the union of `{0}` and the `U g` with `g ζ = ω`, fits the windows given by `T ω` and `s ω`, with the
low window widened to `[-2 G, 2 G]` if `ℓ ≤ Q`: it holds the old low window as `η ≤ G`, and the far
windows of the thin `g` as `δ + W ≤ G`. -/
lemma New.Selmer.fitsWindows_letterJumps {ℓ : ℕ} [ThePrime ℓ] [Γ : GroupOverGp ℓ]
    {O : CoeffRing ℓ} {k : KummerChart Γ} {ζ : k.LetterRoot O} {Q G b δ η W : ℕ}
    {th : (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Prop} {ε : (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → ℤˣ}
    {U : (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ} {T : ℂ_[ℓ] → Prop} {s : ℂ_[ℓ] → ℤˣ}
    (h_thick : ∀ g : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ], th g ∨ Q < ℓ → (th g ↔ T (g ζ)))
    (h_sign : ∀ g : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ], th g ∨ Q < ℓ → ε g = s (g ζ))
    (hU : ∀ g : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ], FitsWindows η (ε g) ((if th g then b else G) + δ) W (U g))
    (hη : η ≤ G) (hW : δ + W ≤ G) (i : k.Letter) :
    FitsWindows (if ℓ ≤ Q then 2 * G else η) (s (theta (k.letterTeich i)))
      (if T (theta (k.letterTeich i)) then b + δ else G + δ) W (k.letterJumps ζ U i) := by
  intro u hu
  obtain rfl | hu := mem_insert.1 hu
  · exact .inl ⟨by omega, by omega⟩
  obtain ⟨g, h_letter, hu_g⟩ :
      ∃ g : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ], g ζ = theta (k.letterTeich i) ∧ u ∈ U g := by
    simpa using mem_biUnion.1 hu
  -- `u` is in the low window or in the far window of `g`, as `FitsWindows` says.
  have h_win := hU g u hu_g
  rw [← h_letter]
  by_cases h_read : th g ∨ Q < ℓ
  · -- The letter reads `th g` and `ε g`, so only the low window changes.
    simp only [← h_sign g h_read, ← h_thick g h_read, ← ite_add]
    exact h_win.imp_left fun h_low ↦ by split_ifs <;> omega
  · -- The embedding is thin and `ℓ ≤ Q`: both windows of `g` lie in `[-2 G, 2 G]`.
    obtain ⟨h_thin, hℓ⟩ := not_or.1 h_read
    rw [ite_eq_right h_thin] at h_win
    rw [ite_eq_left (not_lt.1 hℓ)]
    omega

/-- Assume the size conditions `CrystallineSizes`, that the ramification index `e` of the Kummer
chart `k` is at most `h`, and that `2 (b + δ) < h² K`. Then `20 (⌊log_ℓ h³⌋ + 1 + d) · 2 G + ⌊log_ℓ
(2 (b + δ + 10 G))⌋ ≤ K`, where `d = k.differentBound` is `0` if `e = 1` and `v_ℓ(e) + 1`
otherwise. -/
lemma New.Selmer.CrystallineSizes.differentBound_mul_add_log_le {ℓ : ℕ} [ThePrime ℓ]
    [Γ : GroupOverGp ℓ] {k : KummerChart Γ} {Q m h G b δ η W K : ℕ}
    (h_sizes : CrystallineSizes Q m h G b δ η W) (he : k.e ≤ h) (hK : 2 * (b + δ) < h ^ 2 * K) :
    20 * (ℓ.log (h ^ 3) + 1 + k.differentBound) * (2 * G) +
      ℓ.log (2 * (b + δ + 5 * (2 * G))) ≤ K := by
  -- The bracket is at most `h`, the logarithm at most `h G`, and `41 G h ≤ K` because
  -- `198 G h³ ≤ 2 b < h² K`.
  have ⟨_, (hQ : 99 * (Q * Q + (W + 1) * Q + Q + W + m) ≤ h), (hG : 99 * h ^ 3 ≤ G),
    (hb : 99 * (G * h ^ 3 + G) ≤ b), _, (hδ : δ < η),
    (hη : 99 * ((η + W) * Q + η + h) ≤ h ^ 3)⟩ := h_sizes
  have h_log {H : ℕ} (hH : H ≤ 4 * b) : ℓ.log H < m :=
    natLog_lt_of_two_mul_log_lt h_sizes.log_lt hH
  have h_bracket : ℓ.log (h ^ 3) + 1 + k.differentBound ≤ h := by
    have h_cube : ℓ.log (h ^ 3) < m := h_log (by omega)
    have h_val : padicValNat ℓ k.e < m := (padicValNat_le_nat_log k.e).trans_lt (h_log (by omega))
    grw [KummerChart.differentBound, ite_le_sup]
    omega
  have h_last : ℓ.log (2 * (b + δ + 5 * (2 * G))) ≤ h * G :=
    calc _ ≤ m := (h_log (by omega)).le
      _ ≤ h := by omega
      _ ≤ h * G := Nat.le_mul_of_pos_right h (by omega)
  grw [h_bracket, h_last]
  nlinarith only [hK, hb]

/-- The exponent for small primes `ℓ ≤ Q`. Let `Γ → G_ℓ` be an open embedding. The hypothesis
`h_sizes` is the list of inequalities `Q² ≪ h`, `m ≪ h`, `W Q ≪ h`, `h³ ≪ G`, `h³ G ≪ b`,
`Q η ≪ h³`, `2 log (4 b) < m` and `δ < η`. `InClass ⊤ ⊥ U` is the class of crystalline lattices
whose Hodge–Tate jumps at each embedding `g` of `O` lie in `U g`; let `L` lie in the class for `U'`.
Let `k` be a Kummer chart of `Γ`. The letters `i` of `k` are the units of `𝔽_{ℓ^f}`; `ζ` in `O` has
`ζ ^ (ℓ ^ f - 1) = 1`, and `k.letterJumps ζ U i` is the union of `{0}` and the sets `U g` for the
embeddings `g : O → ℂ_ℓ` such that `g ζ` is the Teichmüller root of unity of `i`. The predicate `T`
(thick) and the sign `s` on `ℂ_ℓ` satisfy `LettersReadThick`: the ramification of `k` is at most
`h`, the chart is unramified with `ℓ ≥ 7` or `s` is constant, and thick values are sparse along
`z ↦ z ^ ℓ`; `ι`, `letter`, `th`, `ε` enter only through `h_chart`. At each letter let the jumps
from `U` and `U'` lie in the union of `[-2 G, 2 G]` and opposite far windows of width `W`, starting
at `b + δ` if the letter is thick and at `G + δ` otherwise. If `2 (b + δ) < h² K`, then
`ℓ ^ (10⁴ K (⌊log_ℓ h³⌋ + 1))` times any crystalline cocycle of `L` is orthogonal under cup products
to the class for `U`. -/
lemma New.Selmer.LettersReadThick.hasCupExponent_of_le {ℓ : ℕ} [hp : ThePrime ℓ]
    [Γ : GroupOverGp ℓ] [TopologicalSpace Γ] {O : CoeffRing ℓ} {L : GalLattice O Γ}
    {U U' : (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ} {k : KummerChart Γ} {ι : Type} {letter : ι → ℂ_[ℓ]}
    {th : ι → Prop} {ε : ι → ℤˣ} {Q m h G b δ η W K : ℕ} {T : ℂ_[ℓ] → Prop} [DecidablePred T]
    {s : ℂ_[ℓ] → ℤˣ} (h_chart : LettersReadThick k letter th ε Q h T s)
    (h_sizes : CrystallineSizes Q m h G b δ η W) (hℓ : ℓ ≤ Q) (hK : 2 * (b + δ) < h ^ 2 * K)
    (ζ : k.LetterRoot O) (h_open : Topology.IsOpenEmbedding Γ.overGp.toGp) (hL : InClass ⊤ ⊥ U' L)
    (hU : ∀ i : k.Letter, FitsWindows (2 * G) (-s (theta (k.letterTeich i)))
      (if T (theta (k.letterTeich i)) then b + δ else G + δ) W (k.letterJumps ζ U i))
    (hU' : ∀ i : k.Letter, FitsWindows (2 * G) (s (theta (k.letterTeich i)))
      (if T (theta (k.letterTeich i)) then b + δ else G + δ) W (k.letterJumps ζ U' i)) :
    HasCupExponent (InClass ⊤ ⊥ U) L (10 ^ 4 * (K * (ℓ.log (h ^ 3) + 1))) := by
  -- The thick letters are sparse, with gaps measured up to `J = ⌊log_ℓ h³⌋`, so
  -- `hasCupExponent_sparse_thick` applies with low window `[-2 G, 2 G]` and costs `2 K` and `K`.
  have ⟨_, hQ, (hG : 99 * h ^ 3 ≤ G), (hb : 99 * (G * h ^ 3 + G) ≤ b), _, hδ, hη⟩ := h_sizes
  have he : k.e ≤ h := h_chart.e_le
  have h_pow : h ^ 3 ≤ ℓ ^ (ℓ.log (h ^ 3) + 1) := (lt_pow_succ_log_self hp.out.one_lt _).le
  have h_depth : k.e * (2 * (b + δ + 5 * (2 * G))) ≤ ℓ ^ (ℓ.log (h ^ 3) + 1) * (2 * K) := by
    have h_le : 2 * (b + δ + 5 * (2 * G)) ≤ 2 * (2 * (b + δ)) := by omega
    grw [← h_pow, h_le, hK, he]
    linarith
  have h_far : 10 * ℓ ^ ℓ.log (h ^ 3) * (2 * G) ≤ b + δ := by
    grw [pow_log_le_self _ (by omega)]
    linarith
  have h_sign : k.IsUnramified ∧ 7 ≤ ℓ ∧ 10 * ℓ ^ ℓ.log (h ^ 3) * (2 * G) ≤ b + δ ∨
      (∀ i i' : k.Letter, s (theta (k.letterTeich i)) = s (theta (k.letterTeich i'))) ∧
        8 * k.e ≤ ℓ ^ (ℓ.log (h ^ 3) + 1) := by
    obtain ⟨h_un, h_seven⟩ | ⟨-, h_same⟩ := h_chart.isUnramified_or_sign_eq
    · exact .inl ⟨h_un, h_seven, h_far⟩
    · exact .inr ⟨fun i i' ↦ h_same _ _, h_pow.trans' (by omega)⟩
  have h_gaps : 1 ≤ ℓ.log (h ^ 3) := Nat.log_pos hp.out.one_lt (by omega)
  have h_sparse (i : k.Letter) : ∀ a ∈ Icc 1 (ℓ.log (h ^ 3)), ∀ a' ∈ Icc 1 (ℓ.log (h ^ 3)),
      T (theta (k.letterTeich i)) → T (theta (k.letterTeich ((k.letterFrob ^ a) i))) →
        ¬T (theta (k.letterTeich ((k.letterFrob ^ (a + a')) i))) := by
    -- The Frobenius on letters is `z ↦ z ^ ℓ`.
    have h_shift (t : ℕ) : ⇑(k.letterFrob ^ t) = fun i ↦ i ^ ℓ ^ t :=
      (k.letterFrob.coe_pow t).trans (pow_iterate ℓ t)
    simpa [h_shift] using h_chart.not_thick_pow hℓ (theta (k.letterTeich i))
  have h_exp : HasCupExponent (InClass ⊤ ⊥ U) L (10 ^ 3 * (2 * K + (ℓ.log (h ^ 3) + 1) * K)) :=
    k.hasCupExponent_sparse_thick ζ h_open (by omega) hL hU hU' (by omega) h_gaps h_sparse h_sign
      h_depth (h_sizes.differentBound_mul_add_log_le he hK)
  exact h_exp.mono (by lia)

/-- The exponent for large primes `ℓ > Q` and large loss `v ≥ h³`. Let `Γ → G_ℓ` be an open
embedding and `ℓ ≥ 7`. The hypothesis `h_sizes` is the list of inequalities `Q² ≪ h`, `m ≪ h`,
`W Q ≪ h`, `h³ ≪ G`, `h³ G ≪ b`, `Q η ≪ h³`, `2 log (4 b) < m` and `δ < η`. `InClass ⊤ ⊥ U` is the
class of crystalline lattices whose Hodge–Tate jumps at each embedding `g` of `O` lie in `U g`; let
`L` lie in the class for `U'`. Let `k` be a Kummer chart of `Γ`, unramified. The letters `i` of `k`
are the units of `𝔽_{ℓ^f}`; `ζ` in `O` has `ζ ^ (ℓ ^ f - 1) = 1`, and `k.letterJumps ζ U i` is the
union of `{0}` and the sets `U g` for the embeddings `g : O → ℂ_ℓ` such that `g ζ` is the
Teichmüller root of unity of `i`. At each letter let the jumps from `U` and `U'` lie in the union of
`[-η, η]` and the far windows `-s i · [a, a + W]` and `s i · [a, a + W]`, where `a = b + δ` if `T i`
holds and `a = G + δ` otherwise. If `2 b < ℓ (v + 1)` and `2 v < (K + 1) Q`, then `ℓ ^ (10⁴ K m)`
times any crystalline cocycle of `L` is orthogonal under cup products to the class for `U`. -/
lemma New.Selmer.CrystallineSizes.hasCupExponent_of_cube_le {ℓ : ℕ} [ThePrime ℓ]
    [Γ : GroupOverGp ℓ] [TopologicalSpace Γ] {O : CoeffRing ℓ} {L : GalLattice O Γ}
    {Q m h G b δ η W v K : ℕ} {U U' : (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ}
    (h_sizes : CrystallineSizes Q m h G b δ η W) {k : KummerChart Γ} (h_un : k.IsUnramified)
    (h_seven : 7 ≤ ℓ) (hℓ : Q < ℓ) (ζ : k.LetterRoot O)
    (h_open : Topology.IsOpenEmbedding Γ.overGp.toGp) (hL : InClass ⊤ ⊥ U' L)
    {T : k.Letter → Prop} [DecidablePred T] {s : k.Letter → ℤˣ}
    (hU : ∀ i : k.Letter,
      FitsWindows η (-s i) (if T i then b + δ else G + δ) W (k.letterJumps ζ U i))
    (hU' : ∀ i : k.Letter,
      FitsWindows η (s i) (if T i then b + δ else G + δ) W (k.letterJumps ζ U' i))
    (h_loss : 2 * b < ℓ * (v + 1)) (hv : h ^ 3 ≤ v) (hK : 2 * v < K * Q + Q) :
    HasCupExponent (InClass ⊤ ⊥ U) L (10 ^ 4 * (K * m)) := by
  have ⟨_, hQ, hG, (hb : 99 * (G * h ^ 3 + G) ≤ b), _, (hδ : δ < η),
    (hη : 99 * ((η + W) * Q + η + h) ≤ h ^ 3)⟩ := h_sizes
  have hQ_le : Q ≤ h ^ 3 := by omega
  -- `K` is large enough for `hasCupExponent_any_pattern`.
  have hbK : b + δ < K * ℓ ^ 2 := by nlinarith only [h_loss, hℓ, hb, hη, hδ, hv, hK, hQ_le]
  have hGK : 2 * (G + δ) < K * ℓ := by nlinarith only [h_loss, hℓ, hb, hη, hδ, hv, hK, hQ_le]
  have hWK : W + 4 * η ≤ K := by nlinarith only [hη, hv, hK, hQ_le]
  have h_exp :
      HasCupExponent (InClass ⊤ ⊥ U) L (10 ^ 4 * (K + ℓ.log (2 * (b + δ + (W + 4 * η))))) :=
    k.hasCupExponent_any_pattern ζ h_open h_un h_seven (by omega) le_rfl hL hU hU' (by omega)
      (Nat.add_le_add_right (by omega) δ) hbK hGK hWK
  have h_log : ℓ.log (2 * (b + δ + (W + 4 * η))) < m :=
    natLog_lt_of_two_mul_log_lt h_sizes.log_lt (by omega)
  have hK_pos : 1 ≤ K := by omega
  have h_add : K + ℓ.log (2 * (b + δ + (W + 4 * η))) ≤ K * m := by nlinarith only [h_log, hK_pos]
  exact h_exp.mono (Nat.mul_le_mul_left _ h_add)

/-- The gap condition for small loss. Under the size conditions `h_sizes`, let `2 b < ℓ (v + 1)`
with `v < h³`, and let `ℓ` divide no integer in `(b - 30 h³, b + 30 h³]`. Then `ℓ` divides no
nonzero integer within `6 (2 (v + 1) + η + W)` of `0` or `± a`, for `a = b + δ` and `a = G + δ`. -/
lemma New.Selmer.CrystallineSizes.noMultipleNear {ℓ Q m h G b δ η W v a : ℕ}
    (h_sizes : CrystallineSizes Q m h G b δ η W) (h_loss : 2 * b < ℓ * (v + 1)) (hv : v < h ^ 3)
    (h_not : ∀ u ∈ Ioc (b - 30 * h ^ 3) (b + 30 * h ^ 3), ¬ℓ ∣ u) (ha : a = b + δ ∨ a = G + δ) :
    NoMultipleNear ℓ (6 * (2 * (v + 1) + η + W)) a := by
  have ⟨_, (hQ : 99 * (Q * Q + (W + 1) * Q + Q + W + m) ≤ h), (hG : 99 * h ^ 3 ≤ G),
    (hb : 99 * (G * h ^ 3 + G) ≤ b), _, (hδ : δ < η),
    (hη : 99 * ((η + W) * Q + η + h) ≤ h ^ 3)⟩ := h_sizes
  have h_large : 9 * G ≤ ℓ := by nlinarith only [h_loss, hv, hb]
  have h_lt : G + δ + 6 * (2 * (v + 1) + η + W) < ℓ := by omega
  exact noMultipleNear_of_forall_not_dvd h_lt (by omega) h_not ha

/-- Let `Γ → G_ℓ` be an open embedding, `ℓ ≥ 7`, and `O` the ring of integers of a finite Galois
extension of `ℚ_ℓ`. The hypothesis `h_sizes` is the list of inequalities `Q² ≪ h`, `m ≪ h`,
`W Q ≪ h`, `h³ ≪ G`, `h³ G ≪ b`, `Q η ≪ h³`, `2 log (4 b) < m` and `δ < η`. `InClass ⊤ ⊥ U` is the
class of crystalline lattices whose Hodge–Tate jumps at each embedding `g` of `O` lie in `U g`; let
the `O`-lattice `L` lie in the class for `U'`. Let `k` be a Kummer chart of `Γ`, unramified and with
`f = [G_ℓ : Γ]`. The letters `i` of `k` are the units of `𝔽_{ℓ^f}`; `ζ` in `O` has
`ζ ^ (ℓ ^ f - 1) = 1`, and `k.letterJumps ζ U i` is the union of `{0}` and the sets `U g` for the
embeddings `g : O → ℂ_ℓ` such that `g ζ` is the Teichmüller root of unity of `i`. Assume:
* `hU`, `hU'`: at each letter the jumps from `U` and `U'` lie in the union of `[-η, η]` and the far
  windows `-s i · [a, a + W]` and `s i · [a, a + W]`, where `a = b + δ` if `T i` holds and
  `a = G + δ` otherwise;
* `h_jumps`: either the negative members of all `U g` and `U' g` are at most `-h / 2` and at most
  `μ` jumps of `L` at each `g` lie in `[-η, η]`, or every `U' g` lies in `[-η, 0]`;
* `2 b < ℓ (v + 1)`, `v < h³` and `2 v < (K + 1) Q`;
* `h_gap`: `ℓ` divides no nonzero integer within `6 (2 (v + 1) + η + W)` of `0` or `± a`.

Then the defect of `L` for the class of `U`, the length of the crystalline cocycles modulo those
orthogonal, under cup products, to the crystalline cocycles of the lattices in the class, normalised
so that `O / ℓ` has length `1`, is at most `[G_ℓ : Γ] · y` for any
`y ≥ 10⁵ (rank L · K m + μ v)`. -/
lemma New.Selmer.normLength_dualDefect_le_of_noMultipleNear {ℓ : ℕ} [ThePrime ℓ] [Γ : GroupOverGp ℓ]
    [TopologicalSpace Γ] {O : CoeffRing ℓ} {L : GalLattice O Γ} {Q m h μ G b δ η W v K : ℕ}
    {U U' : (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ} (h_sizes : CrystallineSizes Q m h G b δ η W)
    {k : KummerChart Γ} (h_un : k.IsUnramified) (h_seven : 7 ≤ ℓ)
    (h_index : k.f = Γ.overGp.toGp.range.index) (ζ : k.LetterRoot O)
    (h_open : Topology.IsOpenEmbedding Γ.overGp.toGp) (hL : InClass ⊤ ⊥ U' L)
    {T : k.Letter → Prop} [DecidablePred T] {s : k.Letter → ℤˣ}
    (hU : ∀ i : k.Letter,
      FitsWindows η (-s i) (if T i then b + δ else G + δ) W (k.letterJumps ζ U i))
    (hU' : ∀ i : k.Letter,
      FitsWindows η (s i) (if T i then b + δ else G + δ) W (k.letterJumps ζ U' i))
    (h_jumps : HasFewLowJumps L h μ η U U' ∨ ∀ g : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ], U' g ⊆ Icc (-η : ℤ) 0)
    (h_loss : 2 * b < ℓ * (v + 1)) (hv : v < h ^ 3) (hK : 2 * v < K * Q + Q)
    (h_gap : ∀ i : k.Letter,
      NoMultipleNear ℓ (6 * (2 * (v + 1) + η + W)) (if T i then b + δ else G + δ : ℕ))
    {y : NNReal} (hy : (10 ^ 5 * (finrank O L * (K * m) + μ * v) : ℕ) ≤ y) :
    O.normLength (dualDefect (InClass ⊤ ⊥ U) L) ≤ Γ.overGp.toGp.range.index * y := by
  have ⟨hQ_pos, (hQ : 99 * (Q * Q + (W + 1) * Q + Q + W + m) ≤ h), (hG : 99 * h ^ 3 ≤ G),
    (hb : 99 * (G * h ^ 3 + G) ≤ b), h_log, (hδ : δ < η),
    (hη : 99 * ((η + W) * Q + η + h) ≤ h ^ 3)⟩ := h_sizes
  have h_height (i : k.Letter) :
      (if T i then b + δ else G + δ) + W + η ≤ (ℓ - 3) * (2 * (v + 1)) := by
    grw [ite_le_sup, mul_left_comm, tsub_mul]
    omega
  have h_far (i : k.Letter) : 6 * (2 * (v + 1) + η + W) < if T i then b + δ else G + δ := by
    split_ifs <;> omega
  -- The two bounds of `dualDefect_eq_zero_and_dualDefect_le`, for the length `2 (v + 1)`. The
  -- defect vanishes if `U` and `U'` avoid `[-2 (v + 1), 0)` or `U'` lies in `[-η, 0]`. If at most
  -- `n` jumps lie in `[-η, η]`, it is at most `11 f (n (2 (v + 1) + 1) + rank L · (W + 1))` times
  -- the length of `O / ℓ`.
  obtain ⟨h_zero, h_defect_le⟩ :=
    k.dualDefect_eq_zero_and_dualDefect_le ζ h_open h_un (by omega) h_height (by omega) h_far h_gap
      hL hU hU'
  by_cases h_few : h / 5 ≤ v ∧ HasFewLowJumps L h μ η U U'
  · -- At most `μ` low jumps, and `⌊h / 5⌋ ≤ v`: the bound `h_defect_le` is at most
    -- `11 f (6 μ v + rank L · K)` times the length of `O / ℓ`, and `f` is the index.
    obtain ⟨hv_large, h_low⟩ := h_few
    have hW_lt_K : W + 1 ≤ K := Nat.le_of_mul_le_mul_right (by omega) hQ_pos
    have hm_pos : 1 ≤ m :=
      Nat.zero_lt_of_lt (natLog_lt_of_two_mul_log_lt (ℓ := ℓ) h_log (Nat.zero_le _))
    have h_bound : 11 * (k.f * (μ * (2 * (v + 1) + 1) + finrank O L * (W + 1))) ≤
        k.f * (10 ^ 5 * (finrank O L * (K * m) + μ * v)) := by
      grw [show 2 * (v + 1) + 1 ≤ 6 * v by omega, ← hm_pos, hW_lt_K]
      ring_nf
      omega
    -- The normalised length of `O / ℓ` is `1`.
    grw [h_defect_le μ h_low.sum_jump_le, O.normLength_natCast_mul, ← hy, ← h_index, h_bound]
    simp
  · -- Otherwise `U` and `U'` avoid `[-2 (v + 1), 0)`, since `h / 2 > 2 (v + 1)`, or `U'` lies in
    -- `[-η, 0]`; in both cases the defect vanishes.
    have h_vanish : dualDefect (InClass ⊤ ⊥ U) L = 0 := by
      refine h_zero (h_jumps.imp_left fun h_low g u h_mem hu ↦ ?_)
      have hv_small : v < h / 5 := not_le.1 fun hv' ↦ h_few ⟨hv', h_low⟩
      obtain ⟨hu_ge, hu_neg⟩ : -(2 * (v + 1) : ℕ) ≤ u ∧ u < 0 := mem_Ico.1 hu
      have hu_le : 2 * u ≤ -h := h_low.two_mul_le g u hu_neg h_mem
      omega
    simp [h_vanish]

open scoped Classical in
/-- Let `Γ → G_ℓ = Gal(ℚ̄_ℓ / ℚ_ℓ)` be an open embedding (`h_open`), `O` the ring of integers of a
finite Galois extension of `ℚ_ℓ`, and `L` a finite free `O`-module with an action of `Γ`. Each
embedding `g` of `O` into `ℂ_ℓ` is thick (`th g`) or thin, has a sign `ε g`, and has finite sets
`U g` and `U' g` of allowed Hodge–Tate jumps; `InClass ⊤ ⊥ U` is the class of crystalline lattices
whose jumps at each `g` lie in `U g`. Assume:
* `h_sizes`: `Q² ≪ h`, `h³ ≪ G`, `h³ G ≪ b`, `Q η ≪ h³`, `2 log (4 b) < m` and `δ < η`, in the
  explicit form of `CrystallineSizes`;
* `hU`, `hU'`: with `a = b + δ` at thick `g` and `a = G + δ` at thin `g`, the set `U g` lies in
  `[-η, η] ∪ -ε g · [a, a + W]` and `U' g` lies in `[-η, η] ∪ ε g · [a, a + W]`;
* `hL`: `L` is crystalline with jumps in `U'`;
* `h_jumps`: either the negative members of all `U g` and `U' g` are at most `-h / 2` and at most
  `μ` jumps of `L` at each `g` lie in `[-η, η]`, or every `U' g` lies in `[-η, 0]`;
* `h_chart`: `k` is a Kummer chart of `Γ` of degree `e f = [G_ℓ : Γ]` and ramification `e ≤ h`, and
  `ζ` in `O` has `ζ ^ (ℓ ^ f - 1) = 1`. At thick `g`, and at all `g` if `Q < ℓ`, thickness is
  `T (g ζ)` and the sign is `s (g ζ)`. The chart is unramified with `ℓ ≥ 7`, or `ℓ ≤ Q` and `s` is
  constant. If `ℓ ≤ Q`, no three values with `T` follow one another at distances at most `log_ℓ h³`
  along `z ↦ z ^ ℓ`;
* `hy`: `y ≥ 10⁵ (rank L · ⌊2 λ / Q⌋ · m + μ λ)`, where `λ = crystallineLoss h b ℓ` is the `ℓ`-adic
  valuation of `(2 b)! (∏ n) ^ h³`, with `n` over the positive integers in `(b - 30 h³, b + 30 h³]`.

The defect `dualDefect (InClass ⊤ ⊥ U) L` is the length of the crystalline cocycles of `L` modulo
those orthogonal, under cup products, to the crystalline cocycles of all lattices in the class.
Normalised so that `O / ℓ` has length `1`, it is at most `[G_ℓ : Γ] · y`. -/
lemma New.Selmer.normLength_dualDefect_le_of_crystallineSizes {ℓ : ℕ} [hp : ThePrime ℓ]
    [Γ : GroupOverGp ℓ] [TopologicalSpace Γ] {O : CoeffRing ℓ} {L : GalLattice O Γ}
    (Q m h μ : ℕ) {G b δ η W : ℕ} {th : (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Prop} {ε : (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → ℤˣ}
    {U U' : (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ} (h_sizes : CrystallineSizes Q m h G b δ η W)
    (hU : ∀ g : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ], FitsWindows η (-ε g) ((if th g then b else G) + δ) W (U g))
    (hU' : ∀ g : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ], FitsWindows η (ε g) ((if th g then b else G) + δ) W (U' g))
    (hL : InClass ⊤ ⊥ U' L)
    (h_jumps : HasFewLowJumps L h μ η U U' ∨ ∀ g : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ], U' g ⊆ Icc (-η : ℤ) 0)
    {y : NNReal}
    (hy : (10 ^ 5 * (finrank O L * (2 * crystallineLoss h b ℓ / Q * m) +
      μ * crystallineLoss h b ℓ) : ℕ) ≤ y)
    (h_open : Topology.IsOpenEmbedding Γ.overGp.toGp)
    (k : KummerChart Γ) (ζ : k.LetterRoot O) {T : ℂ_[ℓ] → Prop} {s : ℂ_[ℓ] → ℤˣ}
    (h_chart : LettersReadThick k (fun g : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ] ↦ g ζ) th ε Q h T s) :
    O.normLength (dualDefect (InClass ⊤ ⊥ U) L) ≤ Γ.overGp.toGp.range.index * y := by
  -- Write `v = crystallineLoss h b ℓ` and `K = ⌊2 v / Q⌋`. If `ℓ ≤ Q` or `v ≥ h³`, a power
  -- `ℓ ^ (10⁴ K x)` with `x ≤ m` carries `crysCocycles` into the annihilator, which gives the
  -- bound. Otherwise `ℓ` divides no nonzero integer near the windows, and
  -- `normLength_dualDefect_le_of_noMultipleNear` applies.
  have hQ : 99 * (Q * Q + (W + 1) * Q + Q + W + m) ≤ h := h_sizes.sq_le
  have hG : 99 * h ^ 3 ≤ G := h_sizes.cube_le
  have hb : 99 * (G * h ^ 3 + G) ≤ b := h_sizes.mul_cube_le
  have hδ : δ < η := h_sizes.shift_lt
  have hη : 99 * ((η + W) * Q + η + h) ≤ h ^ 3 := h_sizes.low_le
  have hη_le : η ≤ G := by omega
  have hW_le : δ + W ≤ G := by omega
  -- Besides `hy`, only these facts about `v` and `K` are used below.
  have h_loss : 2 * b < ℓ * (crystallineLoss h b ℓ + 1) := two_mul_lt_mul_crystallineLoss_succ h b
  have h_cube {n : ℕ} (hn : n ∈ Ioc (b - 30 * h ^ 3) (b + 30 * h ^ 3)) (h_dvd : ℓ ∣ n) :
      h ^ 3 ≤ crystallineLoss h b ℓ := cube_le_crystallineLoss_of_dvd hn h_dvd
  have hK : 2 * crystallineLoss h b ℓ < 2 * crystallineLoss h b ℓ / Q * Q + Q :=
    lt_div_mul_add h_sizes.bound_pos
  generalize crystallineLoss h b ℓ = v at *
  generalize 2 * v / Q = K at *
  -- The windows in terms of the letters.
  have h_winU (i : k.Letter) :
      FitsWindows (if ℓ ≤ Q then 2 * G else η) (-s (theta (k.letterTeich i)))
        (if T (theta (k.letterTeich i)) then b + δ else G + δ) W (k.letterJumps ζ U i) :=
    fitsWindows_letterJumps (s := fun z ↦ -s z) h_chart.thick_iff
      (fun g hg ↦ congrArg Neg.neg (h_chart.sign_eq g hg)) hU hη_le hW_le i
  have h_winU' (i : k.Letter) :
      FitsWindows (if ℓ ≤ Q then 2 * G else η) (s (theta (k.letterTeich i)))
        (if T (theta (k.letterTeich i)) then b + δ else G + δ) W (k.letterJumps ζ U' i) :=
    fitsWindows_letterJumps h_chart.thick_iff h_chart.sign_eq hU' hη_le hW_le i
  -- An exponent `10⁴ K x` with `x ≤ m` is small enough for the bound.
  have h_exp {x : ℕ} (hx : x ≤ m) : finrank O L * (2 * (10 ^ 4 * (K * x) : ℕ)) ≤ y := by
    refine hy.trans' (mod_cast ?_)
    grw [hx]
    ring_nf
    omega
  by_cases hℓ : ℓ ≤ Q
  · -- For small `ℓ` the thick letters are sparse.
    simp only [hℓ, ite_true] at h_winU h_winU'
    have hbK : 2 * (b + δ) < h ^ 2 * K := by
      have h_add : h + δ ≤ b := by omega
      nlinarith only [hK, h_loss, hℓ, hQ, h.le_mul_self, h_add]
    have h_log : ℓ.log (h ^ 3) < m := natLog_lt_of_two_mul_log_lt h_sizes.log_lt (by omega)
    exact normLength_dualDefect_le_of_hasCupExponent hL.isPotentiallyCrystalline (h_exp h_log)
      (h_chart.hasCupExponent_of_le h_sizes hℓ hbK ζ h_open hL h_winU h_winU')
  -- From now on `ℓ > Q`, so the chart is unramified and `ℓ ≥ 7`.
  simp only [hℓ, ite_false] at h_winU h_winU'
  obtain ⟨h_un, h_seven⟩ : k.IsUnramified ∧ 7 ≤ ℓ :=
    h_chart.isUnramified_or_sign_eq.resolve_right fun ⟨h_le, _⟩ ↦ hℓ h_le
  by_cases hv : h ^ 3 ≤ v
  · exact normLength_dualDefect_le_of_hasCupExponent hL.isPotentiallyCrystalline (h_exp le_rfl)
      (h_sizes.hasCupExponent_of_cube_le h_un h_seven (not_le.1 hℓ) ζ h_open hL h_winU h_winU'
        h_loss hv hK)
  -- If `v < h³`, then `ℓ` divides no integer near `b`.
  have h_gap (z : ℂ_[ℓ]) :
      NoMultipleNear ℓ (6 * (2 * (v + 1) + η + W)) (if T z then b + δ else G + δ : ℕ) :=
    h_sizes.noMultipleNear h_loss (not_le.1 hv) (fun u hu h_dvd ↦ hv (h_cube hu h_dvd))
      (ite_eq_or_eq (T z) (b + δ) (G + δ))
  have h_index : k.f = Γ.overGp.toGp.range.index := by
    obtain ⟨-, he_one : k.e = 1, -⟩ := h_un
    rw [← h_chart.e_mul_f_eq_index, he_one, one_mul]
  exact normLength_dualDefect_le_of_noMultipleNear h_sizes h_un h_seven h_index ζ h_open hL
    h_winU h_winU' h_jumps h_loss (not_le.1 hv) hK (fun i ↦ h_gap (theta (k.letterTeich i))) hy

end CrystallineBound
