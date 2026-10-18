import GowersSzemeredi.Proofs15Restriction
import GowersSzemeredi.Proofs15DegenerateRange

/-!
# Lemma 15.5 with a single Fejér selection (Notes L.16)

Lemma 15.5 restricts `B` at random so that almost every surviving
8-arrangement is respected. The printed proof (`Proofs15Restriction`) keeps a
point with the Riesz weight `(1 + cos θ)/2 = |1 + e(θ)|²/4` and iterates
`2^(M−1)` independent stages, `M = 2^(k+4)`, because one stage favours a
respected arrangement only by the factor `1 + 2^(1−M)`. Hence the exponent
`arrangementSelectionExponent k = 2^(2^(k+4)+k+3)`.

Here one stage uses the Fejér weight of order `m`,
`|∑_{a ≤ m} e(a θ)|² / (m + 1)²` (the Riesz weight is `m = 1`). Averaging
over the phase (`fejer_oneStage_average`) counts digit pairs `(a, b)` whose
values `a − b` annihilate every feature:
* a respected arrangement has at least `∑_{j<T} (m+1−j)^M` of them, from the
  multiples `j·ε` of the parity pattern (`fejerValidRelations_card_good`);
* a non-respected arrangement without a dependence in `[−m, m]` has only the
  `(m+1)^M` diagonal ones (`fejerValidRelations_subset_diagonal`), by the
  `m`-range Lemma 15.4 of `Proofs15DegenerateRange`.

With `m + 1 = M·⌈6/(αη)⌉` Bernoulli's inequality gives a gain of
`(T+1)/2 ≥ 3/(αη)` in one stage, at the density cost `(m+1)^(−M)`. The result
(`fejer_arrangement_restriction`) is Lemma 15.5 with exponent
`fejerSelectionExponent k = 2^(k+4)·(k+6)`, and it implies the printed one
(`lemma_15_5_of_fejer_restriction`).

The finite Bernoulli averaging uses `Proofs12BernoulliSelection`. The hyperedge
bookkeeping, parity moment and vertex injectivity are those of
`Proofs15Restriction`.

`FejerArrangementRestriction`, `fejer_arrangement_restriction`,
`fejer_scale_estimate` and `lemma_15_5_of_fejer_restriction` are in
`Proofs15FejerSelectionSide`, outside the final route. -/

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Arrangements as finite hyperedges -/

private def fejerPhaseValue {N k : Nat} [NeZero N]
    (C : SelectionPhase N k) (phi : Point N (k + 1) → ZMod N)
    (z : Point N (k + 1)) : ZMod N :=
  ∑ F, C F * selectionFeatureValue phi F z

attribute [simp] exponential_add

attribute [simp] star_exponential

attribute [simp] exponential_zero

/-! ## Fejér weights of order `m` -/

/-- A Fejér digit: a pair `(a, b)`, whose value is `a − b`. The Riesz digits
`{0, 0, 1, −1}` of Lemma 15.5 are the case `m = 1`. -/
private abbrev FejerDigit (m : Nat) := Fin (m + 1) × Fin (m + 1)

private def fejerDigitInt {m : Nat} (p : FejerDigit m) : Int :=
  ((p.1 : Nat) : Int) - ((p.2 : Nat) : Int)

private lemma fejerDigitInt_bound {m : Nat} (p : FejerDigit m) :
    -(m : Int) ≤ fejerDigitInt p ∧ fejerDigitInt p ≤ m := by
  unfold fejerDigitInt
  have h1 := p.1.isLt
  have h2 := p.2.isLt
  omega

/-- The relation of an integer coefficient pattern on one feature. -/
private def fejerRelationInt {N k : Nat} [NeZero N]
    (eta : selectionIndex k → Int) (F : SelectionFeature k)
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) : ZMod N :=
  ∑ z, (eta z : ZMod N) * selectionFeatureValue phi F (selectionVertex R z)

/-- The Fejér selection weight of order `m`,
`|∑_{a ≤ m} e(a·θ)|² / (m + 1)²`. -/
private def fejerKernelWeight {N k : Nat} [NeZero N] (m : Nat)
    (C : SelectionPhase N k) (phi : Point N (k + 1) → ZMod N)
    (z : Point N (k + 1)) : Real :=
  Complex.normSq (∑ a : Fin (m + 1),
      exponential (((a : Nat) : ZMod N) * fejerPhaseValue C phi z)) /
    ((m : Real) + 1) ^ 2

private lemma fejerKernelWeight_nonneg {N k : Nat} [NeZero N] (m : Nat)
    (C : SelectionPhase N k) (phi : Point N (k + 1) → ZMod N)
    (z : Point N (k + 1)) : 0 ≤ fejerKernelWeight m C phi z := by
  unfold fejerKernelWeight
  exact div_nonneg (Complex.normSq_nonneg _) (by positivity)

private lemma fejerKernelWeight_le_one {N k : Nat} [NeZero N] (m : Nat)
    (C : SelectionPhase N k) (phi : Point N (k + 1) → ZMod N)
    (z : Point N (k + 1)) : fejerKernelWeight m C phi z ≤ 1 := by
  rw [fejerKernelWeight, div_le_one (by positivity), ← Complex.sq_norm]
  gcongr
  exact (norm_sum_le _ _).trans (by simp [cor57_norm_exponential])

private lemma fejerKernelWeight_complex {N k : Nat} [NeZero N] (m : Nat)
    (C : SelectionPhase N k) (phi : Point N (k + 1) → ZMod N)
    (z : Point N (k + 1)) :
    ((fejerKernelWeight m C phi z : Real) : Complex) =
      (((m : Complex) + 1) ^ 2)⁻¹ * ∑ p : FejerDigit m,
        exponential ((fejerDigitInt p : ZMod N) * fejerPhaseValue C phi z) := by
  -- `|∑_a e(aθ)|² = ∑_a ∑_b e(aθ) e(-bθ) = ∑_(a,b) e((a - b)θ)`
  rw [fejerKernelWeight, Complex.ofReal_div, ← Complex.mul_conj, starRingEnd_apply, star_sum,
    Finset.sum_mul_sum, Fintype.sum_prod_type, div_eq_inv_mul]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [star_exponential, ← exponential_add, fejerDigitInt]
  congr 1
  push_cast
  ring

private lemma fejer_product_complex {N k : Nat} [NeZero N] (m : Nat)
    (C : SelectionPhase N k) (phi : Point N (k + 1) → ZMod N)
    (R : GeneralArrangement N k 8) :
    ((∏ z : selectionIndex k, fejerKernelWeight m C phi (selectionVertex R z) : Real) : Complex) =
      ((((m : Complex) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 4)) *
        ∑ eps : selectionIndex k → FejerDigit m,
          exponential (∑ F, C F *
            fejerRelationInt (fun z => fejerDigitInt (eps z)) F phi R) := by
  rw [Complex.ofReal_prod]
  simp_rw [fejerKernelWeight_complex]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, selection_index_card]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro eps _
  rw [fejer_prod_exponential]
  congr 1
  unfold fejerPhaseValue fejerRelationInt
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun F _ => Finset.sum_congr rfl fun z _ => by ring

/-- The digit patterns whose integer values annihilate every feature. -/
private noncomputable def fejerValidRelations {N k : Nat} [NeZero N] (m : Nat)
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    Finset (selectionIndex k → FejerDigit m) := by
  classical
  exact Finset.univ.filter fun eps ↦
    ∀ F, fejerRelationInt (fun z => fejerDigitInt (eps z)) F phi R = 0

/-- **The one-stage average**: averaging the product of Fejér weights over
the random phase counts the valid digit patterns. -/
private lemma fejer_oneStage_average {N k : Nat} [NeZero N] (m : Nat)
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    (𝔼 C : SelectionPhase N k,
      ∏ z : selectionIndex k, fejerKernelWeight m C phi (selectionVertex R z)) =
      ((((m : Real) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 4)) *
        (fejerValidRelations m phi R).card := by
  apply Complex.ofReal_injective
  simp_rw [Complex.ofReal_expect, fejer_product_complex]
  rw [← Finset.mul_expect, Finset.expect_sum_comm]
  simp_rw [selection_expect_phase]
  push_cast
  rw [fejerValidRelations, Finset.natCast_card_filter]

/-! ## Valid patterns: multiples of the parity relation -/

private def fejerEtaZeroIdx {k : Nat} (z : selectionIndex k) : Int :=
  selectionEtaZero z.1 z.2

private lemma fejerRelationInt_smul {N k : Nat} [NeZero N] (c : Int)
    (eta : selectionIndex k → Int) (F : SelectionFeature k)
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    fejerRelationInt (fun z => c * eta z) F phi R =
      (c : ZMod N) * fejerRelationInt eta F phi R := by
  unfold fejerRelationInt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  push_cast
  ring

private lemma fejerRelationInt_some {N k : Nat} [NeZero N]
    (eta : selectionIndex k → Int) (A : Finset (Fin (k + 1)))
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    fejerRelationInt eta (some A) phi R =
      arrangementMoment R (fun e j => eta (e, j)) A := by
  classical
  unfold fejerRelationInt arrangementMoment selectionFeatureValue
  rw [Fintype.sum_prod_type]
  rfl

private lemma fejerRelationInt_etaZero_none {N k : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    fejerRelationInt fejerEtaZeroIdx none phi R =
      ∑ j : Fin 16, selectionIndexSign (N := N) j * R.cubeValue phi j := by
  classical
  unfold fejerRelationInt selectionFeatureValue GeneralArrangement.cubeValue
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [fejerEtaZeroIdx]
  rw [selectionEtaZero_cast]
  by_cases hj : (j : Nat) < 8 <;>
    simp [arrangementParityCoefficient, parityCharacter, selectionIndexSign, hj, selectionVertex]

private lemma fejerRelationInt_etaZero_none_eq_zero_iff {N k : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    fejerRelationInt fejerEtaZeroIdx none phi R = 0 ↔ R.IsRespected phi := by
  rw [fejerRelationInt_etaZero_none]
  unfold GeneralArrangement.IsRespected
  exact (selection_additive_iff (R.cubeValue phi)).symm

/-- The digit patterns with values `j·ε`. -/
private noncomputable def fejerMultiplePatterns {k : Nat} (m j : Nat) :
    Finset (selectionIndex k → FejerDigit m) := by
  classical
  exact Fintype.piFinset fun z => Finset.univ.filter fun p : FejerDigit m =>
    fejerDigitInt p = (j : Int) * fejerEtaZeroIdx z

private lemma fejer_digit_count_pos (m j : Nat) (hj : j ≤ m) :
    (Finset.univ.filter fun p : FejerDigit m => fejerDigitInt p = (j : Int)).card =
      m + 1 - j := by
  classical
  have himg : (Finset.univ.filter fun p : FejerDigit m => fejerDigitInt p = (j : Int)) =
      (Finset.univ : Finset (Fin (m + 1 - j))).image
        (fun a : Fin (m + 1 - j) => ((⟨(a : Nat) + j, by have := a.isLt; omega⟩ : Fin (m + 1)),
          (⟨(a : Nat), by have := a.isLt; omega⟩ : Fin (m + 1)))) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hp
      unfold fejerDigitInt at hp
      refine ⟨⟨(p.2 : Nat), by omega⟩, Prod.ext (Fin.ext ?_) (Fin.ext rfl)⟩
      simp only
      omega
    · rintro ⟨a, rfl⟩
      unfold fejerDigitInt
      simp
  rw [himg, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    simp only [Prod.mk.injEq, Fin.mk.injEq] at hab
    exact Fin.ext hab.2

private lemma fejer_digit_count (m j : Nat) (hj : j ≤ m) (s : Int)
    (hs : s = 1 ∨ s = -1) :
    (Finset.univ.filter fun p : FejerDigit m => fejerDigitInt p = (j : Int) * s).card =
      m + 1 - j := by
  classical
  rcases hs with rfl | rfl
  · simpa using fejer_digit_count_pos m j hj
  · have himg : (Finset.univ.filter fun p : FejerDigit m =>
          fejerDigitInt p = (j : Int) * -1) =
        (Finset.univ.filter fun p : FejerDigit m =>
          fejerDigitInt p = (j : Int)).image Prod.swap := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hp
        refine ⟨p.swap, ?_, Prod.swap_swap p⟩
        unfold fejerDigitInt at hp ⊢
        simp only [Prod.fst_swap, Prod.snd_swap]
        omega
      · rintro ⟨q, hq, rfl⟩
        unfold fejerDigitInt at hq ⊢
        simp only [Prod.fst_swap, Prod.snd_swap]
        omega
    rw [himg, Finset.card_image_of_injective _ Prod.swap_injective]
    exact fejer_digit_count_pos m j hj

private lemma fejerMultiplePatterns_card {k : Nat} (m j : Nat) (hj : j ≤ m) :
    (fejerMultiplePatterns (k := k) m j).card = (m + 1 - j) ^ (2 ^ (k + 4)) := by
  classical
  unfold fejerMultiplePatterns
  rw [Fintype.card_piFinset]
  rw [Finset.prod_congr rfl (fun z _ => fejer_digit_count m j hj (fejerEtaZeroIdx z)
    (selectionEtaZero_cases z.1 z.2))]
  simp only [Finset.prod_const, Finset.card_univ, selection_index_card]

private lemma fejerMultiplePatterns_valid {N k : Nat} [NeZero N] (m j : Nat)
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8)
    (hadd : IsAdditiveTuple R.crossSection) (hres : R.IsRespected phi) :
    fejerMultiplePatterns (k := k) m j ⊆ fejerValidRelations m phi R := by
  classical
  intro eps heps
  have hval : (fun z => fejerDigitInt (eps z)) = fun z => (j : Int) * fejerEtaZeroIdx z := by
    funext z
    exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp heps z)).2
  unfold fejerValidRelations
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro F
  rw [hval, fejerRelationInt_smul]
  cases F with
  | none => rw [(fejerRelationInt_etaZero_none_eq_zero_iff phi R).mpr hres, mul_zero]
  | some A =>
    rw [fejerRelationInt_some]
    have hmom := selectionEtaZero_moment R hadd A
    have heq : (fun e j => fejerEtaZeroIdx (k := k) (e, j)) = selectionEtaZero := rfl
    rw [heq, hmom, mul_zero]

private lemma fejerMultiplePatterns_disjoint {k : Nat} (m : Nat) {j j' : Nat}
    (hjj : j ≠ j') :
    Disjoint (fejerMultiplePatterns (k := k) m j) (fejerMultiplePatterns (k := k) m j') := by
  classical
  rw [Finset.disjoint_left]
  intro eps h1 h2
  have e1 := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp h1 (fun _ => false, 0))).2
  have e2 := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp h2 (fun _ => false, 0))).2
  simp only [fejerEtaZeroIdx] at e1 e2
  rcases selectionEtaZero_cases (k := k) (fun _ => false) 0 with h | h <;>
    · rw [h] at e1 e2
      omega

/-- **Respected arrangements have many valid patterns**: at least
`∑_{j<T} (m+1−j)^M`, from the multiples `j·ε`. -/
private lemma fejerValidRelations_card_good {N k : Nat} [NeZero N] (m T : Nat)
    (hT : T ≤ m + 1) (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8)
    (hadd : IsAdditiveTuple R.crossSection) (hres : R.IsRespected phi) :
    ∑ j ∈ Finset.range T, (m + 1 - j) ^ (2 ^ (k + 4)) ≤
      (fejerValidRelations m phi R).card := by
  classical
  have hsub : (Finset.range T).biUnion (fun j => fejerMultiplePatterns (k := k) m j) ⊆
      fejerValidRelations m phi R :=
    Finset.biUnion_subset.mpr fun j _ => fejerMultiplePatterns_valid m j phi R hadd hres
  have hdisj : ((Finset.range T : Finset Nat) : Set Nat).PairwiseDisjoint
      (fun j => fejerMultiplePatterns (k := k) m j) :=
    fun j _ j' _ hjj => fejerMultiplePatterns_disjoint m hjj
  calc ∑ j ∈ Finset.range T, (m + 1 - j) ^ (2 ^ (k + 4))
      = ∑ j ∈ Finset.range T, (fejerMultiplePatterns (k := k) m j).card := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [fejerMultiplePatterns_card m j (by have := Finset.mem_range.mp hj; omega)]
    _ = ((Finset.range T).biUnion fun j => fejerMultiplePatterns (k := k) m j).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **Non-respected, non-degenerate arrangements have only the diagonal
patterns**: a valid pattern is a modular multiple of `ε`, the multiple is
zero because the arrangement is not respected, and a pattern with values in
`[−m, m]` that vanishes modulo `N > m` vanishes. -/
private lemma fejerValidRelations_subset_diagonal {N k : Nat} [NeZero N]
    [Fact N.Prime] (m : Nat) (hmN : m < N)
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8)
    (hnondeg : ¬ R.IsDegenerateWithin m) (hbad : ¬ R.IsRespected phi) :
    fejerValidRelations m phi R ⊆
      Fintype.piFinset fun _ : selectionIndex k =>
        Finset.univ.filter fun p : FejerDigit m => p.1 = p.2 := by
  classical
  intro eps heps
  have hvalid := (Finset.mem_filter.mp heps).2
  -- a valid pattern is a modular multiple `q·ε` of the parity pattern
  obtain ⟨q, hq⟩ : IsModularMultiple (fun z => fejerDigitInt (eps z))
      (fun z => arrangementParityCoefficient (N := N) (d := 8) z.1 z.2) := not_not.mp fun hnot =>
    hnondeg ⟨fun e j => fejerDigitInt (eps (e, j)), fun e j => fejerDigitInt_bound _, hnot,
      fun A => by simpa only [fejerRelationInt_some] using hvalid (some A)⟩
  -- and `q = 0`, as the arrangement is not respected
  have hrel : fejerRelationInt (fun z => fejerDigitInt (eps z)) none phi R =
      q * fejerRelationInt fejerEtaZeroIdx none phi R := by
    simp only [fejerRelationInt, hq, fejerEtaZeroIdx, selectionEtaZero_cast, Finset.mul_sum,
      mul_assoc]
  have hq0 : q = 0 := (mul_eq_zero.mp (hrel.symm.trans (hvalid none))).resolve_right
    (mt (fejerRelationInt_etaZero_none_eq_zero_iff phi R).mp hbad)
  -- so every digit value vanishes modulo `N > m`, hence vanishes
  refine Fintype.mem_piFinset.mpr fun z => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.ext ?_⟩
  have hz : ((fejerDigitInt (eps z) : Int) : ZMod N) = 0 := by rw [hq z, hq0, zero_mul]
  have hb := fejerDigitInt_bound (eps z)
  have h0 := Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hz)
    (abs_lt.mpr ⟨by omega, by omega⟩)
  unfold fejerDigitInt at h0
  omega

private lemma fejer_diagonal_card {k : Nat} (m : Nat) :
    (Fintype.piFinset fun _ : selectionIndex k =>
      Finset.univ.filter fun p : FejerDigit m => p.1 = p.2).card =
      (m + 1) ^ (2 ^ (k + 4)) := by
  classical
  rw [Fintype.card_piFinset]
  have hdiag : (Finset.univ.filter fun p : FejerDigit m => p.1 = p.2) =
      (Finset.univ : Finset (Fin (m + 1))).image fun a => (a, a) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hp
      exact ⟨p.1, Prod.ext rfl hp⟩
    · rintro ⟨a, rfl⟩
      rfl
  rw [hdiag, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
  simp only [Finset.card_univ, Fintype.card_fin, Finset.prod_const, selection_index_card]

/-! ## The averages over good and bad arrangements -/

private lemma fejer_bad_average_upper {N k : Nat} [NeZero N] [Fact N.Prime]
    (m : Nat) (hmN : m < N) (phi : Point N (k + 1) → ZMod N)
    (R : GeneralArrangement N k 8)
    (hnondeg : ¬ R.IsDegenerateWithin m) (hbad : ¬ R.IsRespected phi) :
    (𝔼 C : SelectionPhase N k,
        ∏ z : selectionIndex k, fejerKernelWeight m C phi (selectionVertex R z)) ≤
      (((m : Real) + 1)⁻¹) ^ (2 ^ (k + 4)) := by
  rw [fejer_oneStage_average]
  have hcard : ((fejerValidRelations m phi R).card : Real) ≤
      ((m : Real) + 1) ^ (2 ^ (k + 4)) := by
    have h := Finset.card_le_card
      (fejerValidRelations_subset_diagonal m hmN phi R hnondeg hbad)
    rw [fejer_diagonal_card] at h
    exact_mod_cast h
  calc ((((m : Real) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 4)) * (fejerValidRelations m phi R).card
      ≤ ((((m : Real) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 4)) * ((m : Real) + 1) ^ (2 ^ (k + 4)) :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = (((m : Real) + 1)⁻¹) ^ (2 ^ (k + 4)) := by
        rw [← mul_pow]
        congr 1
        field_simp

/-- Bernoulli: `∑_{j<T} ((m+1−j)/(m+1))^M ≥ (T+1)/2` when `m + 1 = M·T`. -/
private lemma fejer_ratio_sum_lower (M T : Nat) (hM : 1 ≤ M) (hT : 1 ≤ T) :
    ((T : Real) + 1) / 2 ≤
      ∑ j ∈ Finset.range T,
        (((M * T - j : Nat) : Real) / (M * T : Nat)) ^ M := by
  have hM0 : (M : Real) ≠ 0 := by positivity
  have hT0 : (T : Real) ≠ 0 := by positivity
  -- Bernoulli: `1 − j/T = 1 + M·(−j/(MT)) ≤ (1 − j/(MT))^M`
  have hterm (j : Nat) (hj : j ∈ Finset.range T) :
      1 - (j : Real) / T ≤ (((M * T - j : Nat) : Real) / (M * T : Nat)) ^ M := by
    have hjle : j ≤ M * T := (Finset.mem_range.mp hj).le.trans (Nat.le_mul_of_pos_left T hM)
    have hj1 : (j : Real) / (M * T) ≤ 1 :=
      div_le_one_of_le₀ (by exact_mod_cast hjle) (by positivity)
    refine (le_of_eq ?_).trans ((one_add_mul_le_pow (a := -((j : Real) / (M * T)))
      (by linarith) M).trans_eq ?_)
    · field_simp; ring
    · rw [Nat.cast_sub hjle]; push_cast; field_simp; ring
  -- and `∑_{j<T} (1 − j/T) = (T + 1)/2`
  have hid := congrArg (fun n : Nat => (n : Real)) (Finset.sum_range_id_mul_two T)
  push_cast [Nat.cast_sub hT] at hid
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hterm)
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_range, nsmul_one]
  field_simp
  linarith

/-! ## Degenerate arrangements and the carrier score -/

private lemma fejer_isDegenerateWithin_of_isDegenerate {N k : Nat} [NeZero N] {m : Nat}
    (hm : 1 ≤ m) (R : GeneralArrangement N k 8) (h : R.IsDegenerate) :
    R.IsDegenerateWithin m := by
  obtain ⟨eta, ht, hn, hmom⟩ := h
  refine ⟨eta, ?_, hn, hmom⟩
  intro e j
  rcases ht (e, j) with h | h | h <;> simp only at h <;> rw [h] <;> constructor <;> omega

private noncomputable def fejerGoodNondegenerate {N k : Nat} [NeZero N] (m : Nat)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) :
    Finset (GeneralArrangement N k 8) := by
  classical
  exact (selectionGoodArrangements B phi).filter fun R ↦ ¬ R.IsDegenerateWithin m

private noncomputable def fejerBadNondegenerate {N k : Nat} [NeZero N] (m : Nat)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) :
    Finset (GeneralArrangement N k 8) := by
  classical
  exact (selectionBadArrangements B phi).filter fun R ↦ ¬ R.IsDegenerateWithin m

private noncomputable def fejerDegenerateFinset (N k m : Nat) [NeZero N] :
    Finset (GeneralArrangement N k 8) := by
  classical
  exact Finset.univ.filter fun R ↦
    IsAdditiveTuple R.crossSection ∧ R.IsDegenerateWithin m

private lemma fejerDegenerateFinset_card (N k m : Nat) [NeZero N] :
    (fejerDegenerateFinset N k m).card =
      degenerateGeneralArrangementCountWithin (N := N) (k := k) m 8 := by
  classical
  unfold fejerDegenerateFinset degenerateGeneralArrangementCountWithin countWhere
  apply congrArg Finset.card
  ext R
  simp

private lemma fejerGoodNondegenerate_card_lower {N k : Nat} [NeZero N] (m : Nat)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) :
    (selectionGoodArrangements B phi).card ≤
      (fejerGoodNondegenerate m B phi).card +
        degenerateGeneralArrangementCountWithin (N := N) (k := k) m 8 := by
  classical
  let goodDeg := (selectionGoodArrangements B phi).filter fun R ↦ R.IsDegenerateWithin m
  have hsplit :
      (fejerGoodNondegenerate m B phi).card + goodDeg.card =
        (selectionGoodArrangements B phi).card := by
    simpa [fejerGoodNondegenerate, goodDeg] using
      (Finset.card_filter_add_card_filter_not
        (s := selectionGoodArrangements B phi) (fun R ↦ ¬ R.IsDegenerateWithin m))
  have hsub : goodDeg ⊆ fejerDegenerateFinset N k m := by
    intro R hR
    have hR' := Finset.mem_filter.mp hR
    have hgoodData : R ∈ selectionArrangements B ∧ R.IsRespected phi := by
      simpa [selectionGoodArrangements] using hR'.1
    have hIsIn : R.IsIn B := by
      simpa [selectionArrangements] using hgoodData.1
    simp [fejerDegenerateFinset, hIsIn.1, hR'.2]
  have hcard : goodDeg.card ≤ degenerateGeneralArrangementCountWithin (N := N) (k := k) m 8 := by
    calc goodDeg.card ≤ (fejerDegenerateFinset N k m).card := Finset.card_le_card hsub
      _ = _ := fejerDegenerateFinset_card N k m
  omega

private lemma fejer_carrier_score_lower {N k : Nat} [NeZero N]
    (hN : 2 ≤ N) (m : Nat) (hm : 1 ≤ m) (eta : Real) (heta : 0 ≤ eta)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (C : SelectionPhase N k) :
    eta * (∑ R ∈ fejerGoodNondegenerate m B phi,
      ∏ z : selectionIndex k, fejerKernelWeight m C phi (selectionVertex R z)) -
      (∑ R ∈ fejerBadNondegenerate m B phi,
        ∏ z : selectionIndex k, fejerKernelWeight m C phi (selectionVertex R z)) -
      degenerateGeneralArrangementCountWithin (N := N) (k := k) m 8 ≤
    eta * (∑ R ∈ selectionGoodArrangements B phi,
      ∏ z ∈ selectionCarrier R, fejerKernelWeight m C phi z) -
      ∑ R ∈ selectionBadArrangements B phi,
        ∏ z ∈ selectionCarrier R, fejerKernelWeight m C phi z := by
  classical
  have hp0 (z : Point N (k + 1)) := fejerKernelWeight_nonneg m C phi z
  -- on a non-degenerate arrangement the carrier product is the vertex product
  have hnd (R : GeneralArrangement N k 8) (h : ¬ R.IsDegenerateWithin m) :
      ∏ z ∈ selectionCarrier R, fejerKernelWeight m C phi z =
        ∏ z : selectionIndex k, fejerKernelWeight m C phi (selectionVertex R z) :=
    selectionCarrier_prod_of_nondegenerate hN R
      (fun hd => h (fejer_isDegenerateWithin_of_isDegenerate hm R hd)) _
  rw [sub_sub]
  refine sub_le_sub (mul_le_mul_of_nonneg_left ?_ heta) ?_
  · exact (Finset.sum_congr rfl fun R hR => (hnd R (Finset.mem_filter.mp hR).2).symm).trans_le
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun R _ _ => Finset.prod_nonneg fun z _ => hp0 z)
  -- the bad sum splits off its degenerate part, of weight at most the degenerate count
  rw [← Finset.sum_filter_add_sum_filter_not (selectionBadArrangements B phi)
    fun R ↦ ¬ R.IsDegenerateWithin m, ← fejerDegenerateFinset_card]
  gcongr ?_ + ?_
  · exact le_of_eq (Finset.sum_congr rfl fun R hR => hnd R (Finset.mem_filter.mp hR).2)
  refine (Finset.sum_le_card_nsmul _ _ 1 fun R _ => Finset.prod_le_one (fun z _ => hp0 z)
    fun z _ => fejerKernelWeight_le_one m C phi z).trans ?_
  rw [nsmul_one]
  refine Nat.cast_le.mpr (Finset.card_le_card fun R hR => ?_)
  obtain ⟨hRbad, hRdeg⟩ := Finset.mem_filter.mp hR
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hRbad).1).2.1, not_not.mp hRdeg⟩

/-- The phase average of the score over non-degenerate arrangements. -/
private lemma fejer_phase_score_lower {N k : Nat} [NeZero N] [Fact N.Prime]
    (m T : Nat) (hT : T ≤ m + 1) (hmN : m < N) (eta : Real) (heta : 0 ≤ eta)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) :
    eta * (fejerGoodNondegenerate m B phi).card *
        (((((m : Real) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 4)) *
          (∑ j ∈ Finset.range T, ((m + 1 - j : Nat) : Real) ^ (2 ^ (k + 4)))) -
      (fejerBadNondegenerate m B phi).card * (((m : Real) + 1)⁻¹) ^ (2 ^ (k + 4)) ≤
    𝔼 C : SelectionPhase N k, (
      eta * (∑ R ∈ fejerGoodNondegenerate m B phi,
        ∏ z : selectionIndex k, fejerKernelWeight m C phi (selectionVertex R z)) -
      ∑ R ∈ fejerBadNondegenerate m B phi,
        ∏ z : selectionIndex k, fejerKernelWeight m C phi (selectionVertex R z)) := by
  classical
  rw [Finset.expect_sub_distrib, ← Finset.mul_expect, Finset.expect_sum_comm,
    Finset.expect_sum_comm, mul_assoc, ← nsmul_eq_mul, ← nsmul_eq_mul, ← Finset.sum_const]
  -- termwise: the good averages are large, the bad ones small
  refine sub_le_sub (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun R hR => ?_) heta)
    (Finset.sum_le_card_nsmul _ _ _ fun R hR => ?_)
  · obtain ⟨hRsel, hres⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hR).1
    rw [fejer_oneStage_average]
    gcongr
    exact_mod_cast fejerValidRelations_card_good m T hT phi R (Finset.mem_filter.mp hRsel).2.1 hres
  · obtain ⟨hRbad, hnd⟩ := Finset.mem_filter.mp hR
    obtain ⟨hRsel, hRgood⟩ := Finset.mem_sdiff.mp hRbad
    exact fejer_bad_average_upper m hmN phi R hnd
      fun hres => hRgood (Finset.mem_filter.mpr ⟨hRsel, hres⟩)

/-! ## The Fejér restriction -/

/-- The exponent of the single Fejér selection: `2^(k+4)·(k+6)`, against
`2^(2^(k+4)+k+3)` for the iterated Riesz selection. -/
def fejerSelectionExponent (k : Nat) : Nat := 2 ^ (k + 4) * (k + 6)

/-- The density loss `t = (M·T)^(−M)` dominates `(αη/4)^(M(k+6))`. -/
private lemma fejer_loss_lower (k : Nat) (a : Real) (ha : 0 < a) (ha1 : a ≤ 1) :
    (a / 4) ^ fejerSelectionExponent k ≤
      (((2 ^ (k + 4) * ⌈6 / a⌉₊ : Nat) : Real)⁻¹) ^ (2 ^ (k + 4)) := by
  -- `⌈6/a⌉·a < 6 + a ≤ 7`
  have hc : (⌈6 / a⌉₊ : Real) * a ≤ 7 := by
    have h := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (show 0 ≤ 6 / a by positivity)) ha
    rw [add_mul, div_mul_cancel₀ 6 ha.ne', one_mul] at h
    linarith
  have hp : (a / 4 * 2) ^ (k + 4) ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
  -- the base comparison `(a/4)^(k+6)·2^(k+4)·⌈6/a⌉ = (a/2)^(k+4)·(a/16)·(⌈6/a⌉·a) ≤ 7/16`
  rw [fejerSelectionExponent, pow_mul' (a / 4) (2 ^ (k + 4)) (k + 6)]
  gcongr
  rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
  push_cast
  calc (a / 4) ^ (k + 6) * (2 ^ (k + 4) * ⌈6 / a⌉₊)
      = (a / 4 * 2) ^ (k + 4) * (a / 16) * (⌈6 / a⌉₊ * a) := by
        rw [mul_pow (a / 4) 2 (k + 4)]; ring
    _ ≤ 1 * (1 / 16) * 7 := by gcongr
    _ ≤ 1 := by norm_num

/-- The order `m` of the Fejér kernel: `m + 1 = 2^(k+4)·⌈6/(min(α,1)·η)⌉`. -/
def fejerOrder (k : Nat) (alpha eta : Real) : Nat :=
  2 ^ (k + 4) * ⌈6 / (min alpha 1 * eta)⌉₊ - 1

/-- The density loss `(m+1)^(−2^(k+4))` of one Fejér stage. -/
def fejerLoss (k : Nat) (alpha eta : Real) : Real :=
  (((fejerOrder k alpha eta : Nat) : Real) + 1)⁻¹ ^ (2 ^ (k + 4))

/-- The constant of the `m`-range degenerate count:
`(2m+1)^(2·8·2^k)·k`. -/
def fejerDegenerateConst (k : Nat) (alpha eta : Real) : Real :=
  (2 * ((fejerOrder k alpha eta : Nat) : Real) + 1) ^ (2 * 8 * 2 ^ k) * k

/-- **The explicit modulus threshold of the Fejér selection**:
`max(m + 1, 3, 2·c₀/(scale·t))`. -/
def fejerExplicitThreshold (k : Nat) (alpha scale eta : Real) : Real :=
  max (((fejerOrder k alpha eta : Nat) : Real) + 1)
    (max 3 (2 * fejerDegenerateConst k alpha eta / (scale * fejerLoss k alpha eta)))

set_option maxHeartbeats 1000000 in
/-- **The Fejér selection at an arbitrary scale**, above the explicit
threshold `fejerExplicitThreshold`: if `B` carries at most
`scale·N^(17k+15)` arrangements, of which at least `α·scale·N^(17k+15)` are
respected, then some `B' ⊆ B` carries at least
`(αη/4)^(2^(k+4)(k+6))·scale·N^(17k+15)` arrangements, of which a
`1 − η` fraction is respected. -/
theorem fejer_scale_estimate_explicit (k : Nat) (alpha scale eta : Real) (hk : 1 ≤ k)
    (halpha : 0 < alpha) (hscale : 0 < scale) (heta : 0 < eta) (heta_one : eta ≤ 1) :
    ∀ (N : Nat) [NeZero N], fejerExplicitThreshold k alpha scale eta ≤ (N : Real) →
      Nat.Prime N → Odd N →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        (generalArrangementCount 8 B : Real) ≤ scale * (N : Real) ^ (17 * k + 15) →
        alpha * scale * (N : Real) ^ (17 * k + 15) ≤
            respectedGeneralArrangementCount 8 B phi →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (alpha * eta / 4) ^ fejerSelectionExponent k * scale *
              (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - eta) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi := by
  classical
  -- the order of the Fejér kernel: `m + 1 = M·T` with `M = 2^(k+4)`, `T = ⌈6/a⌉`
  set M : Nat := 2 ^ (k + 4) with hM
  have hM2 : 1 < M := Nat.one_lt_two_pow (by omega)
  set a : Real := min alpha 1 * eta with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := mul_le_one₀ (min_le_right _ _) heta.le heta_one
  set T : Nat := ⌈6 / a⌉₊ with hTdef
  have hT1 : 1 ≤ T := Nat.one_le_ceil_iff.mpr (by positivity)
  set m : Nat := M * T - 1 with hmdef
  have hMT := Nat.le_mul_of_pos_right M hT1
  have hm1 : m + 1 = M * T := by omega
  have hm : 1 ≤ m := by omega
  have hTm : T ≤ m + 1 := by rw [hm1]; exact Nat.le_mul_of_pos_left T (by omega)
  set t : Real := (((m : Real) + 1)⁻¹) ^ M with htdef
  have ht0 : 0 < t := by positivity
  set c0 : Real := (2 * (m : Real) + 1) ^ (2 * 8 * 2 ^ k) * k
  intro N _ hN hprime hodd B phi hu hrespected
  letI : Fact N.Prime := ⟨hprime⟩
  change max ((m : Real) + 1) (max 3 (2 * c0 / (scale * t))) ≤ N at hN
  obtain ⟨hmN, -, hNbig⟩ := (max_le_iff.mp hN).imp_right max_le_iff.mp
  replace hmN : m < N := by exact_mod_cast (show (m : Real) < N by linarith)
  have hNpos : (0 : Real) < N := Nat.cast_pos.mpr (NeZero.pos N)
  set G : Real := scale * (N : Real) ^ (17 * k + 15) with hG
  have hG0 : 0 < G := by positivity
  -- `α ≤ 1`, since `αG` respected arrangements are among at most `G` ones; so `a = αη`
  have hrespLe : (respectedGeneralArrangementCount 8 B phi : Real) ≤ generalArrangementCount 8 B :=
    by exact_mod_cast selection_respected_le_arrangement B phi
  have halpha1 : alpha ≤ 1 := le_of_mul_le_mul_right (by linarith : alpha * G ≤ 1 * G) hG0
  have haeq : a = alpha * eta := by rw [ha, min_eq_left halpha1]
  -- the `m`-degenerate count `D ≤ c₀·N^(17k+14)`; above the threshold `2D ≤ tG`
  set D : Real := ((degenerateGeneralArrangementCountWithin (N := N) (k := k) m 8 : Nat) : Real)
    with hD
  have hDsmall : 2 * D ≤ t * G := by
    have hDle := degenerate_count_within_le N m k 8 hprime hodd hk (by norm_num)
    rw [show (2 * 8 + 1) * k + 2 * 8 - 2 = 17 * k + 14 by omega] at hDle
    have h1 := (div_le_iff₀ (by positivity : (0 : Real) < scale * t)).mp hNbig
    calc 2 * D ≤ 2 * c0 * (N : Real) ^ (17 * k + 14) := by linarith
      _ ≤ N * (scale * t) * (N : Real) ^ (17 * k + 14) := by gcongr
      _ = t * G := by rw [hG]; ring
  -- Bernoulli: the good average weight is at least `t·(T+1)/2`, and `ηα(T+1)/2 ≥ 3`
  have hL : t * (((T : Real) + 1) / 2) ≤ (((m : Real) + 1) ^ 2)⁻¹ ^ M *
      ∑ j ∈ Finset.range T, ((m + 1 - j : Nat) : Real) ^ M := by
    have hmR : (m : Real) + 1 = ((M * T : Nat) : Real) := by exact_mod_cast hm1
    refine (mul_le_mul_of_nonneg_left (fejer_ratio_sum_lower M T (by omega) hT1)
      ht0.le).trans_eq ?_
    rw [htdef, hm1, hmR, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hgain : 3 ≤ eta * alpha * (((T : Real) + 1) / 2) := by
    have hTa : 6 / (alpha * eta) ≤ T := by rw [← haeq]; exact Nat.le_ceil _
    have := (div_le_iff₀ (by positivity : (0 : Real) < alpha * eta)).mp hTa
    linarith [mul_pos halpha heta]
  have hP : t * (((T : Real) + 1) / 2) ≤ 1 := by
    have h1 : t ≤ ((m : Real) + 1)⁻¹ := by
      rw [htdef]
      exact pow_le_of_le_one (by positivity)
        (inv_le_one_of_one_le₀ (le_add_of_nonneg_left m.cast_nonneg)) (by omega)
    have h2 : ((T : Real) + 1) / 2 ≤ (m : Real) + 1 := by
      rw [div_le_iff₀ two_pos]; exact_mod_cast (by omega : T + 1 ≤ (m + 1) * 2)
    calc t * (((T : Real) + 1) / 2) ≤ ((m : Real) + 1)⁻¹ * ((m : Real) + 1) := by gcongr
      _ = 1 := inv_mul_cancel₀ (by positivity)
  -- the non-degenerate good and bad counts
  have hgoodCard : alpha * G - D ≤ (fejerGoodNondegenerate m B phi).card := by
    have h : (respectedGeneralArrangementCount 8 B phi : Real) ≤
        (fejerGoodNondegenerate m B phi).card + D := by
      rw [← selectionGoodArrangements_card, hD]
      exact_mod_cast fejerGoodNondegenerate_card_lower m B phi
    linarith
  have hbadCard : ((fejerBadNondegenerate m B phi).card : Real) ≤ G := le_trans (by
    exact_mod_cast Finset.card_le_card (fun R hR => (Finset.mem_sdiff.mp
      (Finset.mem_filter.mp hR).1).1 : fejerBadNondegenerate m B phi ⊆ selectionArrangements B)) hu
  -- a phase `C` whose score is at least the phase average, which is at least `ηtG + D`
  have hphase := fejer_phase_score_lower (k := k) m T hTm hmN eta heta.le B phi
  rw [← hM, ← htdef] at hphase
  obtain ⟨C, -, hC⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty
    (le_trans (show eta * t * G + D ≤ _ by
      linarith [mul_le_mul_of_nonneg_left (mul_le_mul hgoodCard hL (by positivity)
          (by positivity)) heta.le, mul_le_mul_of_nonneg_right hbadCard ht0.le,
        mul_le_mul_of_nonneg_right hgain (by positivity : (0 : Real) ≤ t * G),
        mul_le_mul (mul_le_mul_of_nonneg_right heta_one (by positivity : (0 : Real) ≤ D)) hP
          (by positivity) (by positivity),
        mul_le_mul_of_nonneg_right heta_one (by positivity : (0 : Real) ≤ t * G)]) hphase)
  -- the Bernoulli selection with the weights of `C`
  have hcarrier := fejer_carrier_score_lower (by omega) m hm eta heta.le B phi C
  obtain ⟨S, hSB, hS⟩ := _root_.LeanProofs.GowersSzemeredi.exists_subset_count_score B
    (fejerKernelWeight m C phi) (fun z _ ↦ fejerKernelWeight_nonneg m C phi z)
    (fun z _ ↦ fejerKernelWeight_le_one m C phi z)
    (selectionGoodArrangements B phi) (selectionBadArrangements B phi) selectionCarrier
    (fun R hR ↦ selectionCarrier_subset B R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).2)
    (fun R hR ↦ selectionCarrier_subset B R (Finset.mem_filter.mp (Finset.mem_sdiff.mp hR).1).2)
    eta (eta * t * G) (by linarith only [hC, hcarrier])
  have hsplit := selection_good_bad_restrict_card B S phi hSB
  rw [selection_good_restrict_card B S phi hSB] at hS hsplit
  have hb0 := Nat.cast_nonneg (α := Real)
    ((selectionBadArrangements B phi).filter fun R ↦ selectionCarrier R ⊆ S).card
  have hgS : t * G ≤ respectedGeneralArrangementCount 8 S phi :=
    le_of_mul_le_mul_left (by linarith) heta
  -- the density loss `(αη/4)^(2^(k+4)·(k+6)) ≤ t`
  have hloss := fejer_loss_lower k (alpha * eta) (by positivity) (haeq.symm.trans_le ha1)
  rw [show ⌈6 / (alpha * eta)⌉₊ = T by rw [hTdef, haeq], ← hM, ← hm1, Nat.cast_succ,
    ← htdef] at hloss
  refine ⟨S, hSB, ?_, ?_⟩ <;> rw [← hsplit] <;> push_cast
  · linarith [mul_le_mul_of_nonneg_right hloss hG0.le]
  · linarith [mul_nonneg heta.le hb0, (by positivity : (0 : Real) ≤ eta * t * G)]

end LeanProofs.GowersSzemeredi
