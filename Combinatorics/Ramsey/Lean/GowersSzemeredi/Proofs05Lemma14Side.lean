import GowersSzemeredi.Proofs05Lemma14

/-! Declarations of `Proofs05Lemma14` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ### Lemma 5.14 -/

/-- Lemma 5.14 follows from the polynomial partition of Corollary 5.6.

The local additive error is summed over the input partition, while Jensen's
inequality turns the sum of local sublinear cell counts into the claimed
`M^(1/K) N^(1-1/K)` global bound. -/
theorem lemma_5_14_holds_of_corollary_5_6
    (h56 : corollary_5_6) : lemma_5_14 := by
  intro k alpha hk halpha
  refine ⟨section5LocalRefinementConstant k alpha,
    section5LocalRefinementConstant_pos k alpha, ?_⟩
  intro N M _inst phi f Q hphi hf hQ hphase
  have hM : 0 < M := by
    by_contra hMnot
    have hMzero : M = 0 := Nat.eq_zero_of_not_pos hMnot
    subst M
    obtain ⟨i, _hi⟩ := (hQ.1 (0 : ZMod N)).mp (Finset.mem_univ _)
    exact Fin.elim0 i
  have hdisc : DiscValued (fun s ↦ (f s : Complex)) := by
    intro s
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hf s
  choose L R hRpart hRproper hRcount hRerror using
    fun i : Fin M ↦
      section5_efficient_local_phase_refinement_arbitrary_of_corollary_5_6
        h56 (Q i) phi alpha hk hphi halpha
  refine ⟨∑ i, L i, section5Flatten L R,
    section5Flatten_refinement Q L R hQ hRpart,
    section5Flatten_isProper L R hRproper, ?_, ?_⟩
  · have hK : 0 < polynomialPartitionConstant k := by
      unfold polynomialPartitionConstant
      positivity
    have hcards : ∑ i, (Q i).carrier.card = N := by
      simpa only [Finset.card_univ, ZMod.card] using IsPartition.sum_card hQ
    have hjensen := section5_sum_rpow_le hM hK
      (fun i ↦ (Q i).carrier.card) hcards
    have hlocalCount :
        ((∑ i, L i : Nat) : Real) ≤
          section5LocalRefinementConstant k alpha *
            ∑ i, ((Q i).carrier.card : Real) ^
              (1 - (polynomialPartitionConstant k : Real)⁻¹) := by
      rw [Nat.cast_sum]
      calc
        ∑ i, (L i : Real) ≤
            ∑ i, section5LocalRefinementConstant k alpha *
              ((Q i).carrier.card : Real) ^
                (1 - (polynomialPartitionConstant k : Real)⁻¹) :=
          Finset.sum_le_sum fun i _hi ↦ hRcount i
        _ = section5LocalRefinementConstant k alpha *
            ∑ i, ((Q i).carrier.card : Real) ^
              (1 - (polynomialPartitionConstant k : Real)⁻¹) := by
          rw [Finset.mul_sum]
    calc
      ((∑ i, L i : Nat) : Real) ≤
          section5LocalRefinementConstant k alpha *
            ∑ i, ((Q i).carrier.card : Real) ^
              (1 - (polynomialPartitionConstant k : Real)⁻¹) := hlocalCount
      _ ≤ section5LocalRefinementConstant k alpha *
          ((M : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ *
            (N : Real) ^
              (1 - (polynomialPartitionConstant k : Real)⁻¹)) :=
        mul_le_mul_of_nonneg_left hjensen
          (section5LocalRefinementConstant_pos k alpha).le
      _ = section5LocalRefinementConstant k alpha *
            (M : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ *
          (N : Real) ^
            (1 - (polynomialPartitionConstant k : Real)⁻¹) := by ring
  · have hnormReal (A : Finset (ZMod N)) :
        ‖∑ s ∈ A, (f s : Complex)‖ = |∑ s ∈ A, f s| := by
      rw [← Complex.ofReal_sum]
      simp only [Complex.norm_real, Real.norm_eq_abs]
    have hlocalError (i : Fin M) :
        ‖∑ s ∈ (Q i).carrier,
            (f s : Complex) * exponential (-(phi s))‖ ≤
          (∑ j, |∑ s ∈ (R i j).carrier, f s|) +
            alpha / 2 * (Q i).carrier.card := by
      simpa only [hnormReal] using hRerror i (fun s ↦ (f s : Complex)) hdisc
    have hcardsReal :
        ∑ i, ((Q i).carrier.card : Real) = (N : Real) := by
      have hcardsNat : ∑ i, (Q i).carrier.card = N := by
        simpa only [Finset.card_univ, ZMod.card] using IsPartition.sum_card hQ
      exact_mod_cast hcardsNat
    have hphaseUpper :
        ∑ i, ‖∑ s ∈ (Q i).carrier,
            (f s : Complex) * exponential (-(phi s))‖ ≤
          (∑ i, ∑ j, |∑ s ∈ (R i j).carrier, f s|) +
            alpha / 2 * N := by
      calc
        ∑ i, ‖∑ s ∈ (Q i).carrier,
              (f s : Complex) * exponential (-(phi s))‖ ≤
            ∑ i, ((∑ j, |∑ s ∈ (R i j).carrier, f s|) +
              alpha / 2 * (Q i).carrier.card) :=
          Finset.sum_le_sum fun i _hi ↦ hlocalError i
        _ = (∑ i, ∑ j, |∑ s ∈ (R i j).carrier, f s|) +
              alpha / 2 * N := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcardsReal]
    have hplain :
        (alpha / 2) * N ≤
          ∑ i, ∑ j, |∑ s ∈ (R i j).carrier, f s| := by
      nlinarith
    calc
      (alpha / 2) * N ≤
          ∑ i, ∑ j, |∑ s ∈ (R i j).carrier, f s| := hplain
      _ = ∑ j, |∑ s ∈ (section5Flatten L R j).carrier, f s| :=
        (section5Flatten_sum L R
          (fun P ↦ |∑ s ∈ P.carrier, f s|)).symm

end LeanProofs.GowersSzemeredi
