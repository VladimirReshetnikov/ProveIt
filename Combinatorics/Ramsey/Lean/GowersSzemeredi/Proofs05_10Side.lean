import GowersSzemeredi.Proofs05_10
import GowersSzemeredi.Sections08_09

/-! Declarations of `Proofs05_10` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod Combinatorics.Additive
open Finset

namespace LeanProofs.GowersSzemeredi

/-- Passing to the graph injects every quadruple respected by `phi` into an
additive-energy quadruple in the product group. -/
theorem lemma_6_2_holds : lemma_6_2 := by
  intro N _ gamma B phi _ hadd
  unfold GammaAdditive at hadd
  apply hadd.trans
  norm_cast
  unfold phiAdditiveCount countWhere Finset.addEnergy
  let graphPoint : ZMod N → ZMod N × ZMod N := fun x => (x, phi x)
  let toEnergy : (Fin 4 → ZMod N) →
      ((ZMod N × ZMod N) × (ZMod N × ZMod N)) ×
        ((ZMod N × ZMod N) × (ZMod N × ZMod N)) :=
    fun q => ((graphPoint (q 0), graphPoint (q 2)),
      (graphPoint (q 1), graphPoint (q 3)))
  refine Finset.card_le_card_of_injOn toEnergy ?_ ?_
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rcases hq with ⟨hqB, hqadd, hqphi⟩
    constructor
    · simp only [Finset.mem_product]
      repeat' constructor
      all_goals
        simp only [toEnergy, graphPoint, functionGraph, Finset.mem_image]
        exact ⟨_, hqB _, rfl⟩
    · exact Prod.ext hqadd hqphi
  · intro q _ r _ hqr
    simp only [toEnergy, graphPoint, Prod.mk.injEq] at hqr
    funext i
    fin_cases i <;> tauto

/-- Lemma 5.15 is a finite averaging argument: mean zero makes the total
positive discrepancy half the total absolute discrepancy, and pigeonholing
then supplies a large cell. -/
theorem lemma_5_15_holds : lemma_5_15 := by
  intro N M _ f P alpha hM hAlpha hf hmean hpart hlarge
  let S : Fin M → ℝ := fun j => ∑ s ∈ P j, f s
  have hpair : ((Finset.univ : Finset (Fin M)) : Set (Fin M)).PairwiseDisjoint P := by
    intro i _ j _ hij
    apply hpart.2 i j
    simp [hij]
  have hunion : (Finset.univ : Finset (Fin M)).biUnion P = Finset.univ := by
    ext s
    simpa only [Finset.mem_biUnion, Finset.mem_univ, true_and] using (hpart.1 s).symm
  have hsum : ∑ j, S j = 0 := by
    rw [show (∑ j, S j) = ∑ j ∈ (Finset.univ : Finset (Fin M)), ∑ s ∈ P j, f s by
      simp [S]]
    rw [← Finset.sum_biUnion hpair, hunion]
    simpa using hmean
  have hcardsNat : ∑ j, (P j).card = N := by
    rw [show (∑ j, (P j).card) =
        ∑ j ∈ (Finset.univ : Finset (Fin M)), (P j).card by simp]
    rw [← Finset.card_biUnion hpair, hunion]
    simp
  have hcards : (∑ j, ((P j).card : ℝ)) = N := by exact_mod_cast hcardsNat
  have hS_le_card (j : Fin M) : S j ≤ (P j).card := by
    calc
      S j ≤ ∑ s ∈ P j, |f s| := by
        apply Finset.sum_le_sum
        intro s _
        exact le_abs_self (f s)
      _ ≤ ∑ _s ∈ P j, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro s _
        exact hf s
      _ = (P j).card := by simp
  by_cases hAlphaZero : alpha = 0
  · subst alpha
    have hne : (Finset.univ : Finset (Fin M)).Nonempty := ⟨⟨0, hM⟩, Finset.mem_univ _⟩
    obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le hne
      (f := fun _ : Fin M => (0 : ℝ)) (g := S) (by simp [hsum])
    exact ⟨j, by simpa using hj, by simp⟩
  · have hAlphaPos : 0 < alpha := lt_of_le_of_ne hAlpha (Ne.symm hAlphaZero)
    have hNPos : 0 < N := NeZero.pos N
    have hNReal : (0 : ℝ) < N := by exact_mod_cast hNPos
    have hMReal : (0 : ℝ) < M := by exact_mod_cast hM
    let T : ℝ := alpha * N / (4 * M)
    have hTPos : 0 < T := by
      dsimp [T]
      positivity
    by_contra hexists
    have hbad (j : Fin M) :
        S j < alpha * (P j).card / 4 ∨ ((P j).card : ℝ) < T := by
      by_cases hdisc : alpha * (P j).card / 4 ≤ S j
      · right
        by_contra hcard
        exact hexists ⟨j, hdisc, le_of_not_gt hcard⟩
      · exact Or.inl (lt_of_not_ge hdisc)
    have hmax (j : Fin M) :
        max (S j) 0 < alpha * (P j).card / 4 + T := by
      rcases hbad j with hdisc | hcard
      · by_cases hS : 0 ≤ S j
        · rw [max_eq_left hS]
          linarith
        · rw [max_eq_right (le_of_not_ge hS)]
          positivity
      · by_cases hS : 0 ≤ S j
        · rw [max_eq_left hS]
          have := hS_le_card j
          nlinarith [mul_nonneg hAlpha (Nat.cast_nonneg (P j).card)]
        · rw [max_eq_right (le_of_not_ge hS)]
          positivity
    have hne : (Finset.univ : Finset (Fin M)).Nonempty := ⟨⟨0, hM⟩, Finset.mem_univ _⟩
    have hmaxsum :
        (∑ j, max (S j) 0) < ∑ j, (alpha * (P j).card / 4 + T) :=
      Finset.sum_lt_sum_of_nonempty hne fun j _ => hmax j
    have hright : (∑ j, (alpha * (P j).card / 4 + T)) = alpha * N / 2 := by
      calc
        _ = (∑ j, (alpha / 4) * (P j).card) + ∑ _j : Fin M, T := by
          rw [Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (alpha / 4) * (∑ j, ((P j).card : ℝ)) + (M : ℝ) * T := by
          rw [Finset.mul_sum]
          simp
        _ = alpha * N / 2 := by
          rw [hcards]
          dsimp [T]
          field_simp
          ring
    rw [hright] at hmaxsum
    have habs (j : Fin M) : |S j| = 2 * max (S j) 0 - S j := by
      rcases le_total 0 (S j) with hS | hS
      · rw [abs_of_nonneg hS, max_eq_left hS]
        ring
      · rw [abs_of_nonpos hS, max_eq_right hS]
        ring
    have habssum : (∑ j, |S j|) = 2 * ∑ j, max (S j) 0 := by
      simp_rw [habs, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [hsum, sub_zero]
    have hlargeS : alpha * N ≤ ∑ j, |S j| := by simpa [S] using hlarge
    rw [habssum] at hlargeS
    linarith

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- Lemma 9.1 is the weighted Hölder inequality with weight and function
both equal to `a i ^ 2`, and exponent seven. -/
theorem lemma_9_1_holds : lemma_9_1 := by
  intro n a _
  have h := Real.inner_le_weight_mul_Lp_of_nonneg
    (s := (Finset.univ : Finset (Fin n))) (p := (7 : ℝ)) (by norm_num)
    (fun i => a i ^ 2) (fun i => a i ^ 2)
    (fun i => sq_nonneg (a i)) (fun i => sq_nonneg (a i))
  have h4 : (∑ i, a i ^ 2 * a i ^ 2) = ∑ i, a i ^ 4 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h4] at h
  norm_num [Real.rpow_natCast] at h
  ring_nf at h
  exact h

end LeanProofs.GowersSzemeredi
