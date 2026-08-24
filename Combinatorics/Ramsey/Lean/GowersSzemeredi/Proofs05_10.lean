import GowersSzemeredi.Section05
import GowersSzemeredi.Sections06_07
import GowersSzemeredi.Sections08_09
import GowersSzemeredi.Section10
import GowersSzemeredi.ProofInfrastructure
import Mathlib.Analysis.MeanInequalities
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Proofs for Gowers (2001), Sections 5--10

This file supplies proofs of those formalized statements from Sections 5--10
that follow directly from general results already available in Mathlib or from
finite combinatorial identities.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod Combinatorics.Additive
open Finset

namespace LeanProofs.GowersSzemeredi

/-- Lemma 5.4 is Mathlib's Dirichlet approximation theorem, with the resulting
rational written in reduced numerator/denominator form. -/
theorem lemma_5_4_holds : lemma_5_4 := by
  intro alpha u hu
  obtain ⟨r, hr, hru⟩ := Real.exists_rat_abs_sub_le_and_den_le alpha (by omega : 0 < u)
  refine ⟨r.num, r.den, r.den_pos, hru, r.reduced, ?_⟩
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hu_real : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  calc
    |alpha - (r.num : ℝ) / (r.den : ℝ)| = |alpha - (r : ℝ)| := by
      congr 2
      exact (Rat.cast_def r).symm
    _ ≤ 1 / (((u : ℝ) + 1) * r.den) := by simpa using hr
    _ ≤ (((r.den : ℝ) * u))⁻¹ := by
      rw [inv_eq_one_div]
      refine one_div_le_one_div_of_le (mul_pos hden hu_real) ?_
      nlinarith

/-- Passing to the graph injects every quadruple respected by `phi` into an
additive-energy quadruple in the product group. -/
theorem lemma_6_2_holds : lemma_6_2 := by
  intro N _ gamma B phi _ hadd
  classical
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
  · intro q hq r hr hqr
    simp only [toEnergy, graphPoint, Prod.mk.injEq] at hqr
    funext i
    fin_cases i <;> tauto

/-- Lemma 5.15 is a finite averaging argument: mean zero makes the total
positive discrepancy half the total absolute discrepancy, and pigeonholing
then supplies a large cell. -/
theorem lemma_5_15_holds : lemma_5_15 := by
  intro N M _ f P alpha hM hAlpha hf hmean hpart hlarge
  classical
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
    have hne : (Finset.univ : Finset (Fin M)).Nonempty := by
      exact ⟨⟨0, hM⟩, Finset.mem_univ _⟩
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
    have hne : (Finset.univ : Finset (Fin M)).Nonempty := by
      exact ⟨⟨0, hM⟩, Finset.mem_univ _⟩
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

/-- Finite Fubini--Markov interchange in the form used by Lemma 10.7. -/
private theorem almostEvery_swap_of_nonneg {X Y : Type*}
    [DecidableEq X] [DecidableEq Y] (theta : ℝ) (U : Finset X) (V : Finset Y)
    (Q : X → Y → Prop) (htheta : 0 ≤ theta)
    (hcol : ∀ y, y ∈ V → AlmostEvery (1 - theta) U fun x => Q x y) :
    AlmostEvery (1 - Real.sqrt theta) U fun x =>
      AlmostEvery (1 - Real.sqrt theta) V fun y => Q x y := by
  classical
  simp only [AlmostEvery] at hcol ⊢
  let t : ℝ := Real.sqrt theta
  let row : X → ℕ := fun x => (V.filter fun y => Q x y).card
  let col : Y → ℕ := fun y => (U.filter fun x => Q x y).card
  let good : X → Prop := fun x => (1 - t) * V.card ≤ row x
  let G : Finset X := U.filter good
  let H : Finset X := U.filter fun x => ¬good x
  change (1 - t) * U.card ≤ (G.card : ℝ)
  by_cases ht_large : 1 ≤ t
  · exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht_large)
      (Nat.cast_nonneg U.card)).trans (Nat.cast_nonneg G.card)
  by_cases ht_zero : t = 0
  · have htheta_zero : theta = 0 := by
      exact (Real.sqrt_eq_zero htheta).mp (by simpa [t] using ht_zero)
    have hQ : ∀ x, x ∈ U → ∀ y, y ∈ V → Q x y := by
      intro x hx y hy
      have hc := hcol y hy
      have hcNat : U.card ≤ (U.filter fun x => Q x y).card := by
        exact_mod_cast (by simpa [htheta_zero] using hc)
      have heq : (U.filter fun x => Q x y) = U :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hcNat
      have hxfilter : x ∈ U.filter (fun z => Q z y) := by
        rw [heq]
        exact hx
      exact (Finset.mem_filter.mp hxfilter).2
    have hGU : G = U := by
      apply Finset.filter_eq_self.2
      intro x hx
      change (1 - t) * (V.card : ℝ) ≤ (row x : ℝ)
      have hrow : row x = V.card := by
        dsimp [row]
        rw [Finset.filter_eq_self.2]
        exact fun y hy => hQ x hx y hy
      rw [hrow, ht_zero]
      simp
    rw [hGU, ht_zero]
    simp
  have ht_pos : 0 < t := lt_of_le_of_ne (by dsimp [t]; positivity) (Ne.symm ht_zero)
  have ht_lt_one : t < 1 := lt_of_not_ge ht_large
  have htheta_sq : t ^ 2 = theta := by
    dsimp [t]
    exact Real.sq_sqrt htheta
  by_cases hV : V = ∅
  · subst V
    have hGU : G = U := by simp [G, good, row]
    rw [hGU]
    have ht_nonneg : 0 ≤ t := by dsimp [t]; positivity
    have hU_nonneg : (0 : ℝ) ≤ U.card := Nat.cast_nonneg U.card
    nlinarith
  have hVposNat : 0 < V.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hV)
  have hVpos : (0 : ℝ) < V.card := by exact_mod_cast hVposNat
  by_contra hgoal
  have hGlt : (G.card : ℝ) < (1 - t) * U.card := lt_of_not_ge hgoal
  have hGHNat : G.card + H.card = U.card := by
    simpa [G, H] using Finset.card_filter_add_card_filter_not (s := U) good
  have hGH : (G.card : ℝ) + H.card = U.card := by exact_mod_cast hGHNat
  have hlower :
      (1 - theta) * U.card * V.card ≤ ∑ y ∈ V, (col y : ℝ) := by
    calc
      _ = ∑ _y ∈ V, ((1 - theta) * U.card) := by simp; ring
      _ ≤ ∑ y ∈ V, (col y : ℝ) := by
        apply Finset.sum_le_sum
        intro y hy
        simpa [col] using hcol y hy
  have hdouble :
      (∑ y ∈ V, (col y : ℝ)) = ∑ x ∈ U, (row x : ℝ) := by
    dsimp [col, row]
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    rw [Finset.sum_comm]
  have hupper :
      (∑ x ∈ U, (row x : ℝ)) ≤
        (G.card : ℝ) * V.card + H.card * ((1 - t) * V.card) := by
    calc
      _ = (∑ x ∈ U with good x, (row x : ℝ)) +
          ∑ x ∈ U with ¬good x, (row x : ℝ) := by
            exact (Finset.sum_filter_add_sum_filter_not U good
              (fun x => (row x : ℝ))).symm
      _ ≤ (∑ _x ∈ U with good _x, (V.card : ℝ)) +
          ∑ _x ∈ U with ¬good _x, ((1 - t) * V.card) := by
            apply add_le_add
            · apply Finset.sum_le_sum
              intro x _
              exact_mod_cast Finset.card_filter_le V (Q x)
            · apply Finset.sum_le_sum
              intro x hx
              exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hx).2)
      _ = (G.card : ℝ) * V.card + H.card * ((1 - t) * V.card) := by
        simp [G, H]
  have hbound :
      (1 - theta) * U.card * V.card ≤
        (G.card : ℝ) * V.card + H.card * ((1 - t) * V.card) := by
    exact hlower.trans (hdouble.le.trans hupper)
  have hpositive :
      0 < (((1 - t) * (U.card : ℝ) - G.card) * t * V.card) := by
    exact mul_pos (mul_pos (sub_pos.mpr hGlt) ht_pos) hVpos
  have hid :
      (1 - theta) * (U.card : ℝ) * V.card -
          ((G.card : ℝ) * V.card + H.card * ((1 - t) * V.card)) =
        ((1 - t) * U.card - G.card) * t * V.card := by
    rw [← htheta_sq, ← hGH]
    ring
  nlinarith

/-- Lemma 10.7 is the preceding finite Fubini--Markov interchange applied to
the local difference relation. -/
theorem lemma_10_7_holds : lemma_10_7 := by
  intro N _ X _ _ D phi W B B' psi eta
  dsimp
  intro hmodel
  rcases hmodel with ⟨_, _, hmodel⟩
  apply almostEvery_swap_of_nonneg
  · apply mul_nonneg (by norm_num)
    by_cases heta : 0 ≤ eta
    · exact Real.rpow_nonneg heta _
    · have heta_neg : eta < 0 := lt_of_not_ge heta
      rw [Real.rpow_def_of_neg heta_neg]
      apply mul_nonneg (Real.exp_pos _).le
      exact (Real.cos_pos_of_mem_Ioo (by
        have hpi := Real.pi_pos
        constructor <;> norm_num <;> nlinarith)).le
  · exact hmodel

/-- Lemma 9.1 is the weighted Hölder inequality with weight and function
both equal to `a i ^ 2`, and exponent seven. -/
theorem lemma_9_1_holds : lemma_9_1 := by
  intro n a ha
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
