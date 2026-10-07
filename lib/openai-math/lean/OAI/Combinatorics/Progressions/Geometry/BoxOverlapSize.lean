/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.OverlapCubeWeights

namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem weight_correlating_large_overlaps {A : Type*} [AddCommGroup A] [DecidableEq A]
    {Q : Finset A} (hQ : Q.Nonempty) (f u : A → ℂ) {ρ B δ : ℝ}
    (hρ : 0 ≤ ρ) (hB : 0 < B) (hδ : 0 ≤ δ)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hu : ∀ x ∈ Q, ‖u x‖ ≤ B)
    (hcorr : ρ ≤ ‖finiteCorrelation Q f u‖) :
    ρ ^ 2 / (2 * B ^ 2) - δ * (cubeDifferenceSupport Q).card / Q.card ≤
      ∑ h ∈ cubeDifferenceSupport Q, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        (if ρ ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
            (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ ∧
          δ * Q.card < ((derivativeSupport Q h).card : ℝ) then (1 : ℝ) else 0) := by
  classical
  let I := cubeDifferenceSupport Q
  let w := fun h => ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2
  let good := fun h => ρ ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
    (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖
  let small := fun h => ((derivativeSupport Q h).card : ℝ) ≤ δ * Q.card
  have hw (h : A) : 0 ≤ w h := by dsimp [w]; positivity
  have hpoint (h : A) : w h * (if good h then (1 : ℝ) else 0) ≤
      w h * (if good h ∧ ¬small h then (1 : ℝ) else 0) + (if small h then w h else 0) := by
    by_cases hg : good h <;> by_cases hs : small h <;> simp [hg, hs, hw]
  have hsplit := Finset.sum_le_sum (fun h (_ : h ∈ I) => hpoint h)
  rw [Finset.sum_add_distrib] at hsplit
  have hgood := weight_correlating_overlaps hQ f u hρ hB hf hu hcorr
  change ρ ^ 2 / (2 * B ^ 2) ≤ ∑ h ∈ I, w h * (if good h then (1 : ℝ) else 0) at hgood
  have hsmall : (∑ h ∈ I, if small h then w h else 0) ≤ δ * I.card / Q.card := by
    rw [← Finset.sum_filter]
    exact weight_small_overlaps hQ hδ
  have hresult : ρ ^ 2 / (2 * B ^ 2) - δ * I.card / Q.card ≤
      ∑ h ∈ I, w h * (if good h ∧ ¬small h then (1 : ℝ) else 0) := by linarith
  simpa only [I, w, good, small, not_le] using hresult

theorem weight_correlating_large_box_overlaps {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (T : ι → ℕ) [∀ i, NeZero (T i)] (f u : (ι → ℤ) → ℂ)
    {ρ B δ : ℝ} (hρ : 0 ≤ ρ) (hB : 0 < B) (hδ : 0 ≤ δ)
    (hf : ∀ x ∈ translatedIntegerBox a T, ‖f x‖ ≤ 1)
    (hu : ∀ x ∈ translatedIntegerBox a T, ‖u x‖ ≤ B)
    (hcorr : ρ ≤ ‖finiteCorrelation (translatedIntegerBox a T) f u‖) :
    let Q := translatedIntegerBox a T
    ρ ^ 2 / (2 * B ^ 2) - 2 ^ Fintype.card ι * δ ≤
      ∑ h ∈ cubeDifferenceSupport Q, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        (if ρ ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
            (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ ∧
          δ * Q.card < ((derivativeSupport Q h).card : ℝ) then (1 : ℝ) else 0) := by
  let Q := translatedIntegerBox a T
  have hQ : Q.Nonempty := translatedIntegerBox_nonempty T a
  have hq : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  have hd : ((cubeDifferenceSupport Q).card : ℝ) ≤ (2 : ℝ) ^ Fintype.card ι * Q.card := by
    exact_mod_cast card_box_differenceSupport_le a T
  have hloss : δ * (cubeDifferenceSupport Q).card / Q.card ≤ 2 ^ Fintype.card ι * δ := by
    apply (div_le_iff₀ hq).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd hδ]
  exact le_trans (by linarith) (weight_correlating_large_overlaps hQ f u hρ hB hδ hf hu hcorr)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

theorem box_gowers_lower_bound_of_overlaps {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (T : ι → ℕ) [∀ i, NeZero (T i)] (j : ℕ)
    (f : (ι → ℤ) → ℂ) (P : (ι → ℤ) → Prop) [DecidablePred P]
    {δ η μ : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hμ : μ ≤ ∑ h ∈ cubeDifferenceSupport (translatedIntegerBox a T),
      (((derivativeSupport (translatedIntegerBox a T) h).card : ℝ) /
        ((translatedIntegerBox a T).card : ℝ) ^ 2) * (if P h then (1 : ℝ) else 0))
    (hretained : ∀ h ∈ cubeDifferenceSupport (translatedIntegerBox a T), P h →
      δ * (translatedIntegerBox a T).card ≤
        ((derivativeSupport (translatedIntegerBox a T) h).card : ℝ) ∧
      η ≤ finiteSupportGowersNorm (j + 1) (derivativeSupport (translatedIntegerBox a T) h)
        (multiplicativeDerivative f h)) :
    ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) ^ Fintype.card ι * δ ^ (j + 1) *
        η ^ (2 ^ (j + 1)) * μ ≤
      finiteSupportGowersNorm (j + 2) (translatedIntegerBox a T) f ^ (2 ^ (j + 2)) := by
  let Q := translatedIntegerBox a T
  let c := ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) ^ Fintype.card ι
  let K := c * δ ^ (j + 1) * η ^ (2 ^ (j + 1))
  let W := fun h => ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2
  let V := fun h => (Nat.card (SupportedCube (j + 1) (derivativeSupport Q h : Set (ι → ℤ))) : ℝ) /
    Nat.card (SupportedCube (j + 2) (Q : Set (ι → ℤ)))
  let N := fun h => finiteSupportGowersNorm (j + 1) (derivativeSupport Q h) (multiplicativeDerivative f h)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hN (h : ι → ℤ) : 0 ≤ N h := by
    have hφ := (translatedIntegerBox_reflectsPairSums T a).mono
      (fun _ hx => (Finset.mem_filter.mp hx).1 :
        (derivativeSupport Q h : Set (ι → ℤ)) ⊆ (Q : Set (ι → ℤ)))
    dsimp [N]
    rw [finiteSupportGowersNorm_eq_restricted hφ]
    exact restrictedGowersNorm_nonneg j _ _
  have hpoint (h : ι → ℤ) (hh : h ∈ cubeDifferenceSupport Q) :
      K * (W h * (if P h then (1 : ℝ) else 0)) ≤ V h * N h ^ (2 ^ (j + 1)) := by
    by_cases hp : P h
    · simp only [ite_eq_left hp, mul_one]
      have hw : c * δ ^ (j + 1) * W h ≤ V h :=
        box_overlap_cube_weight a T j hh hδ (hretained h hh hp).1
      have hn : η ^ (2 ^ (j + 1)) ≤ N h ^ (2 ^ (j + 1)) :=
        pow_le_pow_left₀ hη (hretained h hh hp).2 _
      calc
        _ = (c * δ ^ (j + 1) * W h) * η ^ (2 ^ (j + 1)) := by dsimp [K]; ring
        _ ≤ _ := mul_le_mul hw hn (pow_nonneg hη _) (by dsimp [V]; positivity)
    · simp only [ite_eq_right hp, mul_zero]
      exact mul_nonneg (by dsimp [V]; positivity) (pow_nonneg (hN h) _)
  calc
    _ ≤ K * (∑ h ∈ cubeDifferenceSupport Q, W h * (if P h then (1 : ℝ) else 0)) :=
      mul_le_mul_of_nonneg_left hμ hK
    _ = ∑ h ∈ cubeDifferenceSupport Q, K * (W h * (if P h then (1 : ℝ) else 0)) :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ h ∈ cubeDifferenceSupport Q, V h * N h ^ (2 ^ (j + 1)) := Finset.sum_le_sum hpoint
    _ = _ := (finiteSupportGowersNorm_derivative (translatedIntegerBox_reflectsPairSums T a)
      (translatedIntegerBox_nonempty T a) j f).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem side_gt_of_prod_gt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : ι → ℝ) (hS : ∀ i, 0 ≤ S i) (hT : ∀ i, 0 < T i)
    (hST : ∀ i, S i ≤ T i) {δ : ℝ}
    (hprod : δ * ∏ i, T i < ∏ i, S i) (i : ι) : δ * T i < S i := by
  have hrest : (∏ j ∈ Finset.univ.erase i, S j) ≤ ∏ j ∈ Finset.univ.erase i, T j :=
    Finset.prod_le_prod₀ (fun j _ => hS j) (fun j _ => hST j)
  have hrestpos : 0 < ∏ j ∈ Finset.univ.erase i, T j := Finset.prod_pos (fun j _ => hT j)
  have hbound : (∏ j, S j) ≤ S i * ∏ j ∈ Finset.univ.erase i, T j := by
    rw [← Finset.mul_prod_erase Finset.univ S (Finset.mem_univ i)]
    exact mul_le_mul_of_nonneg_left hrest (hS i)
  have hlt := hprod.trans_le hbound
  rw [← Finset.mul_prod_erase Finset.univ T (Finset.mem_univ i), ← mul_assoc] at hlt
  exact (mul_lt_mul_iff_left₀ hrestpos).mp hlt

theorem box_overlap_side_gt_of_card_gt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (T : ι → ℕ) (hT : ∀ i, 0 < T i) (h : ι → ℤ) {δ : ℝ}
    (hcard : δ * (translatedIntegerBox a T).card <
      ((derivativeSupport (translatedIntegerBox a T) h).card : ℝ)) (i : ι) :
    δ * T i < (((T i : ℤ) - |h i|).toNat : ℝ) := by
  have hlen (j : ι) : ((T j : ℤ) - |h j|).toNat ≤ T j := by
    have ha := abs_nonneg (h j)
    omega
  apply side_gt_of_prod_gt (fun j => (((T j : ℤ) - |h j|).toNat : ℝ))
    (fun j => (T j : ℝ)) (fun j => Nat.cast_nonneg _) (fun j => by exact_mod_cast hT j)
    (fun j => by exact_mod_cast hlen j) _ i
  rw [derivativeSupport_translatedIntegerBox] at hcard
  simpa only [translatedIntegerBox, card_translateSupport, card_integerBox, Nat.cast_prod] using hcard

theorem cardinality_ge_overlap_weight {A : Type*} [AddCommGroup A] [DecidableEq A]
    {Q : Finset A} (hQ : Q.Nonempty) (I : Finset A) (P : A → Prop) [DecidablePred P]
    {μ : ℝ}
    (hweight : μ ≤ ∑ h ∈ I, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
      (if P h then (1 : ℝ) else 0)) :
    μ * Q.card ≤ ((I.filter P).card : ℝ) := by
  have hq : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  have hbound (h : A) : ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2 ≤
      1 / Q.card := by
    have hc : ((derivativeSupport Q h).card : ℝ) ≤ Q.card := by
      exact_mod_cast Finset.card_filter_le Q (fun x => x + h ∈ Q)
    apply (div_le_div_iff₀ (sq_pos_of_pos hq) hq).mpr
    nlinarith
  have hsum : (∑ h ∈ I, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
      (if P h then (1 : ℝ) else 0)) ≤ ((I.filter P).card : ℝ) / Q.card := by
    calc
      _ = ∑ h ∈ I.filter P, ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro h _
        split_ifs <;> simp
      _ ≤ ∑ _h ∈ I.filter P, 1 / (Q.card : ℝ) := Finset.sum_le_sum (fun h _ => hbound h)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  exact (le_div_iff₀ hq).mp (hweight.trans hsum)

end Erdos3

end

end OAI
