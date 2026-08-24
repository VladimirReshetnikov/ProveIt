import GowersSzemeredi.Proofs03ProgressionAverage

/-!
# Counting modular progressions from higher uniformity

This module proves the repaired prime-modulus form of Corollary 3.3.  The
empty-family and one-function cases are retained explicitly, while every
nontrivial summand is padded by constant-one functions up to its largest
index and bounded by Theorem 3.2.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma cor33_countWhere_cast_complex {T : Type*} [Fintype T]
    (P : T → Prop) [DecidablePred P] :
    (countWhere P : Complex) = ∑ x : T, if P x then 1 else 0 := by
  classical
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  simp

private lemma cor33_translated_count_eq_indicator {N k : Nat} [NeZero N]
    (A : Fin k → Finset (ZMod N)) :
    (translatedIntersectionCount A : Complex) =
      ∑ r : ZMod N, ∑ s : ZMod N,
        ∏ i : Fin k, indicator (A i) (s - (((i : Nat) + 1 : ZMod N) * r)) := by
  classical
  unfold translatedIntersectionCount
  rw [cor33_countWhere_cast_complex, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : ∀ i : Fin k, s - ((i : Nat) + 1) * r ∈ A i
  · simp [h, indicator]
  · simp only [h, if_false, indicator]
    change 0 = ∏ i ∈ (Finset.univ : Finset (Fin k)),
      if s - ((i : Nat) + 1) * r ∈ A i then 1 else 0
    rw [Finset.prod_boole]
    simpa using h

private lemma cor33_density_eq {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (delta : Real)
    (hcard : (A.card : Real) = delta * N) : density A = delta := by
  rw [density, hcard]
  exact mul_div_cancel_right₀ delta (by exact_mod_cast NeZero.ne N)

private lemma cor33_indicator_eq_balanced_add {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (delta : Real)
    (hcard : (A.card : Real) = delta * N) (x : ZMod N) :
    indicator A x = balanced A x + delta := by
  rw [balanced, cor33_density_eq A delta hcard]
  ring

private lemma cor33_balanced_discValued {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) : DiscValued (balanced A) := by
  intro x
  classical
  have hd0 : 0 ≤ density A := density_nonneg A
  have hd1 : density A ≤ 1 := density_le_one A
  by_cases hx : x ∈ A
  · simp only [balanced, indicator, hx, if_true]
    norm_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hd1)]
    linarith
  · simp only [balanced, indicator, hx, if_false, zero_sub]
    norm_cast
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hd0]
    exact hd1

private def cor33Coefficient {k : Nat} (delta : Fin k → Real)
    (B : Finset (Fin k)) : Real :=
  ∏ i ∈ Bᶜ, delta i

private def cor33Progression {N k : Nat} [NeZero N]
    (A : Fin k → Finset (ZMod N)) (B : Finset (Fin k)) : Complex :=
  ∑ r : ZMod N, ∑ s : ZMod N,
    ∏ i ∈ B, balanced (A i) (s - (((i : Nat) + 1 : ZMod N) * r))

private def cor33PrefixFamily {N k m : Nat} [NeZero N]
    (A : Fin k → Finset (ZMod N)) (B : Finset (Fin k)) (hm : m ≤ k) :
    Fin m → ZMod N → Complex :=
  fun i x ↦ if Fin.castLE hm i ∈ B then balanced (A (Fin.castLE hm i)) x else 1

private lemma cor33_prefix_product {N k m : Nat} [NeZero N]
    (A : Fin k → Finset (ZMod N)) (B : Finset (Fin k)) (hm : m ≤ k)
    (hB : ∀ i ∈ B, (i : Nat) < m) (s r : ZMod N) :
    (∏ i : Fin m, cor33PrefixFamily A B hm i (s - (i : Nat) * r)) =
      ∏ i ∈ B, balanced (A i) (s - (i : Nat) * r) := by
  classical
  unfold cor33PrefixFamily
  rw [← Finset.prod_filter]
  apply Finset.prod_bij (fun i _ ↦ Fin.castLE hm i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi
  · intro i₁ _ i₂ _ hii
    apply Fin.ext
    have hv : (Fin.castLE hm i₁).val = (Fin.castLE hm i₂).val :=
      congrArg (fun x : Fin k ↦ x.val) hii
    exact hv
  · intro i hi
    let i' : Fin m := ⟨i, hB i hi⟩
    refine ⟨i', ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [i', Fin.castLE] using hi
    · apply Fin.ext
      rfl
  · intro i _
    rfl

private lemma cor33_progression_eq_prefix {N k m : Nat} [NeZero N]
    (A : Fin k → Finset (ZMod N)) (B : Finset (Fin k)) (hm : m ≤ k)
    (hB : ∀ i ∈ B, (i : Nat) < m) :
    cor33Progression A B = progressionAverage (cor33PrefixFamily A B hm) := by
  classical
  unfold cor33Progression progressionAverage
  apply Finset.sum_congr rfl
  intro r _
  calc
    (∑ s : ZMod N,
        ∏ i ∈ B, balanced (A i) (s - (((i : Nat) + 1 : ZMod N) * r))) =
        ∑ s : ZMod N,
          ∏ i ∈ B,
            balanced (A i) ((s + r) - (((i : Nat) + 1 : ZMod N) * r)) := by
      exact (Equiv.sum_comp (Equiv.addRight r)
        (fun s : ZMod N ↦
          ∏ i ∈ B,
            balanced (A i) (s - (((i : Nat) + 1 : ZMod N) * r)))).symm
    _ = ∑ s : ZMod N,
          ∏ i ∈ B, balanced (A i) (s - (i : Nat) * r) := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.prod_congr rfl
      intro i _
      congr 1
      ring
    _ = ∑ s : ZMod N,
          ∏ i : Fin m, cor33PrefixFamily A B hm i (s - (i : Nat) * r) := by
      apply Finset.sum_congr rfl
      intro s _
      exact (cor33_prefix_product A B hm hB s r).symm

private lemma cor33_prefix_discValued {N k m : Nat} [NeZero N]
    (A : Fin k → Finset (ZMod N)) (B : Finset (Fin k)) (hm : m ≤ k) :
    ∀ i, DiscValued (cor33PrefixFamily A B hm i) := by
  intro i x
  classical
  unfold cor33PrefixFamily
  split
  · exact cor33_balanced_discValued _ _
  · simp

private lemma cor33_balanced_uniform_zero {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) : UniformOfDegree (balanced A) 0 0 := by
  unfold UniformOfDegree Point cubeDifference
  simp [iteratedDifference]

private lemma cor33_progression_bound {N k : Nat} [NeZero N] [Fact N.Prime]
    (hkN : k ≤ N) (A : Fin k → Finset (ZMod N)) (alpha : Real)
    (ha0 : 0 ≤ alpha)
    (huniform : ∀ i : Fin k, 3 ≤ (i : Nat) + 1 →
      UniformSetOfDegree (A i) (alpha ^ ((2 : Nat) ^ (i : Nat))) ((i : Nat) - 1))
    (B : Finset (Fin k)) (hBne : B ≠ ∅) :
    ‖cor33Progression A B‖ ≤ alpha * (N : Real) ^ 2 := by
  classical
  have hBnon : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hBne
  let j : Fin k := B.max' hBnon
  have hjB : j ∈ B := Finset.max'_mem B hBnon
  have hm : (j : Nat) + 1 ≤ k := j.isLt
  have hBinPrefix : ∀ i ∈ B, (i : Nat) < (j : Nat) + 1 := by
    intro i hi
    exact Nat.lt_succ_of_le (Finset.le_max' B i hi)
  let g : Fin ((j : Nat) + 1) → ZMod N → Complex :=
    cor33PrefixFamily A B hm
  have hEq : cor33Progression A B = progressionAverage g := by
    exact cor33_progression_eq_prefix A B hm hBinPrefix
  have hgdisc : ∀ i, DiscValued (g i) :=
    cor33_prefix_discValued A B hm
  rw [hEq]
  by_cases hj0 : (j : Nat) = 0
  · have hembed (i : Fin ((j : Nat) + 1)) : Fin.castLE hm i = j := by
      apply Fin.ext
      change (i : Nat) = (j : Nat)
      omega
    have hg (i : Fin ((j : Nat) + 1)) : g i = balanced (A j) := by
      funext x
      simp only [g, cor33PrefixFamily, hembed i, hjB, if_true]
    have hzero : progressionAverage g = 0 := by
      unfold progressionAverage
      simp_rw [hg]
      apply Finset.sum_eq_zero
      intro r _
      calc
        (∑ s : ZMod N, ∏ i : Fin ((j : Nat) + 1),
            balanced (A j) (s - (i : Nat) * r)) =
            ∑ s : ZMod N, balanced (A j) s := by
          apply Finset.sum_congr rfl
          intro s _
          rw [show (j : Nat) + 1 = 1 by omega, Fin.prod_univ_one]
          simp
        _ = 0 := sum_balanced (A j)
    rw [hzero, norm_zero]
    exact mul_nonneg ha0 (sq_nonneg _)
  · have hj1 : 1 ≤ (j : Nat) := Nat.one_le_iff_ne_zero.mpr hj0
    have hmN : (j : Nat) + 1 ≤ N := hm.trans hkN
    have hlastEmbed : Fin.castLE hm (Fin.last (j : Nat)) = j := by
      apply Fin.ext
      simp
    by_cases hj2 : (j : Nat) = 1
    · have hlastUniform :
          ∀ i : Fin ((j : Nat) + 1), (i : Nat) + 1 = (j : Nat) + 1 →
            UniformOfDegree (g i) 0 ((j : Nat) + 1 - 2) := by
        intro i hi
        have hiLast : i = Fin.last (j : Nat) := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        subst i
        have hgLast : g (Fin.last (j : Nat)) = balanced (A j) := by
          funext x
          simp only [g, cor33PrefixFamily, hlastEmbed, hjB, if_true]
        rw [hgLast]
        convert cor33_balanced_uniform_zero (A j) using 1
        all_goals omega
      have ht := theorem_3_2_holds N ((j : Nat) + 1)
        (by omega) hmN g hgdisc 0 (by norm_num) hlastUniform
      have ht0 : ‖progressionAverage g‖ ≤ 0 := by
        simpa [hj2] using ht
      exact ht0.trans (mul_nonneg ha0 (sq_nonneg _))
    · have hj3 : 3 ≤ (j : Nat) + 1 := by omega
      have hlastUniform :
          ∀ i : Fin ((j : Nat) + 1), (i : Nat) + 1 = (j : Nat) + 1 →
            UniformOfDegree (g i) (alpha ^ ((2 : Nat) ^ (j : Nat)))
              ((j : Nat) + 1 - 2) := by
        intro i hi
        have hiLast : i = Fin.last (j : Nat) := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        subst i
        have hgLast : g (Fin.last (j : Nat)) = balanced (A j) := by
          funext x
          simp only [g, cor33PrefixFamily, hlastEmbed, hjB, if_true]
        rw [hgLast]
        have hU := huniform j hj3
        unfold UniformSetOfDegree at hU
        convert hU using 1
        all_goals omega
      have ht := theorem_3_2_holds N ((j : Nat) + 1)
        (by omega) hmN g hgdisc (alpha ^ ((2 : Nat) ^ (j : Nat)))
        (pow_nonneg ha0 _) hlastUniform
      have hcollapse :
          (alpha ^ ((2 : Nat) ^ (j : Nat))) ^
              ((1 : Real) / (2 : Real) ^ (j : Nat)) = alpha := by
        simpa only [one_div, Nat.cast_pow, Nat.cast_ofNat] using
          (Real.pow_rpow_inv_natCast ha0
            (by positivity : (2 : Nat) ^ (j : Nat) ≠ 0))
      simpa only [Nat.add_sub_cancel, hcollapse] using ht

private lemma cor33_count_expansion {N k : Nat} [NeZero N]
    (A : Fin k → Finset (ZMod N)) (delta : Fin k → Real)
    (hcard : ∀ i, (A i).card = delta i * N) :
    (translatedIntersectionCount A : Complex) =
      ∑ B : Finset (Fin k),
        (cor33Coefficient delta B : Complex) * cor33Progression A B := by
  classical
  rw [cor33_translated_count_eq_indicator]
  have hindicator (i : Fin k) (x : ZMod N) :
      indicator (A i) x = balanced (A i) x + delta i :=
    cor33_indicator_eq_balanced_add (A i) (delta i) (hcard i) x
  calc
    (∑ r : ZMod N, ∑ s : ZMod N,
        ∏ i : Fin k, indicator (A i) (s - (((i : Nat) + 1 : ZMod N) * r))) =
        ∑ r : ZMod N, ∑ s : ZMod N, ∑ B : Finset (Fin k),
          (∏ i ∈ B,
            balanced (A i) (s - (((i : Nat) + 1 : ZMod N) * r))) *
          ∏ i ∈ Bᶜ, (delta i : Complex) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      rw [show (∏ i : Fin k,
          indicator (A i) (s - (((i : Nat) + 1 : ZMod N) * r))) =
          ∏ i : Fin k,
            (balanced (A i) (s - (((i : Nat) + 1 : ZMod N) * r)) +
              (delta i : Complex)) by
        apply Finset.prod_congr rfl
        intro i _
        exact hindicator i _]
      exact Fintype.prod_add _ _
    _ = ∑ B : Finset (Fin k),
        (cor33Coefficient delta B : Complex) * cor33Progression A B := by
      have hcoeff (B : Finset (Fin k)) :
          (cor33Coefficient delta B : Complex) =
            ∏ i ∈ Bᶜ, (delta i : Complex) := by
        unfold cor33Coefficient
        push_cast
        rfl
      simp only [cor33Progression]
      calc
        (∑ r : ZMod N, ∑ s : ZMod N, ∑ B : Finset (Fin k),
            (∏ i ∈ B,
              balanced (A i) (s - (((i : Nat) + 1 : ZMod N) * r))) *
            ∏ i ∈ Bᶜ, (delta i : Complex)) =
            ∑ r : ZMod N, ∑ B : Finset (Fin k), ∑ s : ZMod N,
              (∏ i ∈ B,
                balanced (A i) (s - (((i : Nat) + 1 : ZMod N) * r))) *
              ∏ i ∈ Bᶜ, (delta i : Complex) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_comm]
        _ = ∑ B : Finset (Fin k), ∑ r : ZMod N, ∑ s : ZMod N,
              (∏ i ∈ B,
                balanced (A i) (s - (((i : Nat) + 1 : ZMod N) * r))) *
              ∏ i ∈ Bᶜ, (delta i : Complex) := by
          rw [Finset.sum_comm]
        _ = ∑ B : Finset (Fin k),
            (cor33Coefficient delta B : Complex) *
              ∑ r : ZMod N, ∑ s : ZMod N,
                ∏ i ∈ B,
                  balanced (A i) (s - (((i : Nat) + 1 : ZMod N) * r)) := by
          apply Finset.sum_congr rfl
          intro B _
          rw [hcoeff, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring

private lemma cor33_empty_term {N k : Nat} [NeZero N]
    (A : Fin k → Finset (ZMod N)) (delta : Fin k → Real) :
    (cor33Coefficient delta ∅ : Complex) * cor33Progression A ∅ =
      ((∏ i, delta i) * (N : Real) ^ 2 : Real) := by
  classical
  simp [cor33Coefficient, cor33Progression, ZMod.card, pow_two]

/-- **Corollary 3.3.** The number of translated modular progressions differs
from its density main term by at most `2^k α N²`. -/
theorem corollary_3_3_holds : corollary_3_3 := by
  intro N k _ _ hkN A delta alpha ha0 hcard huniform
  classical
  let T : Finset (Fin k) → Complex := fun B ↦
    (cor33Coefficient delta B : Complex) * cor33Progression A B
  let S : Finset (Finset (Fin k)) :=
    (Finset.univ : Finset (Finset (Fin k))).erase ∅
  have hcount : (translatedIntersectionCount A : Complex) = ∑ B, T B := by
    simpa only [T] using cor33_count_expansion A delta hcard
  have hempty : T ∅ = ((∏ i, delta i) * (N : Real) ^ 2 : Real) := by
    simpa only [T] using cor33_empty_term A delta
  have hrem :
      (((translatedIntersectionCount A : Real) -
          (∏ i, delta i) * (N : Real) ^ 2 : Real) : Complex) =
        ∑ B ∈ S, T B := by
    calc
      (((translatedIntersectionCount A : Real) -
          (∏ i, delta i) * (N : Real) ^ 2 : Real) : Complex) =
          (translatedIntersectionCount A : Complex) - T ∅ := by
        rw [hempty]
        push_cast
        rfl
      _ = (∑ B : Finset (Fin k), T B) - T ∅ := by rw [hcount]
      _ = ∑ B ∈ S, T B := by
        have herase := Finset.sum_erase_add
          (Finset.univ : Finset (Finset (Fin k))) T
          (Finset.mem_univ (∅ : Finset (Fin k)))
        change (∑ B : Finset (Fin k), T B) - T ∅ =
          ∑ B ∈ (Finset.univ : Finset (Finset (Fin k))).erase ∅, T B
        exact (sub_eq_iff_eq_add).2 herase.symm
  have hdelta0 (i : Fin k) : 0 ≤ delta i := by
    rw [← cor33_density_eq (A i) (delta i) (hcard i)]
    exact density_nonneg (A i)
  have hdelta1 (i : Fin k) : delta i ≤ 1 := by
    rw [← cor33_density_eq (A i) (delta i) (hcard i)]
    exact density_le_one (A i)
  have hcoeff (B : Finset (Fin k)) :
      ‖(cor33Coefficient delta B : Complex)‖ ≤ 1 := by
    have hc0 : 0 ≤ cor33Coefficient delta B := by
      unfold cor33Coefficient
      exact Finset.prod_nonneg fun i _ ↦ hdelta0 i
    have hc1 : cor33Coefficient delta B ≤ 1 := by
      unfold cor33Coefficient
      exact Finset.prod_le_one (fun i _ ↦ hdelta0 i) (fun i _ ↦ hdelta1 i)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
    exact hc1
  have hterm (B : Finset (Fin k)) (hBS : B ∈ S) :
      ‖T B‖ ≤ alpha * (N : Real) ^ 2 := by
    have hBne : B ≠ ∅ := (Finset.mem_erase.mp hBS).1
    have hp := cor33_progression_bound hkN A alpha ha0 huniform B hBne
    simp only [T, norm_mul]
    nlinarith [hcoeff B, norm_nonneg (cor33Coefficient delta B : Complex),
      norm_nonneg (cor33Progression A B), mul_nonneg ha0 (sq_nonneg (N : Real))]
  have hScard : S.card ≤ 2 ^ k := by
    calc
      S.card ≤ (Finset.univ : Finset (Finset (Fin k))).card :=
        Finset.card_le_card (Finset.erase_subset _ _)
      _ = 2 ^ k := by simp
  calc
    |(translatedIntersectionCount A : Real) -
        (∏ i, delta i) * (N : Real) ^ 2| =
        ‖(((translatedIntersectionCount A : Real) -
          (∏ i, delta i) * (N : Real) ^ 2 : Real) : Complex)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖∑ B ∈ S, T B‖ := by rw [hrem]
    _ ≤ ∑ B ∈ S, ‖T B‖ := norm_sum_le _ _
    _ ≤ ∑ _B ∈ S, alpha * (N : Real) ^ 2 := by
      apply Finset.sum_le_sum
      intro B hBS
      exact hterm B hBS
    _ = (S.card : Real) * (alpha * (N : Real) ^ 2) := by simp
    _ ≤ (2 ^ k : Real) * (alpha * (N : Real) ^ 2) := by
      gcongr
      exact_mod_cast hScard
    _ = 2 ^ k * alpha * (N : Real) ^ 2 := by ring

end LeanProofs.GowersSzemeredi
