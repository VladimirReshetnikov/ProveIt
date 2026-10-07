import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

noncomputable def partitionCell (cell : Ω → ι) (i : ι) : Finset Ω := by
  classical
  exact Finset.univ.filter (fun x => cell x = i)

omit [Fintype ι] in
theorem mem_partitionCell (cell : Ω → ι) (i : ι) (x : Ω) :
    x ∈ partitionCell cell i ↔ cell x = i := by
  classical
  simp [partitionCell]

theorem sum_partitionCell (cell : Ω → ι) (f : Ω → ℝ) :
    (∑ i, ∑ x ∈ partitionCell cell i, f x) = ∑ x, f x := by
  classical
  simp only [partitionCell, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem card_partitionCell_sum (cell : Ω → ι) :
    (∑ i, ((partitionCell cell i).card : ℝ)) = (Fintype.card Ω : ℝ) := by
  simpa using sum_partitionCell cell (fun _ => 1)

omit [Fintype Ω] in
theorem score_le_frozen_on_cell (S : Finset Ω) (f B : Ω → ℝ) {b c ω : ℝ}
    (hf : ∀ x ∈ S, |f x - b| ≤ 1)
    (hclose : ∀ x ∈ S, |B x - c| ≤ ω) :
    (∑ x ∈ S, (f x - b) * B x) ≤ c * (∑ x ∈ S, (f x - b)) + ω * S.card := by
  have hpoint (x : Ω) (hx : x ∈ S) :
      (f x - b) * B x ≤ c * (f x - b) + ω := by
    have hprod : (f x - b) * (B x - c) ≤ ω := by
      calc
        _ ≤ |(f x - b) * (B x - c)| := le_abs_self _
        _ = |f x - b| * |B x - c| := abs_mul _ _
        _ ≤ 1 * ω := mul_le_mul (hf x hx) (hclose x hx) (abs_nonneg _) (by norm_num)
        _ = ω := one_mul _
    nlinarith
  calc
    _ ≤ ∑ x ∈ S, (c * (f x - b) + ω) := Finset.sum_le_sum hpoint
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

theorem exists_large_cell_positive_sum (cell : Ω → ι) (f B : Ω → ℝ) (c : ι → ℝ)
    {b ω : ℝ} (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hB : ∀ x, B x ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hω : 0 ≤ ω) (hclose : ∀ x, |B x - c (cell x)| ≤ ω)
    (hscore : (Fintype.card ι : ℝ) * L + ω * Fintype.card Ω <
      ∑ x, (f x - b) * B x) :
    ∃ i, L ≤ ((partitionCell cell i).card : ℝ) ∧
      0 < ∑ x ∈ partitionCell cell i, (f x - b) := by
  classical
  by_contra hnone
  push Not at hnone
  have hcell (i : ι) :
      (∑ x ∈ partitionCell cell i, (f x - b) * B x) ≤
        (L : ℝ) + ω * (partitionCell cell i).card := by
    by_cases hlarge : L ≤ ((partitionCell cell i).card : ℝ)
    · have hbalanced := hnone i hlarge
      have hfreeze := score_le_frozen_on_cell (partitionCell cell i) f B (b := b) (c := c i)
        (fun x _ => abs_le.mpr ⟨by linarith [(hf x).1, hb.2], by linarith [(hf x).2, hb.1]⟩)
        (fun x hx => by simpa only [(mem_partitionCell cell i x).mp hx] using hclose x)
      have hnonpos : c i * (∑ x ∈ partitionCell cell i, (f x - b)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (hc i) hbalanced
      linarith
    · have hbound : (∑ x ∈ partitionCell cell i, (f x - b) * B x) ≤
          ((partitionCell cell i).card : ℝ) := by
        calc
          _ ≤ ∑ x ∈ partitionCell cell i, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro x _
            exact ((mul_le_mul_of_nonneg_right (show f x - b ≤ 1 by linarith [(hf x).2, hb.1])
              (hB x).1).trans_eq (one_mul _)).trans (hB x).2
          _ = _ := by simp
      have hcard : ((partitionCell cell i).card : ℝ) ≤ L := le_of_lt (lt_of_not_ge hlarge)
      have herror : 0 ≤ ω * (partitionCell cell i).card := mul_nonneg hω (Nat.cast_nonneg _)
      linarith
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hcell i)
  rw [sum_partitionCell] at htotal
  have hbudget : (∑ i, ((L : ℝ) + ω * (partitionCell cell i).card)) =
      (Fintype.card ι : ℝ) * L + ω * Fintype.card Ω := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, card_partitionCell_sum]
    simp
  rw [hbudget] at htotal
  exact (not_lt_of_ge htotal) hscore

theorem exists_large_cell_density_increment (cell : Ω → ι) (f B : Ω → ℝ) (c : ι → ℝ)
    {b ω : ℝ} (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hB : ∀ x, B x ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hω : 0 ≤ ω) (hclose : ∀ x, |B x - c (cell x)| ≤ ω)
    (hscore : (Fintype.card ι : ℝ) * L + ω * Fintype.card Ω <
      ∑ x, (f x - b) * B x) :
    ∃ i, L ≤ ((partitionCell cell i).card : ℝ) ∧
      b < 𝔼 x ∈ partitionCell cell i, f x := by
  obtain ⟨i, hlarge, hpos⟩ := exists_large_cell_positive_sum cell f B c L hL hf hb hB hc hω hclose hscore
  have hne : (partitionCell cell i).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hpos
    simp at hpos
  refine ⟨i, hlarge, ?_⟩
  rw [Finset.expect_eq_sum_div_card]
  apply (lt_div_iff₀ (show (0 : ℝ) < (partitionCell cell i).card by exact_mod_cast hne.card_pos)).mpr
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hpos
  nlinarith

theorem exists_large_cell_of_normalized_score [Nonempty Ω]
    (cell : Ω → ι) (f B : Ω → ℝ) (c : ι → ℝ)
    {b ω σ : ℝ} (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hB : ∀ x, B x ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hω : 0 ≤ ω) (hclose : ∀ x, |B x - c (cell x)| ≤ ω)
    (hscore : σ ≤ 𝔼 x, (f x - b) * B x)
    (hbudget : (Fintype.card ι : ℝ) * L / Fintype.card Ω + ω < σ) :
    ∃ i, L ≤ ((partitionCell cell i).card : ℝ) ∧
      b < 𝔼 x ∈ partitionCell cell i, f x := by
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hscore' : σ * Fintype.card Ω ≤ ∑ x, (f x - b) * B x := by
    apply (le_div_iff₀ hN).mp
    simpa only [Fintype.expect_eq_sum_div_card] using hscore
  apply exists_large_cell_density_increment cell f B c L hL hf hb hB hc hω hclose
  apply lt_of_lt_of_le _ hscore'
  calc
    _ = ((Fintype.card ι : ℝ) * L / Fintype.card Ω + ω) * Fintype.card Ω := by
      rw [add_mul, div_mul_cancel₀ _ hN.ne']
    _ < σ * Fintype.card Ω := mul_lt_mul_of_pos_right hbudget hN

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_good_partition_score {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]
    (cell : Ω → I) (good : I → Prop) [DecidablePred good] (g : Ω → ℝ) {B τ ρ S : ℝ}
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hg : ∀ x, g x ≤ B)
    (hbad : (𝔼 x, if good (cell x) then (0 : ℝ) else 1) ≤ ρ)
    (hscore : S ≤ 𝔼 x, g x) (hbudget : τ + B * ρ < S) :
    ∃ i, good i ∧ τ < 𝔼 x ∈ partitionCell cell i, g x := by
  classical
  by_contra! hnone
  let b : Ω → ℝ := fun x => if good (cell x) then 0 else 1
  have hcell (i : I) : (∑ x ∈ partitionCell cell i, g x) ≤
      τ * (partitionCell cell i).card + B * ∑ x ∈ partitionCell cell i, b x := by
    by_cases hi : good i
    · have hb : (∑ x ∈ partitionCell cell i, b x) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        simp only [b, (mem_partitionCell _ _ _).mp hx, hi, ite_true]
      rw [hb, mul_zero, add_zero]
      have h := mul_le_mul_of_nonneg_left (hnone i hi)
        (Nat.cast_nonneg (partitionCell cell i).card : (0 : ℝ) ≤ _)
      rw [Finset.card_mul_expect] at h
      simpa only [mul_comm] using h
    · have hb : (∑ x ∈ partitionCell cell i, b x) = (partitionCell cell i).card := by
        calc
          _ = ∑ _x ∈ partitionCell cell i, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro x hx
            simp only [b, (mem_partitionCell _ _ _).mp hx, hi, ite_false]
          _ = _ := by simp
      rw [hb]
      have hs : (∑ x ∈ partitionCell cell i, g x) ≤ B * (partitionCell cell i).card := by
        calc
          _ ≤ ∑ _x ∈ partitionCell cell i, B := Finset.sum_le_sum (fun x _ => hg x)
          _ = _ := by simp [mul_comm]
      exact hs.trans (le_add_of_nonneg_left (mul_nonneg hτ (Nat.cast_nonneg _)))
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) => hcell i)
  rw [sum_partitionCell, Finset.sum_add_distrib, ← Finset.mul_sum, card_partitionCell_sum,
    ← Finset.mul_sum, sum_partitionCell] at hsum
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hupper : (𝔼 x, g x) ≤ τ + B * (𝔼 x, b x) := by
    rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
    apply (div_le_iff₀ hN).mpr
    convert hsum using 1
    field_simp
  have hb : (𝔼 x, b x) ≤ ρ := hbad
  have hfinal := hupper.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hb hB))
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_cell_score {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
    (cell : Ω → ι) (g : Ω → ℝ) {σ τ L : ℝ} (hL : 0 ≤ L) (hτ : 0 ≤ τ)
    (hg : ∀ x, g x ≤ 1) (hscore : σ ≤ 𝔼 x, g x)
    (hbudget : (Fintype.card ι : ℝ) * L / Fintype.card Ω + τ < σ) :
    ∃ i, L ≤ ((partitionCell cell i).card : ℝ) ∧ τ < 𝔼 x ∈ partitionCell cell i, g x := by
  classical
  by_contra! hnone
  have hcell (i : ι) : (∑ x ∈ partitionCell cell i, g x) ≤ L + τ * (partitionCell cell i).card := by
    by_cases hlarge : L ≤ ((partitionCell cell i).card : ℝ)
    · have h := mul_le_mul_of_nonneg_left (hnone i hlarge) (Nat.cast_nonneg (partitionCell cell i).card : (0 : ℝ) ≤ _)
      rw [Finset.card_mul_expect] at h
      nlinarith
    · have hsum : (∑ x ∈ partitionCell cell i, g x) ≤ ((partitionCell cell i).card : ℝ) := by
        calc
          _ ≤ ∑ x ∈ partitionCell cell i, (1 : ℝ) := Finset.sum_le_sum fun x _ => hg x
          _ = _ := by simp
      have hnonneg := mul_nonneg hτ (Nat.cast_nonneg (partitionCell cell i).card : (0 : ℝ) ≤ _)
      linarith
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hcell i)
  rw [sum_partitionCell, Finset.sum_add_distrib, ← Finset.mul_sum, card_partitionCell_sum] at htotal
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htotal
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hscore' := (le_div_iff₀ hN).mp (show σ ≤ (∑ x, g x) / Fintype.card Ω by
    simpa only [Fintype.expect_eq_sum_div_card] using hscore)
  have hbudget' := mul_lt_mul_of_pos_right hbudget hN
  rw [add_mul, div_mul_cancel₀ _ hN.ne'] at hbudget'
  nlinarith

theorem weighted_score_le_of_close {f b B C ε : ℝ}
    (hf : f ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hclose : dist B C ≤ ε) : (f - b) * B ≤ (f - b) * C + ε := by
  have hf' : |f - b| ≤ 1 := abs_le.mpr ⟨by linarith [hf.1, hb.2], by linarith [hf.2, hb.1]⟩
  have hdiff : (f - b) * (B - C) ≤ ε := by
    calc
      _ ≤ |(f - b) * (B - C)| := le_abs_self _
      _ = |f - b| * |B - C| := abs_mul _ _
      _ ≤ 1 * ε := mul_le_mul hf' (by simpa only [Real.dist_eq] using hclose) (abs_nonneg _) (by norm_num)
      _ = ε := one_mul _
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem unit_weight_score_error {a W V ε : ℝ} (ha : |a| ≤ 1) (hclose : dist W V ≤ ε) :
    a * W ≤ a * V + ε := by
  have h : a * (W - V) ≤ ε := by
    calc
      _ ≤ |a * (W - V)| := le_abs_self _
      _ = |a| * |W - V| := abs_mul _ _
      _ ≤ 1 * ε := mul_le_mul ha (by simpa only [Real.dist_eq] using hclose) (abs_nonneg _) (by norm_num)
      _ = ε := one_mul _
  nlinarith

theorem exists_good_frozen_partition_score {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]
    (cell : Ω → I) (good : I → Prop) [DecidablePred good]
    (a W : Ω → ℝ) (V : I → Ω → ℝ) {B τ ρ ε S : ℝ}
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (ha : ∀ x, |a x| ≤ 1) (hW : ∀ x, a x * W x ≤ B)
    (hbad : (𝔼 x, if good (cell x) then (0 : ℝ) else 1) ≤ ρ)
    (hclose : ∀ x, dist (W x) (V (cell x) x) ≤ ε)
    (hscore : S ≤ 𝔼 x, a x * W x) (hbudget : τ + ε + B * ρ < S) :
    ∃ i, good i ∧ τ < 𝔼 x ∈ partitionCell cell i, a x * V i x := by
  obtain ⟨i, hi, hs⟩ := exists_good_partition_score cell good (fun x => a x * W x)
    hB (add_nonneg hτ hε) hW hbad hscore hbudget
  have hne : (partitionCell cell i).Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [hz, Finset.expect_empty] at hs
    linarith
  have herr : (𝔼 x ∈ partitionCell cell i, a x * W x) ≤
      (𝔼 x ∈ partitionCell cell i, a x * V i x) + ε := by
    calc
      _ ≤ 𝔼 x ∈ partitionCell cell i, (a x * V i x + ε) := by
        apply Finset.expect_le_expect
        intro x hx
        apply unit_weight_score_error (ha x)
        simpa only [(mem_partitionCell _ _ _).mp hx] using hclose x
      _ = _ := by rw [Finset.expect_add_distrib, Finset.expect_const hne]
  exact ⟨i, hi, by linarith⟩

end Erdos3

end

end OAI
