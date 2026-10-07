import OAI.Combinatorics.Progressions.Sampling.PivotGridBounds

namespace OAI

section

namespace Erdos3

noncomputable def pivotIterationBound (q r m : ℕ) (p B : ℝ) : ℝ :=
  Real.exp ((r : ℝ) * p * m / q) * B ^ ((r + 2) * m)

theorem pivotIterationBound_nonneg (q r m : ℕ) (p : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ pivotIterationBound q r m p B :=
  mul_nonneg (Real.exp_nonneg _) (pow_nonneg hB _)

theorem pivotIterationBound_zero (q m : ℕ) (p B : ℝ) :
    pivotIterationBound q 0 m p B = B ^ (2 * m) := by
  simp [pivotIterationBound]

theorem pivotIterationBound_step {q : ℕ} (hq : 1 ≤ q) (r m : ℕ) (p : ℝ)
    {B : ℝ} (hB : 1 ≤ B) :
    (B ^ m) ^ (q - 1) * Real.exp ((m : ℝ) * p) *
        pivotIterationBound q r (q * m) p B ≤
      (pivotIterationBound q (r + 1) m p B) ^ q := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have he : (m : ℝ) * p + r * p * (q * m) / q =
      q * (((r + 1 : ℕ) : ℝ) * p * m / q) := by
    push_cast
    field_simp [hq0]
    ring
  have hn : m * (q - 1) + (r + 2) * (q * m) ≤ ((r + 1 + 2) * m) * q := by
    have hsub : q - 1 + 1 = q := Nat.sub_add_cancel hq
    nlinarith
  unfold pivotIterationBound
  simp only [Nat.cast_mul]
  rw [mul_pow, ← Real.exp_nat_mul]
  calc
    (B ^ m) ^ (q - 1) * Real.exp ((m : ℝ) * p) *
        (Real.exp ((r : ℝ) * p * (q * m) / q) * B ^ ((r + 2) * (q * m))) =
      (Real.exp ((m : ℝ) * p) * Real.exp ((r : ℝ) * p * (q * m) / q)) *
        ((B ^ m) ^ (q - 1) * B ^ ((r + 2) * (q * m))) := by ring
    _ = Real.exp (q * (((r + 1 : ℕ) : ℝ) * p * m / q)) *
        B ^ (m * (q - 1) + (r + 2) * (q * m)) := by
      rw [← Real.exp_add, he, ← pow_mul, ← pow_add]
    _ ≤ Real.exp (q * (((r + 1 : ℕ) : ℝ) * p * m / q)) *
        B ^ (((r + 1 + 2) * m) * q) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hn) (Real.exp_nonneg _)
    _ = _ := by rw [pow_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivotStageCount_terminal_le {I R : Type*} [CommRing R] [Fintype R]
    {l q : ℕ} (v : Fin l → R) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (hab : IsUnit (b - a)) {parameter A : ℝ}
    (hparameter : 0 ≤ parameter) (hparameter1 : parameter ≤ 1) (hA : 0 ≤ A)
    (f g : R → ℝ)
    (hf : ∀ choice : (Fin l → Fin q) → Bool,
      (𝔼 z : Fin l → Fin q → R, 𝔼 u, 𝔼 w, ∏ beta : Fin l → Fin q,
        if choice beta then
          f (u + ∑ j, (a - v j) * z j (beta j)) *
          f (w + ∑ j, (a - v j) * z j (beta j)) else 1) ≤ A)
    (hg : ∀ choice : (Fin l → Fin q) → Bool,
      (𝔼 z : Fin l → Fin q → R, 𝔼 u, 𝔼 w, ∏ beta : Fin l → Fin q,
        if choice beta then
          g (u + ∑ j, (b - v j) * z j (beta j)) *
          g (w + ∑ j, (b - v j) * z j (beta j)) else 1) ≤ A) :
    |pivotStageCount (q := q) v (∅ : Finset I) slopes mu a b parameter f g| ≤ A := by
  rw [pivotStageCount_terminal v slopes mu a b hab]
  exact countingKernelProductAverage_outer_abs_le hparameter hparameter1 hA _ _ hf hg

theorem pivotStageCount_iterate {I R : Type*} [DecidableEq I] [CommRing R] [Fintype R]
    (s n : ℕ) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) {p B : ℝ} (hB : 1 ≤ B)
    (hmu : ∀ i x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p)
    (hroot : ∀ {l : ℕ}, l ≤ s → ∀ (v : Fin l → R) (i : I),
      (∀ j, IsUnit (slopes i - v j)) →
      (𝔼 z : Fin l → Fin (2 ^ (n + 1)) → R, 𝔼 w,
        pivotRootFactor v (slopes i) (mu i) z w) ≤ B ^ ((2 ^ (n + 1)) ^ l))
    (hterminal : ∀ {l : ℕ}, l ≤ s → ∀ (v : Fin l → R),
      PivotCompatible v (∅ : Finset I) slopes a b →
      |pivotStageCount (q := 2 ^ (n + 1)) v (∅ : Finset I) slopes mu a b parameter f g| ≤
        B ^ (2 * (2 ^ (n + 1)) ^ l))
    {l : ℕ} (v : Fin l → R) (S : Finset I) (hsize : l + S.card ≤ s)
    (hcompatible : PivotCompatible v S slopes a b) :
    |pivotStageCount (q := 2 ^ (n + 1)) v S slopes mu a b parameter f g| ≤
      pivotIterationBound (2 ^ (n + 1)) S.card ((2 ^ (n + 1)) ^ l) p B := by
  have hq : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow (n + 1) 2 (by omega)
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  induction S using Finset.induction_on generalizing l with
  | empty =>
      simpa only [Finset.card_empty, pivotIterationBound_zero] using
        hterminal (by simpa only [Finset.card_empty, add_zero] using hsize) v hcompatible
  | @insert i S hi ih =>
      have hmem : i ∈ insert i S := Finset.mem_insert_self i S
      have hc := hcompatible.cons_erase hmem
      rw [Finset.erase_insert hi] at hc
      have hs : (l + 1) + S.card ≤ s := by
        rw [Finset.card_insert_of_notMem hi] at hsize
        omega
      have hn := ih (Fin.cons (slopes i) v) hs hc
      have hrep : (2 ^ (n + 1)) ^ (l + 1) = 2 ^ (n + 1) * (2 ^ (n + 1)) ^ l := by
        rw [pow_succ, Nat.mul_comm]
      rw [hrep] at hn
      have hr := pivotStageCount_step n v (insert i S) slopes mu a b parameter f g hmem (hmu i)
      rw [Finset.erase_insert hi] at hr
      have hd := hroot (show l ≤ s by omega) v i
        (fun j => (hcompatible.2.2.2 j).2.2 i hmem)
      have hd0 : 0 ≤ (𝔼 z : Fin l → Fin (2 ^ (n + 1)) → R, 𝔼 w,
          pivotRootFactor v (slopes i) (mu i) z w) :=
        Finset.expect_nonneg (fun z _ => Finset.expect_nonneg
          (fun w _ => pivotRootFactor_nonneg v (slopes i) (mu i) (fun x => (hmu i x).1) z w))
      have hcoef := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hd0 hd (2 ^ (n + 1) - 1))
        (Real.exp_nonneg (((2 ^ (n + 1)) ^ l : ℕ) * p))
      have hcoef0 : 0 ≤ (𝔼 z : Fin l → Fin (2 ^ (n + 1)) → R, 𝔼 w,
          pivotRootFactor v (slopes i) (mu i) z w) ^ (2 ^ (n + 1) - 1) *
          Real.exp (((2 ^ (n + 1)) ^ l : ℕ) * p) :=
        mul_nonneg (pow_nonneg hd0 _) (Real.exp_nonneg _)
      have hpower := hr.trans ((mul_le_mul_of_nonneg_left (le_abs_self _) hcoef0).trans
        (mul_le_mul hcoef hn (abs_nonneg _)
          (mul_nonneg (pow_nonneg (pow_nonneg hB0 _) _) (Real.exp_nonneg _))))
      have hfinal := hpower.trans
        (pivotIterationBound_step hq S.card ((2 ^ (n + 1)) ^ l) p hB)
      rw [Finset.card_insert_of_notMem hi]
      exact le_of_pow_le_pow_left₀ (by omega)
        (pivotIterationBound_nonneg _ _ _ _ hB0) hfinal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_pivot_stage_bound (s : ℕ) {delta C0 : ℝ} (hdelta : 0 < delta) (hC0 : 1 ≤ C0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ {N : ℕ} [NeZero N] {p xi : ℝ}, 2 ≤ p → 0 < xi → xi ≤ xi0 →
      Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ n : ℕ, ((2 ^ (n + 1) : ℕ) : ℝ) ≤ C0 * p →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N) (mu : I → ZMod N → ℝ)
        (a b : ZMod N) (parameter : ℝ) (f g : ZMod N → ℝ),
      0 ≤ parameter → parameter ≤ 1 →
      (∀ i x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p) →
      (∀ i, CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (mu i) (fun _ => 1 + xi)) →
      (∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) f (fun _ => 1 + xi) →
      (∀ x, 0 ≤ g x ∧ g x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) g (fun _ => 1 + xi) →
      ∀ {l : ℕ} (v : Fin l → ZMod N) (S : Finset I), l + S.card ≤ s →
        PivotCompatible v S slopes a b →
        |pivotStageCount (q := 2 ^ (n + 1)) v S slopes mu a b parameter f g| ≤
          pivotIterationBound (2 ^ (n + 1)) S.card ((2 ^ (n + 1)) ^ l) p (1 + delta) := by
  obtain ⟨C, hC, xi0, hxi0, hgrid⟩ := exists_pivot_grid_bounds s hdelta hC0
  refine ⟨C, hC, xi0, hxi0, ?_⟩
  intro N _ p xi hp hxi hxib hodd hN n hqcap I _ slopes mu a b parameter f g
    hparameter hparameter1 hmu hcompare hf hfcompare hg hgcompare l v S hsize hcompatible
  have hq : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow (n + 1) 2 (by omega)
  have hB0 : 0 ≤ 1 + delta := by linarith
  apply pivotStageCount_iterate s n slopes mu a b parameter f g (by linarith) hmu
    (hroot := ?_) (hterminal := ?_) v S hsize hcompatible
  · intro k hk u i hunit
    exact (hgrid hp hxi hxib hodd hN hk hq hqcap u (slopes i) hunit (mu i)
      (hmu i) (@hcompare i)).1
  · intro k hk u hc
    apply pivotStageCount_terminal_le u slopes mu a b hc.1 hparameter hparameter1
      (pow_nonneg hB0 _) f g
    · exact (hgrid hp hxi hxib hodd hN hk hq hqcap u a
        (fun j => (hc.2.2.2 j).1) f hf hfcompare).2
    · exact (hgrid hp hxi hxib hodd hN hk hq hqcap u b
        (fun j => (hc.2.2.2 j).2.1) g hg hgcompare).2

end Erdos3

end

end OAI
