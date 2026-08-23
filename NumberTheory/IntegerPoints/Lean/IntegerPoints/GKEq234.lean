import IntegerPoints.GKStatements

/-!
# Graham–Kolesnik equation (2.3.4)

The Weyl–van der Corput inequality in the interval and indexing convention used
by Graham–Kolesnik §3.3.  The analytic inequality is `AP.weyl_step`; this
module separates its zero shift, reindexes the positive shifts, and absorbs the
result into one absolute constant.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

/-- **Graham–Kolesnik, (2.3.4)** (the Weyl–van der Corput inequality). -/
theorem gk_eq234_holds : gk_eq234 := by
  obtain ⟨CW, hCW⟩ := zhaiCao_lemma4_holds 3 (by norm_num)
  refine ⟨6 * |CW|, ?_⟩
  intro N a b H f hN hNa hab hb hH1 hHN
  have hH1' : (1 : ℝ) ≤ H := by exact_mod_cast hH1
  have hH0 : (0 : ℝ) < H := by linarith
  have hN1 : (1 : ℝ) ≤ N := hH1'.trans hHN
  let R : ℕ → ℝ := fun h =>
    ‖∑ n ∈ intRange a (b - h), e (f n - f (n + h))‖
  change ‖∑ n ∈ intRange a b, e (f n)‖ ^ 2 ≤
    (6 * |CW|) * (N ^ 2 / H + (N / H) * ∑ h ∈ Finset.Icc 1 H, R h)

  have hW := AP.weyl_step CW hCW (N := N) (a := a) (b := b)
    (Q := (H : ℝ)) f hN1 hNa hab hb hH1' hHN
  have hfloor : ⌊(H : ℝ)⌋₊ = H := by simp
  rw [hfloor] at hW
  change ‖∑ n ∈ intRange a b, e (f n)‖ ^ 2 ≤
    |CW| * (2 * N / H) * ∑ q ∈ Finset.range (H + 1), R q at hW
  rw [Finset.sum_range_succ'] at hW

  have hS0 : R 0 ≤ 3 * N := by
    dsimp [R]
    calc
      ‖∑ n ∈ intRange a (b - ((0 : ℕ) : ℝ)),
          e (f n - f (n + ((0 : ℕ) : ℝ)))‖ ≤
          ∑ n ∈ intRange a (b - ((0 : ℕ) : ℝ)),
            ‖e (f n - f (n + ((0 : ℕ) : ℝ)))‖ :=
        norm_sum_le _ _
      _ = (intRange a b).card := by simp [norm_e]
      _ ≤ 3 * N := card_intRange_le hN hNa hab hb

  have hshift : ∑ i ∈ Finset.range H, R (i + 1) =
      ∑ h ∈ Finset.Icc 1 H, R h := by
    rw [show Finset.Icc 1 H = Finset.Ico 1 (H + 1) by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    exact Finset.sum_congr rfl (fun i _ => by rw [add_comm])

  rw [hshift] at hW
  have hfactor0 : 0 ≤ |CW| * (2 * N / (H : ℝ)) := by positivity
  have hsum0 : 0 ≤ ∑ h ∈ Finset.Icc 1 H, R h := by
    exact Finset.sum_nonneg fun h _ => norm_nonneg _
  have hNH0 : 0 ≤ N / (H : ℝ) := div_nonneg hN.le hH0.le
  calc
    ‖∑ n ∈ intRange a b, e (f n)‖ ^ 2 ≤
        |CW| * (2 * N / H) *
          ((∑ h ∈ Finset.Icc 1 H, R h) + R 0) := hW
    _ ≤ |CW| * (2 * N / H) *
          ((∑ h ∈ Finset.Icc 1 H, R h) + 3 * N) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl hS0) hfactor0
    _ = 6 * |CW| * (N ^ 2 / H) +
          2 * |CW| * (N / H) * (∑ h ∈ Finset.Icc 1 H, R h) := by ring
    _ ≤ 6 * |CW| * (N ^ 2 / H) +
          6 * |CW| * (N / H) * (∑ h ∈ Finset.Icc 1 H, R h) := by
      have hcross0 :
          0 ≤ |CW| * (N / (H : ℝ)) * (∑ h ∈ Finset.Icc 1 H, R h) :=
        mul_nonneg (mul_nonneg (abs_nonneg CW) hNH0) hsum0
      have hcross :
          2 * |CW| * (N / H) * (∑ h ∈ Finset.Icc 1 H, R h) ≤
            6 * |CW| * (N / H) * (∑ h ∈ Finset.Icc 1 H, R h) := by
        calc
          2 * |CW| * (N / H) * (∑ h ∈ Finset.Icc 1 H, R h) =
              2 * (|CW| * (N / H) * (∑ h ∈ Finset.Icc 1 H, R h)) := by ring
          _ ≤ 6 * (|CW| * (N / H) * (∑ h ∈ Finset.Icc 1 H, R h)) :=
            mul_le_mul_of_nonneg_right (by norm_num) hcross0
          _ = 6 * |CW| * (N / H) * (∑ h ∈ Finset.Icc 1 H, R h) := by ring
      exact add_le_add le_rfl hcross
    _ = (6 * |CW|) *
          (N ^ 2 / H + (N / H) * ∑ h ∈ Finset.Icc 1 H, R h) := by ring

end LeanProofs.IntegerPoints
