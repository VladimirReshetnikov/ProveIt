import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

noncomputable def denseResidueMeshCap (n : ℕ) (δ ε C : ℝ) : ℕ :=
  ⌈16 * ((n : ℝ) + 1) * C / (ε * δ)⌉₊ + 1

noncomputable def denseResidueMeshStep (n : ℕ) (δ ε L : ℝ) : ℕ :=
  ⌊ε * δ * L / (8 * ((n : ℝ) + 1))⌋₊

theorem denseResidueMesh_budget (n : ℕ) {δ ε C L : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hC : 1 ≤ C)
    (hL : 16 * ((n : ℝ) + 1) / (ε * δ) ≤ L) :
    0 < denseResidueMeshStep n δ ε L ∧
    C * L ≤ ((denseResidueMeshCap n δ ε C * denseResidueMeshStep n δ ε L : ℕ) : ℝ) ∧
    4 * (n : ℝ) * denseResidueMeshStep n δ ε L / (δ * L) ≤ ε / 2 ∧
    2 * (denseResidueMeshStep n δ ε L : ℝ) < δ * L ∧
    4 * (denseResidueMeshStep n δ ε L : ℝ) ≤ δ * L := by
  let M := denseResidueMeshStep n δ ε L
  let K := denseResidueMeshCap n δ ε C
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < ε * δ := mul_pos hε hδ
  have hb : 0 < 8 * ((n : ℝ) + 1) := by positivity
  have hlarge : 16 * ((n : ℝ) + 1) ≤ L * (ε * δ) :=
    (div_le_iff₀ hd).mp hL
  have hLpos : 0 < L := by
    have : 0 < L * (ε * δ) := lt_of_lt_of_le (by positivity) hlarge
    exact (mul_pos_iff_of_pos_right hd).mp this
  have hδL : 0 < δ * L := mul_pos hδ hLpos
  have ht : 2 ≤ ε * δ * L / (8 * ((n : ℝ) + 1)) := by
    apply (le_div_iff₀ hb).mpr
    nlinarith only [hlarge]
  have hMpos : 0 < M := Nat.floor_pos.mpr (by linarith only [ht])
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
  have hMnonneg : (0 : ℝ) ≤ M := by positivity
  have hMupper : (M : ℝ) * (8 * ((n : ℝ) + 1)) ≤ ε * δ * L := by
    apply (le_div_iff₀ hb).mp
    exact Nat.floor_le (by positivity)
  have hMlower : ε * δ * L ≤ 16 * ((n : ℝ) + 1) * M := by
    have hfloor := Nat.lt_floor_add_one (ε * δ * L / (8 * ((n : ℝ) + 1)))
    have hhalf : ε * δ * L / (8 * ((n : ℝ) + 1)) ≤ 2 * M := by
      change ε * δ * L / (8 * ((n : ℝ) + 1)) < (M : ℝ) + 1 at hfloor
      linarith only [hfloor, hMone]
    have := (div_le_iff₀ hb).mp hhalf
    nlinarith only [this]
  have hK : 16 * ((n : ℝ) + 1) * C ≤ (ε * δ) * K := by
    have hceil := Nat.le_ceil (16 * ((n : ℝ) + 1) * C / (ε * δ))
    have hbound : 16 * ((n : ℝ) + 1) * C / (ε * δ) ≤ (K : ℝ) := by
      dsimp [K, denseResidueMeshCap]
      push_cast
      linarith only [hceil]
    have := (div_le_iff₀ hd).mp hbound
    simpa [mul_comm] using this
  refine ⟨hMpos, ?_, ?_, ?_, ?_⟩
  · change C * L ≤ ((K * M : ℕ) : ℝ)
    rw [Nat.cast_mul]
    apply le_of_mul_le_mul_left _ hd
    calc
      (ε * δ) * (C * L) = C * (ε * δ * L) := by ring
      _ ≤ C * (16 * ((n : ℝ) + 1) * M) :=
        mul_le_mul_of_nonneg_left hMlower (by linarith only [hC])
      _ = (16 * ((n : ℝ) + 1) * C) * M := by ring
      _ ≤ ((ε * δ) * K) * M := mul_le_mul_of_nonneg_right hK hMnonneg
      _ = (ε * δ) * ((K : ℝ) * M) := by ring
  · apply (div_le_iff₀ hδL).mpr
    change 4 * (n : ℝ) * M ≤ ε / 2 * (δ * L)
    nlinarith only [hMupper, hMnonneg]
  · change 2 * (M : ℝ) < δ * L
    have hεL : ε * (δ * L) ≤ δ * L :=
      mul_le_of_le_one_left (le_of_lt hδL) hε₁
    nlinarith only [hMupper, hεL, hn, hMone]
  · change 4 * (M : ℝ) ≤ δ * L
    have hεL : ε * (δ * L) ≤ δ * L :=
      mul_le_of_le_one_left (le_of_lt hδL) hε₁
    nlinarith only [hMupper, hεL, hn, hMnonneg]

theorem exists_denseResidueMesh_budget (n : ℕ) {δ ε C : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hC : 1 ≤ C) :
    ∃ K : ℕ, 0 < K ∧ ∀ L : ℝ,
      16 * ((n : ℝ) + 1) / (ε * δ) ≤ L →
      ∃ M : ℕ, 0 < M ∧ C * L ≤ ((K * M : ℕ) : ℝ) ∧
        4 * (n : ℝ) * M / (δ * L) ≤ ε / 2 ∧
        2 * (M : ℝ) < δ * L ∧ 4 * (M : ℝ) ≤ δ * L := by
  refine ⟨denseResidueMeshCap n δ ε C, Nat.succ_pos _, ?_⟩
  intro L hL
  exact ⟨denseResidueMeshStep n δ ε L, denseResidueMesh_budget n hδ hε hε₁ hC hL⟩

theorem denseResidueMesh_side_budget (n : ℕ) {δ ε C L : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hC : 1 ≤ C)
    (hL : 16 * ((n : ℝ) + 1) / (ε * δ) ≤ L)
    (N : ℕ) (hlo : δ * L ≤ (N : ℝ)) (hhi : (N : ℝ) ≤ C * L) :
    N ≤ denseResidueMeshCap n δ ε C * denseResidueMeshStep n δ ε L ∧
    2 * denseResidueMeshStep n δ ε L < N ∧
    4 * (n : ℝ) * denseResidueMeshStep n δ ε L / (N : ℝ) ≤ ε / 2 := by
  obtain ⟨hM, hcover, hboundary, htrim, _⟩ :=
    denseResidueMesh_budget n hδ hε hε₁ hC hL
  have hδL : 0 < δ * L := lt_of_le_of_lt (by positivity) htrim
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast hhi.trans hcover
  · have h := htrim.trans_le hlo
    exact_mod_cast h
  · exact (div_le_div_of_nonneg_left (by positivity) hδL hlo).trans hboundary

end Erdos3

end

section

namespace Erdos3

theorem exists_denseResidueMesh_exponential_budget (n : ℕ) {C : ℝ} (hC : 1 ≤ C) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ (b δ ε : ℝ), 0 ≤ b →
      Real.exp (-b) ≤ δ → δ ≤ 1 → Real.exp (-b) ≤ ε → ε ≤ 1 →
      let Q := ⌈2 / δ⌉₊
      let K := denseResidueMeshCap n δ ε C
      ((Q + 1 : ℕ) : ℝ) ≤ Real.exp ((A : ℝ) + 2 * b) ∧
      ((K + 1 : ℕ) : ℝ) ≤ Real.exp ((A : ℝ) + 2 * b) ∧
      16 * ((n : ℝ) + 1) / (ε * δ) ≤ Real.exp ((A : ℝ) + 2 * b) := by
  let D : ℝ := 16 * ((n : ℝ) + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC0 : 0 ≤ C := by linarith
  have hDC : 0 ≤ D * C := mul_nonneg hD hC0
  obtain ⟨A, hA⟩ := exists_nat_ge (D * C + D + 8)
  have hAtwo : 2 ≤ A := by
    have : (2 : ℝ) ≤ A := by linarith
    exact_mod_cast this
  have hAexp : (A : ℝ) ≤ Real.exp A := by linarith [Real.add_one_le_exp (A : ℝ)]
  have hAfour : (4 : ℝ) ≤ Real.exp A := by linarith
  have hADC : D * C + 3 ≤ Real.exp A := by linarith
  have hAD : D ≤ Real.exp A := by linarith
  refine ⟨A, hAtwo, ?_⟩
  intro b δ ε hb hδ _hδ₁ hε _hε₁
  have hδ0 : 0 < δ := (Real.exp_pos _).trans_le hδ
  have hε0 : 0 < ε := (Real.exp_pos _).trans_le hε
  have hδinv : δ⁻¹ ≤ Real.exp b := by
    have h := one_div_le_one_div_of_le (Real.exp_pos (-b)) hδ
    simpa only [one_div, Real.exp_neg, inv_inv] using h
  have hεinv : ε⁻¹ ≤ Real.exp b := by
    have h := one_div_le_one_div_of_le (Real.exp_pos (-b)) hε
    simpa only [one_div, Real.exp_neg, inv_inv] using h
  have hinv : (ε * δ)⁻¹ ≤ Real.exp (2 * b) := by
    calc
      _ = ε⁻¹ * δ⁻¹ := by simp only [mul_inv_rev, mul_comm]
      _ ≤ Real.exp b * Real.exp b :=
        mul_le_mul hεinv hδinv (inv_nonneg.mpr hδ0.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have heone : 1 ≤ Real.exp (2 * b) := Real.one_le_exp_iff.mpr (by positivity)
  have hδinv2 : δ⁻¹ ≤ Real.exp (2 * b) :=
    hδinv.trans (Real.exp_le_exp.mpr (by linarith))
  have hQceil : (⌈2 / δ⌉₊ : ℝ) ≤ 2 / δ + 1 :=
    (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 / δ)).le
  have hKceil : (⌈D * C / (ε * δ)⌉₊ : ℝ) ≤ D * C / (ε * δ) + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ D * C / (ε * δ))).le
  have hquot : 2 / δ ≤ 2 * Real.exp (2 * b) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hδinv2 (by norm_num)
  have hmesh : D * C / (ε * δ) ≤ D * C * Real.exp (2 * b) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv hDC
  refine ⟨?_, ?_, ?_⟩
  · calc
      ((⌈2 / δ⌉₊ + 1 : ℕ) : ℝ) ≤ 4 * Real.exp (2 * b) := by
        push_cast
        linarith
      _ ≤ Real.exp A * Real.exp (2 * b) :=
        mul_le_mul_of_nonneg_right hAfour (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  · calc
      ((denseResidueMeshCap n δ ε C + 1 : ℕ) : ℝ) ≤
          (D * C + 3) * Real.exp (2 * b) := by
        unfold denseResidueMeshCap
        change (((⌈D * C / (ε * δ)⌉₊ + 1) + 1 : ℕ) : ℝ) ≤ _
        push_cast
        nlinarith
      _ ≤ Real.exp A * Real.exp (2 * b) :=
        mul_le_mul_of_nonneg_right hADC (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  · calc
      16 * ((n : ℝ) + 1) / (ε * δ) = D * (ε * δ)⁻¹ := div_eq_mul_inv _ _
      _ ≤ D * Real.exp (2 * b) := mul_le_mul_of_nonneg_left hinv hD
      _ ≤ Real.exp A * Real.exp (2 * b) :=
        mul_le_mul_of_nonneg_right hAD (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm

end Erdos3

end

end OAI
