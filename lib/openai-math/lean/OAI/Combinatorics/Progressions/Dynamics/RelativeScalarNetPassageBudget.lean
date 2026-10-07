import OAI.Combinatorics.Progressions.Lattices.DenseResidueScalarScoreNet

namespace OAI

section

namespace Erdos3

private theorem exp_neg_add_two_lt_half (b : ℝ) :
    Real.exp (-(b + 2)) < Real.exp (-b) / 2 := by
  have htwo : (3 : ℝ) ≤ Real.exp 2 := by
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hmul : Real.exp (-(b + 2)) * Real.exp 2 = Real.exp (-b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith [Real.exp_pos (-(b + 2))]

theorem exists_relativeScalarNetPassage_power_budget (d r : ℕ) (hr : 1 ≤ r) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ (b density : ℝ), 2 ≤ b →
      Real.exp (-b) ≤ density → density ≤ 1 →
      let accuracy := Real.exp (-b)
      let Q := ⌈2 / density⌉₊
      let K := denseResidueMeshCap d density accuracy (r : ℝ)
      let p := (b + 2) ^ E
      let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
      2 ≤ p ∧ b + 2 ≤ p ∧
      (Fintype.card (DenseResidueSliceNetCode (Fin d) Q K) : ℝ) ≤ Real.exp p ∧
      (Fintype.card (DenseResidueSliceNetCode (Fin d) Q K) : ℝ) *
        Real.exp (-target) < Real.exp (-b) ∧
      Real.exp (-target) < Real.exp (-b) - accuracy / 2 ∧
      (∀ (Λ τ : ℝ), Real.exp (-b) ≤ Λ → τ ≤ 1 / 2 →
        Real.exp (-p) ≤ (1 - τ) * Λ) ∧
      density⁻¹ ≤ Real.exp p ∧
      ((Q + 1 : ℕ) : ℝ) ≤ Real.exp p ∧
      (density / 2)⁻¹ ≤ Real.exp p ∧
      2 * (r : ℝ) ≤ Real.exp p ∧ 4 * (r : ℝ) / density ≤ Real.exp p ∧
      (∀ scalarbudget : ℝ, p ≤ scalarbudget →
        16 * ((d : ℝ) + 1) / (accuracy * density) ≤ Real.exp scalarbudget) ∧
      ∀ L : ℝ, Real.exp p ≤ L → 4 ≤ density * L := by
  obtain ⟨E, hE, hnet⟩ :=
    exists_denseResidueScalarNet_power_budget d (show (1 : ℝ) ≤ r by exact_mod_cast hr)
  refine ⟨E, hE, ?_⟩
  intro b density hb hdensity hdensity1 accuracy Q K p target
  have hb0 : 0 ≤ b := by linarith
  have haccuracy1 : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨_, hcard, hQ, _, hmesh, hhalf, hratio, hwidth, hlarge, _⟩ :=
    hnet b density accuracy hb0 hdensity hdensity1 le_rfl haccuracy1
  have hbase : 1 ≤ b + 2 := by linarith
  have hbp : b + 2 ≤ p := le_self_pow₀ hbase (by omega : E ≠ 0)
  have hp : 2 ≤ p := by linarith
  have htarget : b + 2 ≤ target := by
    have hrd := Nat.cast_nonneg (α := ℝ) (r * d)
    dsimp only [target]
    nlinarith
  have hsubtract : p - target < -b := by
    have hrd := Nat.cast_nonneg (α := ℝ) (r * d)
    dsimp only [target]
    nlinarith
  have hmass : (Fintype.card (DenseResidueSliceNetCode (Fin d) Q K) : ℝ) *
      Real.exp (-target) < Real.exp (-b) := by
    calc
      _ ≤ Real.exp p * Real.exp (-target) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      _ = Real.exp (p - target) := by rw [← Real.exp_add]; rfl
      _ < Real.exp (-b) := Real.exp_lt_exp.mpr hsubtract
  have hgap : Real.exp (-target) < Real.exp (-b) - accuracy / 2 := by
    have hh := (Real.exp_le_exp.mpr (neg_le_neg htarget)).trans_lt
      (exp_neg_add_two_lt_half b)
    dsimp only [accuracy]
    linarith
  have hlevel (Λ τ : ℝ) (hΛ : Real.exp (-b) ≤ Λ) (hτ : τ ≤ 1 / 2) :
      Real.exp (-p) ≤ (1 - τ) * Λ := by
    have hh := (Real.exp_le_exp.mpr (neg_le_neg hbp)).trans_lt
      (exp_neg_add_two_lt_half b)
    have hΛ0 := (Real.exp_pos (-b)).le.trans hΛ
    have hΛhalf : Real.exp (-b) / 2 ≤ Λ / 2 := by linarith
    have hdiscount : Λ / 2 ≤ (1 - τ) * Λ := by nlinarith
    exact hh.le.trans (hΛhalf.trans hdiscount)
  have hdensity0 := (Real.exp_pos (-b)).trans_le hdensity
  have hinv : density⁻¹ ≤ Real.exp p := by
    apply (inv_le_iff_one_le_mul₀' hdensity0).mpr
    calc
      1 = Real.exp (-b) * Real.exp b := by rw [← Real.exp_add]; simp
      _ ≤ density * Real.exp b := mul_le_mul_of_nonneg_right hdensity (Real.exp_nonneg _)
      _ ≤ density * Real.exp p := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith)) hdensity0.le
  refine ⟨hp, hbp, hcard, hmass, hgap, hlevel, hinv, hQ, hhalf, hratio, hwidth, ?_, hlarge⟩
  intro scalarbudget hbudget
  exact hmesh.trans (Real.exp_le_exp.mpr hbudget)

end Erdos3

end

end OAI
