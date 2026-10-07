import OAI.Combinatorics.Progressions.Linear.ChosenBasisGeometryBounds

namespace OAI

section

namespace Erdos3

open Module

noncomputable def nativeResetBracketHeight (p : ℝ) : ℕ :=
  ⌈Real.exp ((p + 4) ^ 11)⌉₊

theorem nativeResetBracketHeight_bounds {p : ℝ} (hp : 0 ≤ p) :
    1 ≤ nativeResetBracketHeight p ∧
    (nativeResetBracketHeight p : ℝ) ≤ Real.exp ((p + 4) ^ 11 + 1) :=
  ⟨one_le_ceil_exp _, ceil_exp_le_exp_add_one (by positivity)⟩

theorem nativeResetBracketLog_ge_input {p : ℝ} (hp : 0 ≤ p) :
    p ≤ (p + 4) ^ 11 := by
  have hpow : p + 4 ≤ (p + 4) ^ 11 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ p + 4)
      (by norm_num : (1 : ℕ) ≤ 11)
  linarith only [hpow]

namespace RationalFilteredNilmanifold

variable {κ L M : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d f : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (Fmark : RationalFilteredNilmanifold M t f) (c : Basis κ ℚ M)

theorem nativeResetBracketGeometry {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hF : Fmark.GeometryComplexityLE p)
    (hc : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p) :
    (d : ℝ) ≤ p ∧ (Fintype.card κ : ℝ) ≤ p ∧
    (∀ i j k, RationalHeightLE (D.basis.repr ⁅D.basis i, D.basis j⁆ k)
      (nativeResetBracketHeight p)) ∧
    (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k)
      (nativeResetBracketHeight p)) := by
  obtain ⟨hdim, _, hbracket⟩ := Fmark.basis_geometry_of_forward_height c hp hF
    (fun i j => (hc i j).trans (by linarith))
  exact ⟨hD.1, hdim,
    fun i j k => rationalHeightLE_ceil_exp
      ((hD.2.2.1 i j k).trans (nativeResetBracketLog_ge_input hp)),
    fun i j k => rationalHeightLE_ceil_exp (hbracket i j k)⟩

theorem nativeResetBracketGeometry_of_height {p : ℝ} {H : ℕ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hF : Fmark.GeometryComplexityLE p)
    (hc : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p)
    (hH : nativeResetBracketHeight p ≤ H) :
    (d : ℝ) ≤ p ∧ (Fintype.card κ : ℝ) ≤ p ∧
    (∀ i j k, RationalHeightLE (D.basis.repr ⁅D.basis i, D.basis j⁆ k) H) ∧
    (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) := by
  obtain ⟨hd, hf, hbracketD, hbracketF⟩ := D.nativeResetBracketGeometry Fmark c hp hD hF hc
  exact ⟨hd, hf, fun i j k => (hbracketD i j k).mono hH,
    fun i j k => (hbracketF i j k).mono hH⟩

theorem nativeResetBracketGeometry_of_logBudget {p q : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hF : Fmark.GeometryComplexityLE p)
    (hc : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p)
    (hbudget : (p + 4) ^ 11 ≤ q) :
    1 ≤ ⌈Real.exp q⌉₊ ∧ (⌈Real.exp q⌉₊ : ℝ) ≤ Real.exp (q + 1) ∧
    (d : ℝ) ≤ p ∧ (Fintype.card κ : ℝ) ≤ p ∧
    (∀ i j k, RationalHeightLE (D.basis.repr ⁅D.basis i, D.basis j⁆ k) ⌈Real.exp q⌉₊) ∧
    (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) ⌈Real.exp q⌉₊) := by
  refine ⟨one_le_ceil_exp _, ceil_exp_le_exp_add_one ?_,
    D.nativeResetBracketGeometry_of_height Fmark c hp hD hF hc ?_⟩
  · exact (show 0 ≤ (p + 4) ^ 11 by positivity).trans hbudget
  · exact Nat.ceil_mono (Real.exp_le_exp.mpr hbudget)

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
