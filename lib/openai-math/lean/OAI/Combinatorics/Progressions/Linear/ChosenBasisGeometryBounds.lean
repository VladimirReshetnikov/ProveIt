import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem basis_geometry_of_forward_height {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (b : Basis ι ℚ L)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hb : ∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p + 1) :
    (Fintype.card ι : ℝ) ≤ p ∧
      (∀ i j, rationalLogHeight (b.repr (D.basis i) j) ≤ (p + 4) ^ 5) ∧
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + 4) ^ 11) := by
  have hdim : (Fintype.card ι : ℝ) ≤ p := by
    rw [← finrank_eq_card_basis b, finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hD.1
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp (p + 1)
  have hHp : (H : ℝ) ≤ Real.exp (p + 2) := by
    simpa only [show p + 1 + 1 = p + 2 by ring] using ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)
  have hentries : ∀ i j, RationalHeightLE (D.basis.repr (b i) j) H :=
    fun i j => rationalHeightLE_ceil_exp (hb i j)
  have hstructure : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => rationalHeightLE_ceil_exp ((hD.2.2.1 i j k).trans (by linarith))
  have hp2 : 0 ≤ p + 2 := by linarith
  have hdim2 : (Fintype.card ι : ℝ) ≤ p + 2 := hdim.trans (by linarith)
  have hd2 : (Fintype.card (Fin d) : ℝ) ≤ p + 2 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 2 by linarith)
  have hinverse : (rationalSolveHeight (Fintype.card ι) H : ℝ) ≤ Real.exp ((p + 4) ^ 5) := by
    simpa only [show p + 2 + 2 = p + 4 by ring] using
      rationalSolveHeight_le_budget (Fintype.card ι) H hp2 hdim2 hHp
  have hbracket : (rationalLieStructureHeight (Fintype.card (Fin d))
      (max H (rationalSolveHeight (Fintype.card ι) H)) : ℝ) ≤ Real.exp ((p + 4) ^ 11) := by
    simpa only [show p + 2 + 2 = p + 4 by ring] using
      rationalLieStructureHeight_inverse_budget (Fintype.card (Fin d)) (Fintype.card ι) H hp2 hd2 hdim2 hHp
  exact ⟨hdim,
    fun i j => rationalLogHeight_le_of_height (inverse_basis_entries_height D.basis b hH hentries i j) hinverse,
    fun i j k => rationalLogHeight_le_of_height
      (basis_change_structure_height D.basis b hH hentries hstructure i j k) hbracket⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
