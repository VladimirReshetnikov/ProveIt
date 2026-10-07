import OAI.Combinatorics.Progressions.Dynamics.ConjugationDenominatorBudget

namespace OAI

section

namespace Erdos3

open Module

theorem denominatorGrid_neg {ι : Type*} (q : ℕ) {x : ι → ℚ}
    (hx : x ∈ denominatorGrid q) : -x ∈ denominatorGrid q := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨-z, ?_⟩
  intro i
  have hi : (q : ℚ) * x i = (z i : ℚ) := hz i
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Int.cast_neg, mul_neg, hi]

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem conjugated_subgroup_inner_grid (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l q : ℕ) (hq : 0 < q)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (z : NilpotentLieBCHGroup L s hnil) (hz : e.equivFun z.coord ∈ denominatorGrid q) :
    scaledIntegerGrid (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * q ^ s) ⊆
      bchSubgroupCoordinates e (Γ.map (MulAut.conj z).toMonoidHom) := by
  intro x hx
  let g : NilpotentLieBCHGroup L s hnil := ⟨e.equivFun.symm x⟩
  have hg : e.equivFun g.coord ∈ scaledIntegerGrid
      (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * q ^ s) := by
    simpa only [g, LinearEquiv.apply_symm_apply] using hx
  have hzinv : e.equivFun (z⁻¹).coord ∈ denominatorGrid q := by
    simpa only [NilpotentLieBCHGroup.coord_inv, map_neg] using denominatorGrid_neg q hz
  have hconj := conjugation_preserves_inner_grid e hnil q l hq z⁻¹ g hzinv hg
  have hmem : z⁻¹ * g * z ∈ Γ := by
    apply (bchSubgroupCoordinates_repr e Γ _).mp
    apply hinner
    simpa only [inv_inv] using hconj
  change g ∈ Γ.map (MulAut.conj z).toMonoidHom
  refine Subgroup.mem_map.mpr ⟨z⁻¹ * g * z, hmem, ?_⟩
  change z * (z⁻¹ * g * z) * z⁻¹ = g
  group

theorem exists_uniform_conjugated_inner_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l q H : ℕ) (p : ℝ),
      0 < l → 0 < q → scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (l : ℝ) ≤ Real.exp p → (q : ℝ) ≤ Real.exp p →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ z : NilpotentLieBCHGroup L s hnil, e.equivFun z.coord ∈ denominatorGrid q →
          scaledIntegerGrid M ⊆ bchSubgroupCoordinates e (Γ.map (MulAut.conj z).toMonoidHom) := by
  obtain ⟨K, hK, hden⟩ := exists_conjugation_denominator_exp_bound s
  refine ⟨K + s + 5, by omega, ?_⟩
  intro ι L _ _ _ e hnil Γ l q H p hl hq hinner hp hd hH hc hlb hqb
  refine ⟨l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * q ^ s,
    Nat.mul_pos (Nat.mul_pos hl (polynomialFamilyDenominator_pos _)) (pow_pos hq _), ?_, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_ofNat] using
      conjugation_grid_allowance_le_exp K s l _ q hp hlb (hden e H p hp hd hH hc) hqb
  · intro z hz
    exact conjugated_subgroup_inner_grid e hnil Γ l q hq hinner z hz

end Erdos3

end

end OAI
