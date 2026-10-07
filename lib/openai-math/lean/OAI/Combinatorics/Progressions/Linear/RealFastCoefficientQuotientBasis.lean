import OAI.Combinatorics.Progressions.Dynamics.FastCoefficientGeneratorBudget
import OAI.Combinatorics.Progressions.Estimates.BlockQuotientRows
import OAI.Combinatorics.Progressions.Geometry.RealFastCoefficientCoordinates
import OAI.Combinatorics.Progressions.Geometry.SubmoduleQuotientCoordinates

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_fast_coefficient_quotient_projection
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)] (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hd : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ p)
    (hdm : ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 420) ∧
    ∃ Q : Matrix (FirstCoefficientIndex w ω) (FirstCoefficientIndex w ω) ℚ,
      Q * Q = Q ∧
      LinearMap.ker Q.mulVecLin = (F.firstCoefficientFastSubmodule w hw U).map
        (F.firstCoefficientBasis e ω hF w).equivFun.toLinearMap ∧
      (∀ i j, i.val.1 ≠ j.val.1 → Q i j = 0) ∧
      ∀ i j, RationalHeightLE (Q i j) H' := by
  have hg := F.exists_fast_coefficient_generators_exp e ω hF w hw U v hspan hH hv hp hn hm hq hHp
  obtain ⟨K, hK, hKp, z, hz, hzK⟩ := hg
  have hblocks := F.firstCoefficientFastSubmodule_monomial_blocks e ω hF w hw U hU
  have he := exists_submodule_block_quotient_projection (F.firstCoefficientBasis e ω hF w)
    (fun i => i.val.1) (F.firstCoefficientFastSubmodule w hw U) z hz hblocks hK hzK
  obtain ⟨Q, hQQ, hker, hblock, hQ⟩ := he
  have hcost : (imageDefiningHeight
      (Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ)
      (Fintype.card (FirstCoefficientIndex w ω)) K : ℝ) ≤ Real.exp ((p + 2) ^ 420) := by
    have h := imageDefiningHeight_le_exp _ _ K (by positivity : 0 ≤ (p + 2) ^ 40)
      (hdm.trans (le_power_budget hp (by decide : 1 ≤ 40)))
      (hd.trans (le_power_budget hp (by decide : 1 ≤ 40))) hKp
    exact exponential_budget_comp hp (by positivity) 40 10 le_rfl h
  exact ⟨_, imageDefiningHeight_pos _ _ _ hK, hcost, Q, hQQ, hker, hblock, hQ⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem exists_fast_coefficient_quotient_basis
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hd : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ p)
    (hdm : ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card (FirstCoefficientIndex w ω) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℚ (F.FirstCoefficientModule w ⧸ F.firstCoefficientFastSubmodule w hw U),
      ∃ D : Matrix (Fin d) (FirstCoefficientIndex w ω) ℚ,
      ∃ S : Matrix (FirstCoefficientIndex w ω) (Fin d) ℚ,
        LinearMap.toMatrix (F.firstCoefficientBasis e ω hF w) b
          (F.firstCoefficientFastSubmodule w hw U).mkQ = D ∧
        D * S = 1 ∧
        (∀ i j, (rows i).val.1 ≠ j.val.1 → D i j = 0) ∧
        (∀ i j, i.val.1 ≠ (rows j).val.1 → S i j = 0) ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 420) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 420)) ∧
        (∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 2954) ∧
          ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 2954)) ∧
        ∀ y : Fin d → ℚ, b.equivFun.symm y =
          (F.firstCoefficientFastSubmodule w hw U).mkQ
            ((F.firstCoefficientBasis e ω hF w).equivFun.symm (S *ᵥ y)) := by
  classical
  have he := F.exists_fast_coefficient_quotient_projection e ω hF w hw U hU v hspan hH hv
    hp hn hm hq hd hdm hHp
  obtain ⟨K, hK, hKp, Q, _, hkerQ, hQb, hQ⟩ := he
  have hr := exists_block_quotient_rows (fun i : FirstCoefficientIndex w ω => i.val.1) Q hQb hK hQ
  obtain ⟨d, hd', rows, hinj, hsurj, hker, S, hDS, hSb, hS⟩ := hr
  let D := Q.submatrix rows id
  have hkerD : LinearMap.ker D.mulVecLin = (F.firstCoefficientFastSubmodule w hw U).map
      (F.firstCoefficientBasis e ω hF w).equivFun.toLinearMap := hker.trans hkerQ
  let b := submoduleQuotientCoordinateBasis (F.firstCoefficientBasis e ω hF w)
    (F.firstCoefficientFastSubmodule w hw U) D hkerD hsurj
  have hSbudget : (rationalKernelHeight d K : ℝ) ≤ Real.exp ((p + 2) ^ 2954) := by
    have h := rationalKernelHeight_le_budget d K (by positivity : 0 ≤ (p + 2) ^ 420)
      (((Nat.cast_le.mpr hd').trans hd).trans (le_power_budget hp (by decide : 1 ≤ 420))) hKp
    exact exponential_budget_comp hp (by positivity) 420 7 le_rfl h
  refine ⟨d, hd', rows, hinj, b, D, S,
    submoduleQuotientCoordinateBasis_matrix _ _ _ _ _, hDS,
    (fun i j h => hQb (rows i) j h), hSb, ?_, ?_, ?_⟩
  · intro i j
    exact ⟨(Nat.cast_le.mpr (hQ (rows i) j).1).trans hKp,
      (Nat.cast_le.mpr (hQ (rows i) j).2).trans hKp⟩
  · intro i j
    exact ⟨(Nat.cast_le.mpr (hS i j).1).trans hSbudget,
      (Nat.cast_le.mpr (hS i j).2).trans hSbudget⟩
  · intro y
    exact submoduleQuotientCoordinateEquiv_symm _ _ _ _ _ S hDS y

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem exists_real_fast_coefficient_quotient_basis
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hd : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ p)
    (hdm : ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card (FirstCoefficientIndex w ω) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
        F.realFirstCoefficientFastSubmodule w hw U),
      ∃ D : Matrix (Fin d) (FirstCoefficientIndex w ω) ℚ,
      ∃ S : Matrix (FirstCoefficientIndex w ω) (Fin d) ℚ,
        LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w) b
          (F.realFirstCoefficientFastSubmodule w hw U).mkQ = D.map (Rat.castHom ℝ) ∧
        D * S = 1 ∧
        (∀ i j, (rows i).val.1 ≠ j.val.1 → D i j = 0) ∧
        (∀ i j, i.val.1 ≠ (rows j).val.1 → S i j = 0) ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 420) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 420)) ∧
        (∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 2954) ∧
          ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 2954)) ∧
        ∀ y : Fin d → ℝ, b.equivFun.symm y =
          (F.realFirstCoefficientFastSubmodule w hw U).mkQ
            ((F.realFirstCoefficientBasis e ω hF w).equivFun.symm
              (S.map (Rat.castHom ℝ) *ᵥ y)) := by
  have h := F.exists_fast_coefficient_quotient_basis e ω hF w hw U hU v hspan hH hv
    hp hn hm hq hd hdm hHp
  obtain ⟨d, hdim, rows, hinj, b, D, S, hD, hDS, hDb, hSb, hDh, hSh, _⟩ := h
  refine ⟨d, hdim, rows, hinj, F.realFastCoefficientBasis w hw U b, D, S,
    ?_, hDS, hDb, hSb, hDh, hSh, ?_⟩
  · rw [F.realFastCoefficientBasis_matrix, hD]
  · exact F.realFastCoefficientBasis_symm w hw U e ω hF b D S hD hDS

end Erdos3.NilpotentLieFiltration

end

end OAI
