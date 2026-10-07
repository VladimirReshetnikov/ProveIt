import OAI.Combinatorics.Progressions.Estimates.NativeRoundedCyclicModel

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators Pointwise
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem joint_affine_recovery {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (l : I → ℕ) (hl : ∀ i, 0 < l i)
    (ε : I → ℝ) (hε : ∀ i, 0 < ε i) (hsmall : ∀ i, 2 * (l i : ℝ) * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let z := roundedModelLogBudget P (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    ∃ J' ⊆ H, J'.Nonempty ∧
      δ * ((2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card) ≤ 16 ^ (Fintype.card I + 2) * (J'.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (ξ : (Fin r → ℤ) →+ ZMod N)
        (h₀ : ZMod N) (α : I → ℝ) (β : Fin r → I → ℝ),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        (∀ i, α i ∈ Set.Ico (0 : ℝ) (1 / l i)) ∧
        (∀ j i, β j i ∈ Set.Ico (0 : ℝ) (1 / l i)) ∧
        ∀ h ∈ J', ∃ x : Fin r → ℤ,
          (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + ξ x ∧
          ∃ q ∈ coordinateDenominatorGrid l, ∀ i,
            |a h i - (α + ∑ j, (x j : ℝ) • β j) i - q i| ≤ 2 * ε i := by
  intro K z δ
  obtain ⟨M, hM, hMsmall, hMerror⟩ := exists_coordinate_rounding_moduli l hl ε hε hsmall
  let _ : ∀ i, NeZero (M i) := fun i => ⟨(hM i).ne'⟩
  obtain ⟨J', hJH, hJ, hsize, r, R, Φ, base, hrank, _hinj, hrepr⟩ :=
    D.variable_graph_affine_model a c M l ε hMsmall hnear
  let ξ := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp Φ
  let ψ := (AddMonoidHom.snd (ZMod N) (∀ i, ZMod (M i))).comp Φ
  refine ⟨J', hJH, hJ, hsize, r, R, ξ, base.1, variableCoefficientLift l base.2,
    (fun j => variableCoefficientLift l (ψ (Pi.single j 1))), hrank, ?_, ?_, ?_⟩
  · exact variableCoefficientLift_mem_Ico l hl base.2
  · intro j
    exact variableCoefficientLift_mem_Ico l hl (ψ (Pi.single j 1))
  · intro h hh
    obtain ⟨x, hx, heq⟩ := hrepr h hh
    obtain ⟨q, hq, herr⟩ := exists_variable_unrounded_affine l hl base.2 ψ x (a h)
      (congrArg Prod.snd heq)
    exact ⟨x, hx, congrArg Prod.fst heq, q, hq, fun i => (herr i).trans (hMerror i)⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
