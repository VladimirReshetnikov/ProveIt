import OAI.Combinatorics.Progressions.Estimates.FinitePushforwardComplexWeights
import OAI.Combinatorics.Progressions.Estimates.RelativePatchAmplification

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical
namespace ResidueBoxSlice
variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q s d : ℕ}

noncomputable def fullSliceInverseParameters (S : ResidueBoxSlice N q) (i : X) : MvPolynomial X ℝ :=
  (q : ℝ)⁻¹ • (MvPolynomial.X i - MvPolynomial.C (S.start i : ℝ))

omit [Fintype X] [DecidableEq X] in
theorem fullSliceInverseParameters_degree (S : ResidueBoxSlice N q) (i : X) :
    S.fullSliceInverseParameters i ∈ weightedSupportLE (fun _ => 1) 1 :=
  (weightedSupportLE _ _).smul_mem _ ((weightedSupportLE _ _).sub_mem
    (weightedSupportLE_X _ _) (weightedSupportLE_C _ _ _))

noncomputable def fullSliceReinsertPatch (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch X s d) : PolynomialPatch X s d :=
  Q.reparam S.fullSliceInverseParameters S.fullSliceInverseParameters_degree

omit [Fintype X] [DecidableEq X] in
theorem fullSliceReinsertPatch_point_value (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch X s d) (hq : 0 < q) (u : ∀ i, Fin (S.length i)) :
    (S.fullSliceReinsertPatch Q).value (fun i => ((S.point u i).val : ℝ)) =
      Q.value (fun i => ((u i).val : ℝ)) := by
  rw [fullSliceReinsertPatch, PolynomialPatch.reparam_value]
  congr 1
  funext i
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [fullSliceInverseParameters, map_smul, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    point, Nat.cast_add, Nat.cast_mul, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
  field_simp
  ring

def fullSlicePointInIntegerBox (S : ResidueBoxSlice N q) (u : ∀ i, Fin (S.length i)) : integerBox N :=
  ⟨fun i => ((S.point u i).val : ℤ), (mem_integerBox _ _).mpr
    (fun i => ⟨Int.natCast_nonneg _, by exact_mod_cast (S.point u i).isLt⟩)⟩

noncomputable def fullSliceLaw (S : ResidueBoxSlice N q) (hlen : ∀ i, 0 < S.length i) :
    FiniteProbabilityWeights (integerBox N) := by
  letI : ∀ i, Nonempty (Fin (S.length i)) := fun i => ⟨⟨0,hlen i⟩⟩
  exact (FiniteProbabilityWeights.uniform (∀ i, Fin (S.length i))).finitePushforward S.fullSlicePointInIntegerBox

theorem fullSliceLaw_mean (S : ResidueBoxSlice N q) (hlen : ∀ i, 0 < S.length i)
    (f : integerBox N → ℝ) :
    (S.fullSliceLaw hlen).mean f = 𝔼 u, f (S.fullSlicePointInIntegerBox u) := by
  let : ∀ i, Nonempty (Fin (S.length i)) := fun i => ⟨⟨0,hlen i⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_mean _ _

theorem fullSliceLaw_score (S : ResidueBoxSlice N q) (hlen : ∀ i, 0 < S.length i)
    (hq : 0 < q) (Q : PolynomialPatch X s d) (f : (X → ℤ) → ℝ) (target : ℝ) :
    (S.fullSliceLaw hlen).mean (fun x => (f x.val-target) *
      (S.fullSliceReinsertPatch Q).value (fun i => (x.val i : ℝ))) =
      relativePatchSliceScore S f target Q := by
  rw [fullSliceLaw_mean]
  unfold relativePatchSliceScore
  congr 1
  · ext u
    simp
  · funext u
    change (f _-target) * (S.fullSliceReinsertPatch Q).value (fun i => ((S.point u i).val : ℝ)) = _
    rw [fullSliceReinsertPatch_point_value S Q hq]
    rfl
end ResidueBoxSlice

theorem RelativePatchSliceConclusion.exists_full_law
    {X : Type*} [Fintype X] [DecidableEq X] {s rankBound : ℕ} {N : X → ℕ}
    {f : (X → ℤ) → ℝ} {target cost : ℝ} (hN : ∀ i, 0 < N i)
    (h : RelativePatchSliceConclusion s N f target rankBound cost) :
    ∃ (d : ℕ) (Q : PolynomialPatch X s d) (law : FiniteProbabilityWeights (integerBox N)),
      d ≤ rankBound ∧ relativePatchComplexity Q ≤ cost ∧ (Q.kernel.lip : ℝ) ≤ Real.exp cost ∧
      Real.exp (-cost) ≤ law.mean (fun x => (f x.val-target) * Q.value (fun i => (x.val i : ℝ))) ∧
      ∃ q, 0 < q ∧ ∃ (S : ResidueBoxSlice N q) (hlen : ∀ i, 0 < S.length i),
        (∀ i, Real.exp (-cost) * (N i : ℝ) ≤ (S.length i : ℝ)) ∧ law = S.fullSliceLaw hlen := by
  obtain ⟨q,hq,S,d,Q,hlength,hd,hcost,hscore⟩ := h
  have hlen : ∀ i, 0 < S.length i := by
    intro i
    exact_mod_cast (mul_pos (Real.exp_pos (-cost)) (Nat.cast_pos.mpr (hN i))).trans_le (hlength i)
  have hlog : Real.log (1+(Q.kernel.lip : ℝ)) ≤ cost := by
    have := Nat.cast_nonneg (α := ℝ) d
    dsimp only [relativePatchComplexity] at hcost
    linarith
  have hlip : (Q.kernel.lip : ℝ) ≤ Real.exp cost := by
    have he := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by positivity : 0 < 1+(Q.kernel.lip : ℝ))] at he
    linarith
  refine ⟨d,S.fullSliceReinsertPatch Q,S.fullSliceLaw hlen,hd,hcost,hlip,?_,q,hq,S,hlen,hlength,rfl⟩
  rwa [S.fullSliceLaw_score hlen hq Q f target]
end Erdos3

end

end OAI
