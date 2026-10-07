/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.FinitePushforwardComplexWeights
import OAI.Combinatorics.Progressions.Estimates.RelativeFiberSlicePatch
import OAI.Combinatorics.Progressions.Estimates.RelativePatchAmplification

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

theorem fiberIntegerPoint_mem_integerBox
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (u : ∀ k, Fin (S.length k)) : S.fiberIntegerPoint fixed u ∈ integerBox N := by
  rw [mem_integerBox]
  intro i
  by_cases hi : keep i
  · change 0 ≤ finiteSplitPoint keep _ fixed i ∧ finiteSplitPoint keep _ fixed i < (N i : ℤ)
    simp only [finiteSplitPoint, dite_eq_left hi]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast (S.point u ⟨i, hi⟩).isLt⟩
  · change 0 ≤ finiteSplitPoint keep _ fixed i ∧ finiteSplitPoint keep _ fixed i < (N i : ℤ)
    simpa only [finiteSplitPoint, dite_eq_right hi] using hfixed ⟨i, hi⟩

theorem fiberIntegerPoint_injective
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hq : 0 < q) (fixed : {x // ¬keep x} → ℤ) :
    Function.Injective (S.fiberIntegerPoint fixed) := by
  let _ : Fintype X := inferInstance
  let _ : DecidableEq X := inferInstance
  intro u v huv
  funext k
  apply Fin.ext
  have hk := congrFun huv k.val
  change finiteSplitPoint keep _ fixed k = finiteSplitPoint keep _ fixed k at hk
  rw [finiteSplitPoint_fixed, finiteSplitPoint_fixed] at hk
  have he : S.start k + q * (u k).val = S.start k + q * (v k).val := by
    exact_mod_cast hk
  exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel he)

def fiberPointInBox (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (u : ∀ k, Fin (S.length k)) : integerBox N :=
  ⟨S.fiberIntegerPoint fixed u, S.fiberIntegerPoint_mem_integerBox fixed hfixed u⟩

noncomputable def fiberSliceLaw
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ)) :
    FiniteProbabilityWeights (integerBox N) := by
  letI : ∀ k, Nonempty (Fin (S.length k)) := fun k => ⟨⟨0, hlen k⟩⟩
  exact (FiniteProbabilityWeights.uniform (∀ k, Fin (S.length k))).finitePushforward
    (S.fiberPointInBox fixed hfixed)

theorem fiberSliceLaw_mean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (test : integerBox N → ℝ) :
    (S.fiberSliceLaw hlen fixed hfixed).mean test =
      𝔼 u, test (S.fiberPointInBox fixed hfixed u) := by
  let : ∀ k, Nonempty (Fin (S.length k)) := fun k => ⟨⟨0, hlen k⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_mean _ _

theorem fiberSliceLaw_weight
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ)) (x : integerBox N) :
    (S.fiberSliceLaw hlen fixed hfixed).weight x =
      𝔼 u, if S.fiberPointInBox fixed hfixed u = x then (1 : ℝ) else 0 := by
  have h := S.fiberSliceLaw_mean hlen fixed hfixed
    (fun y => if y = x then (1 : ℝ) else 0)
  simpa only [FiniteProbabilityWeights.mean, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

theorem fiberSliceLaw_score {s d : ℕ}
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (hq : 0 < q) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (Q : PolynomialPatch {x // keep x} s d) (f : (X → ℤ) → ℝ) (target : ℝ) :
    (S.fiberSliceLaw hlen fixed hfixed).mean
      (fun x => (f x.val - target) *
        (S.fiberReinsertPatch Q).value (fun i => (x.val i : ℝ))) =
      relativePatchSliceScore S (fun x => f (finiteSplitPoint keep x fixed)) target Q := by
  rw [fiberSliceLaw_mean]
  unfold relativePatchSliceScore
  congr 1
  · ext u
    simp
  · funext u
    change (f (S.fiberIntegerPoint fixed u) - target) *
      (S.fiberReinsertPatch Q).value (fun i => (S.fiberIntegerPoint fixed u i : ℝ)) = _
    rw [fiberReinsertPatch_integerPoint_value S Q hq]
    rfl

end ResidueBoxSlice

theorem RelativePatchSliceConclusion.exists_fiber_law
    {X : Type*} [Fintype X] [DecidableEq X] {keep : X → Prop} [DecidablePred keep]
    {s rankBound : ℕ} {N : X → ℕ} {f : (X → ℤ) → ℝ} {target cost : ℝ}
    (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (hN : ∀ k : {x // keep x}, 0 < N k.val)
    (h : RelativePatchSliceConclusion s (fun k : {x // keep x} => N k.val)
      (fun x => f (finiteSplitPoint keep x fixed)) target rankBound cost) :
    ∃ (d : ℕ) (Qfull : PolynomialPatch X s d)
      (law : FiniteProbabilityWeights (integerBox N)),
      d ≤ rankBound ∧ relativePatchComplexity Qfull ≤ cost ∧
      (Qfull.kernel.lip : ℝ) ≤ Real.exp cost ∧
      Real.exp (-cost) ≤ law.mean
        (fun x => (f x.val - target) * Qfull.value (fun i => (x.val i : ℝ))) := by
  obtain ⟨q, hq, S, d, Q, hlength, hd, hcost, hscore⟩ := h
  have hlen : ∀ k, 0 < S.length k := by
    intro k
    exact_mod_cast (mul_pos (Real.exp_pos (-cost))
      (Nat.cast_pos.mpr (hN k))).trans_le (hlength k)
  have hlog : Real.log (1 + (Q.kernel.lip : ℝ)) ≤ cost := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    dsimp only [relativePatchComplexity] at hcost
    linarith
  have hlip : (Q.kernel.lip : ℝ) ≤ Real.exp cost := by
    have hpos : 0 < 1 + (Q.kernel.lip : ℝ) := by positivity
    have he := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hpos] at he
    linarith
  refine ⟨d, S.fiberReinsertPatch Q, S.fiberSliceLaw hlen fixed hfixed,
    hd, hcost, hlip, ?_⟩
  rwa [S.fiberSliceLaw_score hlen hq fixed hfixed Q f target]

theorem RelativePatchSliceConclusion.exists_fiber_law_with_slice
    {X : Type*} [Fintype X] [DecidableEq X] {keep : X → Prop} [DecidablePred keep]
    {s rankBound : ℕ} {N : X → ℕ} {f : (X → ℤ) → ℝ} {target cost : ℝ}
    (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (hN : ∀ k : {x // keep x}, 0 < N k.val)
    (h : RelativePatchSliceConclusion s (fun k : {x // keep x} => N k.val)
      (fun x => f (finiteSplitPoint keep x fixed)) target rankBound cost) :
    ∃ (d : ℕ) (Qfull : PolynomialPatch X s d)
      (law : FiniteProbabilityWeights (integerBox N)),
      d ≤ rankBound ∧ relativePatchComplexity Qfull ≤ cost ∧
      (Qfull.kernel.lip : ℝ) ≤ Real.exp cost ∧
      Real.exp (-cost) ≤ law.mean
        (fun x => (f x.val - target) * Qfull.value (fun i => (x.val i : ℝ))) ∧
      ∃ (q : ℕ), 0 < q ∧
        ∃ (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
          (hlen : ∀ k, 0 < S.length k),
          (∀ k, Real.exp (-cost) * (N k.val : ℝ) ≤ (S.length k : ℝ)) ∧
          law = S.fiberSliceLaw hlen fixed hfixed := by
  obtain ⟨q, hq, S, d, Q, hlength, hd, hcost, hscore⟩ := h
  have hlen : ∀ k, 0 < S.length k := by
    intro k
    exact_mod_cast (mul_pos (Real.exp_pos (-cost))
      (Nat.cast_pos.mpr (hN k))).trans_le (hlength k)
  have hlog : Real.log (1 + (Q.kernel.lip : ℝ)) ≤ cost := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    dsimp only [relativePatchComplexity] at hcost
    linarith
  have hlip : (Q.kernel.lip : ℝ) ≤ Real.exp cost := by
    have hpos : 0 < 1 + (Q.kernel.lip : ℝ) := by positivity
    have he := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hpos] at he
    linarith
  refine ⟨d, S.fiberReinsertPatch Q, S.fiberSliceLaw hlen fixed hfixed,
    hd, hcost, hlip, ?_, q, hq, S, hlen, hlength, rfl⟩
  rwa [S.fiberSliceLaw_score hlen hq fixed hfixed Q f target]

end Erdos3

end

end OAI
