import GRHArticle.ProgressionFree.LightPrimeBlocks
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Order.Compact

/-!
# Compactness of progression-free local rules

A rule is coded by one binary membership value at every exponent vector.
Each forbidden progression restricts finitely many membership values.
The reciprocal mass is jointly continuous in the code and the weights
because the weight vector with every entry one half gives a summable
majorant.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators

/-- The allowable range of a prime reciprocal, including zero for
a prime that tends to infinity. -/
abbrev PrimeWeightInterval : Set ℝ :=
  Set.Icc (0 : ℝ) (1/2)

/-- The exponent vectors accepted by a membership code. -/
def exponentRuleOfCode {ι : Type*} (code : (ι → ℕ) → Fin 2) : Set (ι → ℕ) :=
  {x | code x = 1}

/-- Codes for progression-free rules form a closed subset of the binary
product space. -/
theorem isClosed_progressionFreeExponentCodes (ι : Type*) (k : ℕ) :
    IsClosed {code : (ι → ℕ) → Fin 2 | KTermVectorAPFree k (exponentRuleOfCode code)} := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro code hbad
  have hf : ¬ KTermVectorAPFree k (exponentRuleOfCode code) := hbad
  unfold KTermVectorAPFree at hf
  push Not at hf
  obtain ⟨x,a,d,hmem,hAffine,p,hd⟩ := hf
  let U : Set ((ι → ℕ) → Fin 2) := ⋂ i : Fin k, {c | c (x i) = 1}
  have hU : IsOpen U := isOpen_iInter_of_finite fun i ↦ by
    change IsOpen ((fun c : (ι → ℕ) → Fin 2 ↦ c (x i)) ⁻¹' ({1} : Set (Fin 2)))
    exact (isOpen_discrete _).preimage (continuous_apply (x i))
  have hcode : code ∈ U := Set.mem_iInter.mpr fun i ↦ hmem i
  refine Filter.mem_of_superset (hU.mem_nhds hcode) fun c hc hcF ↦ ?_
  have hcMem (i : Fin k) : x i ∈ exponentRuleOfCode c := Set.mem_iInter.mp hc i
  exact hd (hcF x a d hcMem hAffine p)

/-- A binary membership code and weights in `[0,1/2]` jointly determine
the reciprocal mass continuously. -/
theorem continuous_reciprocalExponentMass_code (ι : Type*) [Fintype ι] :
    Continuous (fun z : (ι → ↥PrimeWeightInterval) × ((ι → ℕ) → Fin 2) ↦
      reciprocalExponentMass (fun p ↦ (z.1 p).val) (exponentRuleOfCode z.2)) := by
  let X := (ι → ↥PrimeWeightInterval) × ((ι → ℕ) → Fin 2)
  let f (z : X) (v : ι → ℕ) :=
    (exponentRuleOfCode z.2).indicator (reciprocalExponentWeight (fun p ↦ (z.1 p).val)) v
  let W : (ι → ℕ) → ℝ := reciprocalExponentWeight (fun _ ↦ (1/2 : ℝ))
  have hSum : Summable W := summable_reciprocalExponentWeight (fun _ ↦ by norm_num)
    (fun _ ↦ by norm_num)
  have ht (v : ι → ℕ) : Continuous (fun z ↦ f z v) := by
    have hCode : Continuous (fun z : X ↦ if z.2 v = 1 then (1 : ℝ) else 0) :=
      (continuous_of_discreteTopology : Continuous (fun t : Fin 2 ↦ if t = 1 then (1 : ℝ) else 0)).comp
        ((continuous_apply v).comp continuous_snd)
    have hWeight : Continuous (fun z : X ↦ reciprocalExponentWeight (fun p ↦ (z.1 p).val) v) := by
      unfold reciprocalExponentWeight
      apply continuous_finsetProd
      intro p _
      have hc : Continuous (fun z : X ↦ z.1 p) :=
        (continuous_apply p : Continuous (fun v : ι → ↥PrimeWeightInterval ↦ v p)).comp continuous_fst
      exact (continuous_subtype_val.comp hc).pow _
    refine (hCode.mul hWeight).congr fun z ↦ ?_
    by_cases hz : z.2 v = 1 <;> simp [f,Set.indicator,exponentRuleOfCode,hz]
  have hb (z : X) (v : ι → ℕ) : ‖f z v‖ ≤ W v := by
    have hn : 0 ≤ f z v := Set.indicator_nonneg
      (fun x _ ↦ reciprocalExponentWeight_nonneg (fun p ↦ (z.1 p).property.1) x) _
    rw [Real.norm_eq_abs,abs_of_nonneg hn]
    by_cases hz : z.2 v = 1
    · rw [show f z v = reciprocalExponentWeight (fun p ↦ (z.1 p).val) v by
        exact Set.indicator_of_mem (show v ∈ exponentRuleOfCode z.2 from hz) _]
      unfold W reciprocalExponentWeight
      exact prod_le_prod (fun p _ ↦ pow_nonneg (z.1 p).property.1 _)
        (fun p _ ↦ pow_le_pow_left₀ (z.1 p).property.1 (z.1 p).property.2 _)
    · rw [show f z v = 0 by
        exact Set.indicator_of_notMem (show v ∉ exponentRuleOfCode z.2 from hz) _]
      exact reciprocalExponentWeight_nonneg (fun _ ↦ by norm_num) _
  rw [continuous_iff_continuousAt]
  intro z
  exact tendsto_tsum_of_dominated_convergence hSum (fun v ↦ (ht v).continuousAt)
    (Eventually.of_forall hb)

theorem exponentRuleOfCode_indicator {ι : Type*} (F : Set (ι → ℕ)) :
    exponentRuleOfCode (fun v ↦ if v ∈ F then (1 : Fin 2) else 0) = F := by
  ext v
  by_cases hv : v ∈ F <;> simp [exponentRuleOfCode,hv]

/-- The maximum reciprocal mass of progression-free rules on a fixed
finite block is attained. -/
theorem exists_maximal_reciprocalExponentMass {ι : Type*} [Fintype ι] {k : ℕ}
    (hk : 0 < k) (u : ι → ↥PrimeWeightInterval) :
    ∃ A : Set (ι → ℕ), KTermVectorAPFree k A ∧
      ∀ B : Set (ι → ℕ), KTermVectorAPFree k B →
        reciprocalExponentMass (fun p ↦ (u p).val) B ≤ reciprocalExponentMass (fun p ↦ (u p).val) A := by
  let S : Set ((ι → ℕ) → Fin 2) :=
    {code | KTermVectorAPFree k (exponentRuleOfCode code)}
  have hS : IsCompact S := (isClosed_progressionFreeExponentCodes ι k).isCompact
  have hS₀ : S.Nonempty := by
    refine ⟨fun _ ↦ 0,?_⟩
    intro x _ _ h
    have h0 : (0 : Fin 2) = 1 := h ⟨0,hk⟩
    exact (by decide : (0 : Fin 2) ≠ 1) h0 |>.elim
  have h := (continuous_reciprocalExponentMass_code ι).comp (continuous_const.prodMk continuous_id
    : Continuous (fun code : (ι → ℕ) → Fin 2 ↦ (u,code)))
  obtain ⟨code,hmem,hMax⟩ := hS.exists_isMaxOn hS₀ h.continuousOn
  refine ⟨exponentRuleOfCode code,hmem,fun B hB ↦ ?_⟩
  let b (v : ι → ℕ) : Fin 2 := if v ∈ B then 1 else 0
  have hEq : exponentRuleOfCode b = B := exponentRuleOfCode_indicator B
  have hb : b ∈ S := by
    change KTermVectorAPFree k (exponentRuleOfCode b)
    rwa [hEq]
  have hh : reciprocalExponentMass (fun p ↦ (u p).val) (exponentRuleOfCode b) ≤
      reciprocalExponentMass (fun p ↦ (u p).val) (exponentRuleOfCode code) := hMax hb
  rwa [hEq] at hh

end GRHArticle.ProgressionFree
