import GRHArticle.ProgressionFree.CompactPrimeBlockRules
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Data.Nat.Prime.Nth

/-!
# A compact space of finitely many prime-block rules

Each prime slot is a finite prime index or the point at infinity.
An unused slot has reciprocal weight zero. The product of normalized
block masses attains a maximum on the compact space of labelled rules
without repeated finite labels.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators OnePoint

private noncomputable def finitePrimeWeight (i : ℕ) : ↥PrimeWeightInterval :=
  ⟨1/(Nat.nth Nat.Prime i : ℝ), by
    have hp := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i
    exact ⟨by positivity,one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp.two_le)⟩⟩

/-- A prime's reciprocal at a finite index, or zero at infinity. -/
noncomputable def primeSlotWeight (x : OnePoint ℕ) : ↥PrimeWeightInterval :=
  x.elim ⟨0,by norm_num⟩ finitePrimeWeight

@[simp] theorem primeSlotWeight_infty :
    (primeSlotWeight (∞ : OnePoint ℕ)).val = 0 := rfl

@[simp] theorem primeSlotWeight_coe (i : ℕ) :
    (primeSlotWeight (i : OnePoint ℕ)).val = 1/(Nat.nth Nat.Prime i : ℝ) := rfl

/-- Prime reciprocal weights tend to zero at the missing label. -/
theorem continuous_primeSlotWeight : Continuous primeSlotWeight := by
  apply (OnePoint.continuous_iff_from_nat _).mpr
  rw [tendsto_subtype_rng]
  change Tendsto (fun i : ℕ ↦ 1/(Nat.nth Nat.Prime i : ℝ)) atTop (𝓝 0)
  exact tendsto_one_div_atTop_nhds_zero_nat.comp
    (Nat.nth_strictMono Nat.infinite_setOf_prime).tendsto_atTop

/-- A finite array of optional prime indices and a rule code for each row. -/
abbrev PrimeBlockSlotConfiguration (m d : ℕ) :=
  (Fin m → Fin d → OnePoint ℕ) × (Fin m → (Fin d → ℕ) → Fin 2)

/-- Each finite label is used once at most, and each row rule is free of
length-`k` progressions. -/
def ValidPrimeBlockSlotConfiguration (k : ℕ) {m d : ℕ}
    (x : PrimeBlockSlotConfiguration m d) : Prop :=
  (∀ a b : Fin m × Fin d, a ≠ b → ∀ p : ℕ,
    ¬ (x.1 a.1 a.2 = (p : OnePoint ℕ) ∧ x.1 b.1 b.2 = (p : OnePoint ℕ))) ∧
  ∀ i, KTermVectorAPFree k (exponentRuleOfCode (x.2 i))

private theorem continuous_slot {m d : ℕ} (a : Fin m × Fin d) :
    Continuous (fun x : PrimeBlockSlotConfiguration m d ↦ x.1 a.1 a.2) := by
  have h₁ : Continuous (fun x : PrimeBlockSlotConfiguration m d ↦ x.1 a.1) :=
    (continuous_apply a.1 : Continuous (fun z : Fin m → Fin d → OnePoint ℕ ↦ z a.1)).comp continuous_fst
  exact (continuous_apply a.2).comp h₁

private theorem isOpen_onePoint_nat_singleton (p : ℕ) :
    IsOpen ({(p : OnePoint ℕ)} : Set (OnePoint ℕ)) := by
  have h : ((↑) '' ({p} : Set ℕ) : Set (OnePoint ℕ)) = {(p : OnePoint ℕ)} := Set.image_singleton ..
  rw [← h]
  exact OnePoint.isOpenMap_coe _ (isOpen_discrete _)

/-- The valid finite configurations form a compact parameter space. -/
theorem isCompact_validPrimeBlockSlotConfigurations (k m d : ℕ) :
    IsCompact {x : PrimeBlockSlotConfiguration m d | ValidPrimeBlockSlotConfiguration k x} := by
  have hLabels :
      IsClosed {x : PrimeBlockSlotConfiguration m d |
        ∀ a b : Fin m × Fin d, a ≠ b → ∀ p : ℕ,
          ¬ (x.1 a.1 a.2 = (p : OnePoint ℕ) ∧ x.1 b.1 b.2 = (p : OnePoint ℕ))} := by
    have hPoint (a : Fin m × Fin d) (p : ℕ) :
      IsOpen {x : PrimeBlockSlotConfiguration m d | x.1 a.1 a.2 = (p : OnePoint ℕ)} :=
      (isOpen_onePoint_nat_singleton p).preimage (continuous_slot a)
    have he :
        {x : PrimeBlockSlotConfiguration m d | ∀ a b : Fin m × Fin d, a ≠ b → ∀ p : ℕ,
          ¬ (x.1 a.1 a.2 = (p : OnePoint ℕ) ∧ x.1 b.1 b.2 = (p : OnePoint ℕ))} =
        ⋂ a : Fin m × Fin d, ⋂ b : Fin m × Fin d, ⋂ _ : a ≠ b, ⋂ p : ℕ,
          ({x : PrimeBlockSlotConfiguration m d | x.1 a.1 a.2 = (p : OnePoint ℕ)} ∩
            {x : PrimeBlockSlotConfiguration m d | x.1 b.1 b.2 = (p : OnePoint ℕ)})ᶜ := by
      ext x
      simp only [Set.mem_setOf_eq,Set.mem_iInter,Set.mem_compl_iff,Set.mem_inter_iff]
    rw [he]
    exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun p ↦
      (hPoint a p |>.inter (hPoint b p)).isClosed_compl
  have hRules : IsClosed {x : PrimeBlockSlotConfiguration m d |
      ∀ i, KTermVectorAPFree k (exponentRuleOfCode (x.2 i))} := by
    have he :
        {x : PrimeBlockSlotConfiguration m d | ∀ i, KTermVectorAPFree k (exponentRuleOfCode (x.2 i))} =
        ⋂ i : Fin m, (fun x : PrimeBlockSlotConfiguration m d ↦ x.2 i) ⁻¹'
          {r | KTermVectorAPFree k (exponentRuleOfCode r)} := by
      ext x
      simp only [Set.mem_setOf_eq,Set.mem_iInter,Set.mem_preimage]
    rw [he]
    exact isClosed_iInter fun i ↦
      (isClosed_progressionFreeExponentCodes (Fin d) k).preimage
        ((continuous_apply i).comp continuous_snd)
  exact (hLabels.inter hRules).isCompact

/-- The mass of one row relative to its greedy rule. -/
noncomputable def primeBlockSlotRowScore (k : ℕ) {m d : ℕ}
    (x : PrimeBlockSlotConfiguration m d) (i : Fin m) : ℝ :=
  reciprocalExponentMass (fun j ↦ (primeSlotWeight (x.1 i j)).val) (exponentRuleOfCode (x.2 i)) /
    reciprocalExponentMass (fun j ↦ (primeSlotWeight (x.1 i j)).val) (greedyExponentPatterns (Fin d) k)

/-- The finite product of each row's mass divided by its greedy mass. -/
noncomputable def primeBlockSlotScore (k : ℕ) {m d : ℕ} (x : PrimeBlockSlotConfiguration m d) : ℝ :=
  ∏ i : Fin m, primeBlockSlotRowScore k x i

/-- The weight of the greedy zero vector makes the normalizer nonzero
even on a row that contains no finite labels. -/
theorem one_le_reciprocalExponentMass_greedy {ι : Type*} [Fintype ι] {k : ℕ} (hk : 2 ≤ k)
    (u : ι → ↥PrimeWeightInterval) :
    1 ≤ reciprocalExponentMass (fun j ↦ (u j).val) (greedyExponentPatterns ι k) := by
  let G := greedyExponentPatterns ι k
  let w (j : ι) : ℝ := (u j).val
  have hsum := summable_reciprocalExponentWeight
    (u := w) (fun j ↦ (u j).property.1) (fun j ↦ (u j).property.2.trans_lt (by norm_num))
  have hz : (0 : ι → ℕ) ∈ G := by
    intro i
    change 0 ∈ greedyLengthExponents k
    exact mem_greedyLengthExponents_of_lt hk (by omega)
  have hs : Summable (G.indicator (reciprocalExponentWeight w)) :=
    summable_subtype_iff_indicator.mp (hsum.subtype _)
  have h := hs.sum_le_tsum ({0} : Finset (ι → ℕ)) (fun v _ ↦ Set.indicator_nonneg
    (fun x _ ↦ reciprocalExponentWeight_nonneg (fun j ↦ (u j).property.1) x) v)
  simpa [reciprocalExponentMass,Set.indicator_of_mem hz,reciprocalExponentWeight] using h

theorem continuous_primeBlockSlotScore {k : ℕ} (hk : 2 ≤ k) (m d : ℕ) :
    Continuous (primeBlockSlotScore k : PrimeBlockSlotConfiguration m d → ℝ) := by
  unfold primeBlockSlotScore primeBlockSlotRowScore
  apply continuous_finsetProd
  intro i _
  let w (x : PrimeBlockSlotConfiguration m d) (j : Fin d) := primeSlotWeight (x.1 i j)
  have hw : Continuous w := continuous_pi fun j ↦ continuous_primeSlotWeight.comp (continuous_slot (i,j))
  have hr : Continuous (fun x : PrimeBlockSlotConfiguration m d ↦ x.2 i) :=
    (continuous_apply i).comp continuous_snd
  have hNum := (continuous_reciprocalExponentMass_code (Fin d)).comp (hw.prodMk hr)
  let b (v : Fin d → ℕ) : Fin 2 := if v ∈ greedyExponentPatterns (Fin d) k then 1 else 0
  have heq : exponentRuleOfCode b = greedyExponentPatterns (Fin d) k := exponentRuleOfCode_indicator _
  have hDen := (continuous_reciprocalExponentMass_code (Fin d)).comp
    (hw.prodMk (continuous_const (y := b)))
  change Continuous (fun x : PrimeBlockSlotConfiguration m d ↦
    reciprocalExponentMass (fun j ↦ (w x j).val) (exponentRuleOfCode (x.2 i)) /
      reciprocalExponentMass (fun j ↦ (w x j).val) (greedyExponentPatterns (Fin d) k))
  rw [← heq]
  exact hNum.div hDen (fun x ↦ ne_of_gt (lt_of_lt_of_le zero_lt_one (by
    rw [heq]
    exact one_le_reciprocalExponentMass_greedy hk (w x))))

/-- Normalized block masses have a positive, attained maximum over the
compact configuration space. -/
theorem exists_maximal_primeBlockSlotScore {k : ℕ} (hk : 2 ≤ k) (m d : ℕ) :
    ∃ x : PrimeBlockSlotConfiguration m d, ValidPrimeBlockSlotConfiguration k x ∧
      1 ≤ primeBlockSlotScore k x ∧
      ∀ y : PrimeBlockSlotConfiguration m d, ValidPrimeBlockSlotConfiguration k y →
        primeBlockSlotScore k y ≤ primeBlockSlotScore k x := by
  let b (v : Fin d → ℕ) : Fin 2 := if v ∈ greedyExponentPatterns (Fin d) k then 1 else 0
  have hb : exponentRuleOfCode b = greedyExponentPatterns (Fin d) k := exponentRuleOfCode_indicator _
  let x₀ : PrimeBlockSlotConfiguration m d := (fun _ _ ↦ ∞,fun _ ↦ b)
  have hx₀ : ValidPrimeBlockSlotConfiguration k x₀ := by
    refine ⟨fun _ _ _ p h ↦ OnePoint.infty_ne_coe p h.1,fun i ↦ ?_⟩
    rw [show x₀.2 i = b from rfl,hb]
    exact kTermVectorAPFree_greedyExponentPatterns _ hk
  have hOne : primeBlockSlotScore k x₀ = 1 := by
    unfold primeBlockSlotScore primeBlockSlotRowScore
    apply Finset.prod_eq_one
    intro i _
    rw [show x₀.2 i = b from rfl,hb]
    exact div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one
      (one_le_reciprocalExponentMass_greedy hk (fun j ↦ primeSlotWeight (x₀.1 i j)))))
  obtain ⟨x,hx,hMax⟩ := (isCompact_validPrimeBlockSlotConfigurations k m d).exists_isMaxOn
    ⟨x₀,hx₀⟩ (continuous_primeBlockSlotScore hk m d).continuousOn
  have h := hMax (show x₀ ∈ {y | ValidPrimeBlockSlotConfiguration k y} from hx₀)
  change primeBlockSlotScore k x₀ ≤ primeBlockSlotScore k x at h
  rw [hOne] at h
  exact ⟨x,hx,h,fun _ hy ↦ hMax hy⟩

end GRHArticle.ProgressionFree
