/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Mathematical statements are unchanged from the pinned upstream source.
Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.CyclicProductBudget
import OAI.Combinatorics.Progressions.Nilpotent.CyclicNiltestDetection

namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3

def CyclicProductNiltestDetection.{u,v} (s : ℕ) (F : ℝ → ℝ) : Prop :=
  ∀ {ι : Type v} [Fintype ι] {L : ι → Type u}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (p : ℝ),
    0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
    ∀ (w : Fin 1 → ℕ), (∀ j, 0 < w j) →
    ∀ (T : ∀ i, (D i).Niltest w), (∀ i, (T i).ComplexityLE p) →
    ∀ (N : ℕ) [NeZero N] (h : ι → ZMod N) (f : ZMod N → ℂ),
    (∀ x, ‖f x‖ ≤ 1) →
    Real.exp (-p) ≤ ‖finiteCorrelation Finset.univ f
      (translatedCyclicProduct h (fun i n => (T i).eval (fun _ => n)))‖ →
    Real.exp (-F p) ≤ gowersNorm (s + 1) f

theorem cyclicProductNiltestDetection_zero.{u,v} :
    CyclicProductNiltestDetection.{u,v} 0 (fun p => p + p ^ 2) := by
  intro ι _ L _ _ d _ _ _ _ D p hp hι w hw T hT N _ h f hf hc
  let c : ℂ := ∏ i, (T i).eval (fun _ => 0)
  have he (x : ZMod N) : translatedCyclicProduct h (fun i n => (T i).eval (fun _ => n)) x = c := by
    unfold translatedCyclicProduct c
    apply Finset.prod_congr rfl
    intro i _
    simp only [RationalFilteredNilmanifold.Niltest.eval_step_zero (D i)]
  have hcnorm : ‖c‖ ≤ Real.exp (p ^ 2) := by
    unfold c
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : ι, Real.exp p :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => (T i).eval_budget (hT i) _)
      _ = Real.exp ((Fintype.card ι : ℝ) * p) := by
        rw [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have heq : finiteCorrelation Finset.univ f
      (translatedCyclicProduct h (fun i n => (T i).eval (fun _ => n))) =
      (𝔼 x, f x) * star c := by
    simp only [finiteCorrelation, he, ← Finset.expect_mul]
  rw [heq, norm_mul, norm_star] at hc
  have hg : Real.exp (-p) / Real.exp (p ^ 2) ≤ ‖𝔼 x, f x‖ := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    exact hc.trans (mul_le_mul_of_nonneg_left hcnorm (norm_nonneg _))
  have he' : Real.exp (-p) / Real.exp (p ^ 2) = Real.exp (-(p + p ^ 2)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rwa [he', ← gowersNorm_one] at hg

end Erdos3

end

section

open scoped TensorProduct BigOperators

namespace Erdos3

theorem exists_cyclicProductNiltestDetection_succ.{u,v} (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicProductNiltestDetection.{u,v} (s + 1) (fun p => (p + C) ^ C) := by
  obtain ⟨c, _, hdet⟩ := exists_intervalNiltestDetection (s + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_cyclicProductDetectionBudget_bound s c
  refine ⟨C, hC, ?_⟩
  intro ι _ L _ _ d _ _ _ _ D p hp hι w hw T hT N _ h f hf hc
  obtain ⟨a, hlen, hbound, hshort, hS, hcorr, hvol⟩ :=
    exists_correlating_niltest_product_piece D w hw T hT h f hf hc
  let len := intervalCutUpper (commonCyclicCuts h) N a - a.val
  let S := fun i => (T i).translate hw (fun _ => cyclicTranslationOffset (h i) a)
  change 0 < len at hlen
  let : NeZero len := ⟨hlen.ne'⟩
  let : FiniteDimensional ℚ (∀ i, L i) :=
    (RationalFilteredNilmanifold.productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, L i)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis D)
  obtain ⟨U, hU, hUeval⟩ := RationalFilteredNilmanifold.exists_product_niltest D S hp hι hS
  have hq := cyclicProductInputBudget_bounds hp
  have heval : (fun n : ℤ => U.eval (fun _ => n)) =
      (fun n => ∏ i, (S i).eval (fun _ => n)) := funext (fun n => hUeval (fun _ => n))
  have hcU : Real.exp (-cyclicProductInputBudget p) ≤
      ‖finiteCorrelation (Finset.Ico (a.val : ℤ) (a.val + len)) (fun x => f (x : ZMod N))
        (fun n => U.eval (fun _ => n))‖ := by
    rw [heval]
    exact (Real.exp_le_exp.mpr (neg_le_neg hq.2.2)).trans
      ((cyclic_product_retained_correlation (Fintype.card ι) hι).trans hcorr)
  have hlocal := hdet (RationalFilteredNilmanifold.pi D) (cyclicProductInputBudget p)
    hq.1 w hw U (hU.mono hq.2.1) (a.val : ℤ) len (fun x => f (x : ZMod N))
    (fun x _ => hf _) hcU
  have hvolume : Real.exp (-cyclicProductVolumeBudget p) ≤ (len : ℝ) / N :=
    (cyclic_product_retained_volume (Fintype.card ι) hp hι).trans hvol
  have hpow := cyclicInterval_gowersNorm_lower_pow (a.val : ℤ) len (s + 1) hshort f
    (Real.exp_nonneg (-cyclicProductVolumeBudget p))
    (Real.exp_nonneg (-((cyclicProductInputBudget p + c) ^ c))) hvolume hlocal
  have hpower : Real.exp (-cyclicProductCutoffBudget s c p) ≤
      gowersNorm (s + 2) (fun x => f x * finiteIndicator (cyclicInterval (a.val : ZMod N) len) x)
        ^ (2 ^ (s + 2)) := by
    apply (cyclic_product_cutoff_exponential s c p).trans
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc, Int.cast_natCast] at hpow ⊢
    exact hpow
  have hcut := exp_neg_le_of_pow (gowersNorm_nonneg (s + 1) _)
    (cyclicProductCutoffBudget_nonneg s c hp) (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hpower
  have htransfer := gowersNorm_transfer_cyclicInterval s f hf (a.val : ZMod N) len
    (Real.exp_pos (-cyclicProductCutoffBudget s c p))
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (cyclicProductCutoffBudget_nonneg s c hp))) hcut
  exact (Real.exp_le_exp.mpr (neg_le_neg (hbudget p hp))).trans
    ((cyclic_product_transfer_exponential s c p).trans htransfer)

theorem exists_cyclicProductNiltestDetection.{u,v} (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicProductNiltestDetection.{u,v} s (fun p => (p + C) ^ C) := by
  cases s with
  | zero =>
    refine ⟨2, le_rfl, ?_⟩
    intro ι _ L _ _ d _ _ _ _ D p hp hι w hw T hT N _ h f hf hc
    have hb : p + p ^ 2 ≤ (p + (2 : ℕ)) ^ 2 := by
      norm_num only [Nat.cast_ofNat]
      nlinarith
    exact (Real.exp_le_exp.mpr (neg_le_neg hb)).trans
      (cyclicProductNiltestDetection_zero D p hp hι w hw T hT N h f hf hc)
  | succ s => exact exists_cyclicProductNiltestDetection_succ s

end Erdos3

end

end OAI
