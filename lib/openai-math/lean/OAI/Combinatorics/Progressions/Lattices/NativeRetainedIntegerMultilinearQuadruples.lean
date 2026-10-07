import OAI.Combinatorics.Progressions.Estimates.NativeMultilinearQuadruples

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def cyclicBranchOffset {N : ℕ} (h : ZMod N) (branch : Bool) : ℤ :=
  (h.val : ℤ) - if branch then (N : ℤ) else 0

theorem cyclicTranslationOffset_eq_branch {N : ℕ} (h : ZMod N) (a : ℕ) :
    cyclicTranslationOffset h a = cyclicBranchOffset h (decide (N - h.val ≤ a)) := by
  by_cases hwrap : N - h.val ≤ a <;> simp [cyclicTranslationOffset, cyclicBranchOffset, hwrap]

theorem exists_two_shift_integer_interval {N : ℕ} [NeZero N]
    (f R : ℤ → ℂ) (h h0 : ZMod N) {rho : ℝ} (hrho : 0 < rho)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hR : ∀ n, ‖R n‖ ≤ 1)
    (hcorr : rho ≤ ‖𝔼 x : ZMod N,
      f x.val * R ((x + h).val : ℤ) * star (R ((x + h0).val : ℤ))‖) :
    ∃ (branch branch0 : Bool) (a len : ℕ), 0 < len ∧ a + len ≤ N ∧
      2 * ((len : ℤ) - 1) < N ∧
      rho / 20 ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
        f n * R (n + cyclicBranchOffset h branch) * star (R (n + cyclicBranchOffset h0 branch0))‖ ∧
      rho / 20 ≤ (len : ℝ) / N := by
  let shifts : Fin 2 → ZMod N := ![h, h0]
  let u : Fin 2 → ℤ → ℂ := ![(fun n => star (R n)), R]
  have heval (x : ZMod N) : translatedCyclicProduct shifts u x =
      star (R ((x + h).val : ℤ)) * R ((x + h0).val : ℤ) := by
    simp [translatedCyclicProduct, shifts, u, Fin.prod_univ_two, add_comm]
  have hucap (x : ZMod N) : ‖translatedCyclicProduct shifts u x‖ ≤ 1 := by
    rw [heval, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hR _)).trans (hR _)
  have hc : rho ≤ ‖finiteCorrelation Finset.univ (fun x : ZMod N => f x.val)
      (translatedCyclicProduct shifts u)‖ := by
    convert hcorr using 1
    congr 1
    unfold finiteCorrelation
    apply Finset.expect_congr rfl
    intro x _
    rw [heval]
    simp only [star_mul, star_star]
    ring
  obtain ⟨a, hlen, hbound, hshort, hcor, hvol⟩ := exists_correlating_integer_product_interval
    shifts u (fun x : ZMod N => f x.val) hrho (by norm_num : (0 : ℝ) < 1)
    (fun x => hf x.val) hucap hc
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at hcor hvol
  let branch := decide (N - h.val ≤ a.val)
  let branch0 := decide (N - h0.val ≤ a.val)
  let len := intervalCutUpper (commonCyclicCuts shifts) N a.val - a.val
  have hprod (n : ℤ) : (∏ i, u i (n + cyclicTranslationOffset (shifts i) a.val)) =
      star (R (n + cyclicBranchOffset h branch)) * R (n + cyclicBranchOffset h0 branch0) := by
    simp only [Fin.prod_univ_two, shifts, u, Matrix.cons_val_zero, Matrix.cons_val_one,
      cyclicTranslationOffset_eq_branch, branch, branch0]
    rfl
  have heq : finiteCorrelation (Finset.Ico (a.val : ℤ) (a.val + len))
      (fun n => f ((n : ZMod N).val : ℤ))
      (fun n => ∏ i, u i (n + cyclicTranslationOffset (shifts i) a.val)) =
      𝔼 n ∈ Finset.Ico (a.val : ℤ) (a.val + len),
        f n * R (n + cyclicBranchOffset h branch) * star (R (n + cyclicBranchOffset h0 branch0)) := by
    unfold finiteCorrelation
    apply Finset.expect_congr rfl
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    have hrep : (((n : ZMod N).val : ℕ) : ℤ) = n := by
      rw [ZMod.val_intCast, Int.emod_eq_of_lt (by omega) (by omega)]
    change f (((n : ZMod N).val : ℕ) : ℤ) *
      star (∏ i, u i (n + cyclicTranslationOffset (shifts i) a.val)) = _
    rw [hrep, hprod, star_mul, star_star]
    ring
  refine ⟨branch, branch0, a.val, len, hlen, hbound, hshort, ?_, ?_⟩
  · rw [← heq]
    exact hcor
  · exact hvol

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_fourPoint_integer_interval {N : ℕ} [NeZero N]
    (f₁ f₂ f₃ f₄ : ℤ → ℂ) (a : ZMod N) {ρ B : ℝ}
    (hρ : 0 < ρ) (hB : 0 < B)
    (hbound : ∀ x : ZMod N,
      ‖fourPointProduct (fun x : ZMod N => f₁ x.val) (fun x : ZMod N => f₂ x.val)
        (fun x : ZMod N => f₃ x.val) (fun x : ZMod N => f₄ x.val) a x‖ ≤ B)
    (hcorr : ρ ≤ ‖𝔼 x : ZMod N,
      fourPointProduct (fun x : ZMod N => f₁ x.val) (fun x : ZMod N => f₂ x.val)
        (fun x : ZMod N => f₃ x.val) (fun x : ZMod N => f₄ x.val) a x‖) :
    ∃ (branch : Bool) (c len : ℕ), 0 < len ∧ c + len ≤ N ∧
      2 * ((len : ℤ) - 1) < N ∧
      ρ / 20 ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
        fourPointProduct f₁ f₂ f₃ f₄ (cyclicBranchOffset a branch) n‖ ∧
      ρ / (20 * B) ≤ (len : ℝ) / N := by
  let shifts : Fin 2 → ZMod N := ![0, a]
  let u : Fin 2 → ℤ → ℂ := ![(fun n => f₁ n * star (f₃ n)), (fun n => star (f₂ n) * f₄ n)]
  have heval (x : ZMod N) : star (translatedCyclicProduct shifts u x) =
      fourPointProduct (fun x : ZMod N => f₁ x.val) (fun x : ZMod N => f₂ x.val)
        (fun x : ZMod N => f₃ x.val) (fun x : ZMod N => f₄ x.val) a x := by
    simp only [translatedCyclicProduct, shifts, u, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_add, star_mul, star_star,
      fourPointProduct, add_comm a x]
    ring
  have hu (x : ZMod N) : ‖translatedCyclicProduct shifts u x‖ ≤ B := by
    rw [← norm_star, heval]
    exact hbound x
  have hc : ρ ≤ ‖finiteCorrelation Finset.univ (fun _ : ZMod N => (1 : ℂ))
      (translatedCyclicProduct shifts u)‖ := by
    simpa only [finiteCorrelation, one_mul, heval] using hcorr
  obtain ⟨c, hlen, hN, hshort, hcor, hvol⟩ := exists_correlating_integer_product_interval
    shifts u (fun _ : ZMod N => (1 : ℂ)) hρ hB (fun _ => by norm_num) hu hc
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at hcor hvol
  let len := intervalCutUpper (commonCyclicCuts shifts) N c.val - c.val
  have hcN : c.val < N := by omega
  have hoff : cyclicTranslationOffset (shifts 0) c.val = 0 := by
    simp [shifts, cyclicTranslationOffset, Nat.not_le.mpr hcN]
  let branch := decide (N - a.val ≤ c.val)
  have hprod (n : ℤ) : star (∏ i, u i (n + cyclicTranslationOffset (shifts i) c.val)) =
      fourPointProduct f₁ f₂ f₃ f₄ (cyclicBranchOffset a branch) n := by
    rw [Fin.prod_univ_two, hoff]
    simp only [u, shifts, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero,
      cyclicTranslationOffset_eq_branch, star_mul, star_star, fourPointProduct, branch]
    ring
  refine ⟨branch, c.val, len, hlen, hN, hshort, ?_, ?_⟩
  · simpa only [finiteCorrelation, one_mul, hprod] using hcor
  · exact hvol

end Erdos3

end

section

namespace Erdos3.NativeCrossWitnesses

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

noncomputable def integerLower (h : H) (n : ℤ) : ℂ := (U h).test.eval (fun _ => n)

noncomputable def integerProduct (M : ZMod N → ℤ → ℂ) (h : H) (n : ℤ) : ℂ :=
  M h.val n * U.integerLower h n

theorem integerLower_val (h : H) (x : ZMod N) : U.integerLower h x.val = U.lower h x := rfl

theorem integerProduct_val (M : ZMod N → ℤ → ℂ)
    (hM : ∀ h x, m h x = M h x.val) (h : H) (x : ZMod N) :
    U.integerProduct M h x.val = U.product h x := by
  rw [integerProduct, integerLower_val, product, hM]
  rfl

theorem extension_quadruple_integer (M : ZMod N → ℤ → ℂ)
    (hM : ∀ h x, m h x = M h x.val) (a h k : ZMod N)
    (h₁ : h ∈ H) (h₂ : h - a ∈ H) (h₃ : k ∈ H) (h₄ : k - a ∈ H) :
    additiveQuadrupleCorrelation U.extension a h k =
      ‖𝔼 x : ZMod N,
        fourPointProduct (fun x : ZMod N => U.integerProduct M ⟨h, h₁⟩ x.val)
          (fun x : ZMod N => U.integerProduct M ⟨h - a, h₂⟩ x.val)
          (fun x : ZMod N => U.integerProduct M ⟨k, h₃⟩ x.val)
          (fun x : ZMod N => U.integerProduct M ⟨k - a, h₄⟩ x.val) a x‖ := by
  simp only [additiveQuadrupleCorrelation, fourPointProduct, U.integerProduct_val M hM,
    U.extension_of_mem h h₁, U.extension_of_mem (h - a) h₂,
    U.extension_of_mem k h₃, U.extension_of_mem (k - a) h₄]

theorem exists_integer_quadruple_interval (M : ZMod N → ℤ → ℂ)
    (hM : ∀ h x, m h x = M h x.val) (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (a h k : ZMod N) (h₁ : h ∈ H) (h₂ : h - a ∈ H) (h₃ : k ∈ H) (h₄ : k - a ∈ H)
    {ρ : ℝ} (hρ : 0 < ρ) (hcorr : ρ ≤ additiveQuadrupleCorrelation U.extension a h k) :
    ∃ (branch : Bool) (c len : ℕ), 0 < len ∧ c + len ≤ N ∧
      2 * ((len : ℤ) - 1) < N ∧
      ρ / 20 ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
        fourPointProduct (U.integerProduct M ⟨h, h₁⟩) (U.integerProduct M ⟨h - a, h₂⟩)
          (U.integerProduct M ⟨k, h₃⟩) (U.integerProduct M ⟨k - a, h₄⟩)
          (cyclicBranchOffset a branch) n‖ ∧
      ρ / (20 * Real.exp (4 * p)) ≤ (len : ℝ) / N := by
  apply exists_fourPoint_integer_interval _ _ _ _ a hρ (Real.exp_pos _)
  · intro x
    simp only [fourPointProduct, U.integerProduct_val M hM, norm_mul, norm_star]
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp p * Real.exp p :=
        mul_le_mul (mul_le_mul (mul_le_mul (U.product_norm hm _ _) (U.product_norm hm _ _)
          (norm_nonneg _) (Real.exp_nonneg _)) (U.product_norm hm _ _)
          (norm_nonneg _) (by positivity)) (U.product_norm hm _ _) (norm_nonneg _) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  · rwa [← U.extension_quadruple_integer M hM a h k h₁ h₂ h₃ h₄]

theorem integerProduct_fourPoint_factorization (A B : ZMod N → ℤ → ℂ)
    (h₁ h₂ h₃ h₄ : H) (a n : ℤ) :
    fourPointProduct (U.integerProduct (fun h x => A h x * B h x) h₁)
      (U.integerProduct (fun h x => A h x * B h x) h₂)
      (U.integerProduct (fun h x => A h x * B h x) h₃)
      (U.integerProduct (fun h x => A h x * B h x) h₄) a n =
      fourPointProduct (A h₁) (A h₂) (A h₃) (A h₄) a n *
      fourPointProduct (B h₁) (B h₂) (B h₃) (B h₄) a n *
      fourPointProduct (U.integerLower h₁) (U.integerLower h₂)
        (U.integerLower h₃) (U.integerLower h₄) a n := by
  simp only [fourPointProduct, integerProduct, star_mul]
  ring

theorem exists_integer_quadruple_interval_budget (M : ZMod N → ℤ → ℂ)
    (hM : ∀ h x, m h x = M h x.val) (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (a h k : ZMod N) (h₁ : h ∈ H) (h₂ : h - a ∈ H) (h₃ : k ∈ H) (h₄ : k - a ∈ H)
    {b : ℝ} (hcorr : Real.exp (-b) ≤ additiveQuadrupleCorrelation U.extension a h k) :
    ∃ (branch : Bool) (c len : ℕ), 0 < len ∧ c + len ≤ N ∧
      2 * ((len : ℤ) - 1) < N ∧
      Real.exp (-(b + 4 * p + 5)) ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
        fourPointProduct (U.integerProduct M ⟨h, h₁⟩) (U.integerProduct M ⟨h - a, h₂⟩)
          (U.integerProduct M ⟨k, h₃⟩) (U.integerProduct M ⟨k - a, h₄⟩)
          (cyclicBranchOffset a branch) n‖ ∧
      Real.exp (-(b + 4 * p + 5)) ≤ (len : ℝ) / N := by
  have hp : 0 ≤ p := (Nat.cast_nonneg (U ⟨h, h₁⟩).dim).trans (U ⟨h, h₁⟩).complexity.1.1
  have h20 : (20 : ℝ) ≤ Real.exp 5 :=
    (by norm_num : (20 : ℝ) ≤ 2 ^ 5).trans (two_pow_le_exp_of_le 5 le_rfl)
  have hfrac : Real.exp (-(b + 4 * p + 5)) ≤ Real.exp (-b) / (20 * Real.exp (4 * p)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 20 * Real.exp (4 * p))).mpr
    calc
      _ ≤ Real.exp (-(b + 4 * p + 5)) * (Real.exp 5 * Real.exp (4 * p)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h20 (Real.exp_nonneg _))
          (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hone : 1 ≤ Real.exp (4 * p) := Real.one_le_exp_iff.mpr (by positivity)
  have hfrac' : Real.exp (-(b + 4 * p + 5)) ≤ Real.exp (-b) / 20 :=
    hfrac.trans (div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num)
      (by nlinarith only [hone]))
  obtain ⟨branch, c, len, hlen, hN, hshort, hc, hvol⟩ := U.exists_integer_quadruple_interval
    M hM hm a h k h₁ h₂ h₃ h₄ (Real.exp_pos (-b)) hcorr
  exact ⟨branch, c, len, hlen, hN, hshort, hfrac'.trans hc, hfrac.trans hvol⟩

end Erdos3.NativeCrossWitnesses

end

section

namespace Erdos3

open scoped BigOperators

structure NativeIntegerQuadrupleWitness {s N : ℕ} [NeZero N] {p : ℝ}
    {f₀ f₁ : ZMod N → ℂ} {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
    (U : NativeCrossWitnesses s N p f₀ f₁ m H) (M : ZMod N → ℤ → ℂ)
    (q : ℝ) (t : ZMod N × ZMod N × ZMod N) where
  first_mem : t.2.1 ∈ H
  second_mem : t.2.1 - t.1 ∈ H
  third_mem : t.2.2 ∈ H
  fourth_mem : t.2.2 - t.1 ∈ H
  integer_relation :
    -(t.2.1.val : ℤ) + (t.2.1 - t.1).val + t.2.2.val - (t.2.2 - t.1).val = 0
  cyclic_correlation : Real.exp (-q) ≤ additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2
  branch : Bool
  start : ℕ
  length : ℕ
  length_pos : 0 < length
  endpoint_le : start + length ≤ N
  length_short : 2 * ((length : ℤ) - 1) < N
  correlation : Real.exp (-q) ≤ ‖𝔼 n ∈ Finset.Ico (start : ℤ) (start + length),
    fourPointProduct
      (U.integerProduct M ⟨t.2.1, first_mem⟩)
      (U.integerProduct M ⟨t.2.1 - t.1, second_mem⟩)
      (U.integerProduct M ⟨t.2.2, third_mem⟩)
      (U.integerProduct M ⟨t.2.2 - t.1, fourth_mem⟩)
      (cyclicBranchOffset t.1 branch) n‖
  length_ratio : Real.exp (-q) ≤ (length : ℝ) / N

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeCorrelationStructure

noncomputable def multilinearFactor {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
    (W : NativeCorrelationStructure s r N p f)
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) q)
    (k : Fin V.outputDim) (i : Fin W.family.outputDim) (h : ZMod N) (n : ℤ) : ℂ :=
  V.eval k (fun j => correlationInput (h.val : ℤ) n j.1) * W.family.eval i h n

end NativeCorrelationStructure

theorem exists_integer_multilinear_quadruples (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          CyclicShortShiftSet H ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∃ U : NativeCrossWitnesses (s - 1) N ((p + C) ^ C)
              (fun x => f x * star (weight x)) f
              (fun h x => W.multilinearFactor V k i h x.val) H,
            ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, ∃ (h₁ : t.2.1 ∈ H) (h₂ : t.2.1 - t.1 ∈ H)
                (h₃ : t.2.2 ∈ H) (h₄ : t.2.2 - t.1 ∈ H),
                -(t.2.1.val : ℤ) + (t.2.1 - t.1).val + t.2.2.val - (t.2.2 - t.1).val = 0 ∧
                Real.exp (-((p + C) ^ C)) ≤
                  additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 ∧
                ∃ (branch : Bool) (c len : ℕ), 0 < len ∧ c + len ≤ N ∧
                  2 * ((len : ℤ) - 1) < N ∧
                  Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
                    fourPointProduct
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.1, h₁⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.1 - t.1, h₂⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.2, h₃⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.2 - t.1, h₄⟩)
                      (cyclicBranchOffset t.1 branch) n‖ ∧
                  Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N := by
  obtain ⟨a, _, hmulti⟩ := exists_multilinear_quadruples s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (17 * (X + Polynomial.C a) ^ a + 20)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : 17 * q + 20 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hHC : q + 1 ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hQC : 13 * (q + 1) + 2 ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hIC : 13 * (q + 1) + 2 + 4 * q + 5 ≤ (p + C) ^ C := by linarith only [hcost]
  obtain ⟨V, hdim, hsymm, k, i, weight, H, hweight, hsub, hH, hdense, U, _⟩ := hmulti W hf
  let M := W.multilinearFactor V k i
  have hm (h x : ZMod N) : ‖M h x.val‖ ≤ 1 := by
    dsimp only [M, NativeCorrelationStructure.multilinearFactor]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hf₀ (x : ZMod N) : ‖f x * star (weight x)‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf x)).trans (hweight x)
  obtain ⟨S, hSH, hS, hshort, hSsize, Q, hQ, hQsize, hquad⟩ :=
    U.exists_short_quadruples hH hf₀ hf hm hdense
  refine ⟨V.mono hqC, hdim, hsymm, k, i, weight, S, hweight,
    fun x hx => hsub (hSH hx), hS, hshort, ?_, (U.restrict hSH).mono hqC, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hHC))
      (Nat.cast_nonneg _)).trans hSsize
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hQC))
      (by positivity)).trans hQsize
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, hrel, hc⟩ := hquad t ht
    obtain ⟨branch, c, len, hlen, hN, hlenShort, hcor, hvol⟩ :=
      U.exists_integer_quadruple_interval_budget M (fun _ _ => rfl) hm
        t.1 t.2.1 t.2.2 (hSH h₁) (hSH h₂) (hSH h₃) (hSH h₄) hc
    refine ⟨h₁, h₂, h₃, h₄, hrel, ?_, branch, c, len, hlen, hN, hlenShort, ?_, ?_⟩
    · change Real.exp (-((p + C) ^ C)) ≤
        additiveQuadrupleCorrelation (U.restrict hSH).extension t.1 t.2.1 t.2.2
      rw [U.restrict_quadruple hSH t.1 t.2.1 t.2.2 h₁ h₂ h₃ h₄]
      exact (Real.exp_le_exp.mpr (neg_le_neg hQC)).trans hc
    · change Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
        fourPointProduct (U.integerProduct M ⟨t.2.1, hSH h₁⟩)
          (U.integerProduct M ⟨t.2.1 - t.1, hSH h₂⟩)
          (U.integerProduct M ⟨t.2.2, hSH h₃⟩)
          (U.integerProduct M ⟨t.2.2 - t.1, hSH h₄⟩) (cyclicBranchOffset t.1 branch) n‖
      exact (Real.exp_le_exp.mpr (neg_le_neg hIC)).trans hcor
    · exact (Real.exp_le_exp.mpr (neg_le_neg hIC)).trans hvol

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_integer_multilinear_quadruples_with_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C) W.mixed.eval
          (fun k x => V.eval k (fun j => x j.1)) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          CyclicShortShiftSet H ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∃ U : NativeCrossWitnesses (s - 1) N ((p + C) ^ C)
              (fun x => f x * star (weight x)) f
              (fun h x => W.multilinearFactor V k i h x.val) H,
            ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, ∃ (h₁ : t.2.1 ∈ H) (h₂ : t.2.1 - t.1 ∈ H)
                (h₃ : t.2.2 ∈ H) (h₄ : t.2.2 - t.1 ∈ H),
                -(t.2.1.val : ℤ) + (t.2.1 - t.1).val + t.2.2.val - (t.2.2 - t.1).val = 0 ∧
                Real.exp (-((p + C) ^ C)) ≤
                  additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 ∧
                ∃ (branch : Bool) (c len : ℕ), 0 < len ∧ c + len ≤ N ∧
                  2 * ((len : ℤ) - 1) < N ∧
                  Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
                    fourPointProduct
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.1, h₁⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.1 - t.1, h₂⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.2, h₃⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.2 - t.1, h₄⟩)
                      (cyclicBranchOffset t.1 branch) n‖ ∧
                  Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N := by
  obtain ⟨a, _, hmulti⟩ := exists_multilinear_quadruples_with_equivalence s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (17 * (X + Polynomial.C a) ^ a + 20)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : 17 * q + 20 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hHC : q + 1 ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hQC : 13 * (q + 1) + 2 ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hIC : 13 * (q + 1) + 2 + 4 * q + 5 ≤ (p + C) ^ C := by linarith only [hcost]
  obtain ⟨V, hdim, hsymm, E, k, i, weight, H, hweight, hsub, hH, hdense, U, _⟩ := hmulti W hf
  let M := W.multilinearFactor V k i
  have hm (h x : ZMod N) : ‖M h x.val‖ ≤ 1 := by
    dsimp only [M, NativeCorrelationStructure.multilinearFactor]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hf₀ (x : ZMod N) : ‖f x * star (weight x)‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf x)).trans (hweight x)
  obtain ⟨S, hSH, hS, hshort, hSsize, Q, hQ, hQsize, hquad⟩ :=
    U.exists_short_quadruples hH hf₀ hf hm hdense
  refine ⟨V.mono hqC, hdim, hsymm, E.mono hqC, k, i, weight, S, hweight,
    fun x hx => hsub (hSH hx), hS, hshort, ?_, (U.restrict hSH).mono hqC, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hHC))
      (Nat.cast_nonneg _)).trans hSsize
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hQC))
      (by positivity)).trans hQsize
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, hrel, hc⟩ := hquad t ht
    obtain ⟨branch, c, len, hlen, hN, hlenShort, hcor, hvol⟩ :=
      U.exists_integer_quadruple_interval_budget M (fun _ _ => rfl) hm
        t.1 t.2.1 t.2.2 (hSH h₁) (hSH h₂) (hSH h₃) (hSH h₄) hc
    refine ⟨h₁, h₂, h₃, h₄, hrel, ?_, branch, c, len, hlen, hN, hlenShort, ?_, ?_⟩
    · change Real.exp (-((p + C) ^ C)) ≤
        additiveQuadrupleCorrelation (U.restrict hSH).extension t.1 t.2.1 t.2.2
      rw [U.restrict_quadruple hSH t.1 t.2.1 t.2.2 h₁ h₂ h₃ h₄]
      exact (Real.exp_le_exp.mpr (neg_le_neg hQC)).trans hc
    · change Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
        fourPointProduct (U.integerProduct M ⟨t.2.1, hSH h₁⟩)
          (U.integerProduct M ⟨t.2.1 - t.1, hSH h₂⟩)
          (U.integerProduct M ⟨t.2.2, hSH h₃⟩)
          (U.integerProduct M ⟨t.2.2 - t.1, hSH h₄⟩) (cyclicBranchOffset t.1 branch) n‖
      exact (Real.exp_le_exp.mpr (neg_le_neg hIC)).trans hcor
    · exact (Real.exp_le_exp.mpr (neg_le_neg hIC)).trans hvol

end Erdos3

end

end OAI
