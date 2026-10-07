import OAI.Combinatorics.Progressions.Estimates.UnitVerticalCyclicDifference

namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def raiseStep {σ : Type*} {w : σ → ℕ} {s t : ℕ} {p : ℝ}
    {f : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion w s p f) (hst : s ≤ t) (hp : 0 ≤ p) :
    NativeIntegerExpansion w t (raisedNiltestBudget p) f :=
  { E with
    count_bound := E.count_bound.trans (Real.exp_le_exp.mpr (le_raisedNiltestBudget p))
    model := fun i => (E.model i).raiseStep hst
    test := fun i => (E.test i).raiseStep hst
    complexity := fun i => (E.test i).raiseStep_complexity hst hp (E.complexity i)
    cost := E.cost.trans (Real.exp_le_exp.mpr (le_raisedNiltestBudget p))
    eval := fun x => by
      simpa only [RationalFilteredNilmanifold.Niltest.raiseStep_eval] using E.eval x }

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_smoothedSecondDifference_expansion_degree (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      ∀ (N : ℕ) (δ : ℝ≥0), 0 < δ → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ (u v : (Fin 2 → ℤ) → ℂ) (k : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s p (integerSecondDifference u v k)) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s p (integerSecondDifference u v (k - N))) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s ((p + e + C) ^ C)
        (smoothedSecondDifference N δ u v k)) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 6) ^ 2 + 7
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((R + Polynomial.C A) ^ A + R + 2)
  refine ⟨C, hC, ?_⟩
  intro p e hp he N δ hδ hinv u v k ⟨E0⟩ ⟨E1⟩
  let r := p + e + (p + e + 6) ^ 2 + 7
  let t := (r + A) ^ A + r
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + e + 6)]
  have her : raisedNiltestBudget (e + 4) ≤ r := by
    have hsq : (e + 6) ^ 2 ≤ (p + e + 6) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    dsimp [raisedNiltestBudget, r]
    nlinarith
  have hrt : r ≤ t := le_add_of_nonneg_left (by positivity)
  have hmt : (r + A) ^ A ≤ t := le_add_of_nonneg_right hr
  have htC : t + 2 ≤ (p + e + C) ^ C := by
    simpa [X, R, r, t, Polynomial.eval₂_pow] using hbudget (p + e) (by linarith)
  obtain ⟨EC⟩ := exists_fixed_shift_smoothCyclicCarry_expansion N δ hδ he hinv k
  obtain ⟨EM0⟩ := hmul hr ((EC.raiseStep hs (by linarith)).mono her) (E0.mono hpr)
  obtain ⟨EM1⟩ := hmul hr ((EC.raiseStep hs (by linarith)).mono her) (E1.mono hpr)
  let w (x : Fin 2 → ℤ) := (smoothCyclicCarry N δ ![k, x 1] : ℂ)
  let fs : Fin 3 → (Fin 2 → ℤ) → ℂ := ![integerSecondDifference u v k,
    (fun x => w x * integerSecondDifference u v (k - N) x),
    (fun x => w x * integerSecondDifference u v k x)]
  have Efs (j : Fin 3) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s t (fs j)) := by
    fin_cases j
    · exact ⟨E0.mono (hpr.trans hrt)⟩
    · exact ⟨EM1.mono hmt⟩
    · exact ⟨EM0.mono hmt⟩
  let cs : Fin 3 → ℂ := ![1, 1, -1]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have E := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (Efs j)) cs
    (by norm_num : (0 : ℝ) ≤ 2) (by simpa using hthree)
    (by convert hthree using 1; norm_num [cs, Fin.sum_univ_succ])).mono htC
  have heq : (fun x => ∑ j, cs j * fs j x) = smoothedSecondDifference N δ u v k := by
    funext x
    simp [cs, fs, w, Fin.sum_univ_succ, smoothedSecondDifference]
    ring
  exact ⟨heq ▸ E⟩

theorem exists_cyclicSecondDifference_approximation_degree (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      ∀ {N : ℕ} [NeZero N], Real.exp (e + 16) ≤ (N : ℝ) →
      ∀ (u v : (Fin 2 → ℤ) → ℂ), (∀ x, ‖u x‖ ≤ 1) → (∀ x, ‖v x‖ ≤ 1) →
      (∀ k : ℤ, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s p
        (integerSecondDifference u v k))) →
      ∀ k : ZMod N, ∃ K : (Fin 2 → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s ((p + e + C) ^ C) K) ∧
        ∀ h : ℤ, (𝔼 n : ZMod N,
          ‖cyclicSecondDifference u v k h n - K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e) := by
  obtain ⟨A, _, hexpand⟩ := exists_smoothedSecondDifference_expansion_degree s hs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + 16 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p e hp he N _ hN u v hu hv hmodel k
  let δ : ℝ≥0 := ⟨Real.exp (-(e + 16)), (Real.exp_pos _).le⟩
  have hδ : 0 < δ := Real.exp_pos _
  have hinv : (δ : ℝ)⁻¹ ≤ Real.exp (e + 16) := by
    change (Real.exp (-(e + 16)))⁻¹ ≤ Real.exp (e + 16)
    rw [← Real.exp_neg, neg_neg]
  have hbudget' : (p + (e + 16) + A) ^ A ≤ (p + e + C) ^ C := by
    have hb := hbudget (p + e) (by linarith)
    simpa [X, Polynomial.eval₂_pow, add_assoc] using hb
  obtain ⟨E⟩ := hexpand hp (by linarith : 0 ≤ e + 16) N δ hδ hinv u v k.val
    (hmodel k.val) (hmodel ((k.val : ℤ) - N))
  refine ⟨smoothedSecondDifference N δ u v k.val, ⟨E.mono hbudget'⟩, ?_⟩
  intro h
  apply (smoothedSecondDifference_mean_error δ hδ u v hu hv k h).trans
  have hNinv : 1 / (N : ℝ) ≤ Real.exp (-(e + 16)) := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos (e + 16)) hN
    simpa only [one_div, ← Real.exp_neg] using hh
  have htwo : 2 / (N : ℝ) ≤ 2 * Real.exp (-(e + 16)) := by
    calc
      _ = 2 * (1 / (N : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hNinv (by norm_num)
  calc
    12 * (δ : ℝ) + 2 / N ≤ 14 * Real.exp (-(e + 16)) := by
      change 12 * Real.exp (-(e + 16)) + 2 / (N : ℝ) ≤ 14 * Real.exp (-(e + 16))
      linarith only [htwo]
    _ ≤ Real.exp 16 * Real.exp (-(e + 16)) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (16 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (-e) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
