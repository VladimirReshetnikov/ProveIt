import OAI.Combinatorics.Progressions.Estimates.DiagonalRowTransfer

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

namespace NativeMultidegreeNilcharacter

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_quadratic_diagonal_niltest {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (i : Fin W.outputDim) :
    ∃ T : W.model.Niltest (fun _ : Unit => 1), T.normBound = 1 ∧ T.ComplexityLE (p + 4) ∧
      ∀ n : ℤ, T.eval (fun _ => n) = W.eval i (fun _ => n) := by
  obtain ⟨T, hT, hcomplexity, heval⟩ := W.exists_linear_niltest i
    (fun _ => { toFun := fun x : Unit → ℤ => x (), map_zero' := rfl, map_add' := fun _ _ => rfl })
  exact ⟨T, hT, hcomplexity, fun n => heval (fun _ => n)⟩

theorem cyclicDiagonalDerivative_same_coordinate {p : ℝ} {N : ℕ} [NeZero N]
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (i : Fin W.outputDim)
    (h n : ZMod N) :
    W.cyclicDiagonalDerivative (i, i) ![h, n] =
      multiplicativeDerivative (fun x : ZMod N => W.eval i (fun _ => (x.val : ℤ))) h n := by
  simp [cyclicDiagonalDerivative, multiplicativeDerivative, add_comm]

end NativeMultidegreeNilcharacter

theorem exists_quadratic_cyclic_integration :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ K : (Fin M.outputDim × Fin M.outputDim) →
                  (Fin M.outputDim × Fin M.outputDim × Fin M.outputDim) → (Fin 2 → ℤ) → ℂ,
                (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
                  ((p + e + C) ^ C) (K a b))) ∧
                (∀ a b, (𝔼 x : Fin 2 → ZMod N,
                  ‖M.cyclicDiagonalDerivative a x *
                      star (M.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
                    K a b (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hintegrate⟩ := exists_quadratic_approximate_integration
  obtain ⟨B, _, hcorrect⟩ := NativeMultidegreeNilcharacter.exists_cyclicDiagonalCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let F := (X + U + 20 + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + F + X + 20 + (U + F + X + 20 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let u := (p + A) ^ A
  let v := p + e
  let umax := (v + A) ^ A
  let t := (p + (e + u + 20) + A) ^ A
  let tmax := (v + umax + 20 + A) ^ A
  let δ : ℝ≥0 := ⟨Real.exp (-(e + 20)), (Real.exp_pos _).le⟩
  have hδval : (δ : ℝ) = Real.exp (-(e + 20)) := rfl
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have humax : 0 ≤ umax := by dsimp [umax]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htmax : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hinv : (δ : ℝ)⁻¹ ≤ Real.exp (e + 20) := by
    rw [hδval, ← Real.exp_neg, neg_neg]
  have hsum : umax + tmax + v + 20 + (umax + tmax + v + 20 + B) ^ B ≤ (p + e + C) ^ C := by
    simpa [X, U, F, umax, tmax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hlast : 0 ≤ (umax + tmax + v + 20 + B) ^ B := by positivity
  have htC : tmax ≤ (p + e + C) ^ C := by linarith
  have hscale : e + 20 ≤ (p + e + C) ^ C := by dsimp [v] at hsum; linarith
  have hCC : (umax + tmax + v + 20 + B) ^ B ≤ (p + e + C) ^ C := by linarith
  have hqu : u ≤ (p + C) ^ C := by
    have hh : u + (p + u + 20 + A) ^ A + p + 20 +
        (u + (p + u + 20 + A) ^ A + p + 20 + B) ^ B ≤ (p + C) ^ C := by
      simpa [X, U, F, u, Polynomial.eval₂_pow] using hbudget p hp
    have h₁ : 0 ≤ (p + u + 20 + A) ^ A := by positivity
    have h₂ : 0 ≤ (u + (p + u + 20 + A) ^ A + p + 20 + B) ^ B := by positivity
    linarith
  have hu_le : u ≤ umax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have ht_le : t ≤ tmax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  obtain ⟨q, hq, hqb, H, hH, hdense, M, i, hderiv, G, hG, _hcap, herr⟩ :=
    hintegrate hp (by linarith : 0 ≤ e + u + 20)
      ((Real.exp_le_exp.mpr (ht_le.trans htC)).trans hN) f hf hGowers
  have hcost : (q + t + (e + 20) + B) ^ B ≤ (p + e + C) ^ C := by
    apply le_trans _ hCC
    apply pow_le_pow_left₀ (by positivity)
    have hqmax := hqb.trans hu_le
    dsimp [v]
    linarith
  have hrecip : 1 / (N : ℝ) ≤ δ := by
    rw [hδval]
    have hh := one_div_le_one_div_of_le (Real.exp_pos (e + 20))
      ((Real.exp_le_exp.mpr hscale).trans hN)
    simpa only [one_div, ← Real.exp_neg] using hh
  have hmodel : (M.outputDim : ℝ) + 1 ≤ 2 * Real.exp u := by
    have hd := M.output_bound.trans (Real.exp_le_exp.mpr hqb)
    have h1 := Real.one_le_exp hu
    linarith
  have hfirst : ((M.outputDim : ℝ) + 1) * Real.exp (-(e + u + 20)) ≤ 2 * (δ : ℝ) := by
    calc
      _ ≤ 2 * Real.exp u * Real.exp (-(e + u + 20)) :=
        mul_le_mul_of_nonneg_right hmodel (Real.exp_nonneg _)
      _ = 2 * (δ : ℝ) := by
        rw [mul_assoc, ← Real.exp_add]
        rw [hδval]
        congr 2
        ring
  have hfinal : (16 : ℝ) * δ ≤ Real.exp (-e) := by
    have h16 : (16 : ℝ) ≤ Real.exp 20 := by linarith [Real.add_one_le_exp (20 : ℝ)]
    calc
      _ ≤ Real.exp 20 * δ := mul_le_mul_of_nonneg_right h16 δ.coe_nonneg
      _ = _ := by rw [hδval, ← Real.exp_add]; congr 1; ring
  have htwo : 2 / (N : ℝ) ≤ 2 * (δ : ℝ) := by
    simpa only [one_div, div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨q, hq, hqb.trans hqu, H, hH, hdense, M, i, hderiv,
    M.cyclicDiagonalCorrection N δ G, ?_, ?_⟩
  · intro a b
    exact ⟨(Classical.choice (hcorrect M N δ hδ ht (by linarith) hinv G hG a b)).mono hcost⟩
  · intro a b
    have hh := M.cyclicDiagonalCorrection_mean_error δ hδ G herr a b
    apply hh.trans
    calc
      _ ≤ 2 * (δ : ℝ) + 12 * (δ : ℝ) + 2 * (δ : ℝ) :=
        add_le_add (add_le_add hfirst le_rfl) htwo
      _ = 16 * (δ : ℝ) := by ring
      _ ≤ _ := hfinal

end Erdos3

end

end OAI
