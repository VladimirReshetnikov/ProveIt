import OAI.Combinatorics.Progressions.Estimates.MixedRootLosses

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedWrappedDiagonalCorrection (N : ℕ)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (MixedNonconstantCorner s → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : MixedNonconstantCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ k, W.mixedDiagonalWrapCoefficient N a.2 k x * F (a.1, k) b x

noncomputable def mixedCyclicDiagonalCorrection (N : ℕ) (δ : ℝ≥0)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (MixedNonconstantCorner s → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : MixedNonconstantCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  (1 - (smoothCyclicCarry N δ x : ℂ)) * F a b x +
    (smoothCyclicCarry N δ x : ℂ) * W.mixedWrappedDiagonalCorrection N F a b x

theorem mixedWrappedDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (MixedNonconstantCorner s → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        F a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : MixedNonconstantCorner s → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedWrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        W.mixedWrappedDiagonalCorrection N F a b (fun z => ((x z).val : ℤ))‖) ≤ W.outputDim * ε := by
  have hpoint (x : Fin 2 → ℤ) :
      ‖W.mixedWrappedDiagonalDerivative N a x * star (W.mixedCanonicalTensor b x) -
        W.mixedWrappedDiagonalCorrection N F a b x‖ ≤
      ∑ k, ‖W.mixedDiagonalDerivative (a.1, k) x * star (W.mixedCanonicalTensor b x) -
        F (a.1, k) b x‖ := by
    have heq : W.mixedWrappedDiagonalDerivative N a x * star (W.mixedCanonicalTensor b x) -
        W.mixedWrappedDiagonalCorrection N F a b x =
        ∑ k, W.mixedDiagonalWrapCoefficient N a.2 k x *
          (W.mixedDiagonalDerivative (a.1, k) x * star (W.mixedCanonicalTensor b x) -
            F (a.1, k) b x) := by
      rw [W.mixedWrappedDiagonalDerivative_resolution, Finset.sum_mul]
      simp only [mixedWrappedDiagonalCorrection, mul_sub, Finset.sum_sub_distrib, mul_assoc]
    rw [heq]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k _
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (W.mixedDiagonalWrapCoefficient_norm N a.2 k x)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N,
        ∑ k, ‖W.mixedDiagonalDerivative (a.1, k) (fun z => ((x z).val : ℤ)) *
            star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
          F (a.1, k) b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_le_expect (fun x _ => hpoint _)
    _ = ∑ k, 𝔼 x : Fin 2 → ZMod N,
        ‖W.mixedDiagonalDerivative (a.1, k) (fun z => ((x z).val : ℤ)) *
            star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
          F (a.1, k) b (fun z => ((x z).val : ℤ))‖ := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _k : Fin W.outputDim, ε := Finset.sum_le_sum (fun k _ => herr (a.1, k) b)
    _ = _ := by simp

theorem mixedCyclicDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (δ : ℝ≥0) (hδ : 0 < δ)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (MixedNonconstantCorner s → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        F a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : MixedNonconstantCorner s → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedCyclicDiagonalDerivative a x * star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        W.mixedCyclicDiagonalCorrection N δ F a b (fun z => ((x z).val : ℤ))‖) ≤
      (W.outputDim + 1) * ε + 12 * (δ : ℝ) + 2 / N := by
  have hpoint (x : Fin 2 → ZMod N) := norm_smoothed_branch_error
    (cyclicCarry (x 0) (x 1)) (smoothCyclicCarry N δ (fun z => ((x z).val : ℤ)))
    (circleCarryCutoff_range δ _)
    (W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
      star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))))
    (W.mixedWrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) *
      star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))))
    (F a b (fun z => ((x z).val : ℤ)))
    (W.mixedWrappedDiagonalCorrection N F a b (fun z => ((x z).val : ℤ)))
    (by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.mixedDiagonalDerivative_norm a _)).trans (W.mixedCanonicalTensor_norm b _))
    (by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.mixedWrappedDiagonalDerivative_norm N a _)).trans (W.mixedCanonicalTensor_norm b _))
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun x _ => hpoint x)
  simp only [Complex.ofReal_sub, Complex.ofReal_one, ← mul_assoc, ← add_mul,
    ← W.mixedCyclicDiagonalDerivative_branches] at hm
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at hm
  have hi := herr a b
  have hw := W.mixedWrappedDiagonalCorrection_mean_error F herr a b
  have hc := smoothCyclicCarry_mean_error (N := N) δ hδ
  dsimp only [mixedCyclicDiagonalCorrection]
  exact hm.trans ((add_le_add (add_le_add hi hw)
    (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))).trans_eq (by ring))

theorem exists_mixedCyclicDiagonalCorrection_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p) (N : ℕ)
      (δ : ℝ≥0), 0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ F : (Fin W.outputDim × Fin W.outputDim) →
          (MixedNonconstantCorner s → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ,
        (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (F a b))) →
        ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2)
          ((p + q + e + C) ^ C) (W.mixedCyclicDiagonalCorrection N δ F a b)) := by
  obtain ⟨A, _, hwrap⟩ := exists_mixedDiagonalWrapCoefficient_expansion s
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + Polynomial.C A) ^ A + X + (X + 6) ^ 2 + 13
  let T := (R + Polynomial.C B) ^ B + X + R + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B + T + 2)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv F hF a b
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q + e
  let r := (v + A) ^ A + v + (v + 6) ^ 2 + 13
  let t := (r + B) ^ B + v + r + 2
  let d := (t + B) ^ B + t
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have har : (p + A) ^ A ≤ r := by
    calc
      _ ≤ (v + A) ^ A := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
      _ ≤ r := by dsimp [r]; nlinarith [sq_nonneg (v + 6)]
  have hqr : q ≤ r := by
    have : 0 ≤ (v + A) ^ A := by positivity
    have hs : 0 ≤ (v + 6) ^ 2 := sq_nonneg _
    dsimp [r, v] at *
    linarith
  have her : raisedNiltestBudget (e + 4) ≤ r := by
    have hpow : (e + 6) ^ 2 ≤ (v + 6) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) 2
    have hA : 0 ≤ (v + A) ^ A := by positivity
    have hev : e ≤ v := by dsimp [v]; linarith
    dsimp [raisedNiltestBudget, r]
    nlinarith
  have hrt : r ≤ t := by
    have : 0 ≤ (r + B) ^ B := by positivity
    dsimp [t]
    linarith
  have hwt : (r + B) ^ B + p ≤ t := by dsimp [t, v]; linarith
  have htd : t ≤ d := le_add_of_nonneg_left (by positivity)
  have hpd : (t + B) ^ B ≤ d := le_add_of_nonneg_right ht
  have hcost : d + 2 ≤ (p + q + e + C) ^ C := by
    simpa [X, R, T, r, t, d, v, Polynomial.eval₂_pow] using hbudget v hv
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hcoeff : (∑ _k : Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hdim
  have hterms (k : Fin W.outputDim) := hmul hr
    ((Classical.choice (hwrap W N a.2 k)).mono har) ((Classical.choice (hF (a.1, k) b)).mono hqr)
  have EW : NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) t
      (W.mixedWrappedDiagonalCorrection N F a b) := by
    have E := (NativeIntegerExpansion.weightedSum (fun k => Classical.choice (hterms k))
      (fun _ => (1 : ℂ)) hp hdim hcoeff).mono hwt
    change NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) t
      (fun x => ∑ k, W.mixedDiagonalWrapCoefficient N a.2 k x * F (a.1, k) b x)
    simpa only [one_mul] using E
  let w := fun x => (smoothCyclicCarry N δ x : ℂ)
  have EC := ((Classical.choice (exists_smoothCyclicCarry_expansion N δ hδ he hinv)).raiseStep
    (by omega : 1 ≤ s + 2) (by positivity : 0 ≤ e + 4)).mono (her.trans hrt)
  have E₀ := (Classical.choice (hF a b)).mono (hqr.trans (hrt.trans htd))
  have E₁ := (Classical.choice (hmul ht EC EW)).mono hpd
  have E₂ := (Classical.choice (hmul ht EC ((Classical.choice (hF a b)).mono (hqr.trans hrt)))).mono hpd
  let fs : Fin 3 → (Fin 2 → ℤ) → ℂ := ![F a b,
    (fun x => w x * W.mixedWrappedDiagonalCorrection N F a b x), (fun x => w x * F a b x)]
  have Efs (j : Fin 3) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) d (fs j)) := by
    fin_cases j
    · exact ⟨E₀⟩
    · exact ⟨E₁⟩
    · exact ⟨E₂⟩
  let cs : Fin 3 → ℂ := ![1, 1, -1]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have E := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (Efs j)) cs
    (by norm_num : (0 : ℝ) ≤ 2) (by simpa using hthree)
    (by convert hthree using 1; norm_num [cs, Fin.sum_univ_succ])).mono hcost
  have heq : (fun x => ∑ j, cs j * fs j x) = W.mixedCyclicDiagonalCorrection N δ F a b := by
    funext x
    simp [cs, fs, Fin.sum_univ_succ, w, mixedCyclicDiagonalCorrection]
    ring
  exact ⟨heq ▸ E⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedRootCyclicCorrection (N : ℕ) (δ : ℝ≥0)
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  W.mixedIntegrationRoot.mixedCyclicDiagonalCorrection N δ (W.mixedRootCornerCorrection G)

theorem mixedRootCyclicCorrection_mean_error {N : ℕ} [NeZero N] (δ : ℝ≥0) (hδ : 0 < δ)
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (b : MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative a x *
          star (W.mixedIntegrationRoot.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
        W.mixedRootCyclicCorrection N δ G a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.mixedIntegrationRoot.outputDim + 1) *
        ((mixedRootCornerCoefficient s : ℝ) * (W.outputDim : ℝ) ^ mixedRootCornerExponent s * ε) +
          12 * (δ : ℝ) + 2 / N :=
  W.mixedIntegrationRoot.mixedCyclicDiagonalCorrection_mean_error δ hδ (W.mixedRootCornerCorrection G)
    (W.mixedRootCornerCorrection_mean_error_power G hε hG herr) a b

theorem exists_mixedRootCyclicCorrection_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p) (N : ℕ) (δ : ℝ≥0),
      0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (s + 2))) k x,
        W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (s + 2)) a).symm j)) = W.eval k x) →
      ∀ G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π a b))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + e + C) ^ C)
        (W.mixedRootCyclicCorrection N δ G a b)) := by
  obtain ⟨A, _, hroot⟩ := exists_mixedRootCornerCorrection_expansion s
  obtain ⟨B, _, hcyclic⟩ := exists_mixedCyclicDiagonalCorrection_expansion s
  let n := mixedRootTensorExponent s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.C (n + 1) * (X + 1) + (X + Polynomial.C A) ^ A + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv hsymm G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q + e
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hA : (p + q + A) ^ A ≤ (v + A) ^ A :=
    pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
  have hbound : (tensorPowerBudget n p + (p + q + A) ^ A + e + B) ^ B ≤
      (p + q + e + C) ^ C := by
    have hh : ((n + 1 : ℝ) * (v + 1) + (v + A) ^ A + v + B) ^ B ≤ (v + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget v hv
    apply le_trans _ hh
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    have hb : tensorPowerBudget n p ≤ (n + 1 : ℝ) * (v + 1) := by
      unfold tensorPowerBudget
      exact mul_le_mul_of_nonneg_left (by dsimp [v]; linarith) (by positivity)
    dsimp only [v] at *
    linarith
  obtain ⟨E⟩ := hcyclic W.mixedIntegrationRoot N δ hδ (by positivity : 0 ≤ (p + q + A) ^ A) he hinv
    (W.mixedRootCornerCorrection G) (hroot W hq hsymm G hG) a b
  exact ⟨E.mono hbound⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
