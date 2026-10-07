import OAI.Combinatorics.Progressions.Estimates.UnitVerticalMeanRowCorrelation
import OAI.Combinatorics.Progressions.Geometry.MixedCoordinateTransfer
import OAI.Combinatorics.Progressions.Lattices.MultidegreeIntegerTranslation

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

noncomputable def rationalDilation (r : ℚ) : NativeMultidegreeNilcharacter bound p :=
  { W with orbit := W.multi.filtration.realification.rationalDilationOrbit r W.orbit }

theorem rationalDilation_eval_rescaled (r : ℚ) (q : ℤ) (hr : r * (q : ℚ) = 1)
    (a : Fin W.outputDim) (x : σ → ℤ) :
    (W.rationalDilation r).eval a (fun i => q * x i) = W.eval a x := by
  unfold eval rationalDilation
  rw [W.multi.filtration.realification.rationalDilationOrbit_rescaled r q hr]

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_quadratic_integer_translation_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (a b : Fin 2 → ℤ),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        (fun i x => W.eval i (x + a)) (fun i x => W.eval i (x + b)) := by
  obtain ⟨C, hC, htranslate⟩ :=
    UnitVerticalObservable.exists_integer_translation_equivalence_budget 1
  refine ⟨C, hC, ?_⟩
  intro p W a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have htop : W.multi.realSubgroup (mixedCorrelationDegree 1) =
      W.model.filtration.realification.subgroup 2 := by
    have hsum : (∑ i, mixedCorrelationDegree 1 i) = 2 := by decide
    simpa only [hsum] using W.multi.realSubgroup_top
  let V : W.model.UnitVerticalObservable (W.model.filtration.realification.subgroup 2)
      (Fin W.outputDim) p :=
    { W.vertical with
      vertical := fun i z hz x => W.vertical.vertical i z (htop.symm ▸ hz) x
      integral := fun z hz hL => W.vertical.integral z (htop.symm ▸ hz) hL }
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have E := htranslate W.model V (W.multi.orbitToOrdinary W.orbit) hp W.complexity.1 hdim a b
  refine ⟨E.left_dimension, E.right_dimension, ?_⟩
  intro i j
  obtain ⟨F⟩ := E.expansion i j
  have heq (k : Fin W.outputDim) (x : Fin 2 → ℤ) :
      V.observable k (QuotientGroup.mk (W.model.filtration.realification.polynomialOrbitEval
        (fun _ : Fin 2 => 1) x (W.multi.orbitToOrdinary W.orbit))) = W.eval k x := by
    rw [W.multi.orbitToOrdinary_eval]
    rfl
  have hf : (fun x => V.observable i (QuotientGroup.mk
      (W.model.filtration.realification.polynomialOrbitEval (fun _ : Fin 2 => 1)
        (x + a) (W.multi.orbitToOrdinary W.orbit))) *
      star (V.observable j (QuotientGroup.mk
        (W.model.filtration.realification.polynomialOrbitEval (fun _ : Fin 2 => 1)
          (x + b) (W.multi.orbitToOrdinary W.orbit))))) =
      (fun x => W.eval i (x + a) * star (W.eval j (x + b))) := by
    funext x
    rw [heq, heq]
  exact ⟨hf ▸ F⟩

theorem half_dilation_integer_representative {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (x : Fin 2 → ℤ) (j : Fin W.outputDim) :
    (W.rationalDilation (1 / 2)).eval j (fun i => x i - ((x i : ZMod 2).val : ℤ)) =
      W.eval j (fun i => x i / 2) := by
  have hx : (fun i => x i - ((x i : ZMod 2).val : ℤ)) = (fun i => 2 * (x i / 2)) := by
    funext i
    rw [ZMod.val_intCast]
    omega
  rw [hx]
  exact W.rationalDilation_eval_rescaled (1 / 2) 2 (by norm_num) j _

theorem exists_half_dilation_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        (W.rationalDilation (1 / 2)).eval (fun j x => W.eval j (fun i => x i / 2)) := by
  obtain ⟨A, _, hshift⟩ := exists_quadratic_integer_translation_equivalence
  obtain ⟨B, _, hparity⟩ := exists_pairParityIndicator_expansion
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + Polynomial.C B + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C D) ^ D + T + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let V := W.rationalDilation (1 / 2)
  let t : ℝ := (p + A) ^ A + B + p + 2
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hb : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hat : (p + A) ^ A ≤ t := by dsimp [t]; linarith
  have hbt : (B : ℝ) ≤ t := by dsimp [t]; linarith
  have hbound : (t + D) ^ D + t + 2 ≤ (p + C) ^ C := by
    simpa [T, t, X, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (t + D) ^ D := by positivity
  have hpc : p ≤ (p + C) ^ C := by linarith
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpc)
  refine ⟨hdim, hdim, ?_⟩
  intro i j
  let F (r : Fin 2 → ZMod 2) (x : Fin 2 → ℤ) :=
    V.eval i x * star (V.eval j (fun k => x k - ((r k).val : ℤ)))
  have hF (r : Fin 2 → ZMod 2) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 t (F r)) := by
    obtain ⟨E⟩ := (hshift V 0 (fun k => -((r k).val : ℤ))).expansion i j
    have heq : (fun x => V.eval i (x + 0) * star (V.eval j (x + fun k => -((r k).val : ℤ)))) = F r := by
      funext x
      simp only [F, add_zero, sub_eq_add_neg]
      rfl
    rw [heq] at E
    exact ⟨E.mono hat⟩
  have hterm (r : Fin 2 → ZMod 2) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
      ((t + D) ^ D) (fun x => pairParityIndicator r x * F r x)) :=
    hmul ht ((Classical.choice (hparity r)).mono hbt) (Classical.choice (hF r))
  have hc : (Fintype.card (Fin 2 → ZMod 2) : ℝ) ≤ Real.exp 2 := by
    norm_num only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have hh := Real.add_one_le_exp (1 : ℝ)
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hcost : (∑ _ : Fin 2 → ZMod 2, ‖(1 : ℂ)‖) ≤ Real.exp 2 := by simpa using hc
  let S := NativeIntegerExpansion.weightedSum (fun r => Classical.choice (hterm r)) (fun _ => 1)
    (by norm_num : (0 : ℝ) ≤ 2) hc hcost
  have heq : (fun x => ∑ r : Fin 2 → ZMod 2, (1 : ℂ) * (pairParityIndicator r x * F r x)) =
      (fun x => V.eval i x * star (W.eval j (fun k => x k / 2))) := by
    funext x
    let r : Fin 2 → ZMod 2 := fun k => (x k : ZMod 2)
    rw [Finset.sum_eq_single r]
    · simp only [pairParityIndicator, r, ite_true, one_mul, F]
      rw [show V.eval j (fun k => x k - ((x k : ZMod 2).val : ℤ)) =
        W.eval j (fun k => x k / 2) from W.half_dilation_integer_representative x j]
    · intro a _ ha
      have hne : (fun k => (x k : ZMod 2)) ≠ a := fun h => ha h.symm
      simp only [pairParityIndicator, hne, ite_false, zero_mul, mul_zero]
    · simp
  rw [heq] at S
  exact ⟨S.mono (by linarith)⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_unit_pair_replacement_error {I J : Type*} [Fintype I] [Fintype J]
    (u : I → ℂ) (v : J → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) (hv : ∑ j, ‖v j‖ ^ 2 = 1)
    (huc : ∀ i, ‖u i‖ ≤ 1) (hvc : ∀ j, ‖v j‖ ≤ 1)
    (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (G : I → J → ℂ) :
    ‖star a * b - ∑ ij : I × J,
      (star (a * star (u ij.1)) * (b * star (v ij.2))) * G ij.1 ij.2‖ ≤
      ∑ ij : I × J, ‖star (u ij.1) * v ij.2 - G ij.1 ij.2‖ := by
  have hleft := congrArg star (complex_unit_vector_resolution u hu a)
  simp only [star_sum, star_mul] at hleft
  have hright := complex_unit_vector_resolution v hv b
  have hrepr : star a * b = ∑ ij : I × J,
      (star (a * star (u ij.1)) * (b * star (v ij.2))) * (star (u ij.1) * v ij.2) := by
    conv_lhs => rw [hleft, hright]
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [star_mul]
    ring
  rw [hrepr, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ij _
  rw [← mul_sub, norm_mul]
  have hcap : ‖star (a * star (u ij.1)) * (b * star (v ij.2))‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans ?_
    · rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (huc _)
    · rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans (hvc _)
  exact mul_le_of_le_one_left (norm_nonneg _) hcap

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def halfDilationExchangeCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ ij : Fin W.outputDim × Fin W.outputDim,
    (star ((W.rationalDilation (1 / 2)).eval a x * star (W.eval ij.1 (fun k => x k / 2))) *
      ((W.rationalDilation (1 / 2)).eval b (fun k => x k.rev) *
        star (W.eval ij.2 (fun k => x k.rev / 2)))) * G ij.1 ij.2 (fun k => x k / 2)

theorem halfDilationExchangeCorrection_pointwise_error
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖(W.rationalDilation (1 / 2)).antisymmetricKernel a b (x 0) (x 1) -
        W.halfDilationExchangeCorrection G a b x‖ ≤
      ∑ ij : Fin W.outputDim × Fin W.outputDim,
        ‖W.antisymmetricKernel ij.1 ij.2 (x 0 / 2) (x 1 / 2) -
          G ij.1 ij.2 (fun k => x k / 2)‖ := by
  have hinput (z : Fin 2 → ℤ) : correlationInput (z 0) (z 1) = z := by
    funext k
    fin_cases k <;> rfl
  have hswap (z : Fin 2 → ℤ) : correlationInput (z 1) (z 0) = (fun k => z k.rev) := by
    funext k
    fin_cases k <;> rfl
  simp only [antisymmetricKernel, hinput x, hswap x,
    hinput (fun k => x k / 2), hswap (fun k => x k / 2), halfDilationExchangeCorrection]
  exact norm_unit_pair_replacement_error
    (fun i => W.eval i (fun k => x k / 2)) (fun j => W.eval j (fun k => x k.rev / 2))
    (W.unit_eval _) (W.unit_eval _) (fun i => W.norm_eval i _) (fun j => W.norm_eval j _)
    ((W.rationalDilation (1 / 2)).eval a x) ((W.rationalDilation (1 / 2)).eval b (fun k => x k.rev))
    ((W.rationalDilation (1 / 2)).norm_eval a _) ((W.rationalDilation (1 / 2)).norm_eval b _)
    (fun i j => G i j (fun k => x k / 2))

theorem halfDilationExchangeCorrection_mean_error {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel i j ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖(W.rationalDilation (1 / 2)).antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
        W.halfDilationExchangeCorrection G a b (fun k => ((x k).val : ℤ))‖) ≤
      4 * (W.outputDim : ℝ) ^ 2 * ε := by
  have hmean := Finset.expect_le_expect (s := Finset.univ)
    (fun (x : Fin 2 → ZMod N) _ => W.halfDilationExchangeCorrection_pointwise_error G a b (fun k => ((x k).val : ℤ)))
  rw [Finset.expect_sum_comm] at hmean
  have he (ij : Fin W.outputDim × Fin W.outputDim) :
      (𝔼 x : Fin 2 → ZMod N,
        ‖W.antisymmetricKernel ij.1 ij.2 (((x 0).val : ℤ) / 2) (((x 1).val : ℤ) / 2) -
          G ij.1 ij.2 (fun k => ((x k).val : ℤ) / 2)‖) ≤ 4 * ε := by
    have h := expect_pair_cyclicHalf_le (fun x : Fin 2 → ZMod N =>
      ‖W.antisymmetricKernel ij.1 ij.2 ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G ij.1 ij.2 (fun k => ((x k).val : ℤ))‖) (fun _ => norm_nonneg _)
    simp only [cyclicHalf_val, Int.natCast_ediv, Nat.cast_ofNat] at h
    exact h.trans (mul_le_mul_of_nonneg_left (herr ij.1 ij.2) (by norm_num))
  apply hmean.trans
  calc
    _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, 4 * ε :=
      Finset.sum_le_sum (fun ij _ => he ij)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      ring

theorem halfDilationExchangeCorrection_norm {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {B : ℝ}
    (hG : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (a b : Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.halfDilationExchangeCorrection G a b (fun k => ((x k).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 2 * B := by
  unfold halfDilationExchangeCorrection
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, B := by
      apply Finset.sum_le_sum
      intro ij _
      rw [norm_mul]
      have hc : ‖star ((W.rationalDilation (1 / 2)).eval a (fun k => ((x k).val : ℤ)) *
          star (W.eval ij.1 (fun k => ((x k).val : ℤ) / 2))) *
          ((W.rationalDilation (1 / 2)).eval b (fun k => ((x k.rev).val : ℤ)) *
          star (W.eval ij.2 (fun k => ((x k.rev).val : ℤ) / 2)))‖ ≤ 1 := by
        rw [norm_mul, norm_star]
        refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans ?_
        · rw [norm_mul, norm_star]
          exact (mul_le_of_le_one_left (norm_nonneg _)
            ((W.rationalDilation (1 / 2)).norm_eval a _)).trans (W.norm_eval _ _)
        · rw [norm_mul, norm_star]
          exact (mul_le_of_le_one_left (norm_nonneg _)
            ((W.rationalDilation (1 / 2)).norm_eval b _)).trans (W.norm_eval _ _)
      apply (mul_le_of_le_one_left (norm_nonneg _) hc).trans
      have h := hG ij.1 ij.2 (fun k => cyclicHalf (x k))
      simpa only [cyclicHalf_val, Int.natCast_ediv, Nat.cast_ofNat] using h
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, pow_two]

theorem exists_halfDilationExchangeCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p), 0 ≤ q →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
        (W.halfDilationExchangeCorrection G a b)) := by
  obtain ⟨A, _, hcompare⟩ := exists_half_dilation_equivalence
  obtain ⟨B, _, hhalf⟩ := NativeIntegerExpansion.exists_halving_expansion
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B + X + 2
  let U := (T + Polynomial.C D) ^ D + T
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((U + Polynomial.C D) ^ D + 2 * T + 2)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG a b
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let t := (v + A) ^ A + (v + B) ^ B + v + 2
  let u := (t + D) ^ D + t
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpt : p ≤ t := by
    have hA : 0 ≤ (v + A) ^ A := by positivity
    have hB : 0 ≤ (v + B) ^ B := by positivity
    dsimp [t, v]
    dsimp [v] at hA hB
    linarith
  have hAt : (p + A) ^ A ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show p + A ≤ v + A by dsimp [v]; linarith) A).trans
    dsimp [t]
    have hB : 0 ≤ (v + B) ^ B := by positivity
    linarith
  have hBt : (q + B) ^ B ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show q + B ≤ v + B by dsimp [v]; linarith) B).trans
    dsimp [t]
    have hA : 0 ≤ (v + A) ^ A := by positivity
    linarith
  have htu : t ≤ u := by
    have hh : 0 ≤ (t + D) ^ D := by positivity
    dsimp [u]
    linarith
  have hprod : (t + D) ^ D ≤ u := by dsimp [u]; linarith
  have hbound : (u + D) ^ D + (2 * t + 2) ≤ (p + q + C) ^ C := by
    simpa [T, U, X, t, u, v, Polynomial.eval₂_pow, add_assoc] using hbudget v hv
  let V := W.rationalDilation (1 / 2)
  let Amap : Fin 2 → ((Fin 2 → ℤ) →+ ℤ) :=
    fun k => { toFun := fun x => x k.rev, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hterm (ij : Fin W.outputDim × Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((u + D) ^ D)
        (fun x => (star (V.eval a x * star (W.eval ij.1 (fun k => x k / 2))) *
          (V.eval b (fun k => x k.rev) * star (W.eval ij.2 (fun k => x k.rev / 2)))) *
          G ij.1 ij.2 (fun k => x k / 2))) := by
    obtain ⟨E⟩ := (hcompare W).expansion a ij.1
    obtain ⟨F⟩ := (hcompare W).expansion b ij.2
    obtain ⟨H⟩ := hhalf hq (Classical.choice (hG ij.1 ij.2))
    obtain ⟨K⟩ := hmul ht (E.conjugate.mono hAt) ((F.linearPullbackHom Amap).mono hAt)
    exact hmul hu (K.mono hprod) (H.mono (hBt.trans htu))
  have hc : (Fintype.card (Fin W.outputDim × Fin W.outputDim) : ℝ) ≤ Real.exp (2 * t + 2) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul W.output_bound W.output_bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add, two_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hcost : (∑ _ : Fin W.outputDim × Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp (2 * t + 2) := by
    simpa using hc
  let S := NativeIntegerExpansion.weightedSum (fun ij => Classical.choice (hterm ij)) (fun _ => 1)
    (by linarith : 0 ≤ 2 * t + 2) hc hcost
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
    (fun x => W.halfDilationExchangeCorrection G a b x)
  simpa only [one_mul, halfDilationExchangeCorrection, V] using S.mono hbound

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def tensorSquareExchangeCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin (W.outputDim ^ 2)) (x : Fin 2 → ℤ) : ℂ :=
  G ((tensorIndexEquiv W.outputDim 2).symm a 0) ((tensorIndexEquiv W.outputDim 2).symm b 0) x *
    G ((tensorIndexEquiv W.outputDim 2).symm a 1) ((tensorIndexEquiv W.outputDim 2).symm b 1) x

theorem tensorSquare_antisymmetricKernel (a b : Fin (W.outputDim ^ 2)) (h n : ℤ) :
    (W.tensorPower 2).antisymmetricKernel a b h n =
      W.antisymmetricKernel ((tensorIndexEquiv W.outputDim 2).symm a 0)
        ((tensorIndexEquiv W.outputDim 2).symm b 0) h n *
      W.antisymmetricKernel ((tensorIndexEquiv W.outputDim 2).symm a 1)
        ((tensorIndexEquiv W.outputDim 2).symm b 1) h n := by
  simp only [antisymmetricKernel, tensorPower_eval, Fin.prod_univ_two, star_mul]
  ring

theorem tensorSquareExchangeCorrection_norm {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {B : ℝ}
    (hB : 0 ≤ B)
    (hcap : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (a b : Fin (W.outputDim ^ 2)) (x : Fin 2 → ZMod N) :
    ‖W.tensorSquareExchangeCorrection G a b (fun k => ((x k).val : ℤ))‖ ≤ B ^ 2 := by
  rw [tensorSquareExchangeCorrection, norm_mul, pow_two B]
  exact mul_le_mul (hcap _ _ x) (hcap _ _ x) (norm_nonneg _) hB

theorem tensorSquareExchangeCorrection_mean_error {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {B ε : ℝ}
    (hB : 0 ≤ B)
    (hcap : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel i j ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : Fin (W.outputDim ^ 2)) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖(W.tensorPower 2).antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
        W.tensorSquareExchangeCorrection G a b (fun k => ((x k).val : ℤ))‖) ≤ (1 + B) * ε := by
  let i := (tensorIndexEquiv W.outputDim 2).symm a
  let j := (tensorIndexEquiv W.outputDim 2).symm b
  let K (r : Fin 2) (x : Fin 2 → ZMod N) :=
    W.antisymmetricKernel (i r) (j r) ((x 0).val : ℤ) ((x 1).val : ℤ)
  let F (r : Fin 2) (x : Fin 2 → ZMod N) := G (i r) (j r) (fun k => ((x k).val : ℤ))
  have hpoint (x : Fin 2 → ZMod N) :
      ‖K 0 x * K 1 x - F 0 x * F 1 x‖ ≤
        ‖K 1 x - F 1 x‖ + B * ‖K 0 x - F 0 x‖ := by
    have heq : K 0 x * K 1 x - F 0 x * F 1 x =
        K 0 x * (K 1 x - F 1 x) + (K 0 x - F 0 x) * F 1 x := by ring
    rw [heq]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul]
    apply add_le_add
    · exact mul_le_of_le_one_left (norm_nonneg _) (W.antisymmetricKernel_norm _ _ _ _)
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hcap _ _ x) (norm_nonneg (K 0 x - F 0 x))
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun x _ => hpoint x)
  rw [Finset.expect_add_distrib, ← Finset.mul_expect] at hm
  have h0 : (𝔼 x, ‖K 0 x - F 0 x‖) ≤ ε := herr _ _
  have h1 : (𝔼 x, ‖K 1 x - F 1 x‖) ≤ ε := herr _ _
  have hbnd := hm.trans (add_le_add h1 (mul_le_mul_of_nonneg_left h0 hB))
  have hfinal : (𝔼 x, ‖K 0 x * K 1 x - F 0 x * F 1 x‖) ≤ (1 + B) * ε :=
    hbnd.trans_eq (by ring)
  simpa only [K, F, i, j, tensorSquare_antisymmetricKernel, tensorSquareExchangeCorrection] using hfinal

theorem exists_tensorSquareExchangeCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p), 0 ≤ q →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((q + C) ^ C)
        (W.tensorSquareExchangeCorrection G a b)) := by
  obtain ⟨C, hC, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG a b
  exact hmul hq (Classical.choice (hG _ _)) (Classical.choice (hG _ _))

theorem explicit_half_root_exchange_mean_error {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (hcap : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel i j ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : Fin (W.outputDim ^ 2)) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖((W.rationalDilation (1 / 2)).tensorPower 2).antisymmetricKernel a b
          ((x 0).val : ℤ) ((x 1).val : ℤ) -
        (W.rationalDilation (1 / 2)).tensorSquareExchangeCorrection
          (W.halfDilationExchangeCorrection G) a b (fun k => ((x k).val : ℤ))‖) ≤
      (1 + (W.outputDim : ℝ) ^ 2) * (4 * (W.outputDim : ℝ) ^ 2 * ε) := by
  apply tensorSquareExchangeCorrection_mean_error (W.rationalDilation (1 / 2))
    (W.halfDilationExchangeCorrection G) (by positivity)
  · intro i j x
    simpa only [mul_one] using W.halfDilationExchangeCorrection_norm G hcap i j x
  · exact W.halfDilationExchangeCorrection_mean_error G herr

theorem exists_explicit_half_root_exchange_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p), 0 ≤ q →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
        ((W.rationalDilation (1 / 2)).tensorSquareExchangeCorrection
          (W.halfDilationExchangeCorrection G) a b)) := by
  obtain ⟨A, _, hhalf⟩ := exists_halfDilationExchangeCorrection_expansion
  obtain ⟨B, _, hsquare⟩ := exists_tensorSquareExchangeCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := hsquare (W.rationalDilation (1 / 2)) (by positivity : 0 ≤ (p + q + A) ^ A)
    (W.halfDilationExchangeCorrection G) (hhalf W hq G hG) a b
  have hbound : ((p + q + A) ^ A + B) ^ B ≤ (p + q + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  exact ⟨E.mono hbound⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
