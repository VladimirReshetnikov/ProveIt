/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.DiagonalWrapComparison
import OAI.Combinatorics.Progressions.Lattices.QuarticIntegerTranslation

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_quartic_diagonal_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p),
      NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
        (fun k (x : Fin 2 → ℤ) => W.eval k (fun _ => x 1 + x 0))
        W.quarticDiagonalTensor := by
  let := replicatedMixed_nonempty 3
  obtain ⟨C, hC, hexpand⟩ := exists_binary_assignment_equivalence quarticAllCoordinates
  refine ⟨C, hC, ?_⟩
  intro p W
  let a : Option QuarticReplicatedIndex → Fin 2
    | none => 0
    | some _ => 1
  have hA (x : Fin 2 → ℤ) : (fun j => x (a j)) = quarticDiagonalSampleInput x := by
    funext j
    cases j <;> rfl
  have E := (hexpand W (by decide)).coordinatePullback a
  change NativeIntegerVectorEquivalence (Fintype.card QuarticReplicatedIndex - 1) ((p + C) ^ C)
    (fun k (x : Fin 2 → ℤ) => W.eval k (coordinateTranslatedInput quarticAllCoordinates (fun j => x (a j))))
    (fun k : (Fin 4 → Fin 2) → Fin W.outputDim => fun x =>
      ∏ v : Fin 4 → Fin 2, W.eval (k v) (binaryLeafInput quarticAllCoordinates v (fun j => x (a j)))) at E
  have hdegree : Fintype.card QuarticReplicatedIndex - 1 = 3 := by
    simp only [replicatedMixed_card, Nat.reduceAdd, Nat.reduceSub]
  rw [hdegree] at E
  refine ⟨E.left_dimension, E.right_dimension, ?_⟩
  intro i k
  obtain ⟨F⟩ := E.expansion i k
  exact ⟨by simpa only [hA, quarticDiagonalSample_sum, quarticDiagonalSample_leaf,
    quarticDiagonalTensor] using F⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

abbrev QuarticNonconstantCorner := {v : Fin 4 → Fin 2 // v ≠ fun _ => 0}

theorem quarticNonconstantCorner_card : Fintype.card QuarticNonconstantCorner = 15 := by
  norm_num [QuarticNonconstantCorner, Fintype.card_subtype_compl]

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticDiagonalDerivative (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.eval a.1 (fun _ => x 1) * star (W.eval a.2 (fun _ => x 1 + x 0))

noncomputable def quarticMixedFifteen (a : QuarticNonconstantCorner → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  star (∏ v, W.eval (a v) (quarticDiagonalCorner v.val x))

theorem quarticDiagonalDerivative_norm (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.quarticDiagonalDerivative a x‖ ≤ 1 := by
  rw [quarticDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem quarticMixedFifteen_norm (a : QuarticNonconstantCorner → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.quarticMixedFifteen a x‖ ≤ 1 := by
  rw [quarticMixedFifteen, norm_star, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem quarticDiagonalDerivative_unit (x : Fin 2 → ℤ) :
    ∑ a, ‖W.quarticDiagonalDerivative a x‖ ^ 2 = 1 := by
  simp only [quarticDiagonalDerivative, Fintype.sum_prod_type, norm_mul, norm_star,
    mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]

theorem quarticMixedFifteen_unit (x : Fin 2 → ℤ) :
    ∑ a : QuarticNonconstantCorner → Fin W.outputDim, ‖W.quarticMixedFifteen a x‖ ^ 2 = 1 := by
  simp only [quarticMixedFifteen, norm_star, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ v : QuarticNonconstantCorner, ∑ a : Fin W.outputDim,
        ‖W.eval a (quarticDiagonalCorner v.val x)‖ ^ 2 := (Fintype.prod_sum _).symm
    _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]

theorem exists_quartic_diagonal_derivative_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p),
      NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
        W.quarticDiagonalDerivative W.quarticMixedFifteen := by
  obtain ⟨A, _, hdiag⟩ := exists_quartic_diagonal_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + 15 * X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hsum : (p + A) ^ A + 15 * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have htwo : 2 * p ≤ (p + C) ^ C := by linarith
  have hfifteen : 15 * p ≤ (p + C) ^ C := by linarith
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hdim15 : (Fintype.card (QuarticNonconstantCorner → Fin W.outputDim) : ℝ) ≤
      Real.exp (15 * p) := by
    simp only [Fintype.card_fun, quarticNonconstantCorner_card, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ 15 := pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound 15
      _ = _ := (Real.exp_nat_mul p 15).symm
  refine ⟨(card_product_le_exp_two hdim hdim).trans (Real.exp_le_exp.mpr htwo),
    hdim15.trans (Real.exp_le_exp.mpr hfifteen), ?_⟩
  intro a b
  let full : (Fin 4 → Fin 2) → Fin W.outputDim := fun v =>
    if h : v = fun _ => 0 then a.1 else b ⟨v, h⟩
  obtain ⟨F⟩ := (hdiag W).expansion a.2 full
  have htensor (x : Fin 2 → ℤ) : W.quarticDiagonalTensor full x =
      W.eval a.1 (fun _ => x 1) *
        ∏ v : QuarticNonconstantCorner, W.eval (b v) (quarticDiagonalCorner v.val x) := by
    rw [quarticDiagonalTensor, Fintype.prod_eq_mul_prod_subtype_ne _ (fun _ => 0)]
    have hzero : full (fun _ => 0) = a.1 := by simp only [full, dite_eq_left rfl]
    have hfull (v : QuarticNonconstantCorner) : full v.val = b v := by
      simp only [full, dite_eq_right v.property]
    simp only [hzero, quarticDiagonalCorner_zero, hfull]
  have heq : (fun x : Fin 2 → ℤ => star (W.eval a.2 (fun _ => x 1 + x 0) *
      star (W.quarticDiagonalTensor full x))) =
      (fun x => W.quarticDiagonalDerivative a x * star (W.quarticMixedFifteen b x)) := by
    funext x
    rw [htensor]
    simp only [quarticDiagonalDerivative, quarticMixedFifteen, star_mul, star_star]
    ring
  exact ⟨heq ▸ F.conjugate.mono hcost⟩

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def quarticRoot {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p) :
    NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) (tensorPowerBudget 64 p) :=
  (W.rationalDilation (((4 : ℕ) : ℚ)⁻¹)).tensorPower 64

theorem quarticRoot_dim {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p) :
    W.quarticRoot.dim = W.dim := rfl

theorem exists_explicit_quartic_root_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p),
      NativeIntegerVectorEquivalence 3 ((p + C) ^ C) W.eval (tensorVector W.quarticRoot.eval 4) := by
  have hsum : (∑ _ : QuarticReplicatedIndex, 1) = (4 : ℕ) := by decide
  have hpos : 1 ≤ ∑ _ : QuarticReplicatedIndex, 1 := by rw [hsum]; norm_num
  obtain ⟨A, _, hdilation⟩ :=
    exists_dilation_degree_equivalence (fun _ : QuarticReplicatedIndex => 1) hpos 4
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + 260 * (X + 1) + X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hA : 0 ≤ (p + A) ^ A := by positivity
  have hbound : (p + A) ^ A + 260 * (p + 1) + p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by linarith
  have hAr : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have hdimBound : 4 * tensorPowerBudget 64 p ≤ (p + C) ^ C := by
    norm_num [tensorPowerBudget]
    linarith
  let V := W.rationalDilation (((4 : ℕ) : ℚ)⁻¹)
  let R := V.tensorPower 64
  have hleft (i : Fin W.outputDim) (x : QuarticReplicatedIndex → ℤ) :
      W.eval i x = integerDilationVector V.eval 4 i x :=
    (W.rationalDilation_eval_rescaled (((4 : ℕ) : ℚ)⁻¹) 4 (by norm_num) i x).symm
  have hright (b : Fin 4 → Fin R.outputDim) (x : QuarticReplicatedIndex → ℤ) :
      tensorVector R.eval 4 b x =
        signedTensorVector V.eval ((4 : ℤ) ^ ∑ _ : QuarticReplicatedIndex, 1)
          (rootTensorIndex W.outputDim 4 (∑ _ : QuarticReplicatedIndex, 1) hpos b) x := by
    exact V.tensorPower_tensor_eval 4 (∑ _ : QuarticReplicatedIndex, 1) hpos b x
  have hdim : (Fintype.card (Fin 4 → Fin R.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (tensorPowerBudget 64 p) ^ 4 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) R.output_bound _
      _ = Real.exp (4 * tensorPowerBudget 64 p) := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (tensorPowerBudget 64 p) 4).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdimBound
  have E := (hdilation V).of_coordinate_maps W.eval (tensorVector R.eval 4) id
    (rootTensorIndex W.outputDim 4 (∑ _ : QuarticReplicatedIndex, 1) hpos) hleft hright
    (by simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpr)) hdim hAr
  change NativeIntegerVectorEquivalence 3 ((p + C) ^ C) W.eval (tensorVector R.eval 4)
  simpa only [hsum, Nat.reduceSub] using E

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticCyclicDiagonalDerivative {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) : ℂ :=
  W.eval a.1 (fun _ => ((x 1).val : ℤ)) *
    star (W.eval a.2 (fun _ => ((x 0 + x 1).val : ℤ)))

theorem quarticCyclicDiagonalDerivative_norm {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.quarticCyclicDiagonalDerivative a x‖ ≤ 1 := by
  rw [quarticCyclicDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem quarticCyclicDiagonalDerivative_unit {N : ℕ} [NeZero N]
    (x : Fin 2 → ZMod N) :
    ∑ a : Fin W.outputDim × Fin W.outputDim, ‖W.quarticCyclicDiagonalDerivative a x‖ ^ 2 = 1 := by
  simp only [quarticCyclicDiagonalDerivative, Fintype.sum_prod_type, norm_mul, norm_star,
    mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]

noncomputable def quarticWrappedDiagonalDerivative (N : ℕ)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  W.eval a.1 (fun _ => x 1) * star (W.eval a.2 (fun _ => x 1 + x 0 - N))

noncomputable def quarticDiagonalWrapCoefficient (N : ℕ) (j k : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.eval k (fun _ => x 1 + x 0) * star (W.eval j (fun _ => x 1 + x 0 - N))

theorem quarticWrappedDiagonalDerivative_norm (N : ℕ) (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.quarticWrappedDiagonalDerivative N a x‖ ≤ 1 := by
  simp only [quarticWrappedDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem quarticDiagonalWrapCoefficient_norm (N : ℕ) (j k : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.quarticDiagonalWrapCoefficient N j k x‖ ≤ 1 := by
  simp only [quarticDiagonalWrapCoefficient, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem quarticWrappedDiagonalDerivative_resolution (N : ℕ)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.quarticWrappedDiagonalDerivative N a x =
      ∑ k, W.quarticDiagonalWrapCoefficient N a.2 k x * W.quarticDiagonalDerivative (a.1, k) x := by
  have h := complex_unit_vector_resolution
    (fun k => W.eval k (fun _ => x 1 + x 0)) (W.unit_eval _)
    (star (W.eval a.2 (fun _ => x 1 + x 0 - N)))
  calc
    _ = W.eval a.1 (fun _ => x 1) *
        ∑ k, (star (W.eval a.2 (fun _ => x 1 + x 0 - N)) *
          star (W.eval k (fun _ => x 1 + x 0))) * W.eval k (fun _ => x 1 + x 0) := by
      rw [← h]
      rfl
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [quarticDiagonalWrapCoefficient, quarticDiagonalDerivative]
      ring

theorem quarticCyclicDiagonalDerivative_branches {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    W.quarticCyclicDiagonalDerivative a x =
      (1 - (cyclicCarry (x 0) (x 1) : ℂ)) *
          W.quarticDiagonalDerivative a (fun z => ((x z).val : ℤ)) +
        (cyclicCarry (x 0) (x 1) : ℂ) *
          W.quarticWrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) := by
  have hval := cyclic_representative_add (x 0) (x 1)
  have hlt := (x 0).val_lt
  by_cases hw : N ≤ (x 0).val + (x 1).val
  · have hcut : N - (x 0).val ≤ (x 1).val := by omega
    simp only [cyclicCarry, hw, ite_true, Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add,
      quarticCyclicDiagonalDerivative, quarticWrappedDiagonalDerivative]
    rw [hval, ite_eq_left hcut]
  · have hcut : ¬N - (x 0).val ≤ (x 1).val := by omega
    simp only [cyclicCarry, hw, ite_false, Complex.ofReal_zero, sub_zero, zero_mul, one_mul, add_zero,
      quarticCyclicDiagonalDerivative, quarticDiagonalDerivative]
    rw [hval, ite_eq_right hcut, sub_zero]

theorem exists_quarticDiagonalWrapCoefficient_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p) (N : ℕ)
      (j k : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 ((p + C) ^ C)
        (W.quarticDiagonalWrapCoefficient N j k)) := by
  obtain ⟨C, hC, htranslate⟩ := exists_quartic_integer_translation_equivalence
  refine ⟨C, hC, ?_⟩
  intro p W N j k
  let A : QuarticReplicatedIndex → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1 + x 0, map_zero' := by simp,
      map_add' := fun x y => by simp only [Pi.add_apply]; ring }
  obtain ⟨F⟩ := (htranslate W 0 (fun _ => -(N : ℤ))).expansion k j
  have H := F.linearPullbackHom A
  have heq : (fun x : Fin 2 → ℤ => W.eval k ((fun l => A l x) + 0) *
      star (W.eval j ((fun l => A l x) + fun _ => -(N : ℤ)))) =
      W.quarticDiagonalWrapCoefficient N j k := by
    funext x
    simp only [add_zero, quarticDiagonalWrapCoefficient, sub_eq_add_neg]
    rfl
  exact ⟨heq ▸ H⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
