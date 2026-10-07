/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.CubicAntisymmetricTransfer

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_cubic_diagonal_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p),
      NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
        (fun k (x : Fin 2 → ℤ) => W.eval k (fun _ => x 1 + x 0))
        W.cubicDiagonalTensor := by
  let : Nonempty CubicReplicatedIndex := ⟨cubicFirstReplica⟩
  obtain ⟨C, hC, hexpand⟩ := exists_translation_expansion_equivalence
    [cubicFirstReplica, cubicLeftReplica, cubicRightReplica]
  refine ⟨C, hC, ?_⟩
  intro p W
  let a : Option CubicReplicatedIndex → Fin 2 := fun j => match j with
    | none => 0
    | some _ => 1
  have E := (hexpand W (by decide)).coordinatePullback a
  have hcard : Fintype.card CubicReplicatedIndex - 1 = 2 := by
    have hc : Fintype.card CubicReplicatedIndex = 3 := by
      calc
        _ = ∑ i : Fin 2, mixedCorrelationDegree 2 i := replicatedIndex_card _
        _ = 3 := by rw [Fin.sum_univ_two]; rfl
    omega
  rw [hcard] at E
  have hleft (k : Fin W.outputDim) (x : Fin 2 → ℤ) :
      W.eval k (coordinateTranslatedInput [cubicFirstReplica, cubicLeftReplica, cubicRightReplica]
        (fun j => x (a j))) = W.eval k (fun _ => x 1 + x 0) := by
    apply congrArg (W.eval k)
    funext j
    rcases j with ⟨j, k⟩
    fin_cases j <;> fin_cases k <;>
      simp [coordinateTranslatedInput, a, cubicFirstReplica, cubicLeftReplica, cubicRightReplica]
  have hright (k : Fin 8 → Fin W.outputDim) (x : Fin 2 → ℤ) :
      coordinateTranslationExpansion W.eval [cubicFirstReplica, cubicLeftReplica, cubicRightReplica]
        (((k 0, k 1), (k 2, k 3)), ((k 4, k 5), (k 6, k 7))) (fun j => x (a j)) =
          W.cubicDiagonalTensor k x := by
    simp only [cubicDiagonalTensor, coordinateTranslationExpansion, Fin.prod_univ_eight]
    change _ = W.eval (k 0) (cubicTrilinearInput (x 1) (x 1) (x 1)) *
      W.eval (k 1) (cubicTrilinearInput (x 1) (x 1) (x 0)) *
      W.eval (k 2) (cubicTrilinearInput (x 1) (x 0) (x 1)) *
      W.eval (k 3) (cubicTrilinearInput (x 1) (x 0) (x 0)) *
      W.eval (k 4) (cubicTrilinearInput (x 0) (x 1) (x 1)) *
      W.eval (k 5) (cubicTrilinearInput (x 0) (x 1) (x 0)) *
      W.eval (k 6) (cubicTrilinearInput (x 0) (x 0) (x 1)) *
      W.eval (k 7) (cubicTrilinearInput (x 0) (x 0) (x 0))
    simp only [mul_assoc]
    repeat' apply congrArg₂ (fun z w : ℂ => z * w)
    all_goals
      apply congrArg (W.eval _)
      funext j
      rcases j with ⟨j, l⟩
      fin_cases j <;> fin_cases l <;>
        simp [coordinateReplaceInput, coordinateReplaceIndex, a, cubicTrilinearInput,
          cubicFirstReplica, cubicLeftReplica, cubicRightReplica, Fin.ext_iff]
  refine ⟨E.left_dimension, ?_, ?_⟩
  · have hc : Fintype.card (Fin 8 → Fin W.outputDim) =
        Fintype.card (BinaryTensorIndex (Fin W.outputDim) 3) := by
      change Fintype.card (Fin 8 → Fin W.outputDim) =
        Fintype.card (((Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim)) ×
          ((Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim)))
      simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod]
      ring
    exact (congrArg (fun n : ℕ => (n : ℝ)) hc).trans_le E.right_dimension
  · intro k l
    obtain ⟨F⟩ := E.expansion k (((l 0, l 1), (l 2, l 3)), ((l 4, l 5), (l 6, l 7)))
    exact ⟨by simpa only [hleft, hright] using F⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicDiagonalDerivative (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.eval a.1 (fun _ => x 1) * star (W.eval a.2 (fun _ => x 1 + x 0))

noncomputable def cubicMixedSeven (a : Fin 7 → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  star (∏ i : Fin 7, W.eval (a i) (cubicDiagonalCorner i.succ x))

theorem cubicDiagonalDerivative_norm (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.cubicDiagonalDerivative a x‖ ≤ 1 := by
  rw [cubicDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans
    (W.norm_eval _ _)

theorem cubicMixedSeven_norm (a : Fin 7 → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.cubicMixedSeven a x‖ ≤ 1 := by
  rw [cubicMixedSeven, norm_star, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem cubicDiagonalDerivative_unit (x : Fin 2 → ℤ) :
    ∑ a, ‖W.cubicDiagonalDerivative a x‖ ^ 2 = 1 := by
  simp only [cubicDiagonalDerivative, Fintype.sum_prod_type, norm_mul, norm_star,
    mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]

theorem cubicMixedSeven_unit (x : Fin 2 → ℤ) :
    ∑ a : Fin 7 → Fin W.outputDim, ‖W.cubicMixedSeven a x‖ ^ 2 = 1 := by
  simp only [cubicMixedSeven, norm_star, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ i : Fin 7, ∑ a : Fin W.outputDim, ‖W.eval a (cubicDiagonalCorner i.succ x)‖ ^ 2 :=
      (Fintype.prod_sum _).symm
    _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]

theorem exists_cubic_diagonal_derivative_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p),
      NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
        W.cubicDiagonalDerivative W.cubicMixedSeven := by
  obtain ⟨A, _, hdiag⟩ := exists_cubic_diagonal_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + 7 * X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hsum : (p + A) ^ A + 7 * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have htwo : 2 * p ≤ (p + C) ^ C := by linarith
  have hseven : 7 * p ≤ (p + C) ^ C := by linarith
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hdim7 : (Fintype.card (Fin 7 → Fin W.outputDim) : ℝ) ≤ Real.exp (7 * p) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ 7 := pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound 7
      _ = _ := (Real.exp_nat_mul p 7).symm
  refine ⟨(card_product_le_exp_two hdim hdim).trans (Real.exp_le_exp.mpr htwo),
    hdim7.trans (Real.exp_le_exp.mpr hseven), ?_⟩
  intro a b
  obtain ⟨F⟩ := (hdiag W).expansion a.2 (Fin.cons a.1 b)
  have hzero (x : Fin 2 → ℤ) : cubicDiagonalCorner 0 x = fun _ => x 1 := by
    funext j
    simp [cubicDiagonalCorner, cubicTrilinearInput]
  have heq : (fun x : Fin 2 → ℤ => star (W.eval a.2 (fun _ => x 1 + x 0) *
      star (W.cubicDiagonalTensor (Fin.cons a.1 b) x))) =
      (fun x => W.cubicDiagonalDerivative a x * star (W.cubicMixedSeven b x)) := by
    funext x
    simp only [cubicDiagonalTensor, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      hzero, cubicDiagonalDerivative, cubicMixedSeven, star_mul, star_star]
    ring
  exact ⟨heq ▸ F.conjugate.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

theorem cubicMixedSeven_explicit (a : Fin 7 → Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.cubicMixedSeven a x = star
      (W.eval (a 0) (cubicTrilinearInput (x 1) (x 1) (x 0)) *
        W.eval (a 1) (cubicTrilinearInput (x 1) (x 0) (x 1)) *
        W.eval (a 2) (cubicTrilinearInput (x 1) (x 0) (x 0)) *
        W.eval (a 3) (cubicTrilinearInput (x 0) (x 1) (x 1)) *
        W.eval (a 4) (cubicTrilinearInput (x 0) (x 1) (x 0)) *
        W.eval (a 5) (cubicTrilinearInput (x 0) (x 0) (x 1)) *
        W.eval (a 6) (cubicTrilinearInput (x 0) (x 0) (x 0))) := by
  rw [cubicMixedSeven, Fin.prod_univ_seven]
  rfl

theorem cubicMixedSeven_replica_reduction
    (hsymm : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) i x,
      W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
        W.eval i x)
    (a : Fin 7 → Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.cubicMixedSeven a x = star
      (W.eval (a 0) (cubicTrilinearInput (x 1) (x 0) (x 1)) *
        W.eval (a 1) (cubicTrilinearInput (x 1) (x 0) (x 1)) *
        W.eval (a 2) (cubicTrilinearInput (x 1) (x 0) (x 0)) *
        W.eval (a 3) (cubicTrilinearInput (x 0) (x 1) (x 1)) *
        W.eval (a 4) (cubicTrilinearInput (x 0) (x 0) (x 1)) *
        W.eval (a 5) (cubicTrilinearInput (x 0) (x 0) (x 1)) *
        W.eval (a 6) (cubicTrilinearInput (x 0) (x 0) (x 0))) := by
  rw [W.cubicMixedSeven_explicit]
  rw [W.eval_cubicTrilinearInput_swap hsymm (a 0) (x 1) (x 1) (x 0),
    W.eval_cubicTrilinearInput_swap hsymm (a 4) (x 0) (x 1) (x 0)]

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
