import OAI.Combinatorics.Progressions.Lattices.NativeIntegerSelfEquivalence

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_finite_sum_coordinate_equivalence {σ : Type*}
    [Fintype σ] [DecidableEq σ] [Nonempty σ] (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p)
      (i : σ), NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun k (x : (σ ⊕ Fin (n + 1)) → ℤ) => W.eval k (finiteSumCoordinateInput i x))
        (fun a : Fin (n + 1) → Fin W.outputDim => fun x =>
          ∏ j, W.eval (a j) (finiteTermCoordinateInput i j x)) := by
  induction n with
  | zero =>
      obtain ⟨C, hC, hself⟩ := exists_integer_self_equivalence (σ := σ)
      refine ⟨C, hC, ?_⟩
      intro p W i
      have E := (hself W).linearPullbackHom (finiteTermCoordinateHom i (0 : Fin 1))
      apply E.of_coordinate_maps _ _ id (fun a => a 0) _ _ E.left_dimension _ le_rfl
      · intro k x
        rw [finiteSumCoordinateInput_one]
        rfl
      · intro a x
        rw [Fin.prod_univ_one]
        rfl
      · simpa only [Fintype.card_fun, Fintype.card_fin, Nat.zero_add, pow_one] using E.right_dimension
  | succ n ih =>
      obtain ⟨A, _, hprevious⟩ := ih
      obtain ⟨B, _, hadd⟩ := exists_multilinearity_equivalence (σ := σ)
      obtain ⟨D, _, hself⟩ := exists_integer_self_equivalence (σ := σ)
      obtain ⟨F, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
      obtain ⟨G, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
      let X : Polynomial ℕ := Polynomial.X
      let R := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B +
        (X + Polynomial.C D) ^ D
      let Q := (R + (R + Polynomial.C F) ^ F + Polynomial.C G) ^ G
      obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
        (Q + Polynomial.C (n + 2) * X + X)
      refine ⟨C, hC, ?_⟩
      intro p W i
      have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
      let r := (p + A) ^ A + (p + B) ^ B + (p + D) ^ D
      let t := (r + F) ^ F
      let q := (r + t + G) ^ G
      have hA : 0 ≤ (p + A) ^ A := by positivity
      have hB : 0 ≤ (p + B) ^ B := by positivity
      have hD : 0 ≤ (p + D) ^ D := by positivity
      have hr : 0 ≤ r := by dsimp [r]; linarith
      have ht : 0 ≤ t := by dsimp [t]; positivity
      have hq : 0 ≤ q := by dsimp [q]; positivity
      have hAr : (p + A) ^ A ≤ r := by dsimp [r]; linarith
      have hBr : (p + B) ^ B ≤ r := by dsimp [r]; linarith
      have hDr : (p + D) ^ D ≤ r := by dsimp [r]; linarith
      have hsum : q + (n + 2 : ℕ) * p + p ≤ (p + C) ^ C := by
        simpa [X, R, Q, r, t, q, Polynomial.eval₂_pow] using hbudget p hp
      have hnp : 0 ≤ (n + 2 : ℕ) * p := mul_nonneg (Nat.cast_nonneg _) hp
      have hqC : q ≤ (p + C) ^ C := by linarith
      have hpC : p ≤ (p + C) ^ C := by linarith
      have hnC : (n + 2 : ℕ) * p ≤ (p + C) ^ C := by linarith
      let tailMap : (σ ⊕ Fin (n + 1)) → (((σ ⊕ Fin (n + 2)) → ℤ) →+ ℤ) := fun j =>
        match j with
        | Sum.inl j =>
          { toFun := fun x => x (Sum.inl j)
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        | Sum.inr a =>
          { toFun := fun x => x (Sum.inr a.succ)
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
      let addMap : Option σ → (((σ ⊕ Fin (n + 2)) → ℤ) →+ ℤ) := fun j =>
        match j with
        | none =>
          { toFun := fun x => ∑ a : Fin (n + 1), x (Sum.inr a.succ)
            map_zero' := by simp
            map_add' := fun x y => by
              simp only [Pi.add_apply, Finset.sum_add_distrib] }
        | some j => finiteTermCoordinateHom i 0 j
      have hleft (x : (σ ⊕ Fin (n + 2)) → ℤ) :
          coordinateAdditionInputs i (fun j => addMap j x) 0 = finiteSumCoordinateInput i x := by
        rw [coordinateAdditionInputs_sum]
        change Function.update (finiteTermCoordinateInput i 0 x) i
          (finiteTermCoordinateInput i 0 x i + ∑ a : Fin (n + 1), x (Sum.inr a.succ)) = _
        simp only [finiteTermCoordinateInput, finiteSumCoordinateInput,
          Function.update_self, Function.update_idem]
        congr 1
        exact (Fin.sum_univ_succ (fun a : Fin (n + 2) => x (Sum.inr a))).symm
      have hfirst (x : (σ ⊕ Fin (n + 2)) → ℤ) :
          coordinateAdditionInputs i (fun j => addMap j x) 1 = finiteTermCoordinateInput i 0 x := rfl
      have htail (x : (σ ⊕ Fin (n + 2)) → ℤ) :
          coordinateAdditionInputs i (fun j => addMap j x) 2 =
            finiteSumCoordinateInput i (fun j => tailMap j x) := by
        rw [coordinateAdditionInputs_right]
        change Function.update (finiteTermCoordinateInput i 0 x) i
          (∑ a : Fin (n + 1), x (Sum.inr a.succ)) = _
        simp only [finiteTermCoordinateInput, finiteSumCoordinateInput, Function.update_idem]
        rfl
      have E₀ : NativeIntegerVectorEquivalence (Fintype.card σ - 1) r
          (fun k x => W.eval k (finiteSumCoordinateInput i x))
          (fun a : Fin W.outputDim × Fin W.outputDim => fun x =>
            W.eval a.1 (finiteTermCoordinateInput i 0 x) *
              W.eval a.2 (finiteSumCoordinateInput i (fun j => tailMap j x))) := by
        have E := ((hadd W i).linearPullbackHom addMap).mono hBr
        simpa only [coordinateSumVector, coordinateTensorVector, hleft, hfirst, htail] using E
      have Efirst := ((hself W).linearPullbackHom
        (finiteTermCoordinateHom i (0 : Fin (n + 2)))).mono hDr
      have Etail := ((hprevious W i).linearPullbackHom tailMap).mono hAr
      have E₂ := htensor hr Efirst Etail
      have hunit (x : (σ ⊕ Fin (n + 2)) → ℤ) :
          ∑ a : Fin W.outputDim × Fin W.outputDim,
            ‖W.eval a.1 (finiteTermCoordinateInput i 0 x) *
              W.eval a.2 (finiteSumCoordinateInput i (fun j => tailMap j x))‖ ^ 2 = 1 := by
        simp only [Fintype.sum_prod_type, norm_mul, mul_pow, ← Finset.mul_sum,
          W.unit_eval, mul_one]
      have H := htrans (add_nonneg hr ht) (E₀.mono (le_add_of_nonneg_right ht))
        (E₂.mono (le_add_of_nonneg_left hr)) hunit
      have hdim : (Fintype.card (Fin (n + 2) → Fin W.outputDim) : ℝ) ≤
          Real.exp ((p + C) ^ C) := by
        simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
        calc
          _ ≤ Real.exp p ^ (n + 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound _
          _ = Real.exp ((n + 2 : ℕ) * p) := (Real.exp_nat_mul p (n + 2)).symm
          _ ≤ _ := Real.exp_le_exp.mpr hnC
      apply H.of_coordinate_maps _ _ id (fun a => (a 0, fun j => a j.succ))
        (fun _ _ => rfl) _ _ hdim hqC
      · intro a x
        rw [Fin.prod_univ_succ]
        rfl
      · simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpC)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
