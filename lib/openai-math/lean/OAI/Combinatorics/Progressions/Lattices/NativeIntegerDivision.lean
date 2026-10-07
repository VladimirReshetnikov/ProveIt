import OAI.Combinatorics.Progressions.Polynomial.PositiveDegreeCyclicDifference

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def divisionPolynomial {σ : Type*} (d : ℕ) (r : σ → ℤ) (i : σ) : MvPolynomial σ ℚ :=
  MvPolynomial.C (d : ℚ)⁻¹ * (MvPolynomial.X i - MvPolynomial.C (r i : ℚ))

theorem divisionPolynomial_support {σ : Type*} (d : ℕ) (r : σ → ℤ) (i : σ) :
    divisionPolynomial d r i ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
  have hx : (MvPolynomial.X i : MvPolynomial σ ℚ) ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : σ => 1) (Finsupp.single i 1) (1 : ℚ)
  simpa only [divisionPolynomial, zero_add] using
    weightedSupportLE_mul (weightedSupportLE_C (fun _ : σ => 1) 0 (d : ℚ)⁻¹)
      (Submodule.sub_mem _ hx (weightedSupportLE_C _ 1 (r i : ℚ)))

theorem divisionPolynomial_eval {σ : Type*} (d : ℕ) [NeZero d] (r x : σ → ℤ)
    (hr : ∀ i, x i % (d : ℤ) = r i) (i : σ) :
    MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (divisionPolynomial d r i) =
      ((x i / (d : ℤ) : ℤ) : ℚ) := by
  have hi : x i = (d : ℤ) * (x i / (d : ℤ)) + r i := by
    calc
      _ = x i % (d : ℤ) + (d : ℤ) * (x i / (d : ℤ)) := (Int.emod_add_mul_ediv _ _).symm
      _ = _ := by rw [hr i]; ring
  have hiq : (x i : ℚ) = (d : ℚ) * ((x i / (d : ℤ) : ℤ) : ℚ) + (r i : ℚ) := by
    exact_mod_cast hi
  simp only [divisionPolynomial, map_mul, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  change (d : ℚ)⁻¹ * ((x i : ℚ) - (r i : ℚ)) = ((x i / (d : ℤ) : ℤ) : ℚ)
  rw [hiq, add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d)), one_mul]

noncomputable def pairResidueIndicator {d : ℕ} (r : Fin 2 → ZMod d) (x : Fin 2 → ℤ) : ℂ :=
  if (fun i => (x i : ZMod d)) = r then 1 else 0

theorem pairResidueIndicator_product {d : ℕ} (r : Fin 2 → ZMod d) (x : Fin 2 → ℤ) :
    pairResidueIndicator r x =
      (if (x 0 : ZMod d) = r 0 then 1 else 0) *
        (if (x 1 : ZMod d) = r 1 then 1 else 0) := by
  classical
  have heq : (fun i => (x i : ZMod d)) = r ↔ (x 0 : ZMod d) = r 0 ∧ (x 1 : ZMod d) = r 1 := by
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i <;> assumption
  unfold pairResidueIndicator
  simp only [heq]
  split_ifs <;> simp_all

theorem exists_pairResidueIndicator_expansion (d s : ℕ) [NeZero d] (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ r : Fin 2 → ZMod d,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s (C : ℝ) (pairResidueIndicator r)) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let D := d + 2 + (d + 4) ^ 2 + 3
  refine ⟨(D + A) ^ A + 2, by omega, ?_⟩
  intro r
  have hd : (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
  obtain ⟨E0⟩ := exists_coordinate_residue_expansion (σ := Fin 2) 0 (r 0) (Nat.cast_nonneg d) hd
  obtain ⟨E1⟩ := exists_coordinate_residue_expansion (σ := Fin 2) 1 (r 1) (Nat.cast_nonneg d) hd
  have hraise : raisedNiltestBudget ((d : ℝ) + 2) = (D : ℝ) := by
    dsimp [D, raisedNiltestBudget]
    push_cast
    ring
  have F0 : NativeIntegerExpansion (fun _ : Fin 2 => 1) s D
      (fun x => if (x 0 : ZMod d) = r 0 then 1 else 0) := by
    simpa only [hraise] using E0.raiseStep hs (by positivity)
  have F1 : NativeIntegerExpansion (fun _ : Fin 2 => 1) s D
      (fun x => if (x 1 : ZMod d) = r 1 then 1 else 0) := by
    simpa only [hraise] using E1.raiseStep hs (by positivity)
  obtain ⟨F⟩ := hmul (Nat.cast_nonneg D) F0 F1
  have hb : ((D : ℝ) + A) ^ A ≤ (((D + A) ^ A + 2 : ℕ) : ℝ) := by
    push_cast
    linarith
  have heq : (fun x => (if (x 0 : ZMod d) = r 0 then (1 : ℂ) else 0) *
      (if (x 1 : ZMod d) = r 1 then 1 else 0)) = pairResidueIndicator r := by
    funext x
    exact (pairResidueIndicator_product r x).symm
  rw [heq] at F
  exact ⟨F.mono hb⟩

theorem card_pairResidue_le_exp (d : ℕ) [NeZero d] :
    (Fintype.card (Fin 2 → ZMod d) : ℝ) ≤ Real.exp ((d : ℝ) ^ 2) := by
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow]
  linarith [Real.add_one_le_exp ((d : ℝ) ^ 2)]

theorem NativeIntegerExpansion.exists_division_expansion (d s : ℕ) [NeZero d] (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} {f : (Fin 2 → ℤ) → ℂ}, 0 ≤ p →
      NativeIntegerExpansion (fun _ : Fin 2 => 1) s p f →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s ((p + C) ^ C)
        (fun x => f (fun i => x i / (d : ℤ)))) := by
  obtain ⟨A, _, hresidue⟩ := exists_pairResidueIndicator_expansion d s hs
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A + 2 + Polynomial.C B) ^ B + Polynomial.C (d ^ 2))
  refine ⟨C, hC, ?_⟩
  intro p f hp E
  classical
  let t : ℝ := p + A + 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; have := Nat.cast_nonneg (α := ℝ) A; linarith
  have hAt : (A : ℝ) ≤ t := by dsimp [t]; linarith
  let P (r : Fin 2 → ZMod d) := divisionPolynomial d (fun i => ((r i).val : ℤ))
  have hP (r : Fin 2 → ZMod d) (i : Fin 2) :
      P r i ∈ weightedSupportLE (fun _ : Fin 2 => 1) 1 := divisionPolynomial_support d _ i
  let F (r : Fin 2 → ZMod d) := E.substitutedValue (P r) (hP r)
  have hF (r : Fin 2 → ZMod d) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s
      ((t + B) ^ B) (fun x => pairResidueIndicator r x * F r x)) :=
    hmul ht ((Classical.choice (hresidue r)).mono hAt)
      ((E.substituteExpansion (P r) (hP r)).mono hpt)
  have hcost : (∑ _ : Fin 2 → ZMod d, ‖(1 : ℂ)‖) ≤ Real.exp ((d : ℝ) ^ 2) := by
    simpa using card_pairResidue_le_exp d
  let S := NativeIntegerExpansion.weightedSum (fun r => Classical.choice (hF r)) (fun _ => 1)
    (sq_nonneg (d : ℝ)) (card_pairResidue_le_exp d) hcost
  have heq : (fun x => ∑ r : Fin 2 → ZMod d, (1 : ℂ) * (pairResidueIndicator r x * F r x)) =
      (fun x => f (fun i => x i / (d : ℤ))) := by
    funext x
    let r : Fin 2 → ZMod d := fun i => (x i : ZMod d)
    rw [Finset.sum_eq_single r]
    · simp only [pairResidueIndicator, r, ite_true, one_mul]
      apply E.substitutedValue_eq (P r) (hP r) x (fun i => x i / (d : ℤ))
      exact divisionPolynomial_eval d _ x (fun i => (ZMod.val_intCast (x i)).symm)
    · intro a _ ha
      have hne : (fun i => (x i : ZMod d)) ≠ a := fun h => ha h.symm
      simp only [pairResidueIndicator, hne, ite_false, zero_mul, mul_zero]
    · simp
  have hb : (t + B) ^ B + (d : ℝ) ^ 2 ≤ (p + C) ^ C := by
    simpa [t, X, Polynomial.eval₂_pow] using hbudget p hp
  rw [heq] at S
  exact ⟨S.mono hb⟩

end Erdos3

end

end OAI
