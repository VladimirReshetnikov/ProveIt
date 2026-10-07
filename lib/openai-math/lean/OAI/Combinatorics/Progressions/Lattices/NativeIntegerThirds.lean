import OAI.Combinatorics.Progressions.Polynomial.PositiveDegreeCyclicDifference

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def thirdsPolynomial {σ : Type*} (r : σ → ℤ) (i : σ) : MvPolynomial σ ℚ :=
  MvPolynomial.C (1 / 3 : ℚ) * (MvPolynomial.X i - MvPolynomial.C (r i : ℚ))

theorem thirdsPolynomial_support {σ : Type*} (r : σ → ℤ) (i : σ) :
    thirdsPolynomial r i ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
  have hx : (MvPolynomial.X i : MvPolynomial σ ℚ) ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : σ => 1) (Finsupp.single i 1) (1 : ℚ)
  simpa only [thirdsPolynomial, zero_add] using
    weightedSupportLE_mul (weightedSupportLE_C (fun _ : σ => 1) 0 (1 / 3 : ℚ))
      (Submodule.sub_mem _ hx (weightedSupportLE_C _ 1 (r i : ℚ)))

theorem thirdsPolynomial_eval {σ : Type*} (r x : σ → ℤ)
    (hr : ∀ i, x i % 3 = r i) (i : σ) :
    MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (thirdsPolynomial r i) =
      ((x i / 3 : ℤ) : ℚ) := by
  have hi : x i = 3 * (x i / 3) + r i := by
    have h := hr i
    omega
  have hiq : (x i : ℚ) = 3 * ((x i / 3 : ℤ) : ℚ) + (r i : ℚ) := by exact_mod_cast hi
  simp only [thirdsPolynomial, map_mul, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  change (1 / 3 : ℚ) * ((x i : ℚ) - (r i : ℚ)) = ((x i / 3 : ℤ) : ℚ)
  linarith

noncomputable def pairThirdIndicator (r : Fin 2 → ZMod 3) (x : Fin 2 → ℤ) : ℂ :=
  if (fun i => (x i : ZMod 3)) = r then 1 else 0

theorem pairThirdIndicator_product (r : Fin 2 → ZMod 3) (x : Fin 2 → ℤ) :
    pairThirdIndicator r x =
      (if (x 0 : ZMod 3) = r 0 then 1 else 0) *
        (if (x 1 : ZMod 3) = r 1 then 1 else 0) := by
  classical
  have heq : (fun i => (x i : ZMod 3)) = r ↔ (x 0 : ZMod 3) = r 0 ∧ (x 1 : ZMod 3) = r 1 := by
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i <;> assumption
  unfold pairThirdIndicator
  simp only [heq]
  split_ifs <;> simp_all

theorem exists_pairThirdIndicator_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ r : Fin 2 → ZMod 3,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 (C : ℝ) (pairThirdIndicator r)) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  refine ⟨(43 + A) ^ A + 2, by omega, ?_⟩
  intro r
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  obtain ⟨E0⟩ := exists_coordinate_residue_expansion (σ := Fin 2) 0 (r 0)
    (by norm_num : (0 : ℝ) ≤ 2) hthree
  obtain ⟨E1⟩ := exists_coordinate_residue_expansion (σ := Fin 2) 1 (r 1)
    (by norm_num : (0 : ℝ) ≤ 2) hthree
  have hraise : raisedNiltestBudget ((2 : ℝ) + 2) = 43 := by norm_num [raisedNiltestBudget]
  have F0 : NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 43
      (fun x => if (x 0 : ZMod 3) = r 0 then 1 else 0) := by
    simpa only [hraise] using E0.raiseStep (by decide : 1 ≤ 2) (by norm_num)
  have F1 : NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 43
      (fun x => if (x 1 : ZMod 3) = r 1 then 1 else 0) := by
    simpa only [hraise] using E1.raiseStep (by decide : 1 ≤ 2) (by norm_num)
  obtain ⟨F⟩ := hmul (by norm_num : (0 : ℝ) ≤ 43) F0 F1
  have hb : (43 + (A : ℝ)) ^ A ≤ (((43 + A) ^ A + 2 : ℕ) : ℝ) := by
    push_cast
    norm_num
  have heq : (fun x => (if (x 0 : ZMod 3) = r 0 then (1 : ℂ) else 0) *
      (if (x 1 : ZMod 3) = r 1 then 1 else 0)) = pairThirdIndicator r := by
    funext x
    exact (pairThirdIndicator_product r x).symm
  rw [heq] at F
  exact ⟨F.mono hb⟩

theorem card_pairThird_le_exp : (Fintype.card (Fin 2 → ZMod 3) : ℝ) ≤ Real.exp 9 := by
  norm_num only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_ofNat]
  linarith [Real.add_one_le_exp (9 : ℝ)]

theorem NativeIntegerExpansion.exists_thirds_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} {f : (Fin 2 → ℤ) → ℂ}, 0 ≤ p →
      NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 p f →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((p + C) ^ C)
        (fun x => f (fun i => x i / 3))) := by
  obtain ⟨A, _, hresidue⟩ := exists_pairThirdIndicator_expansion
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A + 2 + Polynomial.C B) ^ B + 9)
  refine ⟨C, hC, ?_⟩
  intro p f hp E
  classical
  let t : ℝ := p + A + 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; have := Nat.cast_nonneg (α := ℝ) A; linarith
  have hAt : (A : ℝ) ≤ t := by dsimp [t]; linarith
  let P (r : Fin 2 → ZMod 3) := thirdsPolynomial (fun i => ((r i).val : ℤ))
  have hP (r : Fin 2 → ZMod 3) (i : Fin 2) :
      P r i ∈ weightedSupportLE (fun _ : Fin 2 => 1) 1 := thirdsPolynomial_support _ i
  let F (r : Fin 2 → ZMod 3) := E.substitutedValue (P r) (hP r)
  have hF (r : Fin 2 → ZMod 3) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2
      ((t + B) ^ B) (fun x => pairThirdIndicator r x * F r x)) :=
    hmul ht ((Classical.choice (hresidue r)).mono hAt)
      ((E.substituteExpansion (P r) (hP r)).mono hpt)
  have hcost : (∑ _ : Fin 2 → ZMod 3, ‖(1 : ℂ)‖) ≤ Real.exp 9 := by
    simpa using card_pairThird_le_exp
  let S := NativeIntegerExpansion.weightedSum (fun r => Classical.choice (hF r)) (fun _ => 1)
    (by norm_num : (0 : ℝ) ≤ 9) card_pairThird_le_exp hcost
  have heq : (fun x => ∑ r : Fin 2 → ZMod 3, (1 : ℂ) * (pairThirdIndicator r x * F r x)) =
      (fun x => f (fun i => x i / 3)) := by
    funext x
    let r : Fin 2 → ZMod 3 := fun i => (x i : ZMod 3)
    rw [Finset.sum_eq_single r]
    · simp only [pairThirdIndicator, r, ite_true, one_mul]
      apply E.substitutedValue_eq (P r) (hP r) x (fun i => x i / 3)
      exact thirdsPolynomial_eval _ x (fun i => (ZMod.val_intCast (x i)).symm)
    · intro a _ ha
      have hne : (fun i => (x i : ZMod 3)) ≠ a := fun h => ha h.symm
      simp only [pairThirdIndicator, hne, ite_false, zero_mul, mul_zero]
    · simp
  have hb : (t + B) ^ B + 9 ≤ (p + C) ^ C := by
    simpa [t, X, Polynomial.eval₂_pow] using hbudget p hp
  rw [heq] at S
  exact ⟨S.mono hb⟩

end Erdos3

end

end OAI
