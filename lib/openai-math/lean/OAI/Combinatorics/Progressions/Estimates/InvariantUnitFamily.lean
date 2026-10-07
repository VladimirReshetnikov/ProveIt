import OAI.Combinatorics.Progressions.Geometry.SymmetricEvaluationMetric

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def symmetricEvaluationRadius (m n : ℕ) : ℝ≥0 :=
  ⟨momentLowerConstant m / (n + 1 : ℝ) ^ m, by
    have := momentLowerConstant_pos m
    positivity⟩

theorem symmetricEvaluationRadius_pos (m n : ℕ) : 0 < symmetricEvaluationRadius m n := by
  change 0 < momentLowerConstant m / (n + 1 : ℝ) ^ m
  have := momentLowerConstant_pos m
  positivity

noncomputable def symmetricUnitFamilyLip (m n : ℕ) (K : ℝ≥0) : ℝ≥0 :=
  2 / symmetricEvaluationRadius m n *
    ((n ^ m * (m * m + 1) + 1 : ℝ≥0) * symmetricEvaluationLip m K)

theorem exists_symmetric_unit_family {m : ℕ} {I X : Type*} [Fintype I] [PseudoMetricSpace X]
    (f : Fin m → I → X → ℂ) {K : ℝ≥0}
    (hf : ∀ i j, LipschitzWith K (f i j))
    (hunit : ∀ i x, ∑ j, ‖f i j x‖ ^ 2 = 1) :
    ∃ g : SymmetricEvaluationIndex m I → X → ℂ,
      (∀ x, ∑ k, ‖g k x‖ ^ 2 = 1) ∧ (∀ k x, ‖g k x‖ ≤ 1) ∧
      (∀ k, LipschitzWith (symmetricUnitFamilyLip m (Fintype.card I) K) (g k)) ∧
      ∀ x y (c : ℂ) (e : Equiv.Perm (Fin m)), ‖c‖ = 1 →
        (∀ i j, f i j x = c * f (e i) j y) → ∀ k, g k x = c ^ m * g k y := by
  have hnorm (i j x) : ‖f i j x‖ ≤ 1 := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => ‖f i j x‖ ^ 2) (fun j _ => sq_nonneg ‖f i j x‖) (Finset.mem_univ j)
    rw [hunit] at h
    nlinarith [norm_nonneg (f i j x)]
  let u (k : SymmetricEvaluationIndex m I) (x : X) := symmetricEvaluation (fun i j => f i j x) k
  have hlower (x) : ∃ k, (symmetricEvaluationRadius m (Fintype.card I) : ℝ) ≤ ‖u k x‖ :=
    symmetricEvaluation_lower (fun i j => f i j x) (fun i => hunit i x)
  obtain ⟨g, hgunit, hgnorm, hglip, hgphase⟩ := exists_normalized_complex_family u
    (symmetricEvaluationRadius_pos m (Fintype.card I))
    (fun k => (symmetricEvaluation_metric f hf hnorm k).2) hlower
  refine ⟨g, hgunit, hgnorm, ?_, ?_⟩
  · intro k
    simpa only [symmetricUnitFamilyLip, symmetricEvaluationIndex_card,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hglip k
  · intro x y c e hc hxy k
    apply hgphase x y (c ^ m) (by rw [norm_pow, hc, one_pow]) _ k
    intro a
    change symmetricEvaluation (fun i j => f i j x) a =
      c ^ m * symmetricEvaluation (fun i j => f i j y) a
    simp_rw [hxy]
    rw [symmetricEvaluation_const_mul]
    exact congrArg (fun z => c ^ m * z)
      (congrFun (symmetricEvaluation_permute (fun i j => f i j y) e) a)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_invariant_unit_family {Γ I X : Type*} [Group Γ] [Fintype Γ]
    [Fintype I] [PseudoMetricSpace X] [MulAction Γ X]
    (f : I → X → ℂ) {K A : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j))
    (hunit : ∀ x, ∑ j, ‖f j x‖ ^ 2 = 1)
    (hact : ∀ a : Γ, LipschitzWith A (fun x : X => a • x)) :
    ∃ g : SymmetricEvaluationIndex (Fintype.card Γ) I → X → ℂ,
      (∀ x, ∑ k, ‖g k x‖ ^ 2 = 1) ∧ (∀ k x, ‖g k x‖ ≤ 1) ∧
      (∀ k, LipschitzWith
        (symmetricUnitFamilyLip (Fintype.card Γ) (Fintype.card I) (K * A)) (g k)) ∧
      (∀ a : Γ, ∀ k x, g k (a • x) = g k x) ∧
      ∀ x y (c : ℂ), ‖c‖ = 1 → (∀ a : Γ, ∀ j, f j (a • x) = c * f j (a • y)) →
        ∀ k, g k x = c ^ Fintype.card Γ * g k y := by
  classical
  let e := (Fintype.equivFin Γ).symm
  let F (i : Fin (Fintype.card Γ)) (j : I) (x : X) := f j (e i • x)
  obtain ⟨g, hgunit, hgnorm, hglip, hgphase⟩ := exists_symmetric_unit_family F
    (fun i j => (hf j).comp (hact (e i))) (fun i x => hunit (e i • x))
  refine ⟨g, hgunit, hgnorm, hglip, ?_, ?_⟩
  · intro a k x
    let ε : Equiv.Perm (Fin (Fintype.card Γ)) := e.trans ((Equiv.mulRight a).trans e.symm)
    have he (i) : e (ε i) = e i * a := by simp [ε]
    have h := hgphase (a • x) x 1 ε (by simp) (fun i j => by
      change f j (e i • (a • x)) = 1 * f j (e (ε i) • x)
      rw [he, mul_smul, one_mul]) k
    simpa only [one_pow, one_mul] using h
  · intro x y c hc hxy k
    exact hgphase x y c (Equiv.refl _) hc (fun i j => hxy (e i) j) k

end Erdos3

end

end OAI
