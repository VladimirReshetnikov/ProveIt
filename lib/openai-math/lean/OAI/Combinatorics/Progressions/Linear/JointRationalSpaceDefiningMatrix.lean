import OAI.Combinatorics.Progressions.Estimates.JointRationalSpaceGenerators

namespace OAI

section

namespace Erdos3

open scoped Matrix

namespace VectorPolynomial

theorem exists_jointRationalSpace_defining_matrix {J C V : Type*}
    [Fintype J] [Fintype C] [Fintype V]
    (B : Matrix J C ℚ) (A : Matrix V J ℚ) {H R : ℕ}
    (hH : 1 ≤ H)
    (hB : ∀ i j, RationalHeightLE (B i j) H)
    (hA : ∀ v j, RationalHeightLE (A v j) R) :
    ∃ Q : Matrix (J ⊕ V) J ℚ,
      (∀ v j, RationalHeightLE (Q v j)
        (max (imageDefiningHeight (Fintype.card C) (Fintype.card J) H) R)) ∧
      LinearMap.ker (Matrix.of (fun v j => (Q v j : ℝ))).mulVecLin =
        jointRationalSpace B A := by
  obtain ⟨Q, hQ, hQker⟩ := exists_real_span_defining_matrix B hH hB
  let A' : Matrix (J ⊕ V) J ℚ :=
    Matrix.of (fun v j => Sum.elim (fun i => Q i j) (fun v => A v j) v)
  refine ⟨A', ?_, ?_⟩
  · intro v j
    cases v with
    | inl i => exact (hQ i j).mono (le_max_left _ _)
    | inr v => exact (hA v j).mono (le_max_right _ _)
  · ext x
    change LinearMap.ker (Matrix.of (fun i j => (Q i j : ℝ))).mulVecLin =
      LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin at hQker
    change (Matrix.of (fun v j => (A' v j : ℝ)) *ᵥ x = 0) ↔
      x ∈ LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin ∧
      Matrix.of (fun v j => (A v j : ℝ)) *ᵥ x = 0
    rw [← hQker]
    change (Matrix.of (fun v j => (A' v j : ℝ)) *ᵥ x = 0) ↔
      (Matrix.of (fun i j => (Q i j : ℝ)) *ᵥ x = 0) ∧
      Matrix.of (fun v j => (A v j : ℝ)) *ᵥ x = 0
    constructor
    · intro hx
      exact ⟨funext (fun i => congrFun hx (.inl i)),
        funext (fun v => congrFun hx (.inr v))⟩
    · rintro ⟨hQx, hAx⟩
      ext v
      cases v with
      | inl i => exact congrFun hQx i
      | inr v => exact congrFun hAx v

end VectorPolynomial

theorem jointSpaceDefiningHeight_le_exp (ambient columns H R : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (ha : (ambient : ℝ) ≤ p) (hc : (columns : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hR : (R : ℝ) ≤ Real.exp p) :
    ((max (imageDefiningHeight columns ambient H) R : ℕ) : ℝ) ≤
      Real.exp ((p+2)^10) := by
  rw [Nat.cast_max]
  exact max_le (imageDefiningHeight_le_exp columns ambient H hp hc ha hH)
    (hR.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide : 1 ≤ 10))))

end Erdos3

end

end OAI
