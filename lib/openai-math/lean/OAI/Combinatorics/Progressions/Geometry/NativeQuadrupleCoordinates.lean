import OAI.Combinatorics.Progressions.Dynamics.NativeCorrelationQuadrupleBudget

namespace OAI

section

namespace Erdos3

def additiveQuadrupleShift {G : Type*} [AddGroup G] (a h k : G) (i : Bool × Bool) : G :=
  (if i.1 then k else h) - (if i.2 then a else 0)

namespace NativeCorrelationStructure

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

theorem selectedCoordinate_card_bound :
    (Fintype.card (Fin W.mixed.outputDim × Fin W.family.outputDim) : ℝ) ≤ Real.exp (2 * p) := by
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  calc
    _ ≤ Real.exp p * Real.exp p := mul_le_mul W.mixed.output_bound W.family.output_bound
      (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem exists_fixed_coordinate_quadruples (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ (coordinate : Bool × Bool → Fin W.mixed.outputDim × Fin W.family.outputDim)
      (Q : Finset (ZMod N × ZMod N × ZMod N)), Q.Nonempty ∧
      Real.exp (-((p + 3) ^ 3 + 8 * p)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      (∀ t ∈ Q, ∀ i : Bool × Bool,
        ∃ hi : additiveQuadrupleShift t.1 t.2.1 t.2.2 i ∈ W.shifts,
          (W.selectedWitness ⟨additiveQuadrupleShift t.1 t.2.1 t.2.2 i, hi⟩).coordinate = coordinate i) ∧
      ∀ t ∈ Q, Real.exp (-((p + 3) ^ 3)) ≤
        additiveQuadrupleCorrelation W.selectedCorrelator t.1 t.2.1 t.2.2 := by
  classical
  obtain ⟨Q, hQ, hdense, hcorr⟩ := W.exists_selected_correlator_quadruples_budget hf
  have hmem (t) (ht : t ∈ Q) (i : Bool × Bool) :
      additiveQuadrupleShift t.1 t.2.1 t.2.2 i ∈ W.shifts := by
    obtain ⟨h₁, h₂, h₃, h₄, _⟩ := hcorr t ht
    rcases i with ⟨b, c⟩
    cases b <;> cases c
    · simpa only [additiveQuadrupleShift, Bool.false_eq_true, ite_false, sub_zero] using h₁
    · simpa only [additiveQuadrupleShift, Bool.false_eq_true, ite_false, ite_true] using h₂
    · simpa only [additiveQuadrupleShift, Bool.false_eq_true, ite_false, ite_true, sub_zero] using h₃
    · simpa only [additiveQuadrupleShift, ite_true] using h₄
  let rel (t : ZMod N × ZMod N × ZMod N) (i : Bool × Bool)
      (j : Fin W.mixed.outputDim × Fin W.family.outputDim) : Prop :=
    ∃ hi : additiveQuadrupleShift t.1 t.2.1 t.2.2 i ∈ W.shifts,
      (W.selectedWitness ⟨additiveQuadrupleShift t.1 t.2.1 t.2.2 i, hi⟩).coordinate = j
  have hchoice : ∀ t ∈ Q, ∀ i, ∃ j, rel t i j := by
    intro t ht i
    exact ⟨_, hmem t ht i, rfl⟩
  obtain ⟨coordinate, S, hsub, hS, hsize, hfixed⟩ := exists_large_fixed_choices Q hQ rel hchoice
    W.selectedCoordinate_card_bound
  have hsize' : Real.exp (-(8 * p)) * (Q.card : ℝ) ≤ (S.card : ℝ) := by
    have hcard : (Fintype.card (Bool × Bool) : ℝ) = 4 := by norm_num
    rw [hcard, show -(2 * p) * 4 = -(8 * p) by ring] at hsize
    exact hsize
  refine ⟨coordinate, S, hS, ?_, hfixed, fun t ht => (hcorr t (hsub ht)).2.2.2.2⟩
  calc
    _ = Real.exp (-(8 * p)) * (Real.exp (-((p + 3) ^ 3)) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-(8 * p)) * (Q.card : ℝ) :=
      mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
    _ ≤ _ := hsize'

end NativeCorrelationStructure

end Erdos3

end

end OAI
