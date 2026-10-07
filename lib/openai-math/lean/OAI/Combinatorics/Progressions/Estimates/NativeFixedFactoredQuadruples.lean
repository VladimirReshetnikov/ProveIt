import OAI.Combinatorics.Progressions.Geometry.NativeQuadrupleCoordinates

namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def selectedMixed (h : W.shifts) (x : ZMod N) : ℂ :=
  W.mixed.evalCyclic N (W.selectedWitness h).coordinate.1 (correlationInput h.val x)

noncomputable def selectedRank (h : W.shifts) (x : ZMod N) : ℂ :=
  W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x

noncomputable def selectedLower (h : W.shifts) (x : ZMod N) : ℂ :=
  (W.selectedWitness h).test.evalCyclic N (fun _ => x)

theorem selectedProduct_eq (h : W.shifts) (x : ZMod N) :
    W.selectedProduct h x = W.selectedMixed h x * W.selectedRank h x * W.selectedLower h x := rfl

theorem selectedProduct_fourPoint_factorization (h₁ h₂ h₃ h₄ : W.shifts) (a x : ZMod N) :
    fourPointProduct (W.selectedProduct h₁) (W.selectedProduct h₂)
      (W.selectedProduct h₃) (W.selectedProduct h₄) a x =
      fourPointProduct (W.selectedMixed h₁) (W.selectedMixed h₂)
        (W.selectedMixed h₃) (W.selectedMixed h₄) a x *
      fourPointProduct (W.selectedRank h₁) (W.selectedRank h₂)
        (W.selectedRank h₃) (W.selectedRank h₄) a x *
      fourPointProduct (W.selectedLower h₁) (W.selectedLower h₂)
        (W.selectedLower h₃) (W.selectedLower h₄) a x := by
  simp only [fourPointProduct, W.selectedProduct_eq, star_mul]
  ring

theorem selectedCorrelator_quadruple_factored (a h k : ZMod N)
    (h₁ : h ∈ W.shifts) (h₂ : h - a ∈ W.shifts)
    (h₃ : k ∈ W.shifts) (h₄ : k - a ∈ W.shifts) :
    additiveQuadrupleCorrelation W.selectedCorrelator a h k =
      ‖𝔼 x,
        fourPointProduct (W.selectedMixed ⟨h, h₁⟩) (W.selectedMixed ⟨h - a, h₂⟩)
          (W.selectedMixed ⟨k, h₃⟩) (W.selectedMixed ⟨k - a, h₄⟩) a x *
        fourPointProduct (W.selectedRank ⟨h, h₁⟩) (W.selectedRank ⟨h - a, h₂⟩)
          (W.selectedRank ⟨k, h₃⟩) (W.selectedRank ⟨k - a, h₄⟩) a x *
        fourPointProduct (W.selectedLower ⟨h, h₁⟩) (W.selectedLower ⟨h - a, h₂⟩)
          (W.selectedLower ⟨k, h₃⟩) (W.selectedLower ⟨k - a, h₄⟩) a x‖ := by
  unfold additiveQuadrupleCorrelation
  congr 1
  apply Finset.expect_congr rfl
  intro x _
  rw [W.selectedCorrelator_of_mem h h₁, W.selectedCorrelator_of_mem (h - a) h₂,
    W.selectedCorrelator_of_mem k h₃, W.selectedCorrelator_of_mem (k - a) h₄]
  exact W.selectedProduct_fourPoint_factorization ⟨h, h₁⟩ ⟨h - a, h₂⟩ ⟨k, h₃⟩ ⟨k - a, h₄⟩ a x

theorem exists_factored_correlation_quadruples (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
      Real.exp (-((p + 3) ^ 3)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, ∃ (h₁ : t.2.1 ∈ W.shifts) (h₂ : t.2.1 - t.1 ∈ W.shifts)
        (h₃ : t.2.2 ∈ W.shifts) (h₄ : t.2.2 - t.1 ∈ W.shifts),
        Real.exp (-((p + 3) ^ 3)) ≤
          ‖𝔼 x,
            fourPointProduct (W.selectedMixed ⟨t.2.1, h₁⟩) (W.selectedMixed ⟨t.2.1 - t.1, h₂⟩)
              (W.selectedMixed ⟨t.2.2, h₃⟩) (W.selectedMixed ⟨t.2.2 - t.1, h₄⟩) t.1 x *
            fourPointProduct (W.selectedRank ⟨t.2.1, h₁⟩) (W.selectedRank ⟨t.2.1 - t.1, h₂⟩)
              (W.selectedRank ⟨t.2.2, h₃⟩) (W.selectedRank ⟨t.2.2 - t.1, h₄⟩) t.1 x *
            fourPointProduct (W.selectedLower ⟨t.2.1, h₁⟩) (W.selectedLower ⟨t.2.1 - t.1, h₂⟩)
              (W.selectedLower ⟨t.2.2, h₃⟩) (W.selectedLower ⟨t.2.2 - t.1, h₄⟩) t.1 x‖ := by
  obtain ⟨Q, hQ, hdense, hcorr⟩ := W.exists_selected_correlator_quadruples_budget hf
  refine ⟨Q, hQ, hdense, ?_⟩
  intro t ht
  obtain ⟨h₁, h₂, h₃, h₄, hc⟩ := hcorr t ht
  refine ⟨h₁, h₂, h₃, h₄, ?_⟩
  rwa [W.selectedCorrelator_quadruple_factored t.1 t.2.1 t.2.2 h₁ h₂ h₃ h₄] at hc

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

theorem exists_fixed_factored_correlation_quadruples (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ (coordinate : Bool × Bool → Fin W.mixed.outputDim × Fin W.family.outputDim)
      (Q : Finset (ZMod N × ZMod N × ZMod N)), Q.Nonempty ∧
      Real.exp (-((p + 3) ^ 3 + 8 * p)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      (∀ t ∈ Q, ∀ i : Bool × Bool,
        ∃ hi : additiveQuadrupleShift t.1 t.2.1 t.2.2 i ∈ W.shifts,
          (W.selectedWitness ⟨additiveQuadrupleShift t.1 t.2.1 t.2.2 i, hi⟩).coordinate = coordinate i) ∧
      ∀ t ∈ Q, ∃ (h₁ : t.2.1 ∈ W.shifts) (h₂ : t.2.1 - t.1 ∈ W.shifts)
        (h₃ : t.2.2 ∈ W.shifts) (h₄ : t.2.2 - t.1 ∈ W.shifts),
        Real.exp (-((p + 3) ^ 3)) ≤
          ‖𝔼 x,
            fourPointProduct (W.selectedMixed ⟨t.2.1, h₁⟩) (W.selectedMixed ⟨t.2.1 - t.1, h₂⟩)
              (W.selectedMixed ⟨t.2.2, h₃⟩) (W.selectedMixed ⟨t.2.2 - t.1, h₄⟩) t.1 x *
            fourPointProduct (W.selectedRank ⟨t.2.1, h₁⟩) (W.selectedRank ⟨t.2.1 - t.1, h₂⟩)
              (W.selectedRank ⟨t.2.2, h₃⟩) (W.selectedRank ⟨t.2.2 - t.1, h₄⟩) t.1 x *
            fourPointProduct (W.selectedLower ⟨t.2.1, h₁⟩) (W.selectedLower ⟨t.2.1 - t.1, h₂⟩)
              (W.selectedLower ⟨t.2.2, h₃⟩) (W.selectedLower ⟨t.2.2 - t.1, h₄⟩) t.1 x‖ := by
  obtain ⟨coordinate, Q, hQ, hdense, hfixed, hcorr⟩ := W.exists_fixed_coordinate_quadruples hf
  refine ⟨coordinate, Q, hQ, hdense, hfixed, ?_⟩
  intro t ht
  obtain ⟨h₁, _⟩ := hfixed t ht (false, false)
  obtain ⟨h₂, _⟩ := hfixed t ht (false, true)
  obtain ⟨h₃, _⟩ := hfixed t ht (true, false)
  obtain ⟨h₄, _⟩ := hfixed t ht (true, true)
  have hh₁ : t.2.1 ∈ W.shifts := by simpa [additiveQuadrupleShift] using h₁
  have hh₂ : t.2.1 - t.1 ∈ W.shifts := by simpa [additiveQuadrupleShift] using h₂
  have hh₃ : t.2.2 ∈ W.shifts := by simpa [additiveQuadrupleShift] using h₃
  have hh₄ : t.2.2 - t.1 ∈ W.shifts := by simpa [additiveQuadrupleShift] using h₄
  refine ⟨hh₁, hh₂, hh₃, hh₄, ?_⟩
  have hc := hcorr t ht
  rwa [W.selectedCorrelator_quadruple_factored t.1 t.2.1 t.2.2 hh₁ hh₂ hh₃ hh₄] at hc

end Erdos3.NativeCorrelationStructure

end

end OAI
