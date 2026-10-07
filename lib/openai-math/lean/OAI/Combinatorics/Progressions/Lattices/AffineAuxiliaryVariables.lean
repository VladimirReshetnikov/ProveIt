import OAI.Combinatorics.Progressions.Estimates.UnitCoefficientSourceMarginal

namespace OAI

section

namespace Erdos3

noncomputable def affineCoefficientAllowance (c w : ℝ) : ℝ := 1+|c|+|w|

noncomputable def normalizedAffineParameter (c w r : ℝ) : ℝ :=
  (c+w*r)/affineCoefficientAllowance c w

theorem affineCoefficientAllowance_pos (c w : ℝ) : 0 < affineCoefficientAllowance c w := by
  unfold affineCoefficientAllowance
  positivity

theorem normalizedAffineParameter_identity (c w r : ℝ) :
    affineCoefficientAllowance c w*normalizedAffineParameter c w r = c+w*r := by
  unfold normalizedAffineParameter
  field_simp [(affineCoefficientAllowance_pos c w).ne']

theorem normalizedAffineParameter_abs_le (c w r : ℝ) (hr : |r| ≤ 1) :
    |normalizedAffineParameter c w r| ≤ 1 := by
  rw [normalizedAffineParameter, abs_div, abs_of_pos (affineCoefficientAllowance_pos c w)]
  apply (div_le_one (affineCoefficientAllowance_pos c w)).mpr
  calc
    |c+w*r| ≤ |c|+|w*r| := abs_add_le _ _
    _ = |c|+|w| * |r| := by rw [abs_mul]
    _ ≤ |c|+|w| := by nlinarith [abs_nonneg w]
    _ ≤ affineCoefficientAllowance c w := by unfold affineCoefficientAllowance; linarith

theorem affineParameter_abs_upper (c w r : ℝ) (hr : |r| ≤ 1) : |c+w*r| ≤ |c|+|w| := by
  calc
    _ ≤ |c|+|w*r| := abs_add_le _ _
    _ = |c|+|w| * |r| := by rw [abs_mul]
    _ ≤ _ := by nlinarith [abs_nonneg w]

theorem affineParameter_abs_lower (c w r : ℝ) (hr : |r| ≤ 1) : |c|-|w| ≤ |c+w*r| := by
  have h := abs_add_le (c+w*r) (-(w*r))
  have hb : |w*r| ≤ |w| := by rw [abs_mul]; nlinarith [abs_nonneg w]
  simp only [add_neg_cancel_right, abs_neg] at h
  linarith

end Erdos3

end

section

namespace Erdos3

abbrev AffineAuxiliaryIndex (Z : Type*) {D : Type*} (C : D → Type*) := Z ⊕ (Σ d, C d)

noncomputable def affineAuxiliaryVariables {Z D : Type*} {C : D → Type*}
    (c w : ∀ d, C d → ℝ) (z : Z → ℝ) (r : ∀ d, C d → ℝ) : AffineAuxiliaryIndex Z C → ℝ :=
  Sum.elim z (fun j => normalizedAffineParameter (c j.1 j.2) (w j.1 j.2) (r j.1 j.2))

def affineAuxiliaryCoefficient {Z D : Type*} {C : D → Type*} (d : D) (j : C d) :
    AffineAuxiliaryIndex Z C := Sum.inr ⟨d, j⟩

def affineAuxiliaryExtra {Z D G α : Type*} {C : D → Type*}
    (extra : G → Option α → Z) (g : G) (a : Option α) : AffineAuxiliaryIndex Z C :=
  Sum.inl (extra g a)

theorem affineAuxiliaryVariables_coefficient {Z D : Type*} {C : D → Type*}
    (c w : ∀ d, C d → ℝ) (z : Z → ℝ) (r : ∀ d, C d → ℝ) (d : D) (j : C d) :
    affineCoefficientAllowance (c d j) (w d j) *
      affineAuxiliaryVariables c w z r (affineAuxiliaryCoefficient d j) = c d j+w d j*r d j :=
  normalizedAffineParameter_identity _ _ _

theorem affineAuxiliaryVariables_abs_le {Z D : Type*} {C : D → Type*}
    (c w : ∀ d, C d → ℝ) (z : Z → ℝ) (r : ∀ d, C d → ℝ)
    (hz : ∀ a, |z a| ≤ 1) (hr : ∀ d j, |r d j| ≤ 1) :
    ∀ a, |affineAuxiliaryVariables c w z r a| ≤ 1 := by
  intro a
  cases a with
  | inl a => exact hz a
  | inr j => exact normalizedAffineParameter_abs_le _ _ _ (hr j.1 j.2)

theorem affineAuxiliaryVariables_measurable {Ω Z D : Type*} [MeasurableSpace Ω] {C : D → Type*}
    (c w : ∀ d, C d → ℝ) (z : Ω → Z → ℝ) (r : Ω → ∀ d, C d → ℝ)
    (hz : ∀ a, Measurable (fun ω => z ω a)) (hr : ∀ d j, Measurable (fun ω => r ω d j)) :
    ∀ a, Measurable (fun ω => affineAuxiliaryVariables c w (z ω) (r ω) a) := by
  intro a
  cases a with
  | inl a => exact hz a
  | inr j =>
    change Measurable (fun ω => (c j.1 j.2+w j.1 j.2*r ω j.1 j.2)/affineCoefficientAllowance (c j.1 j.2) (w j.1 j.2))
    fun_prop

theorem normalizedCubeTuple_affineAuxiliary {Z D G α : Type*} [Fintype α] [DecidableEq α]
    {B C : D → Type*} (h : D → ℕ) (extra : G → Option α → Z)
    (c w : ∀ d, C d → ℝ) (z : Z → ℝ) (r : ∀ d, C d → ℝ)
    (x : JointBlockParameter B h α → ℝ) (t : Finset α) (k : SamplerTupleIndex G B h) :
    normalizedCubeTuple (canonicalTupleInput (affineAuxiliaryExtra (C := C) extra))
      (affineAuxiliaryVariables c w z r) x t k = normalizedCubeTuple (canonicalTupleInput extra) z x t k := by
  cases k <;> rfl

theorem rawCanonicalCubeTuple_affineAuxiliary {Z D G α : Type*} [Fintype α] [DecidableEq α]
    {B C : D → Type*} (h : D → ℕ) (extra : G → Option α → Z) (T : SamplerTupleIndex G B h → ℝ)
    (c w : ∀ d, C d → ℝ) (z : Z → ℝ) (r : ∀ d, C d → ℝ) (x : JointBlockParameter B h α → ℝ) :
    rawCanonicalCubeTuple (affineAuxiliaryExtra (C := C) extra) T (affineAuxiliaryVariables c w z r) x =
      rawCanonicalCubeTuple extra T z x := by
  funext t k
  cases k <;> rfl

end Erdos3

end

end OAI
