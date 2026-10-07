import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y : Type*} [Nonempty X] [PseudoMetricSpace Y]
  (φ : X → Y) (L : ℝ≥0)

noncomputable def mcShaneEnvelope (f : X → ℝ) (y : Y) : ℝ :=
  ⨅ x, f x + L * dist y (φ x)

omit [Nonempty X] in
theorem mcShaneEnvelope_bddBelow (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (y : Y) :
    BddBelow (Set.range (fun x => f x + L * dist y (φ x))) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact add_nonneg (hf x) (mul_nonneg L.coe_nonneg dist_nonneg)

theorem mcShaneEnvelope_nonneg (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (y : Y) :
    0 ≤ mcShaneEnvelope φ L f y :=
  le_ciInf (fun x => add_nonneg (hf x) (mul_nonneg L.coe_nonneg dist_nonneg))

omit [Nonempty X] in
theorem mcShaneEnvelope_le (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (y : Y) (x : X) :
    mcShaneEnvelope φ L f y ≤ f x + L * dist y (φ x) :=
  ciInf_le (mcShaneEnvelope_bddBelow φ L f hf y) x

theorem mcShaneEnvelope_lipschitz (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    LipschitzWith L (mcShaneEnvelope φ L f) := by
  apply LipschitzWith.of_le_add_mul
  intro y z
  rw [← sub_le_iff_le_add]
  apply le_ciInf
  intro x
  rw [sub_le_iff_le_add]
  calc
    mcShaneEnvelope φ L f y ≤ f x + L * dist y (φ x) := mcShaneEnvelope_le φ L f hf y x
    _ ≤ f x + L * dist z (φ x) + L * dist y z := by
      have h := mul_le_mul_of_nonneg_left (dist_triangle y z (φ x)) L.coe_nonneg
      linarith

theorem mcShaneEnvelope_eq (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hLip : ∀ x z, |f x - f z| ≤ L * dist (φ x) (φ z)) (x : X) :
    mcShaneEnvelope φ L f (φ x) = f x := by
  apply le_antisymm
  · simpa only [dist_self, mul_zero, add_zero] using mcShaneEnvelope_le φ L f hf (φ x) x
  · apply le_ciInf
    intro z
    have h := (le_abs_self (f x - f z)).trans (hLip x z)
    linarith

theorem mcShaneEnvelope_le_add (f g : X → ℝ) (hf : ∀ x, 0 ≤ f x) {δ : ℝ}
    (hfg : ∀ x, f x ≤ g x + δ) (y : Y) :
    mcShaneEnvelope φ L f y ≤ mcShaneEnvelope φ L g y + δ := by
  rw [← sub_le_iff_le_add]
  apply le_ciInf
  intro x
  have h := mcShaneEnvelope_le φ L f hf y x
  linarith [hfg x]

theorem mcShaneEnvelope_abs_sub_le (f g : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) {δ : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ δ) (y : Y) :
    |mcShaneEnvelope φ L f y - mcShaneEnvelope φ L g y| ≤ δ := by
  apply abs_le.mpr
  constructor
  · have h := mcShaneEnvelope_le_add φ L g f hg
      (fun x => by have hx := (abs_le.mp (hfg x)).1; linarith) y
    linarith
  · have h := mcShaneEnvelope_le_add φ L f g hf
      (fun x => by have hx := (abs_le.mp (hfg x)).2; linarith) y
    linarith

end Erdos3

end

end OAI
