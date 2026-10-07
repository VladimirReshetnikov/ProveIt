import OAI.Combinatorics.Progressions.Estimates.SeparatedLabelExtension
import OAI.Combinatorics.Progressions.Fourier.ParametricQuarterTorusExtension

namespace OAI

section

namespace Erdos3

open scoped NNReal Classical

variable {A : Type*} [Fintype A] (q : A → ℕ) [∀ a, NeZero (q a)]

noncomputable def residueTuplePoint (r : ∀ a, ZMod (q a)) : A → AddCircle (1 : ℝ) :=
  fun a => ZMod.toAddCircle (r a)

theorem residueTuplePoint_separated (D : ℝ≥0) (hD : ∀ a, (q a : ℝ) ≤ D)
    {r s : ∀ a, ZMod (q a)} (hrs : r ≠ s) :
    (1 : ℝ) ≤ D * dist (residueTuplePoint q r) (residueTuplePoint q s) := by
  obtain ⟨a, ha⟩ := not_forall.mp (fun h : ∀ a, r a = s a => hrs (funext h))
  have h := CircleFourier.one_le_mul_dist_toAddCircle ha
  exact h.trans ((mul_le_mul_of_nonneg_right (hD a) dist_nonneg).trans
    (mul_le_mul_of_nonneg_left (dist_le_pi_dist (residueTuplePoint q r) (residueTuplePoint q s) a) D.coe_nonneg))

theorem exists_residue_tuple_extension {X : Type*} [PseudoMetricSpace X]
    (D L B : ℝ≥0) (hD : ∀ a, (q a : ℝ) ≤ D)
    (f : (∀ a, ZMod (q a)) → X → ℂ)
    (hf : ∀ r, LipschitzWith L (f r)) (hb : ∀ r x, ‖f r x‖ ≤ B) :
    ∃ g : (A → AddCircle (1 : ℝ)) × X → ℂ,
      LipschitzWith (2 * max L (2 * B * D)) g ∧
      (∀ r x, g (residueTuplePoint q r, x) = f r x) ∧ ∀ z, ‖g z‖ ≤ 2 * B :=
  exists_bounded_extension_on_separated_labels (residueTuplePoint q) D L B
    (fun _ _ h => residueTuplePoint_separated q D hD h) f hf hb

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_residue_quarter_extension {A D : Type*} [Fintype A] [Fintype D]
    (q : A → ℕ) [∀ a, NeZero (q a)] (V L : ℝ≥0) (hV : ∀ a, (q a : ℝ) ≤ V)
    (f : (∀ a, ZMod (q a)) → (D → ℝ) → ℂ)
    (hf : ∀ r, LipschitzWith L (f r)) (hb : ∀ r x, ‖f r x‖ ≤ 1) :
    ∃ g : (A → AddCircle (1 : ℝ)) × (D → AddCircle (1 : ℝ)) → ℂ,
      LipschitzWith (4 * max L (2 * V)) g ∧ (∀ z, ‖g z‖ ≤ 4) ∧
      ∀ r (v : D → ℝ), (∀ i, |v i| ≤ 1 / 4) →
        g (residueTuplePoint q r, fun i => (v i : AddCircle (1 : ℝ))) = f r v := by
  obtain ⟨F, hF, hFeq, hFb⟩ := exists_residue_tuple_extension q V L 1 hV f hf hb
  have hF' : LipschitzWith (2 * max L (2 * V)) F := by simpa only [mul_one] using hF
  have hFb' : ∀ z, ‖F z‖ ≤ (2 : ℝ≥0) := by simpa using hFb
  obtain ⟨g, hg, hgb, hgeq⟩ := exists_parametric_quarter_torus_extension F
    (2 * max L (2 * V)) 2 hF' hFb'
  refine ⟨g, ?_, ?_, ?_⟩
  · convert hg using 1
    ring
  · convert hgb using 1
    norm_num
  · intro r v hv
    exact (hgeq (residueTuplePoint q r) v hv).trans (hFeq r v)

end Erdos3

end

end OAI
