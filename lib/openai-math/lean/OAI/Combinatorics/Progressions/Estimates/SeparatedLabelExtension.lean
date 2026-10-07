import OAI.Combinatorics.Progressions.Estimates.LipschitzExtensionAlongMap
import OAI.Combinatorics.Progressions.Lattices.CircleResiduePartition

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_bounded_extension_on_separated_labels
    {A Y X : Type*} [PseudoMetricSpace Y] [PseudoMetricSpace X]
    (embed : A → Y) (D L B : ℝ≥0)
    (hsep : ∀ a b, a ≠ b → (1 : ℝ) ≤ D * dist (embed a) (embed b))
    (f : A → X → ℂ) (hf : ∀ a, LipschitzWith L (f a))
    (hb : ∀ a x, ‖f a x‖ ≤ B) :
    ∃ g : Y × X → ℂ, LipschitzWith (2 * max L (2 * B * D)) g ∧
      (∀ a x, g (embed a, x) = f a x) ∧ ∀ z, ‖g z‖ ≤ 2 * B := by
  classical
  let S : Set (Y × X) := {z | z.1 ∈ Set.range embed}
  let label (z : S) : A := Classical.choose z.property
  have hlabel (z : S) : embed (label z) = z.val.1 := Classical.choose_spec z.property
  let F : S → ℂ := fun z => f (label z) z.val.2
  let K : ℝ≥0 := max L (2 * B * D)
  have hLK : (L : ℝ) ≤ K := by exact_mod_cast le_max_left L (2 * B * D)
  have hDK : (2 * B * D : ℝ≥0) ≤ K := le_max_right _ _
  have hF : LipschitzWith K F := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    have hY : dist z.val.1 w.val.1 ≤ dist z w := by
      change dist z.val.1 w.val.1 ≤ max (dist z.val.1 w.val.1) (dist z.val.2 w.val.2)
      exact le_max_left _ _
    have hX : dist z.val.2 w.val.2 ≤ dist z w := by
      change dist z.val.2 w.val.2 ≤ max (dist z.val.1 w.val.1) (dist z.val.2 w.val.2)
      exact le_max_right _ _
    by_cases h : label z = label w
    · have he : dist (F z) (F w) ≤ (L : ℝ) * dist z.val.2 w.val.2 := by
        simpa only [F, h] using (hf (label w)).dist_le_mul z.val.2 w.val.2
      exact he.trans ((mul_le_mul_of_nonneg_left hX L.coe_nonneg).trans
        (mul_le_mul_of_nonneg_right hLK dist_nonneg))
    · have hs := hsep (label z) (label w) h
      rw [hlabel z, hlabel w] at hs
      have hs' : (1 : ℝ) ≤ D * dist z w :=
        hs.trans (mul_le_mul_of_nonneg_left hY D.coe_nonneg)
      have hnorm : dist (F z) (F w) ≤ 2 * (B : ℝ) := by
        rw [dist_eq_norm]
        exact (norm_sub_le _ _).trans ((add_le_add (hb (label z) z.val.2)
          (hb (label w) w.val.2)).trans_eq (two_mul (B : ℝ)).symm)
      calc
        _ ≤ 2 * (B : ℝ) := hnorm
        _ ≤ (2 * (B : ℝ)) * (D * dist z w) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ 2 * (B : ℝ))
        _ = ((2 * B * D : ℝ≥0) : ℝ) * dist z w := by
          simp only [NNReal.coe_mul, NNReal.coe_ofNat]
          ring
        _ ≤ (K : ℝ) * dist z w := mul_le_mul_of_nonneg_right (by exact_mod_cast hDK) dist_nonneg
  obtain ⟨g, hg, heq, hgB⟩ := exists_complex_extension_from_subset S F K B hF
    (fun z => hb (label z) z.val.2)
  refine ⟨g, hg, ?_, hgB⟩
  intro a x
  let z : S := ⟨(embed a, x), ⟨a, rfl⟩⟩
  have ha : label z = a := by
    by_contra h
    have hs := hsep (label z) a h
    rw [hlabel z] at hs
    change (1 : ℝ) ≤ D * dist (embed a) (embed a) at hs
    simp only [dist_self, mul_zero] at hs
    norm_num at hs
  simpa only [F, ha, z] using heq z

theorem exists_residue_real_extension {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ → ℂ) (L : ℝ≥0)
    (hf : ∀ r, LipschitzWith L (f r)) (hb : ∀ r x, ‖f r x‖ ≤ 1) :
    ∃ g : AddCircle (1 : ℝ) × ℝ → ℂ,
      LipschitzWith (2 * max L (2 * (q : ℝ≥0))) g ∧
      (∀ r x, g (ZMod.toAddCircle r, x) = f r x) ∧ ∀ z, ‖g z‖ ≤ 2 := by
  simpa using exists_bounded_extension_on_separated_labels
    (fun r : ZMod q => ZMod.toAddCircle r) (q : ℝ≥0) L 1
    (fun r s hrs => by exact_mod_cast CircleFourier.one_le_mul_dist_toAddCircle hrs) f hf hb

end Erdos3

end

end OAI
