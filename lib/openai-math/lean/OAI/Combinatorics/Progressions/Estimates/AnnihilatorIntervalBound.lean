import OAI.Combinatorics.Progressions.Lattices.AnnihilatingCoordinateResidue
import OAI.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost

namespace OAI

section

namespace Erdos3

theorem annihilatorInterval_card_le {I : Type*} [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (v : I → ℤ) (i : I)
    (hi : 0 < orderOf (latticeCharacterCoordinates χ i)) (a b : ℤ) (hab : a ≤ b) :
    ((Finset.filter (fun x => χ (Function.update v i x) = 1) (Finset.Ico a b)).card : ℝ) ≤
      ((b - a : ℤ) : ℝ) / orderOf (latticeCharacterCoordinates χ i) + 1 := by
  classical
  obtain ⟨r, hr⟩ := annihilating_coordinate_residue χ v i
  have hsub : Finset.filter (fun x => χ (Function.update v i x) = 1) (Finset.Ico a b) ⊆
      Finset.filter (fun x => x ≡ r [ZMOD (orderOf (latticeCharacterCoordinates χ i) : ℤ)])
        (Finset.Ico a b) := by
    intro x hx
    obtain ⟨hxb, hχx⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxb, hr x hχx⟩
  have hc : ((Finset.filter (fun x => χ (Function.update v i x) = 1) (Finset.Ico a b)).card : ℝ) ≤
      (Finset.filter (fun x => x ≡ r [ZMOD (orderOf (latticeCharacterCoordinates χ i) : ℤ)])
        (Finset.Ico a b)).card := by exact_mod_cast Finset.card_le_card hsub
  exact hc.trans (by
    simpa only [Int.cast_natCast] using scalarResidue_card_real_le a b
      (orderOf (latticeCharacterCoordinates χ i) : ℤ) r hab (by exact_mod_cast hi))

theorem annihilatorInterval_probability_le {I : Type*} [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (v : I → ℤ) (i : I)
    (hi : 0 < orderOf (latticeCharacterCoordinates χ i)) (a b : ℤ) (hab : a < b) :
    ((Finset.filter (fun x => χ (Function.update v i x) = 1) (Finset.Ico a b)).card : ℝ) /
        ((b - a : ℤ) : ℝ) ≤
      1 / (orderOf (latticeCharacterCoordinates χ i) : ℝ) + 1 / ((b - a : ℤ) : ℝ) := by
  have hlen : (0 : ℝ) < (b - a : ℤ) := by exact_mod_cast sub_pos.mpr hab
  have hd : (0 : ℝ) < orderOf (latticeCharacterCoordinates χ i) := by exact_mod_cast hi
  apply (div_le_div_of_nonneg_right (annihilatorInterval_card_le χ v i hi a b hab.le) hlen.le).trans_eq
  field_simp

theorem exists_annihilating_coordinate_bound {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (χ : AddChar (I → ℤ) ℂ) (hχ : 0 < orderOf χ) :
    ∃ i, ∀ (v : I → ℤ) (a b : ℤ), a < b →
      ((Finset.filter (fun x => χ (Function.update v i x) = 1) (Finset.Ico a b)).card : ℝ) /
          ((b - a : ℤ) : ℝ) ≤
        1 / (orderOf χ : ℝ) ^ (1 / (Fintype.card I : ℝ)) + 1 / ((b - a : ℤ) : ℝ) := by
  obtain ⟨i, hi, hroot⟩ := exists_coordinate_order_rpow_ge χ hχ
  refine ⟨i, fun v a b hab => ?_⟩
  apply (annihilatorInterval_probability_le χ v i hi a b hab).trans
  exact add_le_add
    (one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hχ) _) hroot) le_rfl

end Erdos3

end

end OAI
