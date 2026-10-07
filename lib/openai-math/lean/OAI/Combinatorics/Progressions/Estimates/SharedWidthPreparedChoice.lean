import OAI.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality

namespace OAI

section

namespace Erdos3

theorem sharedWidthPreparedChoice {T : Type*} (width : T → ℝ) (Plate : ℝ)
    (hpositive : ∀ t, 0 < width t)
    (hreciprocal : ∀ t, (width t)⁻¹ ≤ Real.exp Plate) :
    let ξ := Real.exp (-Plate)
    0 < ξ ∧ ξ⁻¹ = Real.exp Plate ∧ ∀ t, ξ ≤ width t := by
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · simp only [Real.exp_neg, inv_inv]
  · intro t
    have h := (inv_le_inv₀ (Real.exp_pos Plate) (inv_pos.mpr (hpositive t))).2
      (hreciprocal t)
    simpa only [Real.exp_neg, inv_inv] using h

theorem sharedWidthPreparedChoice_le_one {Plate : ℝ} (hPlate : 0 ≤ Plate) :
    Real.exp (-Plate) ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hPlate)

theorem sharedWidthNormalizedTuplePreparedChoice {T G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X]
    (q M : T → ℕ) (selection : ∀ t, Fin (q t) ↪ G) (p E : T → ℝ) (Plate : ℝ)
    (hreciprocal : ∀ t,
      (normalizedTupleNarrowWidth X N (selection t) (M t) (p t) (E t))⁻¹ ≤
        Real.exp Plate) :
    let ξ := Real.exp (-Plate)
    0 < ξ ∧ ξ⁻¹ = Real.exp Plate ∧ ∀ t,
      ξ ≤ normalizedTupleNarrowWidth X N (selection t) (M t) (p t) (E t) := by
  exact sharedWidthPreparedChoice
    (fun t => normalizedTupleNarrowWidth X N (selection t) (M t) (p t) (E t)) Plate
    (fun t => normalizedTupleNarrowWidth_pos X N (selection t) (M t) (p t) (E t))
    hreciprocal

end Erdos3

end

end OAI
