import GowersSzemeredi.Proofs16AllScaleCoverTransfer

/-! All-box multiple multilinearity from cubic slice controls.
Package the uniform large-box affine lift and cap its exponent to cover
short boxes as well. The resulting control functions are explicit; no
comparison to the manuscript's prescribed control functions is asserted.

`Section16AllBoxLineCoversWith.cubic_large_box_profile`,
`Section16AllBoxLineCoversWith.cubic_multiplyLinearWith`,
`section16CubicLiftExponent`, `section16CubicLiftExponent_pos`,
`section16CubicLiftGraphBound` and `section16CubicLiftThreshold` are in
`Proofs16CubicAllScaleCoverSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem partialGraph_fiber_card_le_one {N k : Nat}
    (B : Finset (Point N k)) (phi : Point N k → ZMod N) (x : Point N k) :
    ((partialGraph B phi).filter fun z => z.1 = x).card ≤ 1 := by
  have hsub : (partialGraph B phi).filter (fun z => z.1 = x) ⊆ {(x, phi x)} := by
    intro z hz
    obtain ⟨hz, hx⟩ := Finset.mem_filter.mp hz
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
    change y = x at hx
    subst y
    simp
  simpa using Finset.card_le_card hsub

end LeanProofs.GowersSzemeredi
