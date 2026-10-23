import DiophantineConsistency.FreeCarrierRatio

open DiophantineConsistency.FreeCarrierRatio

/-- A valid primitive assignment with the smallest free carrier and negative Q. -/
private def smallCarrier : FreeVars := ⟨1,1,4,1,1,0⟩

example : (smallCarrier.base 8 8 1 0 32).C=1 := by decide
example : (smallCarrier.base 8 8 1 0 32).Q = -18 := by decide
example : 0<smallCarrier.Qstar 8 8 1 0 32 := by decide
example : smallCarrier.margin 8 8 1 0 32 1 ≤ 0 := by decide

example : Bounds (smallCarrier.base 8 8 1 0 32) (smallCarrier.H 8 8 1 0 32)
    (smallCarrier.k 8 8 1 0 32) :=
  register_bounds smallCarrier (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- No positive final witness is spuriously admitted at this negative margin. -/
example (n : ℕ) (hn : 0<n) : smallCarrier.finalValue 8 8 1 0 32 1 n ≠ 0 := by
  intro hz
  have hc := (exists_finalValue_zero_iff_conditions smallCarrier (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mp ⟨n,hn,hz⟩
  have hm : smallCarrier.margin 8 8 1 0 32 1 ≤ 0 := by decide
  have hpos := hc.2.2.2
  omega

private def oldBoundary : DiophantineConsistency.NativeNineRatio52.NewVars := ⟨1,1,1,0,1,0⟩

/-- The existing phi=0,j=0 boundary is preserved by the explicit carrier map. -/
example : (FreeVars.ofRatio oldBoundary 8 1).toRatio 8 1 = oldBoundary := by decide
example : (FreeVars.ofRatio oldBoundary 8 1).H 8 8 1 0 32 = oldBoundary.Hnew 8 8 1 0 32 :=
  FreeVars.H_ofRatio oldBoundary 8 8 1 0 32

example : 8*smallCarrier.margin 8 8 1 0 32 1 = smallCarrier.oldMargin 8 8 1 0 32 :=
  smallCarrier.margin_scale 8 8 1 0 32 1 (by decide)

#print axioms FreeVars.finalValue
#print axioms FreeVars.margin_scale
#print axioms register_bounds
#print axioms carrier_range_of_margin_pos
#print axioms shifted_Q_bounds
#print axioms exists_finalValue_zero_iff_conditions
#print axioms ratio_sound
#print axioms ratio_complete
