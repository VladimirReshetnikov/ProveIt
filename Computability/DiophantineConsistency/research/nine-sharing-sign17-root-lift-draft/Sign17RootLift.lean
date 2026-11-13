import DiophantineConsistency.Sign17OrderedGap

/-! SOURCE-ONLY: signed lift for the sign17 root's algebraic shape. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17RootLift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def root (beta x1 x9 B C : V) : DiffRing V :=
  (ι x9) * ((ι beta) * ((ι x1) + 1) + 1) + (ι beta) * ((ι x1) + 1) + (ι B) + (ι C)

def scale (beta x1 x9 k B C : V) : DiffRing V :=
  ((ι k) + 1) * root beta x1 x9 B C * (root beta x1 x9 B C + 2)

theorem root_positive (beta x1 x9 B C : V) (hb : 0 < beta) :
    0 < root beta x1 x9 B C := by
  have hbR : (0 : DiffRing V) < ι beta := by simpa only [map_zero] using (ι_lt_ι.mpr hb)
  have hx1 := ι_nonneg x1
  have hx9 := ι_nonneg x9
  have hB := ι_nonneg B
  have hC := ι_nonneg C
  have hA : (0 : DiffRing V) ≤ (ι beta) * ((ι x1) + 1) + 1 := by positivity
  have hrest : (0 : DiffRing V) ≤ (ι x9) * ((ι beta) * ((ι x1) + 1) + 1) + (ι B) + (ι C) := by positivity
  have hp := Sign17OrderedGap.root_positive (ι beta) (ι x1)
    ((ι x9) * ((ι beta) * ((ι x1) + 1) + 1) + (ι B) + (ι C)) hbR hx1 hrest
  unfold root
  linarith

theorem scale_positive (beta x1 x9 k B C : V) (hb : 0 < beta) :
    0 < scale beta x1 x9 k B C := by
  unfold scale
  exact Sign17OrderedGap.scale_positive (ι k) (root beta x1 x9 B C)
    (ι_nonneg k) (root_positive beta x1 x9 B C hb)

theorem exists_signed_lift (beta x1 x9 k B C f W : V) (hb : 0 < beta)
    (hNa : ((ι f)+1)*((ι f)+1) - (scale beta x1 x9 k B C)*(scale beta x1 x9 k B C)*
      (((ι f)+1)*((ι f)+1)-(ι W)*(ι W)) - 1 = 0) :
    ∃ gap : V, ι gap = ((ι f)+1)*((ι f)+1)-(ι W)*(ι W) := by
  have hf : (1 : DiffRing V) ≤ (ι f)+1 := by have h := ι_nonneg f; linarith
  have hn := Sign17OrderedGap.difference_nonnegative ((ι f)+1) (scale beta x1 x9 k B C) (ι W)
    hf (scale_positive beta x1 x9 k B C hb) hNa
  obtain ⟨gap, hgap⟩ := nonneg_iff.mp hn
  exact ⟨gap, hgap.symm⟩
end DiophantineConsistency.Sign17RootLift
#print axioms DiophantineConsistency.Sign17RootLift.root_positive
#print axioms DiophantineConsistency.Sign17RootLift.scale_positive
#print axioms DiophantineConsistency.Sign17RootLift.exists_signed_lift
