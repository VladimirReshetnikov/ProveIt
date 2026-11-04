import DiophantineConsistency.Compact44.FixedGraphAlignedShift
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace AlignedAnchorPhase
open CleanGeometry

theorem nat_zero (d : ℕ) (hd : d<8807)
    (h1 : BadNat ((2195+8807-d)%8807)) (h2 : BadNat ((3296+8807-d)%8807)) : d=0 := by
  unfold BadNat at h1 h2
  omega
#print axioms AlignedAnchorPhase.nat_zero
end AlignedAnchorPhase
