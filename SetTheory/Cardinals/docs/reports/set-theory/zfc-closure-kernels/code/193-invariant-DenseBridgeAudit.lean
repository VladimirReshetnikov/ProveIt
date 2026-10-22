import BusyBeaver.ZFC.KDenseBridge

/-! Public clients of the revised bridge, with exactly the existing hypotheses. -/

namespace SetTheory.BusyBeaver.ZFC.DenseBridgeAudit

open KZip KDenseBridge

example {m : Nat} {D : Machine (m + 1)} {M : TMN} {ex : Nat → Nat} {H : Nat}
    (hc : Commutes D M ex H) (hH : ∀ b, M H b = none) :
    BlankHalts D ↔ Halts M (zc (ex 0) [] []) :=
  blank_iff hc hH

theorem nonhalting_iff {m : Nat} {D : Machine (m + 1)} {M : TMN}
    {ex : Nat → Nat} {H : Nat}
    (hc : Commutes D M ex H) (hH : ∀ b, M H b = none) :
    (¬ BlankHalts D) ↔ ¬ Halts M (zc (ex 0) [] []) :=
  not_congr (blank_iff hc hH)

#check @KDenseBridge.Commutes
#check @KDenseBridge.Rel
#check @KDenseBridge.rel_step
#check @KDenseBridge.rel_halt
#check @KDenseBridge.run_succ
#check @KDenseBridge.blank_iff
#print axioms KDenseBridge.blank_iff
#print axioms nonhalting_iff

end SetTheory.BusyBeaver.ZFC.DenseBridgeAudit
