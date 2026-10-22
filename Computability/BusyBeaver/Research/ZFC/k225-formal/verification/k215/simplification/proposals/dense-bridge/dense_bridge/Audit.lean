import BusyBeaver.ZFC.KDenseBridge

open SetTheory.BusyBeaver
open SetTheory.BusyBeaver.ZFC

-- The original public type, including every hypothesis, is unchanged.
theorem dense_bridge_public_type {m : Nat} {D : Machine (m + 1)}
    {M : KZip.TMN} {ex : Nat → Nat} {H : Nat}
    (hc : KDenseBridge.Commutes D M ex H)
    (hH : ∀ b, M H b = none) :
    KDenseBridge.BlankHalts D ↔ KZip.Halts M (KZip.zc (ex 0) [] []) :=
  KDenseBridge.blank_iff hc hH

#print axioms KDenseBridge.blank_iff
#print axioms dense_bridge_public_type
