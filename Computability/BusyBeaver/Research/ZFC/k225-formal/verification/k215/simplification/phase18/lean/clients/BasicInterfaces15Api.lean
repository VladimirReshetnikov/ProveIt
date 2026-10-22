import BusyBeaver.ZFC.PSCCalibration
import BusyBeaver.ZFC.KDenseBridge

namespace BasicInterfaces15Api

open SetTheory SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

universe u

theorem power_sets {V : Type u} (mem : V → V → Prop) :
    PSCCalibration.PowerSets mem ↔
      ∀ a, ∃ p, ∀ y, mem y p ↔ SetTheory.Sub mem y a := Iff.rfl

theorem calibration :
    (¬ BProv PSCCalibration.PSCAx [] Form.fBot) ↔
      (¬ BProv PSCCalibration.ZF0Ax [] Form.fBot) :=
  PSCCalibration.psc_consistency_iff_zf0

theorem dense {m : Nat} {D : Machine (m + 1)} {M : KZip.TMN}
    {ex : Nat → Nat} {H : Nat}
    (hc : KDenseBridge.Commutes D M ex H) (hH : ∀ b, M H b = none) :
    KDenseBridge.BlankHalts D ↔ KZip.Halts M (KZip.zc (ex 0) [] []) :=
  KDenseBridge.blank_iff hc hH

#print axioms power_sets
#print axioms calibration
#print axioms dense

end BasicInterfaces15Api
