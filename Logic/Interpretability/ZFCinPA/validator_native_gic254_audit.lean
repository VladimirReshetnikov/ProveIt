import ZFCinPA.ValidatorNativeGic254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open LeanProofs.ZFCinPA
open ArithmeticCode254 ValidatorProvability254 ValidatorNativeGic254
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.ValidatorNativeGic254.bundleG_eq_internalGic
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGic254.cProv_container
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGic254.cProv_internalGic
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGic254.pad_gt_three
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGic254.pad_equivalent
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGic254.cProv_paddedGic_bounded
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGic254.cProv_paddedGic
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGic254.cProv_closed_paddedGic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (a b c : V) : ArithmeticTemplates254.bundleG a b c = internalGic a b c c :=
  bundleG_eq_internalGic a b c
example (a b c : V) (ha : c ≠ a) (hb : c ≠ b) :
    CProv (ArithmeticTemplates254.bundleC a b c) := cProv_container a b c ha hb
example (a b c : V) (ha : c ≠ a) (hb : c ≠ b) :
    CProv (internalGic a b c c) := cProv_internalGic a b c ha hb
example (p : V) : (3 : V) < pad p := pad_gt_three p
example (p : V) : CProv (wim p (pad p)) := (pad_equivalent p).1
example (p : V) : CProv (wim (pad p) p) := (pad_equivalent p).2
example (a b p : V) (ha : a ≤ 3) (hb : b ≤ 3) :
    CProv (internalGic a b (pad p) (pad p)) := cProv_paddedGic_bounded a b p ha hb
example (p : V) : CProv (internalGic 1 3 (pad p) (pad p)) := cProv_paddedGic p
example (p : V) : CProv (wal 3 (internalGic 1 3 (pad p) (pad p))) :=
  cProv_closed_paddedGic p
example : CProv (wal (3 : V) (internalGic 1 3 (pad 0) (pad 0))) :=
  cProv_closed_paddedGic 0
