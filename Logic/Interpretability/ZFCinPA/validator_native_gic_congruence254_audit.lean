import ZFCinPA.ValidatorNativeGicCongruence254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open LeanProofs.ZFCinPA
open ArithmeticCode254 ValidatorProvability254 ValidatorQuantifierCore254
open ValidatorNativeGic254 ValidatorNativeGicCongruence254
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.ValidatorNativeGicCongruence254.cProv_imp_mono
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGicCongruence254.cProv_conj_mono
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGicCongruence254.internalGic_matrix_imp
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGicCongruence254.internalGic_matrix_equivalent
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGicCongruence254.internalGic_pad_equivalent
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGicCongruence254.cProv_unpaddedGic_bounded
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGicCongruence254.cProv_unpaddedGic
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGicCongruence254.cProv_closed_unpaddedGic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (p p' q q' : V) (hp : CProv (wim p' p)) (hq : CProv (wim q q')) :
    CProv (wim (wim p q) (wim p' q')) := cProv_imp_mono hp hq
example (p p' q q' : V) (hp : CProv (wim p p')) (hq : CProv (wim q q')) :
    CProv (wim (conj p q) (conj p' q')) := cProv_conj_mono hp hq
example (a b c p q : V) (hpq : CProv (wim p q)) (hqp : CProv (wim q p)) :
    CProv (wim (internalGic a b c p) (internalGic a b c q)) :=
  internalGic_matrix_imp a b c hpq hqp
example (a b c p q : V) (hpq : CProv (wim p q)) (hqp : CProv (wim q p)) :
    CProv (wim (internalGic a b c p) (internalGic a b c q)) ∧
      CProv (wim (internalGic a b c q) (internalGic a b c p)) :=
  internalGic_matrix_equivalent a b c hpq hqp
example (a b p : V) :
    CProv (wim (internalGic a b (pad p) p) (internalGic a b (pad p) (pad p))) :=
  (internalGic_pad_equivalent a b p).1
example (a b p : V) :
    CProv (wim (internalGic a b (pad p) (pad p)) (internalGic a b (pad p) p)) :=
  (internalGic_pad_equivalent a b p).2
example (a b p : V) (ha : a ≤ 3) (hb : b ≤ 3) :
    CProv (internalGic a b (pad p) p) := cProv_unpaddedGic_bounded a b p ha hb
example (p : V) : CProv (internalGic 1 3 (pad p) p) := cProv_unpaddedGic p
example (p : V) : CProv (wal 3 (internalGic 1 3 (pad p) p)) :=
  cProv_closed_unpaddedGic p
example : CProv (wal (3 : V) (internalGic 1 3 (pad 0) 0)) :=
  cProv_closed_unpaddedGic 0
example (a p q : V) (hpq : CProv (wim p q)) (hqp : CProv (wim q p)) :
    CProv (wim (internalGic a a a p) (internalGic a a a q)) :=
  internalGic_matrix_imp a a a hpq hqp
