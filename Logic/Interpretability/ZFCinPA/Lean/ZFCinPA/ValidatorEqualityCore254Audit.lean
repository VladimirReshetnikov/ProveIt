import ZFCinPA.ValidatorEqualityCore254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254
open LeanProofs.ZFCinPA.ValidatorEqualityCore254
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.ValidatorEqualityCore254.eq_refl
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityCore254.eq_symm
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityCore254.eq_trans
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityCore254.rel_left
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityCore254.rel_right
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityCore254.eq_left
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityCore254.eq_right
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityCore254.rel_congr
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityCore254.eq_congr

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (x : V) : CProv (weq x x) := eq_refl x
example (x y : V) : CProv (wim (weq x y) (weq y x)) := eq_symm x y
example (x y z : V) : CProv (wim (weq x y) (wim (weq y z) (weq x z))) := eq_trans x y z
example (x y z : V) : CProv (wim (weq x y) (wim (wel x z) (wel y z))) := rel_left x y z
example (x y z : V) : CProv (wim (weq x y) (wim (wel z x) (wel z y))) := rel_right x y z
example (x y z : V) : CProv (wim (weq x y) (wim (weq x z) (weq y z))) := eq_left x y z
example (x y z : V) : CProv (wim (weq x y) (wim (weq z x) (weq z y))) := eq_right x y z
example (a a' b b' : V) :
    CProv (wim (weq a a') (wim (weq b b') (wim (wel a b) (wel a' b')))) := rel_congr a a' b b'
example (a a' b b' : V) :
    CProv (wim (weq a a') (wim (weq b b') (wim (weq a b) (weq a' b')))) := eq_congr a a' b b'
example : CProv (weq (0 : V) 0) := eq_refl 0
example (a b : V) : CProv (wim (weq a b) (wim (wel a a) (wel b b))) := by
  exact cProv_mp
    (cProv_mp (cProv_s (weq a b) (weq a b) (wim (wel a a) (wel b b))) (rel_congr a b a b))
    (Kalmar.self_imp cProv_classical (weq a b))
example (a b c d : V) (ha : CProv (weq a c)) (hb : CProv (weq b d)) (hm : CProv (wel a b)) :
    CProv (wel c d) := cProv_mp (cProv_mp (cProv_mp (rel_congr a c b d) ha) hb) hm
