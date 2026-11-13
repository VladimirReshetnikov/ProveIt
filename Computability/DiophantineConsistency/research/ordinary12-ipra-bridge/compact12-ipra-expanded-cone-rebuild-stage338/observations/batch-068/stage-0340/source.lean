import ZFCinPA.ValidatorQuantifierCore254

set_option autoImplicit false
noncomputable section

/-!
Finite equality and atomic congruence proofs for the literal validator.
Labels are arbitrary internal arithmetic values. Reflexivity derives its
fresh witness from x+1 and uses both actual atomic-vacuity gates. No formula
renamer, source-proof compiler, or induction on ordinary syntax is used.
-/
namespace LeanProofs.ZFCinPA.ValidatorEqualityCore254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254 ValidatorProvability254 ValidatorQuantifierCore254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local notation "h0" => (ValidatorImplicationContext.h0 CProv)
local notation "h1" => (ValidatorImplicationContext.h1 CProv)
local notation "h2" => (ValidatorImplicationContext.h2 CProv)
local notation "ded1" => (ValidatorImplicationContext.ded1 CProv cProv_classical)
local notation "ded2" => (ValidatorImplicationContext.ded2 CProv cProv_classical)
local notation "ded3" => (ValidatorImplicationContext.ded3 CProv cProv_classical)

lemma eq_refl (x : V) : CProv (weq x x) := by
  let c := x+1
  have hc : c≠x := ne_of_gt (lt_add_one x)
  have hr : CProv (wim (weq c x) (wim (weq c x) (weq x x))) := by
    change CProv (ArithmeticTemplates254.rho7 x x c)
    exact cProv_rho7 x x c
  have hi : CProv (wim (weq c x) (weq x x)) :=
    ded1 (.mp (.mp (.ax hr) h0) h0)
  have he : CProv (ex c (weq x x)) := cProv_mp (ex_mono c hi) (ex_equality c x)
  exact cProv_mp (ex_elim_of_vac (vac_eq x x c hc hc)) he

lemma eq_symm (x y : V) : CProv (wim (weq x y) (weq y x)) := by
  have hr : CProv (wim (weq x y) (wim (weq x x) (weq y x))) := by
    change CProv (ArithmeticTemplates254.rho7 y x x)
    exact cProv_rho7 y x x
  exact ded1 (.mp (.mp (.ax hr) h0) (.ax (eq_refl x)))

lemma eq_trans (x y z : V) :
    CProv (wim (weq x y) (wim (weq y z) (weq x z))) := by
  have hr : CProv (wim (weq y x) (wim (weq y z) (weq x z))) := by
    change CProv (ArithmeticTemplates254.rho7 x z y)
    exact cProv_rho7 x z y
  exact ded2 (.mp (.mp (.ax hr) (.mp (.ax (eq_symm x y)) h1)) h0)

lemma rel_left (x y z : V) :
    CProv (wim (weq x y) (wim (wel x z) (wel y z))) := by
  change CProv (ArithmeticTemplates254.rho5 y z x)
  exact cProv_rho5 y z x
lemma rel_right (x y z : V) :
    CProv (wim (weq x y) (wim (wel z x) (wel z y))) := by
  change CProv (ArithmeticTemplates254.rho3 x y z)
  exact cProv_rho3 x y z
lemma eq_left (x y z : V) :
    CProv (wim (weq x y) (wim (weq x z) (weq y z))) := by
  change CProv (ArithmeticTemplates254.rho7 y z x)
  exact cProv_rho7 y z x
lemma eq_right (x y z : V) :
    CProv (wim (weq x y) (wim (weq z x) (weq z y))) :=
  ded2 (.mp (.mp (.ax (eq_trans z x y)) h0) h1)

private lemma congr_of_sides (R : V → V → V) (a a' b b' : V)
    (hl : CProv (wim (weq a a') (wim (R a b) (R a' b))))
    (hr : CProv (wim (weq b b') (wim (R a' b) (R a' b')))) :
    CProv (wim (weq a a') (wim (weq b b') (wim (R a b) (R a' b')))) :=
  ded3 (.mp (.mp (.ax hr) h1) (.mp (.mp (.ax hl) h2) h0))

lemma rel_congr (a a' b b' : V) :
    CProv (wim (weq a a') (wim (weq b b') (wim (wel a b) (wel a' b')))) :=
  congr_of_sides wel a a' b b' (rel_left a a' b) (rel_right b b' a')
lemma eq_congr (a a' b b' : V) :
    CProv (wim (weq a a') (wim (weq b b') (wim (weq a b) (weq a' b')))) :=
  congr_of_sides weq a a' b b' (eq_left a a' b) (eq_right b b' a')

end LeanProofs.ZFCinPA.ValidatorEqualityCore254
