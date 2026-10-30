import ZFCinPA.ValidatorEqualityCore222

import ZFCinPA.ValidatorImplicationContext

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-!
Finite quantifier deductions for the actual internal C222 checker. All codes
and labels range over an arbitrary internal IΣ1 model. The relational atom
vacuity theorem uses precisely the two actual helper-free seed gates. There
is deliberately no primitive equality-vacuity rule. This supplies the fixed
relational and binder-renaming deductions needed for indiscernibility;
it does not establish semantic seed validity or translate arbitrary proofs.
-/
namespace LeanProofs.ZFCinPA.ValidatorRelationalCore222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254
open ValidatorProvability222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

abbrev neg (p : V) : V := wim p 1
abbrev conj (p q : V) : V := neg (wim p (neg q))
abbrev ex (i p : V) : V := neg (wal i (neg p))
def Vac (i p : V) : Prop := CProv (wim p (wal i p))

local notation "h0" => (ValidatorImplicationContext.h0 CProv)
local notation "h1" => (ValidatorImplicationContext.h1 CProv)
local notation "h2" => (ValidatorImplicationContext.h2 CProv)
local notation "ded2" => (ValidatorImplicationContext.ded2 CProv cProv_classical)
local notation "ded3" => (ValidatorImplicationContext.ded3 CProv cProv_classical)

lemma compose {a b c : V} (hab : CProv (wim a b)) (hbc : CProv (wim b c)) :
    CProv (wim a c) :=
  ValidatorImplicationContext.compose CProv cProv_classical hab hbc

lemma contrapose (a b : V) :
    CProv (wim (wim a b) (wim (neg b) (neg a))) :=
  ValidatorImplicationContext.contrapose CProv cProv_classical a b

lemma contrapose_of {a b : V} (h : CProv (wim a b)) :
    CProv (wim (neg b) (neg a)) := cProv_mp (contrapose a b) h
lemma double_neg_elim (a : V) : CProv (wim (neg (neg a)) a) :=
  ValidatorImplicationContext.double_neg_elim CProv cProv_classical a

lemma double_neg_intro (a : V) : CProv (wim a (neg (neg a))) :=
  ValidatorImplicationContext.double_neg_intro CProv cProv_classical a

lemma all_distribution (i p q : V) :
    CProv (wim (wal i (wim p q)) (wim (wal i p) (wal i q))) := by
  change CProv (ArithmeticTemplates254.rho2 i p q)
  exact cProv_rho2 i p q
lemma all_swap (i j p : V) :
    CProv (wim (wal i (wal j p)) (wal j (wal i p))) := by
  change CProv (ArithmeticTemplates254.rho4 i j p)
  exact cProv_rho4 i j p
lemma ex_all_elim (i p : V) : CProv (wim (ex i (wal i p)) p) := by
  change CProv (ArithmeticTemplates254.rho6 i p)
  exact cProv_rho6 i p
lemma ex_equality (i j : V) : CProv (ex i (weq i j)) := cProv_rho1 i j

lemma all_mono (i : V) {p q : V} (h : CProv (wim p q)) :
    CProv (wim (wal i p) (wal i q)) :=
  cProv_mp (all_distribution i p q) (cProv_gen i h)
lemma ex_mono (i : V) {p q : V} (h : CProv (wim p q)) :
    CProv (wim (ex i p) (ex i q)) :=
  contrapose_of (all_mono i (contrapose_of h))
lemma ex_elim_of_vac {i p : V} (h : Vac i p) : CProv (wim (ex i p) p) :=
  compose (ex_mono i h) (ex_all_elim i p)
lemma vac_neg {i p : V} (h : Vac i p) : Vac i (neg p) :=
  compose (contrapose_of (ex_elim_of_vac h)) (double_neg_elim (wal i (neg p)))

lemma conj_left (a b : V) : CProv (wim (conj a b) a) :=
  ValidatorImplicationContext.conj_left CProv cProv_classical a b

lemma conj_right (a b : V) : CProv (wim (conj a b) b) :=
  ValidatorImplicationContext.conj_right CProv cProv_classical a b

lemma conj_intro {a b : V} (ha : CProv a) (hb : CProv b) : CProv (conj a b) :=
  ValidatorImplicationContext.conj_intro CProv cProv_classical ha hb

/-- Only membership vacuity is extracted from the actual new seed; in
particular no arbitrary-binder primitive equality vacuity is available. -/
lemma vac_rel (a b i : V) (ha : i ≠ a) (hb : i ≠ b) : Vac i (wel a b) := by
  change CProv (ArithmeticSeedTemplates222.vrel a b i)
  exact ValidatorEqualityCore222.cProv_vrel a b i ha hb

lemma vac_truth (i : V) : Vac i (0 : V) :=
  cProv_mp (cProv_k (wal i 0) 0) (cProv_gen i cProv_truth)
lemma vac_falsum (i : V) : Vac i (1 : V) := cProv_ex_falso (wal i 1)

private lemma imp_cases (a b c : V) :
    CProv (wim (wim (neg a) c) (wim (wim b c) (wim (wim a b) c))) :=
  ValidatorImplicationContext.imp_cases CProv cProv_classical a b c

lemma vac_imp {i a b : V} (ha : Vac i a) (hb : Vac i b) : Vac i (wim a b) := by
  have hna : CProv (wim (neg a) (wal i (wim a b))) :=
    compose (vac_neg ha)
      (all_mono i (ded2 (.mp (.ax (cProv_ex_falso b)) (.mp h1 h0))))
  have hbb : CProv (wim b (wal i (wim a b))) :=
    compose hb (all_mono i (cProv_k b a))
  exact cProv_mp (cProv_mp (imp_cases a b (wal i (wim a b))) hna) hbb
lemma vac_all (j : V) {i p : V} (hp : Vac i p) : Vac i (wal j p) :=
  compose (all_mono j hp) (all_swap j i p)

lemma all_imp_ex (i p q : V) :
    CProv (wim (wal i (wim p q)) (wim (ex i p) (ex i q))) :=
  ValidatorEqualityCore222.all_ex i p q

lemma vac_conj {i a b : V} (ha : Vac i a) (hb : Vac i b) : Vac i (conj a b) :=
  vac_neg (vac_imp ha (vac_neg hb))

/-- A conjunction-introduction certificate usable under an open context. -/
lemma conj_rule (a b : V) : CProv (wim a (wim b (conj a b))) := by
  apply ded3
  exact .mp (.mp h0 h2) h1

/-- Generalize a theorem under two assumptions whose vacuity is supplied. -/
lemma all_under_two (i : V) {h p q : V}
    (hpq : CProv (wim h (wim p q))) (hh : Vac i h) (hp : Vac i p) :
    CProv (wim h (wim p (wal i q))) :=
  ValidatorImplicationContext.all_under_two CProv cProv_classical cProv_gen all_distribution i hpq hh hp

/-- A finite two-binder congruence step with every freshness resource explicit.
No global proof renaming or ordinary syntax induction is used. -/
lemma all_relational (h p q x y : V)
    (hpq : CProv (wim h (wim (weq x y) (wim p q))))
    (vxh : Vac x h) (vxq : Vac x q)
    (vyh : Vac y h) (vyall : Vac y (wal x p)) :
    CProv (wim h (wim (wal x p) (wal y q))) :=
  ValidatorImplicationContext.all_relational CProv cProv_classical cProv_gen all_distribution
    all_imp_ex ex_equality ex_elim_of_vac h p q x y hpq vxh vxq vyh vyall

end LeanProofs.ZFCinPA.ValidatorRelationalCore222
