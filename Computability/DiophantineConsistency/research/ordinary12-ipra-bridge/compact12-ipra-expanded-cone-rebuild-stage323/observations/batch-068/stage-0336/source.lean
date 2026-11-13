import ZFCinPA.ValidatorProvability254

import ZFCinPA.ValidatorImplicationContext

set_option autoImplicit false
noncomputable section

/-!
Finite derived quantifier and vacuity arguments for the literal validator.
All formula/label arguments are arbitrary internal arithmetic values. Each
proof uses the checked CProv row closures and the polymorphic finite Kalmar
deduction theorem; there is no induction over ordinary formula syntax.

The final two-binder bridge exposes the four vacuity proof witnesses that
an eventual represented environment/alpha induction must supply. It does
not rename arbitrary accepted proofs or theory bundles.
-/
namespace LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254
open ValidatorProvability254
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
  ValidatorImplicationContext.vac_neg CProv cProv_classical ex_elim_of_vac h

lemma conj_left (a b : V) : CProv (wim (conj a b) a) :=
  ValidatorImplicationContext.conj_left CProv cProv_classical a b

lemma conj_right (a b : V) : CProv (wim (conj a b) b) :=
  ValidatorImplicationContext.conj_right CProv cProv_classical a b

lemma conj_intro {a b : V} (ha : CProv a) (hb : CProv b) : CProv (conj a b) :=
  ValidatorImplicationContext.conj_intro CProv cProv_classical ha hb

/-- The two gated atomic projections share the same bundle certificate. -/
private lemma vac_atoms (a b i : V) (ha : i≠a) (hb : i≠b) :
    Vac i (wel a b) ∧ Vac i (weq a b) := by
  let m : V := wim (wel a b) (wal i (wel a b))
  let e : V := wim (weq a b) (wal i (weq a b))
  have hall : CProv (conj
      (conj (ArithmeticTemplates254.bundleC a b i) (ArithmeticTemplates254.bundleG a b i))
      (conj m e)) := by
    change CProv (ArithmeticTemplates254.bundle a b i)
    exact cProv_bundle a b i ha hb
  have hv := cProv_mp (conj_right _ _) hall
  exact ⟨cProv_mp (conj_left m e) hv, cProv_mp (conj_right m e) hv⟩

lemma vac_rel (a b i : V) (ha : i≠a) (hb : i≠b) : Vac i (wel a b) :=
  (vac_atoms a b i ha hb).1
lemma vac_eq (a b i : V) (ha : i≠a) (hb : i≠b) : Vac i (weq a b) :=
  (vac_atoms a b i ha hb).2

lemma vac_truth (i : V) : Vac i (0 : V) :=
  cProv_mp (cProv_k (wal i 0) 0) (cProv_gen i cProv_truth)
lemma vac_falsum (i : V) : Vac i (1 : V) := cProv_ex_falso (wal i 1)

lemma vac_imp {i a b : V} (ha : Vac i a) (hb : Vac i b) : Vac i (wim a b) :=
  ValidatorImplicationContext.vac_imp CProv cProv_classical cProv_gen all_distribution
    ex_elim_of_vac ha hb
lemma vac_all (j : V) {i p : V} (hp : Vac i p) : Vac i (wal j p) :=
  compose (all_mono j hp) (all_swap j i p)

lemma all_imp_ex (i p q : V) :
    CProv (wim (wal i (wim p q)) (wim (ex i p) (ex i q))) := by
  have h1' : CProv (wim (wal i (wim p q)) (wal i (wim (neg q) (neg p)))) :=
    all_mono i (contrapose p q)
  have h3 := compose h1' (all_distribution i (neg q) (neg p))
  exact ValidatorImplicationContext.contra_under CProv cProv_classical h3

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

end LeanProofs.ZFCinPA.ValidatorQuantifierCore254
