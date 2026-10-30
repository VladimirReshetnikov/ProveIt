import ZFCinPA.ValidatorImplicationContext
import ZFCinPA.ValidatorSeedWitness222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Actual internal C222 seed-closure witnesses. The closure's negative
universal is normalized by a finite certificate. Vacuity is supplied only
for its input binder, never for the self-labelled matrix/container binder.
Empty objects and singletons up to Eind are derived; full CP/GIC, semantic
seed validity and arbitrary proof translation are not asserted. -/
namespace LeanProofs.ZFCinPA.ValidatorSeedClosure222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorEind222
open ValidatorSeedWitness222
open ArithmeticSeedTemplates222 (req clos)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private abbrev D (G : List V) (p : V) := Kalmar.Der wim CProv G p
local notation "h0" => (ValidatorImplicationContext.h0 CProv)
local notation "h1" => (ValidatorImplicationContext.h1 CProv)
local notation "ded1" => (ValidatorImplicationContext.ded1 CProv cProv_classical)
local notation "ded2" => (ValidatorImplicationContext.ded2 CProv cProv_classical)

/-- Every member satisfies an input-independent matrix. The only vacuity
resource is the explicitly supplied Vac a m; all four codes are arbitrary. -/
theorem closure_support (a b k m : V) (hm : Vac a m) :
    CProv (wim (clos a b k m) (wal b (wim (wel b k) m))) := by
  let U := wal a (wim (wal k (wim (wel k a) (wel k b))) (req b k m))
  let I := neg (wal a (wim m (neg U)))
  have inner : CProv (wim I m) :=
    compose (not_all_imp_ex_conj a m U).1
      (compose (ex_mono a (conj_left m U)) (ex_elim_of_vac hm))
  have point : CProv (wim (wim (wel b k) I) (wim (wel b k) m)) :=
    imp_mono (ded1 h0) inner
  exact all_mono b point

/-- This projection retains the literal seed gates, including legal c=0
and a=b instances. It asserts no vacuity at the self-label c. -/
theorem seed_supported_request (a b c : V) (hca : c ≠ a) (hcb : c ≠ b)
    (hc : Vac a c) :
    CProv (ex c (conj (wal b (wim (wel b c) c)) (req b c c))) := by
  have point : CProv (wim (conj (clos a b c c) (req b c c))
      (conj (wal b (wim (wel b c) c)) (req b c c))) := by
    apply ded1
    exact .mp (.mp (.ax (conj_rule _ _))
      (.mp (.ax (closure_support a b c c hc)) (.mp (.ax (conj_left _ _)) h0)))
      (.mp (.ax (conj_right _ _)) h0)
  exact cProv_mp (ex_mono c point) (seed_pair a b c hca hcb)

/-- The false matrix has code1. Both input/output roles are0, so its
literal seed gates hold without fresh-label or positivity assumptions. -/
theorem empty_object : CProv (ex (1 : V) (wal 0 (neg (wel 0 1)))) :=
  cProv_mp (ex_mono 1 (compose (conj_left _ _)
    (closure_support 0 0 1 1 (vac_falsum 0))))
    (seed_pair 0 0 1 _root_.one_ne_zero _root_.one_ne_zero)

theorem Eind_symm (b p : V) : CProv (wim (Eind b p) (Eind p b)) := by
  have refl : CProv (Eind b b) :=
    cProv_mp (Eq_Eind b b) (ValidatorEqualityCore222.cProv_refl b)
  exact ded1 (.mp (.mp (.ax (Eind_euclid p b b)) h0) (.ax refl))

/-- Decode both directions of membership using actual Eind certificates.
The universal output binder is generalized only under p∈k, whose vacuity
uses the two displayed inequalities. No unrestricted GEN-under-hypothesis
or primitive-equality vacuity is introduced. -/
theorem seed_singleton (a b p k : V) (hbp : b ≠ p) (hbk : b ≠ k)
    (hm : Vac a (Eind b p)) :
    CProv (wim (conj (clos a b k (Eind b p)) (req b k (Eind b p)))
      (conj (wel p k) (wal b (biff (wel b k) (Eind b p))))) := by
  have back : CProv (wim (wel p k) (wim (Eind b p) (wel b k))) := by
    apply ded2
    exact .mp (.mp (.ax (Eind_el_l b k p)) (.mp (.ax (Eind_symm b p)) h0)) h1
  have backAll := compose (vac_rel p k b hbp hbk) (all_mono b back)
  have combine := all_mono2 b (conj_rule (wim (wel b k) (Eind b p))
    (wim (Eind b p) (wel b k)))
  apply ded1
  have hc : D [conj (clos a b k (Eind b p)) (req b k (Eind b p))]
      (clos a b k (Eind b p)) := .mp (.ax (conj_left _ _)) h0
  have hr : D [conj (clos a b k (Eind b p)) (req b k (Eind b p))]
      (req b k (Eind b p)) := .mp (.ax (conj_right _ _)) h0
  have member : D [conj (clos a b k (Eind b p)) (req b k (Eind b p))] (wel p k) :=
    .mp (.ax (request_eind_member b p k hbp hbk)) hr
  have forward : D [conj (clos a b k (Eind b p)) (req b k (Eind b p))]
      (wal b (wim (wel b k) (Eind b p))) :=
    .mp (.ax (closure_support a b k (Eind b p) hm)) hc
  have reverse : D [conj (clos a b k (Eind b p)) (req b k (Eind b p))]
      (wal b (wim (Eind b p) (wel b k))) := .mp (.ax backAll) member
  exact .mp (.mp (.ax (conj_rule _ _)) member) (.mp (.mp (.ax combine) forward) reverse)

def singletonBody (p : V) : V :=
  conj (wel p (containerLabel p))
    (wal (p + 1) (biff (wel (p + 1) (containerLabel p)) (Eind (p + 1) p)))

/-- k=Eind(p+1,p) is the fixed matrix/container code. The new input role
a=k+1 is outside both matrix argument labels; only Vac a k is used.
The conclusion holds for every internal p, including0. -/
theorem singleton_object (p : V) : CProv (ex (containerLabel p) (singletonBody p)) := by
  let b := p + 1
  let k := containerLabel p
  let a := k + 1
  have hkb : b < k := (containerLabel_bounds p).1
  have hkp : p < k := (containerLabel_bounds p).2
  have hab : a ≠ b := ne_of_gt (lt_trans hkb (lt_add_one k))
  have hap : a ≠ p := ne_of_gt (lt_trans hkp (lt_add_one k))
  have hm : Vac a (Eind b p) := Eind_vac b p a hab hap
  exact cProv_mp
    (ex_mono k (seed_singleton a b p k (ne_of_gt (lt_add_one p))
      (Ne.symm (ne_of_gt hkb)) hm))
    (seed_pair a b k (Ne.symm (ne_of_gt (lt_add_one k))) (ne_of_gt hkb))

theorem closed_singleton_object (p : V) :
    CProv (wal p (ex (containerLabel p) (singletonBody p))) :=
  cProv_gen p (singleton_object p)

theorem empty_object_witness :
    ∃ code : V, ArithmeticHistory222.value code = ex 1 (wal 0 (neg (wel 0 1))) + 1 :=
  empty_object

theorem singleton_object_witness (p : V) :
    ∃ code : V, ArithmeticHistory222.value code =
      ex (containerLabel p) (singletonBody p) + 1 := singleton_object p

end LeanProofs.ZFCinPA.ValidatorSeedClosure222
