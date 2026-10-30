import ZFCinPA.ValidatorProvability222
import ZFCinPA.ValidatorImplicationContext

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Finite internal C222 equality deductions. The proof pattern is the
existing KEqCodes222 argument, instantiated with arbitrary internal values
and actual CProv222 proof witnesses. No external C222 derivability theorem,
seed interpretation or pre-existing rho7 is used. -/
namespace LeanProofs.ZFCinPA.ValidatorEqualityCore222

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

abbrev neg (p : V) : V := wim p 1
abbrev ex (i p : V) : V := neg (wal i (neg p))

private abbrev D (G : List V) (p : V) : Prop := Kalmar.Der wim CProv G p
local notation "d0" => (ValidatorImplicationContext.h0 CProv)
local notation "d1" => (ValidatorImplicationContext.h1 CProv)
local notation "ded1" => (ValidatorImplicationContext.ded1 CProv cProv_classical)
local notation "ded2" => (ValidatorImplicationContext.ded2 CProv cProv_classical)

/-- A fixed finite contraposition certificate, not a semantic implication. -/
theorem contrapose (a b : V) : CProv (wim (wim a b) (wim (neg b) (neg a))) :=
  ValidatorImplicationContext.contrapose CProv cProv_classical a b

private lemma all_distribution (i p q : V) :
    CProv (wim (wal i (wim p q)) (wim (wal i p) (wal i q))) := by
  change CProv (ArithmeticTemplates254.rho2 i p q)
  exact cProv_rho2 i p q

private lemma exists_equality (i j : V) : CProv (ex i (weq i j)) := by
  change CProv (rho1 i j)
  exact cProv_rho1 i j

private lemma ex_all_elim (i p : V) : CProv (wim (ex i (wal i p)) p) := by
  change CProv (ArithmeticTemplates254.rho6 i p)
  exact cProv_rho6 i p

private lemma grow (a b c : V) :
    CProv (wim (weq c a) (wim (weq c b) (wal (wel a b) (weq a b)))) := by
  simpa only [ArithmeticTemplates222.growG_eq] using cProv_growG a b c

theorem all_ex (r a b : V) :
    CProv (wim (wal r (wim a b)) (wim (ex r a) (ex r b))) := by
  have h1 : CProv (wim (wal r (wim a b)) (wal r (wim (neg b) (neg a)))) :=
    cProv_mp (all_distribution r (wim a b) (wim (neg b) (neg a)))
      (cProv_gen r (contrapose a b))
  exact ValidatorImplicationContext.contra_under CProv cProv_classical
    (ValidatorImplicationContext.compose CProv cProv_classical h1 (all_distribution r (neg b) (neg a)))

theorem ex_mono (r : V) {a b : V} (h : CProv (wim a b)) :
    CProv (wim (ex r a) (ex r b)) :=
  cProv_mp (all_ex r a b) (cProv_gen r h)

/-- Equality reflexivity follows from growG, rho1 and rho6. No positivity
or freshness side condition is needed, including at x=0. -/
theorem cProv_refl (x : V) : CProv (weq x x) := by
  have h1 : CProv (wim (weq (wel x x) x) (wal (wel x x) (weq x x))) :=
    ded1 (.mp (.mp (.ax (grow x x (wel x x))) d0) d0)
  have h2 : CProv (ex (wel x x) (wal (wel x x) (weq x x))) :=
    cProv_mp (ex_mono (wel x x) h1) (exists_equality (wel x x) x)
  exact cProv_mp (ex_all_elim (wel x x) (weq x x)) h2

/-- The helper at its actual numeric binder, with no added freshness premise. -/
theorem cProv_helper (a b : V) :
    CProv (wim (weq a b) (wal (wel a b) (weq a b))) :=
  cProv_mp (grow a b a) (cProv_refl a)

/-- Specialization only at the exact helper binder, derived from the rules. -/
theorem cProv_eq_specialize (a b : V) :
    CProv (wim (wal (wel a b) (weq a b)) (weq a b)) := by
  have hk : CProv (wim (wal (wel a b) (weq a b))
      (wal (wel a b) (wim (weq (wel a b) a) (weq a b)))) :=
    cProv_mp (all_distribution (wel a b) (weq a b) (wim (weq (wel a b) a) (weq a b)))
      (cProv_gen (wel a b) (cProv_k (weq a b) (weq (wel a b) a)))
  apply ded1
  have e1 : D [wal (wel a b) (weq a b)] (ex (wel a b) (weq a b)) :=
    .mp (.mp (.ax (all_ex (wel a b) _ _)) (.mp (.ax hk) d0))
      (.ax (exists_equality (wel a b) a))
  have e2 : D [wal (wel a b) (weq a b)] (ex (wel a b) (wal (wel a b) (weq a b))) :=
    .mp (.ax (ex_mono (wel a b) (cProv_helper a b))) e1
  exact .mp (.ax (ex_all_elim (wel a b) (weq a b))) e2

/-- rho7 is a derived theorem of the new calculus, not its tag9 axiom. -/
theorem cProv_rho7 (a b c : V) : CProv (ArithmeticTemplates254.rho7 a b c) := by
  change CProv (wim (weq c a) (wim (weq c b) (weq a b)))
  exact ded2 (.mp (.ax (cProv_eq_specialize a b))
    (.mp (.mp (.ax (grow a b c)) d1) d0))

private lemma not_imp_left (a b : V) : CProv (wim (neg (wim a b)) a) := by
  apply ded1
  have inner : D [neg a, neg (wim a b)] (wim a b) :=
    Kalmar.deduction cProv_classical (.mp (.ax (cProv_ex_falso b)) (.mp d1 d0))
  have hbot : D [neg a, neg (wim a b)] (1 : V) := .mp d1 inner
  exact .mp (.ax (cProv_peirce a 1))
    (Kalmar.deduction cProv_classical (.mp (.ax (cProv_ex_falso a)) hbot))

/-- Membership vacuity uses only the actual two seed gates. Equal a,b or
c=0 are allowed whenever those gates hold; no matrix-validity premise. -/
theorem cProv_vrel (a b c : V) (ha : c ≠ a) (hb : c ≠ b) :
    CProv (ArithmeticSeedTemplates222.vrel a b c) := by
  have hseed := cProv_bundle a b c ha hb
  rw [ArithmeticSeedTemplates222.bundle222_eq] at hseed
  exact cProv_mp (not_imp_left (ArithmeticSeedTemplates222.vrel a b c)
    (ArithmeticSeedTemplates222.nks a b c)) hseed

end LeanProofs.ZFCinPA.ValidatorEqualityCore222
