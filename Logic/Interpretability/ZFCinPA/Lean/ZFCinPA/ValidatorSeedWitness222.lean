import ZFCinPA.ValidatorImplicationContext
import ZFCinPA.ValidatorEind222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Actual internal C222 seed witnesses. Literal negative universal formulas
are converted to the existential/conjunction abbreviations by explicit finite
deductions, not definitional rewriting. The final theorem supplies a container
having a prescribed member; it does not assert the stronger native CP/GIC
axioms, semantic seed validity, or a translation of arbitrary derivations. -/
namespace LeanProofs.ZFCinPA.ValidatorSeedWitness222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorEind222
open ArithmeticSeedTemplates222 (req clos nks vrel)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local notation "h0" => (ValidatorImplicationContext.h0 CProv)
local notation "h1" => (ValidatorImplicationContext.h1 CProv)
local notation "ded1" => (ValidatorImplicationContext.ded1 CProv cProv_classical)
local notation "ded2" => (ValidatorImplicationContext.ded2 CProv cProv_classical)

/-- The inner negation of `ex i (conj p q)` adds two negations to
`p → ¬q`; both directions are actual C222 certificates. -/
theorem not_all_imp_ex_conj (i p q : V) :
    CProv (wim (neg (wal i (wim p (neg q)))) (ex i (conj p q))) ∧
    CProv (wim (ex i (conj p q)) (neg (wal i (wim p (neg q))))) :=
  ⟨contrapose_of (all_mono i (double_neg_elim (wim p (neg q)))),
   contrapose_of (all_mono i (double_neg_intro (wim p (neg q))))⟩

/-- Both literal gates are retained. In particular a=b and c=0 are not
excluded when those gates hold. No matrix well-formedness is assumed. -/
theorem seed_pair (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    CProv (ex c (conj (clos a b c c) (req b c c))) := by
  have hn : CProv (neg (nks a b c)) :=
    cProv_mp (contrapose_of (cProv_k (nks a b c) (vrel a b c)))
      (cProv_bundle a b c hca hcb)
  exact cProv_mp (not_all_imp_ex_conj c (clos a b c c) (req b c c)).1 hn

theorem seed_request (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    CProv (ex c (req b c c)) :=
  cProv_mp (ex_mono c (conj_right (clos a b c c) (req b c c)))
    (seed_pair a b c hca hcb)

/-- The request's inner literal negative universal is normalized explicitly.
The two hypotheses are exactly those needed to eliminate its output binder
from the conclusion p∈k. There is no freshness premise on an equality atom. -/
theorem request_eind_member (b p k : V) (hbp : b ≠ p) (hbk : b ≠ k) :
    CProv (wim (req b k (Eind b p)) (wel p k)) := by
  let M := Eind b p
  let Q := wel p k
  let I := neg (wal b (wim M (neg (wel b k))))
  have vQ : Vac b Q := vac_rel p k b hbp hbk
  have hconj : CProv (wim (conj M (wel b k)) Q) := by
    apply ded1
    exact .mp (.mp (.ax (Eind_el_l p k b)) (.mp (.ax (conj_left _ _)) h0))
      (.mp (.ax (conj_right _ _)) h0)
  have hinner : CProv (wim I Q) :=
    compose (not_all_imp_ex_conj b M (wel b k)).1
      (compose (ex_mono b hconj) (ex_elim_of_vac vQ))
  have hpoint : CProv (wim (wim M I) (wim M Q)) :=
    ded2 (.mp (.ax hinner) (.mp h1 h0))
  have hex : CProv (wim (wal b (wim M Q)) (ex b Q)) :=
    ded1 (.mp (.mp (.ax (all_imp_ex b M Q)) h0) (.ax (Eind_ex b p)))
  exact compose (all_mono b hpoint) (compose hex (ex_elim_of_vac vQ))

private lemma neg_ge (p : V) : p ≤ neg p := (tagged_components 0 p 1).1
private lemma conj_left_ge (p q : V) : p ≤ conj p q :=
  le_trans (tagged_components 0 p (neg q)).1 (neg_ge _)
private lemma biff_arguments_le (p q : V) : p ≤ biff p q ∧ q ≤ biff p q := by
  have hw : wim p q ≤ biff p q := conj_left_ge _ _
  exact ⟨le_trans (tagged_components 0 p q).1 hw,
    le_trans (tagged_components 0 p q).2 hw⟩
private lemma wel_gt_right (a b : V) : b < wel a b := by
  have hb : b ≤ 4 * ArithmeticCantor.cantor a b := by
    simpa only [tagged, add_zero] using (tagged_components (0 : V) a b).2
  exact lt_of_le_of_lt hb (lt_add_one _)

/-- Literal code bounds, obtained from constructor component bounds only. -/
theorem eind_gt_arguments (a b : V) : a < Eind a b ∧ b < Eind a b := by
  have hbin : Bin (aux a b) a b ≤ Eind a b :=
    le_trans (tagged_components 2 (aux a b) (Bin (aux a b) a b)).2
      (conj_left_ge _ _)
  have hargs := biff_arguments_le (wel (aux a b) a) (wel (aux a b) b)
  exact ⟨lt_of_lt_of_le (wel_gt_right _ a) (le_trans hargs.1 hbin),
    lt_of_lt_of_le (wel_gt_right _ b) (le_trans hargs.2 hbin)⟩

def containerLabel (p : V) : V := Eind (p + 1) p

theorem containerLabel_bounds (p : V) : p + 1 < containerLabel p ∧ p < containerLabel p :=
  eind_gt_arguments (p + 1) p

/-- Uniform actual-checker witness that an object belongs to a container.
The diagonal seed roles a=b=p+1 are legal; its matrix/binder code is the
literal Eind(p+1,p), which is strictly larger than both displayed labels.
This is membership containment only, not the native container axiom. -/
theorem membership_container (p : V) :
    CProv (ex (containerLabel p) (wel p (containerLabel p))) := by
  have hk : containerLabel p ≠ p + 1 := ne_of_gt (containerLabel_bounds p).1
  have hb : p + 1 ≠ p := ne_of_gt (lt_add_one p)
  exact cProv_mp
    (ex_mono (containerLabel p)
      (request_eind_member (p + 1) p (containerLabel p) hb (Ne.symm hk)))
    (seed_request (p + 1) (p + 1) (containerLabel p) hk hk)

theorem closed_membership_container (p : V) :
    CProv (wal p (ex (containerLabel p) (wel p (containerLabel p)))) :=
  cProv_gen p (membership_container p)

theorem membership_container_witness (p : V) :
    ∃ code : V, ArithmeticHistory222.value code =
      ex (containerLabel p) (wel p (containerLabel p)) + 1 := membership_container p

end LeanProofs.ZFCinPA.ValidatorSeedWitness222
