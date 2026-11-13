import ZFCinPA.ValidatorQuantifierCore254

set_option autoImplicit false
noncomputable section

/-!
Literal all-internal GIC introduction for the validator. The bundle's third
argument serves both as its matrix code and as an existential variable label.
Double-negation padding supplies the two numeric gates at labels 1 and 3,
including when the input matrix value is zero. This unit does not identify
the result with the configurable encoding of a Foundation GIC body: capture
avoidance, alpha transport, universal closure and the proof translation remain
separate obligations.
-/
namespace LeanProofs.ZFCinPA.ValidatorNativeGic254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254
open ValidatorProvability254 ValidatorQuantifierCore254
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Domain occupies label b; the collection witness uses c. The matrix p is
evaluated under the two input labels a and b in the literal G circuit. -/
noncomputable def internalGic (a b c p : V) : V :=
  ex c (conj
    (wal a (wim (wel a b) (wal b (wim p (ex b (conj p (wel b c)))))))
    (wal b (wim (wel b c) (ex a p))))

lemma bundleG_eq_internalGic (a b c : V) :
    ArithmeticTemplates254.bundleG a b c = internalGic a b c c := rfl

private lemma cProv_native_pair (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    CProv (conj (ArithmeticTemplates254.bundleC a b c)
      (ArithmeticTemplates254.bundleG a b c)) := by
  have hall : CProv (conj
      (conj (ArithmeticTemplates254.bundleC a b c) (ArithmeticTemplates254.bundleG a b c))
      (conj (wim (wel a b) (wal c (wel a b))) (wim (weq a b) (wal c (weq a b))))) := by
    change CProv (ArithmeticTemplates254.bundle a b c)
    exact cProv_bundle a b c hca hcb
  exact cProv_mp (conj_left _ _) hall

lemma cProv_container (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    CProv (ArithmeticTemplates254.bundleC a b c) := by
  exact cProv_mp (conj_left _ _) (cProv_native_pair a b c hca hcb)

lemma cProv_internalGic (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    CProv (internalGic a b c c) := by
  exact cProv_mp (conj_right _ _) (cProv_native_pair a b c hca hcb)

/-- This padding preserves the matrix up to actual CProv equivalence and
forces a code above 3 without a nonzero-matrix premise. -/
noncomputable def pad (p : V) : V := wim (wim p 1) 1

lemma pad_gt_three (p : V) : (3 : V) < pad p := by
  have hc : (1 : V) ≤ cantor (wim p 1) 1 := (components_le _ _).2
  have hm := mul_le_mul_of_nonneg_left hc (show (0 : V) ≤ 4 by simp)
  have hp : (4 : V) ≤ pad p := by
    simpa only [pad, wim, tagged, add_zero, mul_one] using hm
  exact lt_of_lt_of_le (by simpa only [three_add_one_eq_four] using (lt_add_one (3 : V))) hp

lemma pad_equivalent (p : V) :
    CProv (wim p (pad p)) ∧ CProv (wim (pad p) p) :=
  ⟨double_neg_intro p, double_neg_elim p⟩

lemma cProv_paddedGic_bounded (a b p : V) (ha : a ≤ 3) (hb : b ≤ 3) :
    CProv (internalGic a b (pad p) (pad p)) :=
  cProv_internalGic a b (pad p)
    (ne_of_gt (lt_of_le_of_lt ha (pad_gt_three p)))
    (ne_of_gt (lt_of_le_of_lt hb (pad_gt_three p)))

theorem cProv_paddedGic (p : V) :
    CProv (internalGic 1 3 (pad p) (pad p)) :=
  cProv_paddedGic_bounded 1 3 p (by simp) (le_refl 3)

/-- Close the domain label of the literal G instance. Other parameter labels
are still free: this is not the arbitrary universal closure recognizer. -/
theorem cProv_closed_paddedGic (p : V) :
    CProv (wal 3 (internalGic 1 3 (pad p) (pad p))) :=
  cProv_gen 3 (cProv_paddedGic p)

end LeanProofs.ZFCinPA.ValidatorNativeGic254
