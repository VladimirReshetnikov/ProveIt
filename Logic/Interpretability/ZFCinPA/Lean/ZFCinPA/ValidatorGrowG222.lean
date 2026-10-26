import ZFCinPA.ValidatorQuantifierCore254
import BusyBeaver.ZFC.ArithmeticTemplates222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! An internal C254 proof of every C222 equality-template instance.
The binder is fresh for a and b by arithmetic, with no restriction on c.
No changed seed-bundle validity, C222 checker or runtime equivalence is claimed. -/
namespace LeanProofs.ZFCinPA.ValidatorGrowG222

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ValidatorProvability254

section Freshness
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

theorem wel_gt_left (a b : V) : a < wel a b := by
  have h : a ≤ 4 * cantor a b := by
    simpa only [tagged, add_zero] using (tagged_components (0 : V) a b).1
  exact lt_of_le_of_lt h (lt_add_one _)

theorem wel_gt_right (a b : V) : b < wel a b := by
  have h : b ≤ 4 * cantor a b := by
    simpa only [tagged, add_zero] using (tagged_components (0 : V) a b).2
  exact lt_of_le_of_lt h (lt_add_one _)
end Freshness

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cProv_growG_literal (a b c : V) :
    CProv (wim (weq c a) (wim (weq c b) (wal (wel a b) (weq a b)))) := by
  have hv : CProv (wim (weq a b) (wal (wel a b) (weq a b))) :=
    ValidatorQuantifierCore254.vac_eq a b (wel a b)
      (ne_of_gt (wel_gt_left a b)) (ne_of_gt (wel_gt_right a b))
  have hr : CProv (wim (weq c a) (wim (weq c b) (weq a b))) :=
    cProv_rho7 a b c
  have hd : Kalmar.Der wim CProv [weq c b, weq c a]
      (wal (wel a b) (weq a b)) :=
    .mp (.ax hv) (.mp (.mp (.ax hr)
      (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) .cons_head)
  exact (Kalmar.deduction cProv_classical
    (Kalmar.deduction cProv_classical hd)).sound cProv_classical
      (fun _ hm => absurd hm List.not_mem_nil)

theorem cProv_growG (a b c : V) : CProv (ArithmeticTemplates222.growG a b c) :=
  cProv_growG_literal a b c

/-- The witness is an actual internal code for the unchanged twelve-row validator. -/
theorem exists_growG_code (a b c : V) : ∃ d : V,
    ArithmeticHistory254.value d = ArithmeticTemplates222.growG a b c + 1 :=
  cProv_growG a b c

/-- A standard-input consequence, separate from the all-internal theorem. -/
theorem c254_growG (a b c : Nat) : Code254.C254 (KCode222.growG a b c) := by
  apply (cProv_nat_iff _).mp
  simpa only [ArithmeticTemplates222.growG_nat] using
    (cProv_growG (V := Nat) a b c)

end LeanProofs.ZFCinPA.ValidatorGrowG222
