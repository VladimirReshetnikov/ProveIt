import ZFCinPA.SizedDriverBase
import ZFCinPA.SizedStepAtom
import ZFCinPA.SizedStepNeg

/-!
# The bounded driver: atomic cases

The cases `^rel`, `^nrel`, `^⊤`, `^⊥` of the bounded driver induction.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedDriver

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.TemplateTranslateLevel
open LeanProofs.ZFCinPA.SizedCongruence (lt_lvB_succ le_of_add_eq)
open LeanProofs.ZFCinPA.SizedPlaceholderCongruence (conn_le verum_le)
open LeanProofs.ZFCinPA.SizedLNumOK LeanProofs.ZFCinPA.SizedDriverSteps
open LeanProofs.ZFCinPA.SizedEnvForm (Eb Ef0 envForm_le atomOf_le idx_le falsum_le)
open LeanProofs.ZFCinPA.LTemplate LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.LStepAnd
open LeanProofs.ZFCinPA.LStepBasic LeanProofs.ZFCinPA.LStepAtom LeanProofs.ZFCinPA.LStepExT
open LeanProofs.ZFCinPA.LDriverBase LeanProofs.ZFCinPA.LDriverSteps LeanProofs.ZFCinPA.LDriver
open LeanProofs.ZFCinPA.EnvTransform
open LeanProofs.ZFCinPA.NumeralOmega (numChainQ numChainQ_val)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local notation "Fm" => Bootstrapping.Formula V ℒₛₑₜ

theorem succT_le_Gd (M q : V) : (succT (V := V)).val ≤ lvB (Gd M q) :=
  lift_lvB (le_lvB_self _) (le_trans (succT_le_Ad M) (Ad_le_Gd M q))

/-- The two set atoms `=` (tag 0) and `∈` (tag 1) as `AtomT` codes. -/
theorem atom_val {n R v : V} (hR : R = 0 ∨ R = 1) :
    ∃ b, (AtomT b (numChainQ (idx n v.[0])) (numChainQ (idx n v.[1]))).val = atomOf n R v := by
  rcases hR with rfl | rfl
  · exact ⟨true, by rw [atomT_val_eq, atomOf]⟩
  · exact ⟨false, by rw [atomT_val_mem _ _ 1 _root_.one_ne_zero, atomOf]⟩

/-- The numeral-slot derivations and bounds of a binary atom, shared by `case_rel`
and `case_nrel`. -/
theorem atom_slots {M n R v : V} (hR : (ℒₛₑₜ).IsRel 2 R) (hv : IsSemitermVec ℒₛₑₜ 2 n v)
    (hX : n + ⟪(2 : V), R, v⟫ ≤ M) :
    DLv 𝗭𝗙 (insert (NumOKT (numChainQ (idx n v.[0]))).val ∅) (Wd M) ∧
      DLv 𝗭𝗙 (insert (NumOKT (numChainQ (idx n v.[1]))).val ∅) (Wd M) ∧
      (numChainQ (idx n v.[0])).val ≤ lvB (uD M) ∧
      (numChainQ (idx n v.[1])).val ≤ lvB (uD M) ∧ atomOf n R v ≤ lvB (uD M) := by
  have s₀ := slot_idx hv (show (0 : V) < 2 by norm_num) hX
  have s₁ := slot_idx hv (show (1 : V) < 2 by norm_num) hX
  exact ⟨(numOK_leJ s₀).mono (numOK_W s₀), (numOK_leJ s₁).mono (numOK_W s₁),
    lift_lvB (numQ_le_A0 s₀) (A0_le_uD M), lift_lvB (numQ_le_A0 s₁) (A0_le_uD M),
    lift_lvB (atom_le_A0 hR hv hX) (A0_le_uD M)⟩

set_option maxHeartbeats 4000000 in
theorem case_rel (M : V) :
    ∀ n k r v, (ℒₛₑₜ).IsRel k r → IsSemitermVec ℒₛₑₜ k n v →
    ΘB (Ad M) Kd (Wd M + 60) M n (^rel k r v) := by
  have hu := two_le_uD M
  unfold ΘB
  intro n k R v hR hv hnM
  have hR' := hR
  obtain ⟨rfl, hR01⟩ := LDriver.isRel_set hR
  have hrel := envForm_rel (d := n) hR hv.isUTerm
  have hX : n + ⟪(2 : V), R, v⟫ ≤ M :=
    le_trans (_root_.add_le_add le_rfl (le_trans (le_pair_right 0 _) le_self_add)) hnM
  obtain ⟨h₀, h₂, lN₀, lN₂, lAt⟩ := atom_slots hR' hv hX
  obtain ⟨b, hval⟩ := atom_val hR01
  have hK := K6_le lN₀ (top_le hu) lN₂ (top_le hu) (hval.trans_le lAt) (succT_le_uD M)
  have d := atom_step_le b hu hK (wD_le_Wd M) h₀ h₂
  exact ΘB_of_typed _ (hval.trans hrel.symm) succT (succT_le_Gd M _)
    (d.mono (le_of_add_eq (y := 30 + 40 * ^rel 2 R v) (by ring)))

set_option maxHeartbeats 4000000 in
theorem case_nrel (M : V) :
    ∀ n k r v, (ℒₛₑₜ).IsRel k r → IsSemitermVec ℒₛₑₜ k n v →
    ΘB (Ad M) Kd (Wd M + 60) M n (^nrel k r v) := by
  have hu := two_le_uD M
  unfold ΘB
  intro n k R v hR hv hnM
  have hR' := hR
  obtain ⟨rfl, hR01⟩ := LDriver.isRel_set hR
  have hnrel := envForm_nrel (d := n) hR hv.isUTerm
  have hsem : IsSemiformula ℒₛₑₜ n (^nrel 2 R v) := by simp [hR', hv]
  have lN := lift_lvB (envF_le hsem hnM) (A0_le_uD M)
  have hX : n + ⟪(2 : V), R, v⟫ ≤ M :=
    le_trans (_root_.add_le_add le_rfl (le_trans (le_pair_right 1 _) le_self_add)) hnM
  obtain ⟨h₀, h₂, lN₀, lN₂, lAt⟩ := atom_slots hR' hv hX
  obtain ⟨b, hval⟩ := atom_val hR01
  have hK := K6_le lN₀ (top_le hu) lN₂ (top_le hu) (hval.trans_le lAt) (succT_le_uD M)
  have d₁ := atom_step_le b hu hK (wD_le_Wd M) h₀ h₂
  have hnv : (∼AtomT b (numChainQ (idx n v.[0])) (numChainQ (idx n v.[1]))).val =
      envForm n (^nrel 2 R v) := by rw [Bootstrapping.Semiformula.val_neg, hval, hnrel]
  have hKn := K6_le (hval.trans_le lAt) (succT_le_uD M) (top_le hu) (top_le hu)
    (hnv.trans_le lN) (succT_le_uD M)
  have d₂ := neg_step_le hu hKn (le_trans (wD_le_Wd M) le_self_add) d₁
  exact ΘB_of_typed _ hnv succT (succT_le_Gd M _)
    (d₂.mono (le_of_add_eq (y := 40 * ^nrel 2 R v) (by ring)))

set_option maxHeartbeats 4000000 in
theorem case_verum (M : V) :
    ∀ n, ΘB (Ad M) Kd (Wd M + 60) M n ^⊤ := by
  have hu := two_le_uD M
  unfold ΘB
  intro n _
  have hK := K6_le (top_le hu) (top_le hu) (top_le hu) (top_le hu) (top_le hu) (succT_le_uD M)
  have d := top_base_le hu hK (wD_le_Wd M)
  exact ΘB_of_typed ⊤ (by simp) succT (succT_le_Gd M _)
    (d.mono (le_of_add_eq (y := 30 + 40 * ^⊤) (by ring)))

set_option maxHeartbeats 4000000 in
theorem case_falsum (M : V) :
    ∀ n, ΘB (Ad M) Kd (Wd M + 60) M n ^⊥ := by
  have hu := two_le_uD M
  unfold ΘB
  intro n _
  have hK := K6_le (top_le hu) (top_le hu) (top_le hu) (top_le hu)
    (show (⊥ : SF V 1).val ≤ lvB (uD M) by simpa using falsum_le hu) (succT_le_uD M)
  have d := bot_base_le hu hK (wD_le_Wd M)
  exact ΘB_of_typed ⊥ (by simp) succT (succT_le_Gd M _)
    (d.mono (le_of_add_eq (y := 30 + 40 * ^⊥) (by ring)))

end LeanProofs.ZFCinPA.SizedDriver
