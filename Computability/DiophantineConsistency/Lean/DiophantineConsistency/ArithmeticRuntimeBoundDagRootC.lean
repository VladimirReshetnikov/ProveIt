import DiophantineConsistency.ArithmeticRuntimeBoundDagRootB

/-! # Bounded DagPerm root, part C: command step, fetch, root step and root reach

Bounded twins of `command_step`, `fetch_run`, `root_step` of
`ArithmeticDagRootPerm222` and of `root_reach_normal`/`root_reach_halt` of
`ArithmeticDagControlPerm222`. From a boundary record of size at most `tower j L`,
one actual enumerator step costs at most `tower j (L + KR)` DagPerm control steps.
No existing statement is changed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticRuntimeBoundDagMacros
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor ArithmeticDagRun RMDag
open ArithmeticDagMacrosPerm222
open ArithmeticRuntimeBoundDagRun ArithmeticEnumBoundTower
open ArithmeticCode254 (wim)
open ArithmeticDagRootPerm222 (f236 ax_eval mpOut boundary selector_cases)
open DiophantineConsistency.ArithmeticCommandStepPerm222
open DiophantineConsistency.ArithmeticCommandWordPerm222
open DiophantineConsistency.ArithmeticCommandFetchPerm222
open DiophantineConsistency.ArithmeticEnumStepPerm222 (enumValue execValue enum_live)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Offset of one command (selector read plus dispatch). -/
def KC : ℕ := KAX + 20
/-- Offset of one root step (fetch plus command). -/
def KR : ℕ := KC + 7

theorem KC_ge : 130 ≤ KC := by unfold KC KAX; omega

variable {j : V} {L : ℕ} (hL : 2 ≤ L)
include hL

theorem command_stepB (raw np t S d h : V) (hs : sz (boundary raw np t S d h) ≤ tower j L) :
    (stepValue raw (stateValue t S d h) = 0 ∧
      ∃ y, IRB (.node 139) (enc (boundary raw np t S d h)) .halt y (tower j (L+KC))) ∨
    ∃ t' S' d' h', stepValue raw (stateValue t S d h) = someState t' S' d' h' ∧
      RnB (.node 139) (boundary raw np t S d h) (boundary (tailValue raw) np t' S' d' h')
        (tower j (L+KC)) := by
  have hs17 := read_sz hL raw np t S d h hs
  have hK := KC_ge
  have hadd : ∀ k : ℕ, k + 18 ≤ KC →
      tower j (L+17) + tower j (L+17+k) ≤ tower j (L+KC) := fun k hk =>
    le_tower_of (add_le_tower_of (c := L+17+k) (by omega) (by omega) le_rfl le_rfl le_rfl)
      (by omega)
  rcases selector_cases (first raw) with h0|h1|h2|⟨c,hc⟩
  · by_cases hh : h=1
    · refine Or.inl ⟨by simp [stepValue,stateValue,effectValue,h0,hh],?_⟩
      obtain ⟨y,hy⟩ := dispatch_nip_haltB (L := L+17) (by omega)
        (⟨np,t,S,first raw,d,h,0,0,second raw⟩ : AS V) ⟨rfl,rfl⟩ h0 hh hs17
      have hr := read_acM hL (boundary raw np t S d h) ⟨rfl,rfl⟩ hs
      simp only [boundary,zero_add] at hr
      exact ⟨y, irunB_mono (RB.halt_cdr (n:=139) rfl hr.1 hy) (hadd 5 (by omega))⟩
    · refine Or.inr ⟨t,second S,d,first S,by simp [stepValue,stateValue,effectValue,h0,hh],?_⟩
      have hd := (dispatch_nipM (L := L+17) (by omega)
        (⟨np,t,S,first raw,d,h,0,0,second raw⟩ : AS V) ⟨rfl,rfl⟩ h0 hh hs17).1
      exact irunB_mono (irb_eq (read_runT hL raw np t S d h hs hd)
        (by simp [boundary,tailValue,h0])) (hadd 27 (by omega))
  · refine Or.inr ⟨h,cantor t S,d,h,by simp [stepValue,stateValue,effectValue,h1],?_⟩
    have hs1 : sz ({ (⟨np,t,S,0,d,h,0,0,second raw⟩ : AS V) with ac := 1 }) ≤ tower j (L+17) := by
      have := hs17; rw [h1] at this; exact this
    have hd := dispatch_dropT (L := L+17) (by omega) (⟨np,t,S,0,d,h,0,0,second raw⟩ : AS V)
      ⟨rfl,rfl⟩ hs1
    have he : (⟨np,t,S,first raw,d,h,0,0,second raw⟩ : AS V)=
        ⟨np,t,S,1,d,h,0,0,second raw⟩ := by rw [h1]
    exact irunB_mono (irb_eq (read_runT hL raw np t S d h hs (he ▸ hd))
      (by simp [boundary,tailValue,h1])) (hadd 25 (by omega))
  · have hs2 : sz ({ (⟨np,t,S,0,d,h,0,0,second raw⟩ : AS V) with ac := 2 }) ≤ tower j (L+17) := by
      have := hs17; rw [h2] at this; exact this
    have hd := dispatch_mpT (L := L+17) (by omega) (⟨np,t,S,0,d,h,0,0,second raw⟩ : AS V)
      ⟨rfl,rfl⟩ hs2
    have he : (⟨np,t,S,first raw,d,h,0,0,second raw⟩ : AS V)=
        ⟨np,t,S,2,d,h,0,0,second raw⟩ := by rw [h2]
    have hr := irunB_mono (read_runT hL raw np t S d h hs (he ▸ hd)) (hadd 106 (by omega))
    by_cases hm : wim t (d+first (second raw))=h
    · refine Or.inr ⟨d+first (second raw),cantor 0 S,d+first (second raw),0,
        by simp [stepValue,stateValue,effectValue,h2,hm],?_⟩
      simpa only [mpOut,hm,if_true,boundary,tailValue,h2,lt_self_iff_false,if_false] using hr
    · refine Or.inr ⟨0,S,d+first (second raw),0,
        by simp [stepValue,stateValue,effectValue,h2,hm],?_⟩
      simpa only [mpOut,hm,if_false,boundary,tailValue,h2,lt_self_iff_false,if_true] using hr
  · have h3 : (3:V)≤first raw := hc ▸ le_add_self
    have h23 : (2:V)<3 := by simpa only [two_add_one_eq_three] using lt_add_one (2:V)
    have hk := lt_of_lt_of_le h23 h3
    have hz : first raw≠0 := ne_of_gt (lt_trans (by simp : (0:V)<2) hk)
    have ho : first raw≠1 := ne_of_gt (lt_trans (by simp : (1:V)<2) hk)
    have ht : first raw≠2 := ne_of_gt hk
    have hsub : first raw-3=c := by rw [hc,add_tsub_cancel_right]
    refine Or.inr ⟨gateValue (d+first (second (second raw))) (h+first (second raw)) c,
      axStackValue (d+first (second (second raw))) h (h+first (second raw)) c d t S,0,0,
      by simp [stepValue,stateValue,effectValue,hz,ho,ht,hsub],?_⟩
    have hs3 : sz ({ (⟨np,t,S,0,d,h,0,0,second raw⟩ : AS V) with ac := c + 3 }) ≤
        tower j (L+17) := by
      have := hs17; rw [hc] at this; exact this
    have hd := dispatch_axT (L := L+17) (by omega) (⟨np,t,S,0,d,h,0,0,second raw⟩ : AS V)
      ⟨rfl,rfl⟩ c hs3
    have he : (⟨np,t,S,first raw,d,h,0,0,second raw⟩ : AS V)=
        ⟨np,t,S,c+3,d,h,0,0,second raw⟩ := by rw [hc]
    have hr := irunB_mono (read_runT hL raw np t S d h hs (he ▸ hd)) (hadd (KAX+1) (by unfold KC; omega))
    rw [ax_eval] at hr
    simpa only [boundary,tailValue,not_lt_of_ge (le_of_lt hk),ht,if_false] using hr

theorem fetch_runM (pl np t S d h : V) (hs : sz (boundary pl np t S d h) ≤ tower j L) :
    Mac (.node 133) (boundary pl np t S d h)
      (boundary (first (fetchValue pl np)) (second (fetchValue pl np)) t S d h) j L 5 := by
  by_cases hz : pl=0
  · subst pl
    simpa only [boundary,raw_new,next_new] using fetch_zeroM hL (boundary 0 np t S d h) rfl rfl hs
  · have hp := pred_add_one pl hz
    have hf := (fetch_posM hL (boundary pl np t S d h) (pl-1) hp.symm hs).mono (show 1 ≤ 5 by omega)
    simpa only [boundary,fetchValue,hz,if_false,first_cantor,second_cantor] using hf

/-- One actual root execution within `tower j (L+KR)` control steps. -/
theorem root_stepB (pl np t S d h : V) (hs : sz (boundary pl np t S d h) ≤ tower j L) :
    (enumValue (DiophantineConsistency.ArithmeticEnumStepPerm222.liveValue pl np
        (stateValue t S d h)) = 0 ∧
      ∃ y, IRB (.node 0) (enc (boundary pl np t S d h)) .halt y (tower j (L+KR))) ∨
    ∃ pl' np' t' S' d' h',
      enumValue (DiophantineConsistency.ArithmeticEnumStepPerm222.liveValue pl np
        (stateValue t S d h)) =
        DiophantineConsistency.ArithmeticEnumStepPerm222.liveValue pl' np' (stateValue t' S' d' h') ∧
      RnB (.node 0) (boundary pl np t S d h) (boundary pl' np' t' S' d' h') (tower j (L+KR)) ∧
      (pl' < pl ∨ np' = np+1) := by
  have hf := fetch_runM hL pl np t S d h hs
  have hb : tower j (L+5) + tower j (L+5+KC) ≤ tower j (L+KR) :=
    le_tower_of (add_le_tower_of (c := L+5+KC) (by omega) (by omega) le_rfl le_rfl le_rfl)
      (by unfold KR; omega)
  rcases command_stepB (L := L+5) (by omega) (first (fetchValue pl np)) (second (fetchValue pl np))
      t S d h hf.2 with ⟨hz,y,hy⟩|⟨t',S',d',h',he,hr⟩
  · refine Or.inl ⟨?_, y, irunB_mono (RB.halt_cdr (n:=0) rfl hf.1 hy) hb⟩
    rw [enum_live, execValue, hz, if_pos rfl]
  · refine Or.inr ⟨tailValue (first (fetchValue pl np)), second (fetchValue pl np), t', S', d', h',
      ?_, irunB_mono (RB.seq (n:=0) rfl hf.1 hr) hb, ?_⟩
    · rw [enum_live, execValue, he]
      simp [someState]
    · by_cases hz : pl=0
      · right; subst pl; exact next_new np
      · left; exact lt_iff_succ_le.mpr (continuation_progress pl np hz)

omit hL in
/-- `root_reach_normal` with its clock. -/
theorem root_reach_normalB {x y B : V} (h : IRB (.node 0) x .normal y B) :
    ∃ t ≤ B, ArithmeticDagControlPerm222.run t (ArithmeticControlFile.liveValue 1 x) =
      ArithmeticControlFile.liveValue 1 y := by
  simpa [ReachB, ArithmeticDagControlPerm222.rootExit] using
    h 488 1 ArithmeticDagControlPerm222.rootExit ArithmeticDagControlPerm222.root_occ

omit hL in
/-- `root_reach_halt` with its clock. -/
theorem root_reach_haltB {x y B : V} (h : IRB (.node 0) x .halt y B) :
    ∃ t ≤ B, ArithmeticDagControlPerm222.run t (ArithmeticControlFile.liveValue 1 x) = 0 := by
  simpa [ReachB] using
    h 488 1 ArithmeticDagControlPerm222.rootExit ArithmeticDagControlPerm222.root_occ

end DiophantineConsistency.ArithmeticRuntimeBoundDagMacros
