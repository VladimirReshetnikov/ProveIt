import BusyBeaver.ZFC.ArithmeticDagRootPerm222
import DiophantineConsistency.ArithmeticEnumRunPerm222
import BusyBeaver.ZFC.ArithmeticPositiveSimulation254

/-! The actual internal permuted enumerator and the actual DagPerm control run
halt together, from every literal scheduler boundary. The boundary relation is
represented by a fixed Sigma1 formula. Actual root execution and pointer/candidate
progress discharge all simulation premises, including strictly positive clocks
for normal steps. The unchanged generic positive-clock theorem is used only for
internal time transport. No old254 scheduler semantics, supplied structured run,
215 tape/boot simulation, source consistency or PA/HA endpoint is used here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace SetTheory.BusyBeaver.ZFC.ArithmeticDagRuntimePerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticDagMacrosPerm222 ArithmeticDagRootPerm222
open DiophantineConsistency
open ArithmeticCommandStepPerm222 (stateValue)
open ArithmeticEnumStepPerm222 (enumValue)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Control 1 with the actual physical scheduler boundary. -/
noncomputable def controlOf (pl np t S d h : V) : V :=
  ArithmeticControlFile.liveValue 1 (enc (boundary pl np t S d h))

/-- Both scalar codes are actual live states, with the same six internal data. -/
def Related (l c : V) : Prop :=
  ∃ pl np t S d h : V,
    l = ArithmeticEnumStepPerm222.liveValue pl np (stateValue t S d h) ∧
    c = controlOf pl np t S d h

theorem enc_boundary (pl np t S d h : V) :
    enc (boundary pl np t S d h) =
      ArithmeticControlFile.fileValue ![S,pl,t,d,0,0,np,h,0] := rfl

/-- Fixed syntax, before any ambient-model parameters. -/
def relatedDef : 𝚺₁.Semisentence 2 := .mkSigma
  “l c. ∃ pl, ∃ np, ∃ t, ∃ S, ∃ d, ∃ h, ∃ w, ∃ f,
    !ArithmeticCommandStepPerm222.stateDef w t S d h ∧
    !ArithmeticEnumStepPerm222.liveDef l pl np w ∧
    !ArithmeticControlFile.fileDef f S pl t d 0 0 np h 0 ∧
    !ArithmeticControlFile.liveDef c 1 f”

instance related_defined : 𝚺₁-Relation[V] Related via relatedDef := .mk fun e => by
  simp [relatedDef, Related, controlOf, enc_boundary,
    ArithmeticControlFile.file_defined.iff, Matrix.comp_vecCons', Matrix.empty_eq,
    Matrix.constant_eq_singleton]

instance related_definable : 𝚺₁-Relation[V] Related :=
  related_defined.to_definable

theorem related_live {l c : V} (hr : Related l c) : l ≠ 0 := by
  obtain ⟨pl,np,t,S,d,h,rfl,_⟩ := hr
  simp [ArithmeticEnumStepPerm222.liveValue]

theorem related_active {l c : V} (hr : Related l c) : c ≠ 0 := by
  obtain ⟨pl,np,t,S,d,h,_,rfl⟩ := hr
  exact ArithmeticControlFile.live_ne_zero _ _

/-- Root progress changes physical register 1 (pointer) or 6 (candidate). -/
theorem boundary_ne_of_progress {pl np t S d h pl' np' t' S' d' h' : V}
    (hp : pl' < pl ∨ np' = np+1) :
    enc (boundary pl np t S d h) ≠ enc (boundary pl' np' t' S' d' h') := by
  intro he
  have hpl : pl = pl' := by
    simpa [enc_boundary] using
      congrArg (fun x => ArithmeticControlFile.regValue x (1 : Fin 9)) he
  have hnp : np = np' := by
    simpa [enc_boundary] using
      congrArg (fun x => ArithmeticControlFile.regValue x (6 : Fin 9)) he
  rcases hp with hlt | heq
  · exact (_root_.lt_irrefl pl) (hpl ▸ hlt)
  · rw [heq] at hnp
    exact (_root_.lt_irrefl np) (lt_of_lt_of_eq (lt_add_one np) hnp.symm)

private theorem liveFile_inj {q x y : V}
    (he : ArithmeticControlFile.liveValue q x = ArithmeticControlFile.liveValue q y) :
    x = y := by
  simpa only [ArithmeticControlFile.fileCode_live] using
    congrArg ArithmeticControlFile.fileCodeValue he

/-- The unconditional root theorem supplies the next boundary and a clock;
the actual progress clause rules out clock zero. -/
theorem related_step (l c : V) (hr : Related l c) (hn : enumValue l ≠ 0) :
    ∃ k, 0 < k ∧ Related (enumValue l) (ArithmeticDagControlPerm222.run k c) := by
  obtain ⟨pl,np,t,S,d,h,rfl,rfl⟩ := hr
  rcases root_step pl np t S d h with
    ⟨hz,_⟩ | ⟨pl',np',t',S',d',h',hv,hrn,hp⟩
  · exact absurd hz hn
  · obtain ⟨k,hk⟩ := ArithmeticDagControlPerm222.root_reach_normal hrn
    refine ⟨k,?_,pl',np',t',S',d',h',hv,hk⟩
    rcases (Arithmetic.zero_le k).lt_or_eq with hpos | hzero
    · exact hpos
    · exfalso
      rw [← hzero, ArithmeticDagControlPerm222.run_zero] at hk
      exact boundary_ne_of_progress hp (liveFile_inj hk)

/-- Actual scheduler halting gives an actual whole-root halting execution. -/
theorem related_halt (l c : V) (hr : Related l c) (hz : enumValue l = 0) :
    ∃ k, ArithmeticDagControlPerm222.run k c = 0 := by
  obtain ⟨pl,np,t,S,d,h,rfl,rfl⟩ := hr
  rcases root_step pl np t S d h with
    ⟨_,y,hy⟩ | ⟨pl',np',t',S',d',h',hv,_,_⟩
  · exact ArithmeticDagControlPerm222.root_reach_halt hy
  · rw [hv] at hz
    have hn : ArithmeticEnumStepPerm222.liveValue pl' np' (stateValue t' S' d' h') ≠ 0 := by
      simp [ArithmeticEnumStepPerm222.liveValue]
    exact absurd hz hn

/-- A live control state also excludes a zero clock in the halting branch. -/
theorem related_halt_pos (l c : V) (hr : Related l c) (hz : enumValue l = 0) :
    ∃ k, 0 < k ∧ ArithmeticDagControlPerm222.run k c = 0 := by
  obtain ⟨k,hk⟩ := related_halt l c hr hz
  refine ⟨k,?_,hk⟩
  rcases (Arithmetic.zero_le k).lt_or_eq with hpos | hzero
  · exact hpos
  · exfalso
    rw [← hzero, ArithmeticDagControlPerm222.run_zero] at hk
    exact related_active hr hk

/-- Both directions hold at arbitrary internal times and data. The generic
clock invariant is Sigma1; no universal predicate induction is introduced. -/
theorem halts_iff (pl np t S d h : V) :
    (∃ n, ArithmeticEnumRunPerm222.run n
      (ArithmeticEnumStepPerm222.liveValue pl np (stateValue t S d h)) = 0) ↔
    (∃ k, ArithmeticDagControlPerm222.run k (controlOf pl np t S d h) = 0) := by
  haveI : 𝚺₁-Function₁[V] (fun n => ArithmeticEnumRunPerm222.run n
      (ArithmeticEnumStepPerm222.liveValue pl np (stateValue t S d h))) := by
    definability
  apply ArithmeticPositiveSimulation254.halts_iff
    enumValue
    (fun n => ArithmeticEnumRunPerm222.run n
      (ArithmeticEnumStepPerm222.liveValue pl np (stateValue t S d h)))
    ArithmeticDagControlPerm222.run Related (fun c => c = 0)
    (ArithmeticEnumStepPerm222.liveValue pl np (stateValue t S d h))
    (controlOf pl np t S d h)
  · exact ArithmeticEnumRunPerm222.run_zero _
  · intro n; exact ArithmeticEnumRunPerm222.run_succ n _
  · exact ArithmeticDagControlPerm222.run_zero
  · exact ArithmeticDagControlPerm222.run_add
  · exact ⟨pl,np,t,S,d,h,rfl,rfl⟩
  · intro l c hr; exact related_live hr
  · intro l c hr; exact related_active hr
  · exact related_step
  · exact related_halt
  · rintro c rfl k
    exact ArithmeticDagControlPerm222.run_halted k

theorem seed_record : boundary (0 : V) 4 0 0 0 0 =
    (⟨4,0,0,0,0,0,0,0,0⟩ : AS V) := rfl

/-- The current literal seed is pointer 0, candidate 4, and working code 0. -/
theorem seed_halts_iff :
    (∃ n : V, ArithmeticEnumRunPerm222.run n
      (ArithmeticEnumStepPerm222.liveValue 0 4 0) = 0) ↔
    (∃ k : V, ArithmeticDagControlPerm222.run k
      (ArithmeticControlFile.liveValue 1
        (ArithmeticControlFile.fileValue ![0,0,0,0,0,0,4,0,0])) = 0) := by
  have hwork : stateValue (0 : V) 0 0 0 = 0 := by simp [stateValue, cantor, triangle]
  simpa only [controlOf, enc_boundary, hwork] using
    halts_iff (0 : V) 4 0 0 0 0

end SetTheory.BusyBeaver.ZFC.ArithmeticDagRuntimePerm222
