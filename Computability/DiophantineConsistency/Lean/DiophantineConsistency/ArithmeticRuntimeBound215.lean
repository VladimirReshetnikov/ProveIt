import DiophantineConsistency.ArithmeticRuntime215
import DiophantineConsistency.ArithmeticRuntimeBoundBisim
import DiophantineConsistency.ArithmeticEnumBoundSoundness

/-! # Blank decimal215 halt ⇒ refutation below an explicit elementary bound

The halt-to-refutation direction of `ArithmeticCheckerMachine215` composes four
layers. In this direction every time transfer is monotone with an explicit
factor:

* blank machine time `t` ↦ boot-continuation time `t-95714 ≤ t`;
* binary/p215 positive-clock simulation: the logical halting time is `≤` the
  binary one, since every logical step costs a positive clock
  (`logical_halts_le_of_binary_halts`, a bounded form of
  `ArithmeticPositiveSimulation254.logical_halts_of_binary_halts`);
* p215 ↦ DagPerm control: at most `7×` (`ArithmeticRuntimeBoundBisim`);
* DagPerm control ↦ enumerator: again positive clocks, so `≤`.

The enumerator halt at time `n` then exposes an accepted C222 refutation below
`2^(2^(100*n+8))` (`ArithmeticEnumBoundSoundness`). Altogether a blank halt at
internal time `t` yields a refutation code below `2^(2^(700*t+8))`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticRuntimeBound215
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor

section Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Bounded positive-clock transport: a binary halt at `t` forces a logical
halt at some `n ≤ t`. The premises are those of `ArithmeticPositiveSimulation254`. -/
theorem logical_halts_le_of_binary_halts
    (logicalStep : V → V) (logicalRun : V → V) (binaryRun : V → V → V)
    (Related : V → V → Prop) (Halted : V → Prop)
    [𝚺₁-Function₁[V] logicalRun] [𝚺₁-Function₂[V] binaryRun] [𝚺₁-Relation[V] Related]
    (logicalInitial binaryInitial : V)
    (logical_zero : logicalRun 0 = logicalInitial)
    (logical_succ : ∀ n, logicalRun (n+1) = logicalStep (logicalRun n))
    (binary_zero : ∀ b, binaryRun 0 b = b)
    (binary_add : ∀ t u b, binaryRun (t+u) b = binaryRun u (binaryRun t b))
    (initial_related : Related logicalInitial binaryInitial)
    (related_active : ∀ l b, Related l b → ¬ Halted b)
    (related_step : ∀ l b, Related l b → logicalStep l ≠ 0 →
      ∃ k, 0 < k ∧ Related (logicalStep l) (binaryRun k b))
    (halt_persists : ∀ b, Halted b → ∀ k, Halted (binaryRun k b))
    (t : V) (ht : Halted (binaryRun t binaryInitial)) :
    ∃ n ≤ t, logicalRun n = 0 := by
  by_contra hne
  have hl : ∀ n ≤ t, logicalRun n ≠ 0 := fun n hn h => hne ⟨n, hn, h⟩
  have reach : ∀ n : V, n ≤ t → ∃ clock, n ≤ clock ∧
      Related (logicalRun n) (binaryRun clock binaryInitial) := by
    intro n
    induction n using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      intro _
      exact ⟨0, le_rfl, by simpa only [logical_zero, binary_zero] using initial_related⟩
    case succ n ih =>
      intro hn
      obtain ⟨clock, hc, hr⟩ := ih (le_trans le_self_add hn)
      have hcont : logicalStep (logicalRun n) ≠ 0 := by
        rw [← logical_succ]
        exact hl (n+1) hn
      obtain ⟨k, hk, hs⟩ := related_step _ _ hr hcont
      refine ⟨clock+k, _root_.add_le_add hc (by simpa only [zero_add] using lt_iff_succ_le.mp hk), ?_⟩
      rw [logical_succ, binary_add]
      exact hs
  obtain ⟨clock, hc, hr⟩ := reach t le_rfl
  have hh : Halted (binaryRun clock binaryInitial) := by
    have he : t + (clock-t) = clock := add_tsub_cancel_of_le hc
    rw [← he, binary_add]
    exact halt_persists _ ht _
  exact related_active _ _ hr hh

end Transport

section Layers
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- DagPerm control halt from the literal seed file ⇒ enumerator halt no later. -/
theorem enum_halts_le_of_dag (k : V)
    (hk : ArithmeticDagControlPerm222.run k (ArithmeticControlFile.liveValue 1
      (ArithmeticControlFile.fileValue ![0,0,0,0,0,0,4,0,0])) = 0) :
    ∃ n ≤ k, ArithmeticEnumRunPerm222.run n (ArithmeticEnumStepPerm222.liveValue 0 4 0) = 0 := by
  have hwork : ArithmeticCommandStepPerm222.stateValue (0 : V) 0 0 0 = 0 := by
    simp [ArithmeticCommandStepPerm222.stateValue, cantor, triangle]
  have hc : ArithmeticDagRuntimePerm222.controlOf (0 : V) 4 0 0 0 0 =
      ArithmeticControlFile.liveValue 1
        (ArithmeticControlFile.fileValue ![0,0,0,0,0,0,4,0,0]) := by
    simp only [ArithmeticDagRuntimePerm222.controlOf, ArithmeticDagRuntimePerm222.enc_boundary]
  haveI : 𝚺₁-Function₁[V] (fun n => ArithmeticEnumRunPerm222.run n
      (ArithmeticEnumStepPerm222.liveValue 0 4 0)) := by
    definability
  rw [← hc] at hk
  exact logical_halts_le_of_binary_halts
    ArithmeticEnumStepPerm222.enumValue
    (fun n => ArithmeticEnumRunPerm222.run n (ArithmeticEnumStepPerm222.liveValue 0 4 0))
    ArithmeticDagControlPerm222.run ArithmeticDagRuntimePerm222.Related (fun c => c = 0)
    (ArithmeticEnumStepPerm222.liveValue 0 4 0) (ArithmeticDagRuntimePerm222.controlOf 0 4 0 0 0 0)
    (ArithmeticEnumRunPerm222.run_zero _)
    (fun n => ArithmeticEnumRunPerm222.run_succ n _)
    ArithmeticDagControlPerm222.run_zero ArithmeticDagControlPerm222.run_add
    ⟨0, 4, 0, 0, 0, 0, by rw [hwork], rfl⟩
    (fun l c hr => ArithmeticDagRuntimePerm222.related_active hr)
    ArithmeticDagRuntimePerm222.related_step
    (by rintro c rfl k; exact ArithmeticDagControlPerm222.run_halted k)
    k hk

open ArithmeticControlFile ArithmeticControlTable ArithmeticControl215Table
open ArithmeticMachineTape215 ArithmeticControlFrame215

/-- `blank_halts_iff_boot`, forward direction, with the explicit time `t-95714`. -/
theorem boot_halts_le_of_blank (t : V) (ht : first (ArithmeticMachineRun215.run t) = 0) :
    ∃ t' ≤ t, first (runFrom t' (bootCode : V)) = 0 := by
  have hle : (95714 : V) ≤ t := by
    by_contra hn
    have hlt : t < 95714 := lt_of_not_ge hn
    have he : t + (95714 - t) = 95714 := add_tsub_cancel_of_le (le_of_lt hlt)
    have hz : first (ArithmeticMachineRun215.run (95714 : V)) = 0 := by
      rw [← runFrom_blank, ← he, runFrom_add, runFrom_blank, runFrom_halted _ _ ht]
      exact ht
    rw [internal_boot, bootCode_state] at hz
    exact (by simp : (24 : V) ≠ 0) hz
  refine ⟨t - 95714, tsub_le_self, ?_⟩
  rw [← continuation, add_tsub_cancel_of_le hle]
  exact ht

/-- Blank decimal215 halt at `t` ⇒ p215 control halt from the seed at `n ≤ t`. -/
theorem control_halts_le_of_blank (t : V) (ht : first (ArithmeticMachineRun215.run t) = 0) :
    ∃ n ≤ t, run215 n (liveValue 1 ArithmeticRuntime215.seedFile) = 0 := by
  obtain ⟨t', ht', hb⟩ := boot_halts_le_of_blank t ht
  rw [← ArithmeticRuntime215.seed_entry] at hb
  haveI : 𝚺₁-Function₁[V] (fun n => run215 n (liveValue 1 ArithmeticRuntime215.seedFile)) := by
    definability
  obtain ⟨n, hn, hz⟩ := logical_halts_le_of_binary_halts
    (stepValue table215) (fun n => run215 n (liveValue 1 ArithmeticRuntime215.seedFile))
    runFrom ArithmeticRuntime215.Related (fun b => first b = 0)
    (liveValue 1 ArithmeticRuntime215.seedFile)
    (entryValue 1 ArithmeticRuntime215.seedFile 40 1)
    (run215_zero _) (fun n => controlRun_succ table215 n _) runFrom_zero runFrom_add
    ⟨1, ArithmeticRuntime215.seedFile, 40, 1, by simp, ArithmeticRuntime215.seed_supported,
      rfl, rfl⟩
    (fun l b hr => ArithmeticRuntime215.related_active hr)
    ArithmeticRuntime215.related_step
    (fun b hb k => by rwa [ArithmeticRuntime215.halt_absorbs b k hb])
    t' hb
  exact ⟨n, le_trans hn ht', hz⟩

/-- **Blank halt ⇒ enumerator halt, with a linear time bound.** -/
theorem enum_halts_le_of_blank (t : V) (ht : first (ArithmeticMachineRun215.run t) = 0) :
    ∃ n ≤ 7 * t, ArithmeticEnumRunPerm222.run n (ArithmeticEnumStepPerm222.liveValue 0 4 0) = 0 := by
  obtain ⟨n1, hn1, h1⟩ := control_halts_le_of_blank t ht
  obtain ⟨k, hk, h2⟩ := ArithmeticRuntimeBoundBisim.dag_halts_le_of_215
    ArithmeticRuntime215.seedFile n1 h1
  obtain ⟨n, hn, h3⟩ := enum_halts_le_of_dag k h2
  refine ⟨n, le_trans hn (le_trans hk ?_), h3⟩
  exact mul_le_mul_of_nonneg_left hn1 (Arithmetic.zero_le 7)

end Layers

section Endpoint
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **(a) Halt ⇒ refutation, with an explicit elementary witness bound.**
If the literal blank decimal215 machine halts at internal time `t`, the actual
C222 checker accepts a refutation code below `2^(2^(700*t+8))`. -/
theorem refutation_bound_of_blank_halts (t : V)
    (ht : first (ArithmeticMachineRun215.run t) = 0) :
    ∃ proof ≤ Exp.exp (Exp.exp (700 * t + 8)),
      ArithmeticHistory222.checkDef.val.Evalb ![proof,1] := by
  obtain ⟨n, hn, hz⟩ := enum_halts_le_of_blank t ht
  obtain ⟨proof, hp, hc⟩ := ArithmeticEnumBoundSoundness.refutation_bound_of_zero_work_halts n hz
  refine ⟨proof, le_trans hp ?_, hc⟩
  apply exp_monotone_le.mpr
  apply exp_monotone_le.mpr
  refine _root_.add_le_add ?_ le_rfl
  calc 100 * n ≤ 100 * (7 * t) := mul_le_mul_of_nonneg_left hn (Arithmetic.zero_le 100)
    _ = 700 * t := by ring

end Endpoint
end DiophantineConsistency.ArithmeticRuntimeBound215
