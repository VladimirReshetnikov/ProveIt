import BusyBeaver.ZFC.ArithmeticCantor
import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-!
Positive-clock simulation transport in arbitrary IΣ1
models. Concrete simulation premises remain explicit. No register/binary
simulation or consistency endpoint is instantiated here.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticPositiveSimulation254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable (logicalStep : V → V) (logicalRun : V → V)
  (binaryRun : V → V → V) (Related : V → V → Prop) (Halted : V → Prop)
  [𝚺₁-Function₁[V] logicalRun] [𝚺₁-Function₂[V] binaryRun]
  [𝚺₁-Relation[V] Related]
  (logicalInitial binaryInitial : V)
  (logical_zero : logicalRun 0 = logicalInitial)
  (logical_succ : ∀ n, logicalRun (n+1) = logicalStep (logicalRun n))
  (binary_zero : ∀ b, binaryRun 0 b = b)
  (binary_add : ∀ t u b, binaryRun (t+u) b = binaryRun u (binaryRun t b))
  (initial_related : Related logicalInitial binaryInitial)
  (related_live : ∀ l b, Related l b → l ≠ 0)
  (related_active : ∀ l b, Related l b → ¬ Halted b)
  (related_step : ∀ l b, Related l b → logicalStep l ≠ 0 →
    ∃ k, 0 < k ∧ Related (logicalStep l) (binaryRun k b))
  (related_halt : ∀ l b, Related l b → logicalStep l = 0 →
    ∃ k, Halted (binaryRun k b))
  (halt_persists : ∀ b, Halted b → ∀ k, Halted (binaryRun k b))

include logical_zero logical_succ binary_zero binary_add initial_related related_step in
/-- A Sigma1 induction carries an existential clock and relation witness.
The continuation premise is external to that induction predicate. -/
theorem clock_reach
    (continues : ∀ n clock,
      Related (logicalRun n) (binaryRun clock binaryInitial) →
        logicalStep (logicalRun n) ≠ 0) (n : V) :
    ∃ clock, n ≤ clock ∧ Related (logicalRun n) (binaryRun clock binaryInitial) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    refine ⟨0, le_rfl, ?_⟩
    simpa only [logical_zero, binary_zero] using initial_related
  case succ n ih =>
    obtain ⟨clock, hc, hr⟩ := ih
    obtain ⟨k, hk, hs⟩ := related_step _ _ hr (continues n clock hr)
    refine ⟨clock+k, ?_, ?_⟩
    · exact _root_.add_le_add hc (by simpa only [zero_add] using lt_iff_succ_le.mp hk)
    · rw [logical_succ, binary_add]
      exact hs

include logical_zero logical_succ binary_zero binary_add initial_related related_step related_live related_halt in
/-- Logical halting forces binary halting; the binary run may already have
halted before the supplied logical witness time. -/
theorem binary_halts_of_logical_halts
    (hl : ∃ n, logicalRun n = 0) :
    ∃ t, Halted (binaryRun t binaryInitial) := by
  by_contra hn
  have hb : ∀ t, ¬ Halted (binaryRun t binaryInitial) := by
    intro t ht
    exact hn ⟨t, ht⟩
  have continues : ∀ n clock,
      Related (logicalRun n) (binaryRun clock binaryInitial) →
        logicalStep (logicalRun n) ≠ 0 := by
    intro n clock hr hz
    obtain ⟨k, hk⟩ := related_halt _ _ hr hz
    exact hb (clock+k) (by simpa only [binary_add] using hk)
  obtain ⟨n, hn⟩ := hl
  obtain ⟨clock, _, hr⟩ := clock_reach logicalStep logicalRun binaryRun Related
    logicalInitial binaryInitial logical_zero logical_succ binary_zero binary_add
    initial_related related_step continues n
  exact related_live _ _ hr hn

include logical_zero logical_succ binary_zero binary_add initial_related related_step related_active halt_persists in
/-- Positive clocks reach beyond any proposed binary halting time. Absorption
and activity then force a logical halting witness, without an upper clock bound. -/
theorem logical_halts_of_binary_halts
    (hb : ∃ t, Halted (binaryRun t binaryInitial)) :
    ∃ n, logicalRun n = 0 := by
  by_contra hn
  have hl : ∀ n, logicalRun n ≠ 0 := by
    intro n hn'
    exact hn ⟨n, hn'⟩
  have continues : ∀ n clock,
      Related (logicalRun n) (binaryRun clock binaryInitial) →
        logicalStep (logicalRun n) ≠ 0 := by
    intro n _ _ hs
    exact hl (n+1) (by rw [logical_succ, hs])
  obtain ⟨t, ht⟩ := hb
  obtain ⟨clock, hc, hr⟩ := clock_reach logicalStep logicalRun binaryRun Related
    logicalInitial binaryInitial logical_zero logical_succ binary_zero binary_add
    initial_related related_step continues t
  have hh : Halted (binaryRun clock binaryInitial) := by
    have he : t + (clock-t) = clock := add_tsub_cancel_of_le hc
    rw [← he, binary_add]
    exact halt_persists _ ht _
  exact related_active _ _ hr hh

include logical_zero logical_succ binary_zero binary_add initial_related related_step related_live related_active related_halt halt_persists in
/-- The transport theorem retains all concrete simulation obligations. -/
theorem halts_iff :
    (∃ n, logicalRun n = 0) ↔ (∃ t, Halted (binaryRun t binaryInitial)) := by
  constructor
  · exact binary_halts_of_logical_halts logicalStep logicalRun binaryRun Related Halted
      logicalInitial binaryInitial logical_zero logical_succ binary_zero binary_add
      initial_related related_live related_step related_halt
  · exact logical_halts_of_binary_halts logicalStep logicalRun binaryRun Related Halted
      logicalInitial binaryInitial logical_zero logical_succ binary_zero binary_add
      initial_related related_active related_step halt_persists

end SetTheory.BusyBeaver.ZFC.ArithmeticPositiveSimulation254
