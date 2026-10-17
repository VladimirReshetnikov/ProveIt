import BusyBeaver.ZFC.ArithmeticPositiveSimulation254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC.ArithmeticPositiveSimulation254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticPositiveSimulation254.clock_reach
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticPositiveSimulation254.binary_halts_of_logical_halts
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticPositiveSimulation254.logical_halts_of_binary_halts
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticPositiveSimulation254.halts_iff
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
example (continues : ∀ n clock,
    Related (logicalRun n) (binaryRun clock binaryInitial) → logicalStep (logicalRun n) ≠ 0)
    (n : V) : ∃ clock, n ≤ clock ∧ Related (logicalRun n) (binaryRun clock binaryInitial) :=
  clock_reach logicalStep logicalRun binaryRun Related logicalInitial binaryInitial logical_zero logical_succ binary_zero binary_add initial_related related_step continues n
include logical_zero logical_succ binary_zero binary_add initial_related related_step related_live related_halt in
example (hl : ∃ n, logicalRun n = 0) : ∃ t, Halted (binaryRun t binaryInitial) :=
  binary_halts_of_logical_halts logicalStep logicalRun binaryRun Related Halted logicalInitial binaryInitial logical_zero logical_succ binary_zero binary_add initial_related related_live related_step related_halt hl
include logical_zero logical_succ binary_zero binary_add initial_related related_step related_active halt_persists in
example (hb : ∃ t, Halted (binaryRun t binaryInitial)) : ∃ n, logicalRun n = 0 :=
  logical_halts_of_binary_halts logicalStep logicalRun binaryRun Related Halted logicalInitial binaryInitial logical_zero logical_succ binary_zero binary_add initial_related related_active related_step halt_persists hb
include logical_zero logical_succ binary_zero binary_add initial_related related_step related_live related_active related_halt halt_persists in
example : (∃ n, logicalRun n = 0) ↔ (∃ t, Halted (binaryRun t binaryInitial)) :=
  halts_iff logicalStep logicalRun binaryRun Related Halted logicalInitial binaryInitial logical_zero logical_succ binary_zero binary_add initial_related related_live related_active related_step related_halt halt_persists
