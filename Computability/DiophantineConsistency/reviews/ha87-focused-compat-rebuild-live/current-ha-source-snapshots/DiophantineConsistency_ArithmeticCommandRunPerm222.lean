import DiophantineConsistency.ArithmeticCommandTickPerm222
import DiophantineConsistency.ArithmeticUnaryRecursion

/-!
Internal time iteration and drain bound for actual coded
EnumPerm command words. The fixed run graph is total at every time in every
ISigma1 model. For each fixed initial word and working state, a pointwise
Sigma1 induction proves that the word has halted or completed after at most
its shifted numerical word code ticks. No induction hypothesis quantifies
universally over arbitrary changing working states.

Halting and successful completion remain separate coded results. This is not
an append-execution theorem, scheduler theorem, compiler execution contract,
or internal nonhalting/consistency equivalence.
-/
namespace DiophantineConsistency.ArithmeticCommandRunPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCommandTickPerm222
set_option autoImplicit false
set_option Elab.async false
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The one fixed parameter is the entire initial evaluator configuration. -/
def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out initial. out = initial”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index initial. !tickDef out previous”

def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero parameters := parameters 0
  succ _ _ previous := tickValue previous
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef]

/-- Arguments are time first, initial evaluator second. -/
noncomputable def run (time initial : V) : V := construction.result ![initial] time

def runDef : 𝚺₁.Semisentence 3 := blueprint.resultDef
def runDeltaDef : 𝚫₁.Semisentence 3 := blueprint.resultDeltaDef

instance run_defined : 𝚺₁-Function₂[V] run via runDef :=
  ArithmeticUnaryRecursion.result_defined blueprint construction

instance run_defined_delta : 𝚫₁-Function₂[V] run via runDeltaDef := run_defined.graph_delta
instance run_definable : 𝚺₁-Function₂[V] run := run_defined.to_definable

@[simp] theorem run_zero (initial : V) : run 0 initial = initial := by
  simp [run, construction]
@[simp] theorem run_succ (time initial : V) :
    run (time + 1) initial = tickValue (run time initial) := by
  simp [run, PR.Construction.result_succ, construction]

theorem run_total (time initial : V) :
    ∃! out, runDef.val.Evalb ![out,time,initial] := by simp

/-- Already halted and already completed evaluators are genuinely absorbing
at all internal times; this is not merely an external-Nat induction. -/
theorem run_stopped (time initial : V) (hi : Stopped initial) :
    run time initial = initial := by
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ time ih => rw [run_succ, ih, tick_stopped hi]

@[simp] theorem run_halted (time : V) : run time 0 = 0 :=
  run_stopped time 0 (Or.inl rfl)
@[simp] theorem run_done (time w : V) : run time (liveValue 0 w) = liveValue 0 w :=
  run_stopped time _ (Or.inr (remaining_live 0 w))

/-- Semigroup law with all three parameters fixed during time induction. -/
theorem run_add (first second initial : V) :
    run (first + second) initial = run second (run first initial) := by
  induction second using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ second ih => rw [← add_assoc, run_succ, run_succ, ih]

/-- The only time-induction predicate contains fixed word and working-state
parameters and a single changing evaluator, rather than an unbounded forall W. -/
theorem drain_bound (time word w : V) :
    Stopped (run time (liveValue word w)) ∨
      remaining (run time (liveValue word w)) + time ≤ word := by
  induction time using ISigma1.sigma1_succ_induction
  · unfold Stopped
    definability
  case zero => right; simp
  case succ time ih =>
    rw [run_succ]
    by_cases hs : Stopped (run time (liveValue word w))
    · exact Or.inl (stopped_tick hs)
    · have hb := ih.resolve_left hs
      rcases tick_decreases hs with hz | hd
      · left; exact Or.inl hz
      · right
        calc
          remaining (tickValue (run time (liveValue word w))) + (time + 1) =
              (remaining (tickValue (run time (liveValue word w))) + 1) + time := by
                ac_rfl
          _ ≤ remaining (run time (liveValue word w)) + time :=
            _root_.add_le_add hd le_rfl
          _ ≤ word := hb

/-- Every internal shifted word is halted or completed by its own numerical
code bound. Completed configurations remain positive; this does not conflate
them with the halting result0. -/
theorem drained (word w : V) : Stopped (run word (liveValue word w)) := by
  rcases drain_bound word word w with hs | hb
  · exact hs
  · right
    have hz : remaining (run word (liveValue word w)) ≤ 0 := by
      apply (add_le_add_iff_right word).mp
      simpa only [zero_add] using hb
    exact le_antisymm hz (Arithmetic.zero_le _)

/-- The terminal configuration, still distinguishing halt0 and positive done. -/
noncomputable def terminal (word w : V) : V := run word (liveValue word w)

def terminalDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out word w. ∃ initial, !liveDef initial word w ∧ !runDef out word initial”

instance terminal_defined : 𝚺₁-Function₂[V] terminal via terminalDef :=
  .mk fun e => by simp [terminalDef, terminal]

/-- Successful word execution returns the final working state plus1.
Evaluator halt0 is the sole result0; an empty word successfully returns w+1. -/
noncomputable def evalValue (word w : V) : V :=
  if terminal word w = 0 then 0 else working (terminal word w) + 1

def evalDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out word w. ∃ config, !terminalDef config word w ∧
    ((config = 0 ∧ out = 0) ∨
     (config ≠ 0 ∧ ∃ state, !workingDef state config ∧ out = state + 1))”

instance eval_defined : 𝚺₁-Function₂[V] evalValue via evalDef := .mk fun e => by
  classical
  by_cases ht : terminal (e 1) (e 2) = 0 <;> simp [evalDef, evalValue, ht]

instance eval_defined_delta : 𝚫₁-Function₂[V] evalValue via evalDef.graphDelta :=
  eval_defined.graph_delta

@[simp] theorem terminal_zero_word (w : V) : terminal 0 w = liveValue 0 w := by
  simp [terminal]
@[simp] theorem eval_zero_word (w : V) : evalValue 0 w = w + 1 := by
  simp [evalValue]

theorem terminal_stopped (word w : V) : Stopped (terminal word w) := drained word w

theorem eval_eq_zero_iff (word w : V) :
    evalValue word w = 0 ↔ terminal word w = 0 := by
  classical
  by_cases ht : terminal word w = 0 <;> simp [evalValue, ht]

theorem terminal_total (word w : V) :
    ∃! out, terminalDef.val.Evalb ![out,word,w] := by simp

theorem eval_total (word w : V) :
    ∃! out, evalDef.val.Evalb ![out,word,w] := by simp

/-- A closed arithmetic totality assertion for represented command evaluation,
not a compiler contract or consistency equivalence. -/
def totalitySentence : ArithmeticSentence :=
  “∀ word, ∀ w, ∃ out, !evalDef out word w ∧
    ∀ other, !evalDef other word w → other = out”

theorem totalitySentence_true : totalitySentence.Evalb (M := V) ![] := by
  simp [totalitySentence]

theorem isigma1_proves_totality : 𝗜𝚺₁ ⊢ totalitySentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (totalitySentence_true (V := M))

theorem peano_proves_totality : Peano ⊢ totalitySentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) isigma1_proves_totality

end DiophantineConsistency.ArithmeticCommandRunPerm222
