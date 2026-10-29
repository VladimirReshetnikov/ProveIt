import DiophantineConsistency.ArithmeticCommandStepPerm222

/-!
One represented tick of an actual EnumPerm command word.
Evaluator0 is halted. Positive1+P(word,working) is live; shifted word0 is a
completed, absorbing evaluator. Raw command0 is still executed at word1.
All fixed Sigma1 graphs range over arbitrary IOpen model inputs. No bound on
an intermediate is inferred from a halting/shrinking output. This module
states no scheduler, compiled-proof execution, or consistency equivalence.
-/
namespace DiophantineConsistency.ArithmeticCommandTickPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticCommandStepPerm222 ArithmeticCommandWordPerm222
set_option autoImplicit false
set_option Elab.async false
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

/-- Positive coding separates a completed word from an already halted run. -/
noncomputable def liveValue (word w : V) : V := cantor word w + 1

def liveDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out word w. ∃ pair, !ArithmeticCantor.pairDef pair word w ∧ out = pair + 1”

instance live_defined : 𝚺₁-Function₂[V] liveValue via liveDef :=
  .mk fun e => by simp [liveDef, liveValue]

noncomputable def remaining (config : V) : V := first (config - 1)
noncomputable def working (config : V) : V := second (config - 1)

def remainingDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out config. ∃ predecessor, !subDef predecessor config 1 ∧
    !ArithmeticCantor.firstDef out predecessor”

def workingDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out config. ∃ predecessor, !subDef predecessor config 1 ∧
    !ArithmeticCantor.secondDef out predecessor”

instance remaining_defined : 𝚺₁-Function₁[V] remaining via remainingDef :=
  .mk fun e => by simp [remainingDef, remaining]
instance working_defined : 𝚺₁-Function₁[V] working via workingDef :=
  .mk fun e => by simp [workingDef, working]
instance remaining_definable : 𝚺₁-Function₁[V] remaining := remaining_defined.to_definable
instance working_definable : 𝚺₁-Function₁[V] working := working_defined.to_definable

@[simp] theorem live_ne_zero (word w : V) : liveValue word w ≠ 0 := by
  simp [liveValue]
@[simp] theorem remaining_live (word w : V) : remaining (liveValue word w) = word := by
  simp [remaining, liveValue]
@[simp] theorem working_live (word w : V) : working (liveValue word w) = w := by
  simp [working, liveValue]

lemma pred_add_one (config : V) (hc : config ≠ 0) : config - 1 + 1 = config := by
  have hpos : 0 < config := lt_of_le_of_ne (Arithmetic.zero_le config) (Ne.symm hc)
  exact tsub_add_cancel_of_le (by simpa using lt_iff_succ_le.mp hpos)

/-- Every nonzero internal evaluator decodes exactly, with no validity test. -/
theorem live_decode (config : V) (hc : config ≠ 0) :
    liveValue (remaining config) (working config) = config := by
  simp only [liveValue, remaining, working, cantor_projections]
  exact pred_add_one config hc

/-- The positive command-result convention retains the post-command state. -/
noncomputable def nextValue (raw w : V) : V :=
  if stepValue raw w = 0 then 0
  else liveValue (tailValue raw) (stepValue raw w - 1)

def nextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out raw w. ∃ result, !ArithmeticCommandStepPerm222.stepDef result raw w ∧
    ((result = 0 ∧ out = 0) ∨
     (result ≠ 0 ∧ ∃ rest, !tailDef rest raw ∧
       ∃ state, !subDef state result 1 ∧ !liveDef out rest state))”

instance next_defined : 𝚺₁-Function₂[V] nextValue via nextDef := .mk fun e => by
  classical
  by_cases hr : stepValue (e 1) (e 2) = 0 <;>
    simp [nextDef, nextValue, hr]

noncomputable def tickValue (config : V) : V :=
  if config = 0 then 0
  else if remaining config = 0 then config
  else nextValue (remaining config - 1) (working config)

def tickDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out config. (config = 0 ∧ out = 0) ∨
    (config ≠ 0 ∧ ∃ word, !remainingDef word config ∧
      ((word = 0 ∧ out = config) ∨
       (word ≠ 0 ∧ ∃ raw, !subDef raw word 1 ∧
         ∃ state, !workingDef state config ∧ !nextDef out raw state)))”

instance tick_defined : 𝚺₁-Function₁[V] tickValue via tickDef := .mk fun e => by
  classical
  by_cases hc : e 1 = 0
  · simp [tickDef, tickValue, hc]
  · by_cases hw : remaining (e 1) = 0 <;> simp [tickDef, tickValue, hc, hw]
instance tick_definable : 𝚺₁-Function₁[V] tickValue := tick_defined.to_definable

@[simp] theorem tick_zero : tickValue (0 : V) = 0 := by simp [tickValue]
@[simp] theorem tick_done (w : V) : tickValue (liveValue 0 w) = liveValue 0 w := by
  simp [tickValue]

/-- A shifted successor word executes its actual raw head, including raw0. -/
theorem tick_live_succ (raw w : V) :
    tickValue (liveValue (raw + 1) w) = nextValue raw w := by
  simp [tickValue]

/-- Stopped is a control condition; it does not identify halt with completion. -/
def Stopped (config : V) : Prop := config = 0 ∨ remaining config = 0

/-- Decode an active evaluator after restoring the predecessor of its word. -/
theorem live_decode_active (config : V) (hc : ¬ Stopped config) :
    liveValue ((remaining config - 1) + 1) (working config) = config := by
  obtain ⟨h0, hw⟩ := not_or.mp hc
  rw [pred_add_one (remaining config) hw]
  exact live_decode config h0

lemma tick_stopped {config : V} (hc : Stopped config) : tickValue config = config := by
  rcases hc with hc | hw
  · subst config; exact tick_zero
  · by_cases h0 : config = 0 <;> simp [tickValue, h0, hw]

lemma stopped_tick {config : V} (hc : Stopped config) : Stopped (tickValue config) := by
  rwa [tick_stopped hc]

/-- Active ticks either halt or strictly reduce the shifted remaining word.
The inequality is independent of the possibly enormous changing work state. -/
theorem tick_decreases {config : V} (hc : ¬ Stopped config) :
    tickValue config = 0 ∨ remaining (tickValue config) + 1 ≤ remaining config := by
  have hc0 : config ≠ 0 := fun h => hc (Or.inl h)
  have hw0 : remaining config ≠ 0 := fun h => hc (Or.inr h)
  have ht : tickValue config = nextValue (remaining config - 1) (working config) := by
    simp [tickValue, hc0, hw0]
  rw [ht]
  by_cases hr : stepValue (remaining config - 1) (working config) = 0
  · left; simp [nextValue, hr]
  · right
    simp only [nextValue, hr, if_false, remaining_live]
    have hle : tailValue (remaining config - 1) + 1 ≤ (remaining config - 1) + 1 :=
      _root_.add_le_add (tail_le (remaining config - 1)) le_rfl
    simpa only [pred_add_one (remaining config) hw0] using hle

/-- Literal ordinary one-command effect, retaining actual permuted decode. -/
theorem nextValue_nat (raw : ℕ) (w : EnumPerm.W) :
    nextValue raw (encodeW w) =
      match EnumPerm.cstep (EnumPerm.decode raw).1 w with
      | none => 0
      | some w' => liveValue (EnumPerm.decode raw).2 (encodeW w') := by
  rw [nextValue, stepValue_nat, tail_nat]
  cases hs : EnumPerm.cstep (EnumPerm.decode raw).1 w with
  | none => simp [encodeResult]
  | some w' => simp [encodeResult]

end DiophantineConsistency.ArithmeticCommandTickPerm222
