import Init

/-!
# Constructive logical core of the Richardson reduction

STATUS: complete Lean 4 source, inspected but NOT COMPILED in this session.
This file uses only `Init`. It declares no axioms and contains no proof holes.

These are constructive METATHEOREMS in Lean's ambient logic. They are not
object-language proofs in `ConciseIPRA.Prf PRAAx`. Arithmetic, analytic,
machine-coding, and object-proof obligations are explicit structure fields
or theorem parameters. In particular, `Framework.reduction` is an assumption
of `noTotalCorrectDecider`, not a result established by that theorem.
-/

namespace Richardson

/-! ## Negative translation needs no positive witness extraction -/

theorem negIffOfDoubleNegIff {H S : Prop}
    (h : (¬ ¬ H) ↔ (¬ ¬ S)) : (¬ H) ↔ (¬ S) :=
  ⟨fun notH s => (h.mpr (fun notS => notS s)) notH,
   fun notS h0 => (h.mp (fun notH => notH h0)) notS⟩

/-- Ordinary witness equivalence transports absence constructively. -/
theorem negIffOfIff {A B : Prop} (h : A ↔ B) : (¬ A) ↔ (¬ B) :=
  ⟨fun notA b => notA (h.mpr b),
   fun notB a => notB (h.mp a)⟩

/-- If identity means absence of an observation, observation/source
equivalence gives identity/source-absence equivalence. -/
theorem identityIffNoSource {Id Observation Source : Prop}
    (identitySpec : Id ↔ ¬ Observation)
    (witnessSpec : Observation ↔ Source) : Id ↔ ¬ Source :=
  ⟨fun isId source => (identitySpec.mp isId) (witnessSpec.mpr source),
   fun noSource => identitySpec.mpr (fun observation =>
     noSource (witnessSpec.mp observation))⟩

/-- The exact logical interface used by the negative-MRDP route.
No step changes a double-negated existential into an existential. -/
theorem negativeCalibration {Id Observation Sol H : Prop}
    (identitySpec : Id ↔ ¬ Observation)
    (analyticSpec : Observation ↔ Sol)
    (translatedMRDP : (¬ ¬ H) ↔ (¬ ¬ Sol)) : Id ↔ ¬ H := by
  have absent : Id ↔ ¬ Sol := identityIffNoSource identitySpec analyticSpec
  have negative : (¬ H) ↔ (¬ Sol) := negIffOfDoubleNegIff translatedMRDP
  exact ⟨fun isId => negative.mpr (absent.mp isId),
    fun notH => absent.mpr (negative.mp notH)⟩

/-! ## Explicit finite witness transformations -/

/-- The field types deliberately do not assert primitive recursiveness.
An application must separately provide PR codes and internal correctness
derivations for these maps. -/
structure WitnessTransfer where
  source : Nat → Nat → Prop
  observation : Nat → Nat → Prop
  compile : Nat → Nat
  forward : Nat → Nat → Nat
  backward : Nat → Nat → Nat
  forwardCorrect : ∀ e w, source e w →
    observation (compile e) (forward e w)
  backwardCorrect : ∀ e w, observation (compile e) w →
    source e (backward e w)

def HasSource (W : WitnessTransfer) (e : Nat) : Prop :=
  ∃ w, W.source e w

def HasObservation (W : WitnessTransfer) (a : Nat) : Prop :=
  ∃ w, W.observation a w

def ObservationIdentity (W : WitnessTransfer) (a : Nat) : Prop :=
  ¬ HasObservation W a

theorem witnessEquivalence (W : WitnessTransfer) (e : Nat) :
    HasObservation W (W.compile e) ↔ HasSource W e := by
  constructor
  · intro h
    cases h with
    | intro w hw =>
      exact ⟨W.backward e w, W.backwardCorrect e w hw⟩
  · intro h
    cases h with
    | intro w hw =>
      exact ⟨W.forward e w, W.forwardCorrect e w hw⟩

theorem identityEquivalence (W : WitnessTransfer) (e : Nat) :
    ObservationIdentity W (W.compile e) ↔ ¬ HasSource W e :=
  negIffOfIff (witnessEquivalence W e)

/-! ## Finite computation semantics and the diagonal argument -/

/-- `Run d input time bit` certifies one finite terminating computation.
The certificate need not be an exact step count: it may encode the full trace.
Only the explicit interfaces below are used. -/
abbrev RunRelation := Nat → Nat → Nat → Bool → Prop

/-- Machine e halts on its own code, with either Boolean output. -/
def DiagonalHalt (run : RunRelation) (e : Nat) : Prop :=
  ∃ time, ∃ bit, run e e time bit

/-- All semantic and compiler obligations used by the final contradiction.

`diagonal d` is the program that takes input z, runs `d (compile z)`,
halts on `true`, and loops permanently on `false`.

All expression codes here are interpreted by a total normalization convention;
alternatively, add validity and prove that every `compile e` is valid.
-/
structure Framework where
  run : RunRelation
  identity : Nat → Prop
  compile : Nat → Nat
  diagonal : Nat → Nat
  deterministic : ∀ d input s t b c,
    run d input s b → run d input t c → b = c
  diagonalForward : ∀ d s,
    run d (compile (diagonal d)) s true →
    DiagonalHalt run (diagonal d)
  diagonalBackward : ∀ d,
    DiagonalHalt run (diagonal d) →
    ∃ s, run d (compile (diagonal d)) s true
  reduction : ∀ e, identity (compile e) ↔ ¬ DiagonalHalt run e

/-- Totality is required only on the reduction's compiled input domain. -/
def TotalOnCompiled (F : Framework) (d : Nat) : Prop :=
  ∀ e, ∃ time, ∃ bit, F.run d (F.compile e) time bit

/-- Both output branches must be sound. This specification makes no
excluded-middle assumption about identity before a computation is given. -/
def CorrectOnCompiled (F : Framework) (d : Nat) : Prop :=
  (∀ e time, F.run d (F.compile e) time true → F.identity (F.compile e)) ∧
  (∀ e time, F.run d (F.compile e) time false → ¬ F.identity (F.compile e))

/-- The `false` branch excludes diagonal halting by finite-trace determinism. -/
theorem noHaltOfFalse (F : Framework) (d s : Nat)
    (runFalse : F.run d (F.compile (F.diagonal d)) s false) :
    ¬ DiagonalHalt F.run (F.diagonal d) := by
  intro halt
  cases F.diagonalBackward d halt with
  | intro t runTrue =>
    have bad : (false : Bool) = true :=
      F.deterministic d (F.compile (F.diagonal d)) s t false true
        runFalse runTrue
    cases bad

/-- Constructive diagonal contradiction. It uses no recursion theorem,
Markov principle, excluded middle, or double-negation elimination. -/
theorem noTotalCorrectDecider (F : Framework) (d : Nat)
    (total : TotalOnCompiled F d)
    (correct : CorrectOnCompiled F d) : False := by
  cases total (F.diagonal d) with
  | intro time htime =>
    cases htime with
    | intro bit runBit =>
      cases bit with
      | false =>
        have notHalt : ¬ DiagonalHalt F.run (F.diagonal d) :=
          noHaltOfFalse F d time runBit
        have isId : F.identity (F.compile (F.diagonal d)) :=
          (F.reduction (F.diagonal d)).mpr notHalt
        exact correct.2 (F.diagonal d) time runBit isId
      | true =>
        have isId : F.identity (F.compile (F.diagonal d)) :=
          correct.1 (F.diagonal d) time runBit
        have notHalt : ¬ DiagonalHalt F.run (F.diagonal d) :=
          (F.reduction (F.diagonal d)).mp isId
        exact notHalt (F.diagonalForward d time runBit)

theorem noDeciderExists (F : Framework) :
    ¬ ∃ d, TotalOnCompiled F d ∧ CorrectOnCompiled F d := by
  intro h
  cases h with
  | intro d hd =>
    exact noTotalCorrectDecider F d hd.1 hd.2

end Richardson

-- These commands are intended for a future actual compiler run.
-- No output from them is claimed in this delivery.
#print axioms Richardson.negIffOfDoubleNegIff
#print axioms Richardson.negativeCalibration
#print axioms Richardson.witnessEquivalence
#print axioms Richardson.noTotalCorrectDecider
#print axioms Richardson.noDeciderExists
