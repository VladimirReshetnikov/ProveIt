import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact sign cannot be decided by finite observations of rapid names

Packet `foundations/fiber_ipra_2026-11-16`, `thm:no-sign` in
`paper/sections/08_algebra.tex`.

This is an external representation/algorithm metatheorem. Its declarations
are Lean propositions about explicitly defined oracle machines, rather than
object sentences of `Prf PRAAx`. A rapid name of a rational `q` has error at
most `2^(-n)` at sample `n`. Restricting a hypothetical real sign selector to
these rational limits is already impossible.

The machine has actual deterministic halt, internal-step and oracle-query
actions. Fuel bounds computation, and the demand bound is computed from the
actual adaptive execution. Prefix agreement preserves that execution by a
proved induction; it is not an assumed continuity or indistinguishability
principle. Positive and negative perturbations have actual rapid names equal
to the zero name before the demanded bound and exact thereafter.
-/

namespace LeanProofs.IPRA.Foundations.FiniteUseSignObstruction

universe u

abbrev Oracle := ℕ → ℚ

inductive SignValue where
  | negative
  | zero
  | positive
  deriving DecidableEq, Repr

def exactSign (q : ℚ) : SignValue :=
  if q < 0 then .negative else if q = 0 then .zero else .positive

@[simp] theorem exactSign_zero : exactSign 0 = .zero := by simp [exactSign]

theorem exactSign_of_pos {q : ℚ} (hq : 0 < q) : exactSign q = .positive := by
  simp [exactSign, not_lt_of_ge (le_of_lt hq), ne_of_gt hq]

theorem exactSign_of_neg {q : ℚ} (hq : q < 0) : exactSign q = .negative := by
  simp [exactSign, hq]

/-- The represented name's actual error radius. -/
def radius (n : ℕ) : ℚ := (1 / 2 : ℚ) ^ n

theorem radius_pos (n : ℕ) : 0 < radius n := pow_pos (by norm_num) n

/-- A rapidly convergent rational name, with its prescribed rational limit. -/
def RapidName (q : ℚ) (a : Oracle) : Prop := ∀ n, |a n - q| ≤ radius n

def zeroName : Oracle := fun _ => 0

theorem zeroName_rapid : RapidName 0 zeroName := by
  intro n
  simpa only [zeroName, sub_self, abs_zero] using le_of_lt (radius_pos n)

/-- A nonzero perturbation smaller than every radius observed before `M`. -/
def tiny (M : ℕ) : ℚ := radius (M + 3)

theorem tiny_pos (M : ℕ) : 0 < tiny M := radius_pos _

def positiveName (M : ℕ) : Oracle := fun n => if n < M then 0 else tiny M
def negativeName (M : ℕ) : Oracle := fun n => -positiveName M n

theorem positiveName_prefix (M : ℕ) {n : ℕ} (hn : n < M) :
    positiveName M n = zeroName n := by simp [positiveName, zeroName, hn]

theorem negativeName_prefix (M : ℕ) {n : ℕ} (hn : n < M) :
    negativeName M n = zeroName n := by simp [negativeName, positiveName, zeroName, hn]

theorem positiveName_rapid (M : ℕ) : RapidName (tiny M) (positiveName M) := by
  intro n
  by_cases hn : n < M
  · simp only [positiveName, if_pos hn, zero_sub, abs_neg, abs_of_pos (tiny_pos M)]
    exact pow_le_pow_of_le_one (by norm_num : (0 : ℚ) ≤ 1 / 2) (by norm_num)
      ((Nat.le_of_lt hn).trans (Nat.le_add_right M 3))
  · simp only [positiveName, if_neg hn, sub_self, abs_zero]
    exact le_of_lt (radius_pos n)

theorem negativeName_rapid (M : ℕ) : RapidName (-tiny M) (negativeName M) := by
  intro n
  calc
    |negativeName M n - -tiny M| = |-(positiveName M n - tiny M)| := by
      congr 1
      simp only [negativeName]
      ring
    _ = |positiveName M n - tiny M| := abs_neg _
    _ ≤ radius n := positiveName_rapid M n

/-- A machine can halt, perform an internal step, or ask one rational sample.
The continuation may depend on the answer, allowing adaptive queries. -/
inductive Action (State : Type u) where
  | halt (result : SignValue)
  | tick (next : State)
  | query (index : ℕ) (next : ℚ → State)

structure Machine (State : Type u) where
  initial : State
  transition : State → Action State

/-- Actual bounded deterministic oracle execution. -/
def execute {State : Type u} (P : Machine State) : ℕ → State → Oracle → Option SignValue
  | 0, _, _ => none
  | fuel + 1, state, a =>
      match P.transition state with
      | .halt result => some result
      | .tick next => execute P fuel next a
      | .query index next => execute P fuel (next (a index)) a

/-- Exclusive upper bound on every sample inspected by this actual execution. -/
def demandBound {State : Type u} (P : Machine State) : ℕ → State → Oracle → ℕ
  | 0, _, _ => 0
  | fuel + 1, state, a =>
      match P.transition state with
      | .halt _ => 0
      | .tick next => demandBound P fuel next a
      | .query index next => max (index + 1) (demandBound P fuel (next (a index)) a)

def AgreeBelow (M : ℕ) (a b : Oracle) : Prop := ∀ n, n < M → a n = b n

/-- The finite-use property is proved from the adaptive execution semantics. -/
theorem execute_eq_of_agreeBelow {State : Type u} (P : Machine State)
    (fuel : ℕ) (state : State) (a b : Oracle)
    (h : AgreeBelow (demandBound P fuel state a) a b) :
    execute P fuel state b = execute P fuel state a := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    cases action : P.transition state with
    | halt result => simp only [execute, action]
    | tick next =>
      simp only [execute, action]
      apply ih next
      simpa only [AgreeBelow, demandBound, action] using h
    | query index next =>
      have observations : AgreeBelow
          (max (index + 1) (demandBound P fuel (next (a index)) a)) a b := by
        simpa only [demandBound, action] using h
      have answer : a index = b index := observations index
        (lt_of_lt_of_le (Nat.lt_succ_self index) (Nat.le_max_left _ _))
      simp only [execute, action]
      rw [← answer]
      apply ih (next (a index))
      intro n hn
      exact observations n (lt_of_lt_of_le hn (Nat.le_max_right _ _))

/-- Every successful finite execution supplies a finite observational
neighborhood on which its result is unchanged. -/
theorem finite_use_at_halt {State : Type u} (P : Machine State)
    {fuel : ℕ} {state : State} {a : Oracle} {result : SignValue}
    (h : execute P fuel state a = some result) :
    ∃ M, ∀ b, AgreeBelow M a b → execute P fuel state b = some result := by
  exact ⟨demandBound P fuel state a, fun b hb => (execute_eq_of_agreeBelow P fuel state a b hb).trans h⟩

/-- Successful executions at different fuel bounds return the same answer. -/
theorem execute_result_unique {State : Type u} (P : Machine State)
    {fuel fuel' : ℕ} {state : State} {a : Oracle} {result result' : SignValue}
    (h : execute P fuel state a = some result)
    (h' : execute P fuel' state a = some result') : result = result' := by
  induction fuel generalizing fuel' state with
  | zero => simp only [execute, reduceCtorEq] at h
  | succ fuel ih =>
    cases fuel' with
    | zero => simp only [execute, reduceCtorEq] at h'
    | succ fuel' =>
      cases action : P.transition state with
      | halt value =>
        simp only [execute, action, Option.some.injEq] at h h'
        exact h.symm.trans h'
      | tick next =>
        exact ih (state := next) (by simpa only [execute, action] using h)
          (by simpa only [execute, action] using h')
      | query index next =>
        exact ih (state := next (a index)) (by simpa only [execute, action] using h)
          (by simpa only [execute, action] using h')

/-- Both nonzero perturbations preserve every observation of the finite zero
execution, and both are actual names with the claimed strict sign. -/
theorem zero_run_perturbations {State : Type u} (P : Machine State)
    (fuel : ℕ) (state : State) :
    ∃ M, 0 < tiny M ∧ RapidName (tiny M) (positiveName M) ∧
      RapidName (-tiny M) (negativeName M) ∧
      execute P fuel state (positiveName M) = execute P fuel state zeroName ∧
      execute P fuel state (negativeName M) = execute P fuel state zeroName := by
  let M := demandBound P fuel state zeroName
  refine ⟨M, tiny_pos M, positiveName_rapid M, negativeName_rapid M, ?_, ?_⟩
  · apply execute_eq_of_agreeBelow P fuel state zeroName (positiveName M)
    intro n hn
    exact (positiveName_prefix M hn).symm
  · apply execute_eq_of_agreeBelow P fuel state zeroName (negativeName M)
    intro n hn
    exact (negativeName_prefix M hn).symm

/-- Correctness of every answer the machine actually returns on a valid name. -/
def SoundSign {State : Type u} (P : Machine State) : Prop :=
  ∀ (q : ℚ) (a : Oracle), RapidName q a →
    ∀ (fuel : ℕ) (result : SignValue), execute P fuel P.initial a = some result → result = exactSign q

/-- Total exact-sign computation on rapidly convergent rational names. It is
enough to request one successful fuel bound per input. -/
def ComputesExactSign {State : Type u} (P : Machine State) : Prop :=
  ∀ (q : ℚ) (a : Oracle), RapidName q a →
    ∃ fuel, execute P fuel P.initial a = some (exactSign q)

theorem sound_of_computes {State : Type u} (P : Machine State)
    (h : ComputesExactSign P) : SoundSign P := by
  intro q a valid fuel result returned
  obtain ⟨fuel', correct⟩ := h q a valid
  exact execute_result_unique P returned correct

/-- A sound finite-query sign procedure cannot halt on the zero name.
The obstruction uses the positive perturbation of its actual zero execution. -/
theorem no_sound_halting_zero {State : Type u} (P : Machine State)
    (sound : SoundSign P) :
    ¬ ∃ fuel result, execute P fuel P.initial zeroName = some result := by
  rintro ⟨fuel, result, returned⟩
  have isZero : result = .zero := by simpa using sound 0 zeroName zeroName_rapid fuel result returned
  obtain ⟨M, positive, valid, _, unchanged, _⟩ := zero_run_perturbations P fuel P.initial
  have returned' : execute P fuel P.initial (positiveName M) = some result := unchanged.trans returned
  have isPositive : result = .positive := by
    simpa only [exactSign_of_pos positive] using sound (tiny M) (positiveName M) valid fuel result returned'
  have impossible : SignValue.zero = SignValue.positive := isZero.symm.trans isPositive
  cases impossible

/-- `thm:no-sign`: no deterministic finite-query machine computes exact
trichotomy for every rapid rational name, even when every represented limit
is rational. Consequently such a machine cannot work for all real names. -/
theorem no_exact_sign_machine {State : Type u} (P : Machine State) : ¬ ComputesExactSign P := by
  intro computes
  obtain ⟨fuel, returned⟩ := computes 0 zeroName zeroName_rapid
  exact no_sound_halting_zero P (sound_of_computes P computes) ⟨fuel, exactSign 0, returned⟩

#print axioms positiveName_rapid
#print axioms negativeName_rapid
#print axioms execute_eq_of_agreeBelow
#print axioms finite_use_at_halt
#print axioms execute_result_unique
#print axioms zero_run_perturbations
#print axioms no_sound_halting_zero
#print axioms no_exact_sign_machine

end LeanProofs.IPRA.Foundations.FiniteUseSignObstruction
