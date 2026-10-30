import DiophantineConsistency.ArithmeticCommandFetchPerm222
import DiophantineConsistency.ArithmeticCommandStepPerm222

/-! # One represented step of the actual permuted enumerator

A live full state is `1+P(pl,P(np,work))`; zero is absorbing. The unshifted
working word is the command-step encoding `P(tw,P(ws,P(d,h)))`. Fetching an
exhausted program starts the next candidate. Only the command's halting result
halts the enumerator. All graph intermediates below are unbounded.

This packet proves a total internal IOpen graph and its agreement with the
actual ordinary `EnumPerm.enumStep`. It proves no run, scheduling fairness,
derivation invariant, or consistency equivalence.
-/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticEnumStepPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticCommandWordPerm222 ArithmeticCommandFetchPerm222 ArithmeticCommandStepPerm222
attribute [local irreducible] Code254.P
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def liveValue (pl np w : V) : V := cantor pl (cantor np w) + 1

def liveDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out pl np w. ∃ nw, !ArithmeticCantor.pairDef nw np w ∧
    ∃ s, !ArithmeticCantor.pairDef s pl nw ∧ out = s+1”

instance live_defined : 𝚺₁-Function₃[V] liveValue via liveDef :=
  .mk fun e => by simp [liveDef, liveValue]

noncomputable def execValue (raw np w : V) : V :=
  let r := stepValue raw w
  if r=0 then 0 else liveValue (tailValue raw) np (r-1)

def execDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out raw np w. ∃ r, !stepDef r raw w ∧
    ((r = 0 ∧ out = 0) ∨ (r ≠ 0 ∧ ∃ v, !subDef v r 1 ∧
      ∃ tail, !tailDef tail raw ∧ !liveDef out tail np v))”

instance exec_defined : 𝚺₁-Function₃[V] execValue via execDef := .mk fun e => by
  classical
  by_cases h : stepValue (e 1) (e 3)=0 <;> simp [execDef, execValue, h]

noncomputable def enumValue (s : V) : V :=
  if s=0 then 0 else
    let body := s-1
    let fetched := fetchValue (first body) (first (second body))
    execValue (first fetched) (second fetched) (second (second body))

def enumDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out s. (s = 0 ∧ out = 0) ∨ (s ≠ 0 ∧
    ∃ body, !subDef body s 1 ∧
    ∃ pl, !ArithmeticCantor.firstDef pl body ∧
    ∃ nw, !ArithmeticCantor.secondDef nw body ∧
    ∃ np, !ArithmeticCantor.firstDef np nw ∧
    ∃ w, !ArithmeticCantor.secondDef w nw ∧
    ∃ fetched, !fetchDef fetched pl np ∧
    ∃ raw, !ArithmeticCantor.firstDef raw fetched ∧
    ∃ next, !ArithmeticCantor.secondDef next fetched ∧ !execDef out raw next w)”

instance enum_defined : 𝚺₁-Function₁[V] enumValue via enumDef := .mk fun e => by
  classical
  by_cases h : e 1=0 <;> simp [enumDef, enumValue, h]

instance enum_definable : 𝚺₁-Function₁[V] enumValue := enum_defined.to_definable

theorem enum_total (s : V) : ∃! out, enumDef.val.Evalb ![out,s] := by simp

@[simp] theorem enum_zero : enumValue (0 : V)=0 := by simp [enumValue]

theorem enum_live (pl np w : V) :
    enumValue (liveValue pl np w) =
      execValue (first (fetchValue pl np)) (second (fetchValue pl np)) w := by
  simp [enumValue, liveValue]

theorem exec_eq_zero_iff (raw np w : V) :
    execValue raw np w=0 ↔ first raw=0 ∧ second (second (second w))=1 := by
  classical
  by_cases h : stepValue raw w=0
  · simpa [execValue, h] using (stepValue_eq_zero_iff raw w).mp h
  · simp [execValue, h, liveValue, ← stepValue_eq_zero_iff raw w]

/-- An exhausted pointer is not itself a halting condition. -/
theorem enum_live_eq_zero_iff (pl np w : V) :
    enumValue (liveValue pl np w)=0 ↔
      first (first (fetchValue pl np))=0 ∧ second (second (second w))=1 := by
  rw [enum_live, exec_eq_zero_iff]

/-- All ordinary full states are encoded, including arbitrary dirty fields. -/
def encodeState (s : EnumPerm.St) : ℕ :=
  Code254.P s.pl (Code254.P s.np (encodeW (EnumPerm.toW s))) + 1

def encodeStateResult : Option EnumPerm.St → ℕ
  | none => 0
  | some s => encodeState s

@[simp] theorem encodeStateResult_eq_zero_iff (s : Option EnumPerm.St) :
    encodeStateResult s = 0 ↔ s = none := by
  cases s with
  | none => simp [encodeStateResult]
  | some s => simp [encodeStateResult, encodeState]

@[simp] theorem liveValue_nat (s : EnumPerm.St) :
    liveValue s.pl s.np (encodeW (EnumPerm.toW s))=encodeState s := by
  simp only [liveValue, cantor_nat, encodeState]

theorem execValue_nat (raw np : ℕ) (s : EnumPerm.St) :
    execValue raw np (encodeW (EnumPerm.toW s))=
      encodeStateResult (EnumPerm.execAt raw np s) := by
  rw [execValue, stepValue_nat, tail_nat, EnumPerm.execAt]
  cases h : EnumPerm.cstep (EnumPerm.decode raw).1 (EnumPerm.toW s) <;>
    simp [encodeResult, encodeStateResult, liveValue, encodeState, EnumPerm.toW,
      encodeW, cantor_nat]

/-- Literal agreement with actual fetch/execAt for every ordinary state. -/
theorem enumValue_nat (s : EnumPerm.St) :
    enumValue (encodeState s)=encodeStateResult (EnumPerm.enumStep s) := by
  rw [← liveValue_nat s, enum_live, raw_nat, next_nat, execValue_nat]
  rfl

theorem enumValue_nat_eq_zero_iff (s : EnumPerm.St) :
    enumValue (encodeState s)=0 ↔ EnumPerm.enumStep s=none := by
  rw [enumValue_nat, encodeStateResult_eq_zero_iff]

end DiophantineConsistency.ArithmeticEnumStepPerm222
