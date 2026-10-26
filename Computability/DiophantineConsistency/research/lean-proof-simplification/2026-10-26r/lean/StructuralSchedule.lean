import Std

/-!
A standalone, kernel-checkable principle for sharing the numeric and
supplied-program rule schedules in AnnotatedRuleSchedules. The small syntax
stores the schedule once. A realization backend compiles it compositionally.
This file does not import or modify ProveIt, and is not an integrated patch.
-/
namespace StructuralSchedule

private theorem congrArg2 {α β γ : Type} (f : α → β → γ)
    {a a' : α} {b b' : β} (ha : a = a') (hb : b = b') : f a b = f a' b' := by
  cases ha
  cases hb
  rfl

inductive Field where
  | context | shifted | a | b | c | instI | instJ | shiftC | i | j
  deriving DecidableEq, Repr

structure Coding where
  atom : Nat → Nat
  fork : Nat → Nat → Nat
  cons : Nat → Nat → Nat

inductive Term where
  | field (name : Field)
  | literal (value : Nat)
  | atom (arg : Term)
  | fork (left right : Term)
  | cons (head tail : Term)
  deriving Repr

namespace Term

def eval (coding : Coding) (env : Field → Nat) : Term → Nat
  | .field name => env name
  | .literal value => value
  | .atom a => coding.atom (a.eval coding env)
  | .fork a b => coding.fork (a.eval coding env) (b.eval coding env)
  | .cons a b => coding.cons (a.eval coding env) (b.eval coding env)

def binary (tag : Nat) (a b : Term) : Term :=
  .fork (.atom (.literal tag)) (.fork a b)

def unary (tag : Nat) (a : Term) : Term :=
  .fork (.atom (.literal tag)) a

def variableNode (tag : Nat) (i j : Term) : Term :=
  .fork (.atom (.literal tag)) (.fork (.atom i) (.atom j))

def bottom : Term := .fork (.atom (.literal 2)) (.atom (.literal 0))

def list : List Term → Term
  | [] => .literal 0
  | t :: ts => .cons t (list ts)

def evalList (coding : Coding) : List Nat → Nat
  | [] => 0
  | n :: ns => coding.cons n (evalList coding ns)

theorem eval_list (coding : Coding) (env : Field → Nat) (ts : List Term) :
    (list ts).eval coding env = evalList coding (ts.map (eval coding env)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => exact congrArg (coding.cons (t.eval coding env)) ih

end Term

/-- Existing supplied-program combinators can instantiate this interface.
The fields are laws about the actual executable program data, not a choice
of an implementation from a primitive-recursiveness proposition. -/
structure Backend (Input : Type) (coding : Coding) (env : Input → Field → Nat) where
  Code : Type
  run : Code → Input → Nat
  field : Field → Code
  literal : Nat → Code
  atom : Code → Code
  fork : Code → Code → Code
  cons : Code → Code → Code
  run_field : ∀ f x, run (field f) x = env x f
  run_literal : ∀ n x, run (literal n) x = n
  run_atom : ∀ a x, run (atom a) x = coding.atom (run a x)
  run_fork : ∀ a b x, run (fork a b) x = coding.fork (run a x) (run b x)
  run_cons : ∀ a b x, run (cons a b) x = coding.cons (run a x) (run b x)

namespace Backend
variable {Input : Type} {coding : Coding} {env : Input → Field → Nat}

def compile (b : Backend Input coding env) : Term → b.Code
  | .field f => b.field f
  | .literal n => b.literal n
  | .atom a => b.atom (b.compile a)
  | .fork a c => b.fork (b.compile a) (b.compile c)
  | .cons a c => b.cons (b.compile a) (b.compile c)

theorem compile_correct (b : Backend Input coding env) (t : Term) (x : Input) :
    b.run (b.compile t) x = t.eval coding (env x) := by
  induction t with
  | field f => exact b.run_field f x
  | literal n => exact b.run_literal n x
  | atom a ih => exact (b.run_atom _ _).trans (congrArg coding.atom ih)
  | fork a c ia ic => exact (b.run_fork _ _ _).trans (congrArg2 coding.fork ia ic)
  | cons a c ia ic => exact (b.run_cons _ _ _).trans (congrArg2 coding.cons ia ic)

end Backend

structure Schedule where
  output : Term
  premises : List Term
  deriving Repr

/-- Literal transcription of the maintained outputBody/premiseBodies tables.
Tag 17 and above use the same zero/empty default as those definitions. -/
def schedule (tag : Nat) : Schedule :=
  let G := Term.field .context
  let shifted := Term.field .shifted
  let a := Term.field .a
  let b := Term.field .b
  let c := Term.field .c
  let instI := Term.field .instI
  let instJ := Term.field .instJ
  let shiftC := Term.field .shiftC
  let i := Term.field .i
  let j := Term.field .j
  match tag with
  | 0 => ⟨.fork G a, []⟩
  | 1 => ⟨.fork G (.binary 3 a b), [.fork (.fork a G) b]⟩
  | 2 => ⟨.fork G b, [.fork G (.binary 3 a b), .fork G a]⟩
  | 3 => ⟨.fork G a, [.fork G .bottom]⟩
  | 4 => ⟨.fork G (.binary 5 a (.binary 3 a .bottom)), []⟩
  | 5 => ⟨.fork G (.binary 4 a b), [.fork G a, .fork G b]⟩
  | 6 => ⟨.fork G a, [.fork G (.binary 4 a b)]⟩
  | 7 => ⟨.fork G b, [.fork G (.binary 4 a b)]⟩
  | 8 => ⟨.fork G (.binary 5 a b), [.fork G a]⟩
  | 9 => ⟨.fork G (.binary 5 a b), [.fork G b]⟩
  | 10 => ⟨.fork G c,
      [.fork G (.binary 5 a b), .fork (.fork a G) c, .fork (.fork b G) c]⟩
  | 11 => ⟨.fork G (.unary 6 a), [.fork shifted a]⟩
  | 12 => ⟨.fork G instI, [.fork G (.unary 6 a)]⟩
  | 13 => ⟨.fork G (.unary 7 a), [.fork G instI]⟩
  | 14 => ⟨.fork G c, [.fork G (.unary 7 a), .fork (.fork a shifted) shiftC]⟩
  | 15 => ⟨.fork G (.variableNode 1 i i), []⟩
  | 16 => ⟨.fork G instJ, [.fork G (.variableNode 1 i j), .fork G instI]⟩
  | _ => ⟨.literal 0, []⟩

/-! Independent numerical tables, transcribed from the pinned source.
They use no schedule syntax; the theorem below checks the transcription of
all seventeen schedule branches against these two legacy interpretations. -/
namespace Legacy

def binary (coding : Coding) (tag a b : Nat) : Nat :=
  coding.fork (coding.atom tag) (coding.fork a b)

def unary (coding : Coding) (tag a : Nat) : Nat :=
  coding.fork (coding.atom tag) a

def variableNode (coding : Coding) (tag i j : Nat) : Nat :=
  coding.fork (coding.atom tag) (coding.fork (coding.atom i) (coding.atom j))

def bottom (coding : Coding) : Nat := coding.fork (coding.atom 2) (coding.atom 0)

def outputBody (coding : Coding) (env : Field → Nat) (tag : Nat) : Nat :=
  match tag with
  | 0 | 3 | 6 => coding.fork (env .context) (env .a)
  | 1 => coding.fork (env .context) (binary coding 3 (env .a) (env .b))
  | 2 | 7 => coding.fork (env .context) (env .b)
  | 4 => coding.fork (env .context)
      (binary coding 5 (env .a) (binary coding 3 (env .a) (bottom coding)))
  | 5 => coding.fork (env .context) (binary coding 4 (env .a) (env .b))
  | 8 | 9 => coding.fork (env .context) (binary coding 5 (env .a) (env .b))
  | 10 | 14 => coding.fork (env .context) (env .c)
  | 11 => coding.fork (env .context) (unary coding 6 (env .a))
  | 12 => coding.fork (env .context) (env .instI)
  | 13 => coding.fork (env .context) (unary coding 7 (env .a))
  | 15 => coding.fork (env .context) (variableNode coding 1 (env .i) (env .i))
  | 16 => coding.fork (env .context) (env .instJ)
  | _ => 0

def premiseBodies (coding : Coding) (env : Field → Nat) (tag : Nat) : List Nat :=
  match tag with
  | 0 | 4 | 15 => []
  | 1 => [coding.fork (coding.fork (env .a) (env .context)) (env .b)]
  | 2 => [coding.fork (env .context) (binary coding 3 (env .a) (env .b)),
      coding.fork (env .context) (env .a)]
  | 3 => [coding.fork (env .context) (bottom coding)]
  | 5 => [coding.fork (env .context) (env .a), coding.fork (env .context) (env .b)]
  | 6 | 7 => [coding.fork (env .context) (binary coding 4 (env .a) (env .b))]
  | 8 => [coding.fork (env .context) (env .a)]
  | 9 => [coding.fork (env .context) (env .b)]
  | 10 => [coding.fork (env .context) (binary coding 5 (env .a) (env .b)),
      coding.fork (coding.fork (env .a) (env .context)) (env .c),
      coding.fork (coding.fork (env .b) (env .context)) (env .c)]
  | 11 => [coding.fork (env .shifted) (env .a)]
  | 12 => [coding.fork (env .context) (unary coding 6 (env .a))]
  | 13 => [coding.fork (env .context) (env .instI)]
  | 14 => [coding.fork (env .context) (unary coding 7 (env .a)),
      coding.fork (coding.fork (env .a) (env .shifted)) (env .shiftC)]
  | 16 => [coding.fork (env .context) (variableNode coding 1 (env .i) (env .j)),
      coding.fork (env .context) (env .instI)]
  | _ => []

end Legacy

theorem schedule_matches_legacy (coding : Coding) (env : Field → Nat) (tag : Nat) :
    ((schedule tag).output.eval coding env,
      (schedule tag).premises.map (Term.eval coding env)) =
    (Legacy.outputBody coding env tag, Legacy.premiseBodies coding env tag) := by
  match tag with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | 13 => rfl
  | 14 => rfl
  | 15 => rfl
  | 16 => rfl
  | _ + 17 => rfl

/-- Both emitted programs have their specified numerical meaning for every
raw input; the theorem does not assume a validated coordinate packet. -/
theorem schedule_correct {Input : Type} {coding : Coding}
    {env : Input → Field → Nat} (b : Backend Input coding env)
    (tag : Nat) (x : Input) :
    b.run (b.compile (schedule tag).output) x =
        (schedule tag).output.eval coding (env x) ∧
    b.run (b.compile (Term.list (schedule tag).premises)) x =
        Term.evalList coding ((schedule tag).premises.map (Term.eval coding (env x))) := by
  constructor
  · exact b.compile_correct _ _
  · exact (b.compile_correct _ _).trans (Term.eval_list _ _ _)

#print axioms schedule_matches_legacy
#print axioms Backend.compile_correct
#print axioms schedule_correct

end StructuralSchedule
