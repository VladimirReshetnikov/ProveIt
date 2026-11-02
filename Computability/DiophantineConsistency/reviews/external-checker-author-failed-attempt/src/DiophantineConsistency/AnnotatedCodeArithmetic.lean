import DiophantineConsistency.AnnotatedProofCode
import DiophantineConsistency.DirectScalarArithmetic
import DiophantineConsistency.ScalarPROptimizer

/-!
# Supplied arithmetic programs for the annotated-checker wire format

These are finite scalar primitive-recursive program data, not witnesses
extracted from a proposition asserting computability. The guarded workspace
list lookup preserves the difference between a missing entry and a zero entry.
-/

namespace DiophantineConsistency.AnnotatedCodeArithmetic

open SetTheory SetTheory.Form
open ScalarPRCode DirectScalar AnnotatedProofChecker AnnotatedProofCode

set_option maxHeartbeats 600000
set_option maxRecDepth 12000
attribute [local irreducible] Nat.unpair

/-- The two components after removing the positive wire-code marker. -/
def treeLeft (code : Nat) : Nat := code.pred.unpair.1
def treeRight (code : Nat) : Nat := code.pred.unpair.2

/-- Zero is invalid; one denotes an atom and two denotes a fork.
This checks only the outer constructor, not the recursive tree grammar. -/
def treeKind (code : Nat) : Nat :=
  if code=0 then 0 else if treeLeft code=0 then 1 else 2

def treeLeftChild (code : Nat) : Nat := (treeLeft code).pred

def treeLeftProgram : R treeLeft := Realizes.left.comp (pred identity)
def treeRightProgram : R treeRight := Realizes.right.comp (pred identity)
def treeLeftChildProgram : R treeLeftChild := pred treeLeftProgram

def treeKindProgram : R treeKind :=
  ifZero identity Realizes.zero (ifZero treeLeftProgram (constant 1) (constant 2))

def atomConstructor : R (fun n => Tree.quote (.atom n)) :=
  successor (Realizes.zero.pair identity)

def forkConstructor : R (fun n => Nat.pair (n.unpair.1+1) n.unpair.2+1) :=
  successor ((successor Realizes.left).pair Realizes.right)

@[simp] theorem treeLeft_atom (n : Nat) : treeLeft (Tree.atom n).quote=0 := by
  simp [treeLeft,Tree.quote]
@[simp] theorem treeRight_atom (n : Nat) : treeRight (Tree.atom n).quote=n := by
  simp [treeRight,Tree.quote]
@[simp] theorem treeKind_atom (n : Nat) : treeKind (Tree.atom n).quote=1 := by
  simp [treeKind,Tree.quote,treeLeft]
@[simp] theorem treeKind_fork (a b : Tree) : treeKind (Tree.fork a b).quote=2 := by
  simp [treeKind,Tree.quote,treeLeft]
@[simp] theorem treeLeftChild_fork (a b : Tree) :
    treeLeftChild (Tree.fork a b).quote=a.quote := by
  simp [treeLeftChild,treeLeft,Tree.quote]
@[simp] theorem treeRight_fork (a b : Tree) : treeRight (Tree.fork a b).quote=b.quote := by
  simp [treeRight,Tree.quote]

/-- Workspace lists store arbitrary natural values; this is distinct from the
external tree-list wire format. Zero is nil, successor-pair is cons. -/
def listCode : List Nat → Nat
  | [] => 0
  | x::xs => Nat.pair x (listCode xs)+1

def optionCode : Option Nat → Nat
  | none => 0
  | some n => n+1

/-- The guard prevents the terminal nil marker from being read as a value. -/
def listHead (code : Nat) : Nat := if code=0 then 0 else code.pred.unpair.1+1
def listTail (code : Nat) : Nat := if code=0 then 0 else code.pred.unpair.2

def dropCode (code : Nat) : Nat → Nat
  | 0 => code
  | i+1 => listTail (dropCode code i)

def lookup (code index : Nat) : Nat := listHead (dropCode code index)

def listHeadProgram : R listHead :=
  ifZero identity Realizes.zero (successor treeLeftProgram)
def listTailProgram : R listTail :=
  ifZero identity Realizes.zero treeRightProgram

def dropProgram : R (fun n => dropCode n.unpair.1 n.unpair.2) := by
  let p := recursion (g := fun _ _ acc => listTail acc) identity
    (listTailProgram.comp (Realizes.right.comp Realizes.right))
  refine p.ofEq ?_
  intro n
  induction n.unpair.2 <;> simp_all [dropCode]

def lookupProgram : R (fun n => lookup n.unpair.1 n.unpair.2) :=
  listHeadProgram.comp dropProgram

@[simp] theorem listHead_nil : listHead 0=0 := rfl
@[simp] theorem listTail_nil : listTail 0=0 := rfl
@[simp] theorem listHead_cons (x : Nat) (xs : List Nat) :
    listHead (listCode (x::xs))=x+1 := by
  simp [listHead,listCode]
@[simp] theorem listTail_cons (x : Nat) (xs : List Nat) :
    listTail (listCode (x::xs))=listCode xs := by
  simp [listTail,listCode]

theorem dropCode_nil (i : Nat) : dropCode 0 i=0 := by
  induction i <;> simp_all [dropCode]

theorem dropCode_succ (code i : Nat) : dropCode code (i+1)=dropCode (listTail code) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change listTail (dropCode code (i+1))=listTail (dropCode (listTail code) i)
    rw [ih]

/-- Lookup returns zero for an invalid reference and a successor for a found
value, including a found value equal to zero. -/
theorem lookup_listCode (xs : List Nat) (i : Nat) :
    lookup (listCode xs) i=optionCode xs[i]? := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => rfl
    | cons x xs => exact listHead_cons x xs
  | succ i ih =>
    cases xs with
    | nil => simp [lookup,listCode,dropCode_nil,optionCode]
    | cons x xs =>
      rw [lookup,dropCode_succ,listTail_cons]
      exact ih xs

@[simp] theorem optionCode_eq_succ (o : Option Nat) (n : Nat) :
    optionCode o=n+1 ↔ o=some n := by
  cases o <;> simp [optionCode]

/-- Input coordinates are `(history,(backwardIndex,expectedValue))`. -/
def referenceCheck (n : Nat) : Nat :=
  if lookup n.unpair.1 n.unpair.2.unpair.1=n.unpair.2.unpair.2+1 then 1 else 0

def referenceProgram : R referenceCheck := by
  let p : R (fun n => lookup n.unpair.1 n.unpair.2.unpair.1) :=
    (lookupProgram.comp (Realizes.left.pair (Realizes.left.comp Realizes.right))).ofEq
      (fun _ => by simp)
  exact ifEq p (successor (Realizes.right.comp Realizes.right)) (constant 1) Realizes.zero

theorem referenceCheck_listCode (xs : List Nat) (i expected : Nat) :
    referenceCheck (Nat.pair (listCode xs) (Nat.pair i expected))=1 ↔ xs[i]?=some expected := by
  simp [referenceCheck,lookup_listCode]

/-- Judgment quotations reuse the frozen context and formula wire syntax. -/
def quoteJudgment (j : Judgment) : Tree :=
  .fork (quoteContext j.context) (quoteForm j.conclusion)

def parseJudgment : Tree → Option Judgment
  | .fork G f => return ⟨←parseContext G,←parseForm f⟩
  | _ => none

@[simp] theorem parseJudgment_quoteJudgment (j : Judgment) :
    parseJudgment (quoteJudgment j)=some j := by
  cases j
  simp [quoteJudgment,parseJudgment]

def judgmentCode (j : Judgment) : Nat := (quoteJudgment j).quote

theorem judgmentCode_injective : Function.Injective judgmentCode := by
  intro a b h
  have hh := congrArg (parseWith parseJudgment) h
  simpa only [judgmentCode,parseWith_quotation,parseJudgment_quoteJudgment,
    Option.some.injEq] using hh

/-- Numeric parent checking is exactly lookup of the expected original
judgment, so both context and formula equality are retained. -/
theorem referenceCheck_judgments (seen : List Judgment) (i : Nat) (j : Judgment) :
    referenceCheck (Nat.pair (listCode (seen.map judgmentCode))
      (Nat.pair i (judgmentCode j)))=1 ↔ seen[i]?=some j := by
  rw [referenceCheck_listCode,List.getElem?_map]
  change Option.map judgmentCode seen[i]? = Option.map judgmentCode (some j) ↔ _
  exact (Option.map_injective judgmentCode_injective).eq_iff

/-- Each literal supplied program is certified primitive recursive by the
constructor theorem, without extracting program data from that proposition. -/
theorem referenceProgram_primrec : Nat.Primrec referenceProgram.val.eval :=
  referenceProgram.val.primrec

/-- Certified tree sizes of the supplied source programs. These are program
instruction counts, not polynomial variable or scalar-operation counts. -/
theorem lookupProgram_nodeCount : lookupProgram.val.nodeCount=69 := by decide

theorem referenceProgram_nodeCount : referenceProgram.val.nodeCount=225 := by decide

def optimizedReferenceProgram : R referenceCheck := referenceProgram.optimize

theorem optimizedReferenceProgram_nodeCount :
    optimizedReferenceProgram.val.nodeCount=209 := by decide

end DiophantineConsistency.AnnotatedCodeArithmetic
