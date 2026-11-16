import TapeStepCodes
import PA194Rows

/-! Explicit finite primitive-recursive lookup for PA194's pinned dense rows.
The input is the row index `2*state + read`; the three output codes return
write, direction (1 means right), and next state, respectively. The default
outside the 388 rows is `(0,0,194)`. The source table is generated from a
pinned archive member by the adjacent replay script.

The standard-Nat correctness theorem below is not a PRA or iPRA derivation.
-/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace TableDispatch
open DiophantineConsistency
open PRAFiniteFunctionCodes PRATheory PRASelectCode PRAHistoryPairCode PRAIsZero PRAAddOne PRALanguage
open List.Vector

def constantCode (n : Nat) : Code 1 :=
  match n with
  | 0 => .zero 1
  | n+1 => .comp .succ (.cons (constantCode n) (.nil 1))

theorem evalConstant (n x : Nat) : eval (constantCode n) (x ::ᵥ nil) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.succ (eval (constantCode n) (x ::ᵥ nil)) = Nat.succ n
    rw [ih]

/-- Every list is compiled into finite syntax; no function code is chosen. -/
def lookupCode (default : Nat) : List Nat → Code 1
  | [] => constantCode default
  | a :: as => selectAmong isZeroCode (constantCode a)
      (.comp (lookupCode default as) (.cons predCode (.nil 1)))

theorem evalLookup (default : Nat) (xs : List Nat) (x : Nat) :
    eval (lookupCode default xs) (x ::ᵥ nil) = xs.getD x default := by
  induction xs generalizing x with
  | nil => simp [lookupCode, evalConstant]
  | cons a as ih =>
    cases x with
    | zero =>
      change eval selectCode (1 ::ᵥ eval (constantCode a) (0 ::ᵥ nil) ::ᵥ
        eval (lookupCode default as) (0 ::ᵥ nil) ::ᵥ nil) = _
      change eval (constantCode a) (0 ::ᵥ nil) = a
      exact evalConstant a 0
    | succ x =>
      change eval selectCode (0 ::ᵥ eval (constantCode a) ((x+1) ::ᵥ nil) ::ᵥ
        eval (lookupCode default as) (x ::ᵥ nil) ::ᵥ nil) = _
      change eval (lookupCode default as) (x ::ᵥ nil) = as.getD x default
      exact ih x

def writes : List Nat := PA194Rows.rows.map (fun r => r.1)
def directions : List Nat := PA194Rows.rows.map (fun r => r.2.1)
def targets : List Nat := PA194Rows.rows.map (fun r => r.2.2)

def writeCode : Code 1 := lookupCode 0 writes
def directionCode : Code 1 := lookupCode 0 directions
def targetCode : Code 1 := lookupCode 194 targets

theorem evalWrite (i : Nat) : eval writeCode (i ::ᵥ nil) = writes.getD i 0 :=
  evalLookup 0 writes i
theorem evalDirection (i : Nat) : eval directionCode (i ::ᵥ nil) = directions.getD i 0 :=
  evalLookup 0 directions i
theorem evalTarget (i : Nat) : eval targetCode (i ::ᵥ nil) = targets.getD i 194 :=
  evalLookup 194 targets i

/-- Compile the `(state, read)` address into the three row-output codes. -/
def rowIndexCode : Code 2 := bin addCode (bin addCode (.proj 0) (.proj 0)) (.proj 1)
def writeAtCode : Code 2 := .comp writeCode (.cons rowIndexCode (.nil 2))
def directionAtCode : Code 2 := .comp directionCode (.cons rowIndexCode (.nil 2))
def targetAtCode : Code 2 := .comp targetCode (.cons rowIndexCode (.nil 2))

theorem evalRowIndex (q b : Nat) : eval rowIndexCode (q ::ᵥ b ::ᵥ nil) = 2*q+b := by
  change eval addCode (eval addCode (q ::ᵥ q ::ᵥ nil) ::ᵥ b ::ᵥ nil) = _
  rw [eval_addCode, eval_addCode]
  omega

theorem getDMap {α β : Type} (f : α → β) (xs : List α) (i : Nat) (d : α) :
    (xs.map f).getD i (f d) = f (xs.getD i d) := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i <;> simp

theorem evalDispatch (q b : Nat) :
    (eval writeAtCode (q ::ᵥ b ::ᵥ nil),
     eval directionAtCode (q ::ᵥ b ::ᵥ nil),
     eval targetAtCode (q ::ᵥ b ::ᵥ nil)) =
       PA194Rows.rows.getD (2*q+b) (0,0,194) := by
  change (eval writeCode (eval rowIndexCode (q ::ᵥ b ::ᵥ nil) ::ᵥ nil),
    eval directionCode (eval rowIndexCode (q ::ᵥ b ::ᵥ nil) ::ᵥ nil),
    eval targetCode (eval rowIndexCode (q ::ᵥ b ::ᵥ nil) ::ᵥ nil)) = _
  rw [evalRowIndex, evalWrite, evalDirection, evalTarget]
  simp only [writes, directions, targets]
  have h1 := getDMap (fun r : Nat × Nat × Nat => r.1) PA194Rows.rows (2*q+b) (0,0,194)
  have h2 := getDMap (fun r : Nat × Nat × Nat => r.2.1) PA194Rows.rows (2*q+b) (0,0,194)
  have h3 := getDMap (fun r : Nat × Nat × Nat => r.2.2) PA194Rows.rows (2*q+b) (0,0,194)
  change (PA194Rows.rows.map (fun r => r.1)).getD (2*q+b) 0 = _ at h1
  change (PA194Rows.rows.map (fun r => r.2.1)).getD (2*q+b) 0 = _ at h2
  change (PA194Rows.rows.map (fun r => r.2.2)).getD (2*q+b) 194 = _ at h3
  rw [h1, h2, h3]

section models
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAExhaustion
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelLookupZero (default a : Nat) (as : List Nat) :
    Structure.func (L := language) (M := M) (lookupCode default (a :: as))
      (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0) =
    Structure.func (L := language) (constantCode a)
      (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0) := by
  rw [lookupCode, modelSelectAmong, modelIsZeroZero, modelSelectOne]

theorem modelLookupSucc (default a : Nat) (as : List Nat) (x : M) :
    Structure.func (L := language) (lookupCode default (a :: as))
      (fun _ => Structure.func (L := language) Code.succ (fun _ => x)) =
    Structure.func (L := language) (lookupCode default as) (fun _ => x) := by
  rw [lookupCode, modelSelectAmong, modelIsZeroSucc, modelSelectZero, modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  change Structure.func (L := language) predCode
    (fun _ => Structure.func (L := language) Code.succ (fun _ => x)) = x
  exact modelPredSucc x
/-- The standard numeral interpreted using this model's zero and successor. -/
def modelNumeral (M : Type) [Structure language M] : Nat → M
  | 0 => Structure.func (L := language) (Code.zero 0) Fin.elim0
  | n+1 => Structure.func (L := language) Code.succ (fun _ => modelNumeral M n)

theorem modelConstant (n : Nat) (x : M) :
    Structure.func (L := language) (constantCode n) (fun _ => x) = modelNumeral M n := by
  induction n with
  | zero => exact PRAMultiplication.modelZero _
  | succ n ih =>
    rw [constantCode, modelComposition]
    change Structure.func (L := language) Code.succ _ =
      Structure.func (L := language) Code.succ (fun _ => modelNumeral M n)
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    change Structure.func (L := language) (constantCode n) (fun _ => x) = _
    exact ih

/-- Each standard numeral row has its correct output in every candidate PRA model. -/
theorem modelLookupNumeral (default : Nat) (xs : List Nat) (i : Nat) :
    Structure.func (L := language) (M := M) (lookupCode default xs)
      (fun _ => modelNumeral M i) = modelNumeral M (xs.getD i default) := by
  induction xs generalizing i with
  | nil =>
    change Structure.func (L := language) (constantCode default)
      (fun _ => modelNumeral M i) = modelNumeral M default
    exact modelConstant default _
  | cons a as ih =>
    cases i with
    | zero =>
      change Structure.func (L := language) (lookupCode default (a :: as))
        (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0) = modelNumeral M a
      rw [modelLookupZero, modelConstant]
    | succ i =>
      change Structure.func (L := language) (lookupCode default (a :: as))
        (fun _ => Structure.func (L := language) Code.succ (fun _ => modelNumeral M i)) = _
      rw [modelLookupSucc]
      exact ih i
theorem modelWriteNumeral (i : Nat) :
    Structure.func (L := language) (M := M) writeCode (fun _ => modelNumeral M i) =
      modelNumeral M (PA194Rows.rows.getD i (0,0,194)).1 := by
  change Structure.func (L := language) (lookupCode 0 writes) _ = _
  rw [modelLookupNumeral]
  have h := getDMap (fun r : Nat × Nat × Nat => r.1) PA194Rows.rows i (0,0,194)
  change (PA194Rows.rows.map (fun r => r.1)).getD i 0 = _ at h
  exact congrArg (modelNumeral M) h

theorem modelDirectionNumeral (i : Nat) :
    Structure.func (L := language) (M := M) directionCode (fun _ => modelNumeral M i) =
      modelNumeral M (PA194Rows.rows.getD i (0,0,194)).2.1 := by
  change Structure.func (L := language) (lookupCode 0 directions) _ = _
  rw [modelLookupNumeral]
  have h := getDMap (fun r : Nat × Nat × Nat => r.2.1) PA194Rows.rows i (0,0,194)
  change (PA194Rows.rows.map (fun r => r.2.1)).getD i 0 = _ at h
  exact congrArg (modelNumeral M) h

theorem modelTargetNumeral (i : Nat) :
    Structure.func (L := language) (M := M) targetCode (fun _ => modelNumeral M i) =
      modelNumeral M (PA194Rows.rows.getD i (0,0,194)).2.2 := by
  change Structure.func (L := language) (lookupCode 194 targets) _ = _
  rw [modelLookupNumeral]
  have h := getDMap (fun r : Nat × Nat × Nat => r.2.2) PA194Rows.rows i (0,0,194)
  change (PA194Rows.rows.map (fun r => r.2.2)).getD i 194 = _ at h
  exact congrArg (modelNumeral M) h
end models

#print axioms evalConstant
#print axioms evalLookup
#print axioms evalWrite
#print axioms evalDirection
#print axioms evalTarget
#print axioms evalRowIndex
#print axioms evalDispatch
#print axioms modelLookupZero
#print axioms modelLookupSucc
#print axioms modelConstant
#print axioms modelLookupNumeral
#print axioms modelWriteNumeral
#print axioms modelDirectionNumeral
#print axioms modelTargetNumeral
end TableDispatch
