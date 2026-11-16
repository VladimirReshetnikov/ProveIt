import BinaryTapeCodes

/-! Explicit component codes for one binary-tape move after writing `w`.

Inputs are `(left, written, right)`, with each half encoded least-significant
bit first from the head. Direction choice and machine-state dispatch are not
part of these codes. The standard identities use actual division and remainder;
the model theorems only state the composition equations in candidate PRA.
-/
set_option autoImplicit false
namespace TapeStepCodes
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes List.Vector

/-- Append the written cell to the near end of a tape half. -/
def pushCode : Code 3 := bin addCode (bin addCode (.proj 0) (.proj 0)) (.proj 1)
def parityLeftCode : Code 3 := .comp parityCode (.cons (.proj 0) (.nil 3))
def halfLeftCode : Code 3 := .comp halfCode (.cons (.proj 0) (.nil 3))
def parityRightCode : Code 3 := .comp parityCode (.cons (.proj 2) (.nil 3))
def halfRightCode : Code 3 := .comp halfCode (.cons (.proj 2) (.nil 3))
/-- Append the written cell to the right half when moving left. -/
def pushRightCode : Code 3 := bin addCode (bin addCode (.proj 2) (.proj 2)) (.proj 1)

theorem evalPush (l w r : Nat) : eval pushCode (l ::ᵥ w ::ᵥ r ::ᵥ nil) = 2*l+w := by
  change eval addCode (eval addCode (l ::ᵥ l ::ᵥ nil) ::ᵥ w ::ᵥ nil) = _
  rw [eval_addCode, eval_addCode]
  omega

theorem evalPushRight (l w r : Nat) : eval pushRightCode (l ::ᵥ w ::ᵥ r ::ᵥ nil) = 2*r+w := by
  change eval addCode (eval addCode (r ::ᵥ r ::ᵥ nil) ::ᵥ w ::ᵥ nil) = _
  rw [eval_addCode, eval_addCode]
  omega

theorem evalParityLeft (l w r : Nat) : eval parityLeftCode (l ::ᵥ w ::ᵥ r ::ᵥ nil) = l % 2 := by
  change eval parityCode (l ::ᵥ nil) = _
  exact parityEval l

theorem evalHalfLeft (l w r : Nat) : eval halfLeftCode (l ::ᵥ w ::ᵥ r ::ᵥ nil) = l / 2 := by
  change eval halfCode (l ::ᵥ nil) = _
  exact halfEval l

theorem evalParityRight (l w r : Nat) : eval parityRightCode (l ::ᵥ w ::ᵥ r ::ᵥ nil) = r % 2 := by
  change eval parityCode (r ::ᵥ nil) = _
  exact parityEval r

theorem evalHalfRight (l w r : Nat) : eval halfRightCode (l ::ᵥ w ::ᵥ r ::ᵥ nil) = r / 2 := by
  change eval halfCode (r ::ᵥ nil) = _
  exact halfEval r

/-- A legal written bit is recovered at the near end of the updated half. -/
theorem pushBit (l w r : Nat) (hw : w < 2) :
    eval pushCode (l ::ᵥ w ::ᵥ r ::ᵥ nil) % 2 = w ∧
    eval pushCode (l ::ᵥ w ::ᵥ r ::ᵥ nil) / 2 = l := by
  rw [evalPush]
  omega

theorem pushRightBit (l w r : Nat) (hw : w < 2) :
    eval pushRightCode (l ::ᵥ w ::ᵥ r ::ᵥ nil) % 2 = w ∧
    eval pushRightCode (l ::ᵥ w ::ᵥ r ::ᵥ nil) / 2 = r := by
  rw [evalPushRight]
  omega

/-- Output `(left, current, right)` after writing and moving right. -/
def rightComponents (l w r : Nat) : Nat × Nat × Nat :=
  (eval pushCode (l ::ᵥ w ::ᵥ r ::ᵥ nil),
   eval parityRightCode (l ::ᵥ w ::ᵥ r ::ᵥ nil),
   eval halfRightCode (l ::ᵥ w ::ᵥ r ::ᵥ nil))

/-- Output `(left, current, right)` after writing and moving left. -/
def leftComponents (l w r : Nat) : Nat × Nat × Nat :=
  (eval halfLeftCode (l ::ᵥ w ::ᵥ r ::ᵥ nil),
   eval parityLeftCode (l ::ᵥ w ::ᵥ r ::ᵥ nil),
   eval pushRightCode (l ::ᵥ w ::ᵥ r ::ᵥ nil))

/-- Move right, then left without changing the new head cell. -/
theorem rightThenLeft (l w r : Nat) (hw : w < 2) :
    let (l', h', r') := rightComponents l w r
    leftComponents l' h' r' = (l,w,r) := by
  simp only [rightComponents, leftComponents, evalPush, evalParityRight,
    evalHalfRight, evalHalfLeft, evalParityLeft, evalPushRight]
  simp only [Prod.mk.injEq]
  omega

/-- Move left, then right without changing the new head cell. -/
theorem leftThenRight (l w r : Nat) (hw : w < 2) :
    let (l', h', r') := leftComponents l w r
    rightComponents l' h' r' = (l,w,r) := by
  simp only [rightComponents, leftComponents, evalPush, evalParityRight,
    evalHalfRight, evalHalfLeft, evalParityLeft, evalPushRight]
  simp only [Prod.mk.injEq]
  omega

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelPush (e : Fin 3 → M) : Structure.func (L := language) pushCode e =
    Structure.func (L := language) addCode
      ![Structure.func (L := language) addCode ![e 0,e 0],e 1] := by
  simp only [pushCode, modelBin, modelProjection]

theorem modelPushRight (e : Fin 3 → M) : Structure.func (L := language) pushRightCode e =
    Structure.func (L := language) addCode
      ![Structure.func (L := language) addCode ![e 2,e 2],e 1] := by
  simp only [pushRightCode, modelBin, modelProjection]

theorem modelUnaryProjection (f : Code 1) (i : Fin 3) (e : Fin 3 → M) :
    Structure.func (L := language) (.comp f (.cons (.proj i) (.nil 3))) e =
      Structure.func (L := language) f (fun _ => e i) := by
  rw [modelComposition]
  congr 1
  funext j
  refine Fin.cases ?_ (fun k => Fin.elim0 k) j
  change Structure.func (L := language) (Code.proj i) e = _
  rw [modelProjection]

theorem modelParityLeft (e : Fin 3 → M) : Structure.func (L := language) parityLeftCode e =
    Structure.func (L := language) parityCode (fun _ => e 0) := modelUnaryProjection _ _ _
theorem modelHalfLeft (e : Fin 3 → M) : Structure.func (L := language) halfLeftCode e =
    Structure.func (L := language) halfCode (fun _ => e 0) := modelUnaryProjection _ _ _
theorem modelParityRight (e : Fin 3 → M) : Structure.func (L := language) parityRightCode e =
    Structure.func (L := language) parityCode (fun _ => e 2) := modelUnaryProjection _ _ _
theorem modelHalfRight (e : Fin 3 → M) : Structure.func (L := language) halfRightCode e =
    Structure.func (L := language) halfCode (fun _ => e 2) := modelUnaryProjection _ _ _
end models
#print axioms evalPush
#print axioms evalPushRight
#print axioms evalParityLeft
#print axioms evalHalfLeft
#print axioms evalParityRight
#print axioms evalHalfRight
#print axioms pushBit
#print axioms pushRightBit
#print axioms rightThenLeft
#print axioms leftThenRight
#print axioms modelPush
#print axioms modelPushRight
#print axioms modelParityLeft
#print axioms modelHalfLeft
#print axioms modelParityRight
#print axioms modelHalfRight
end TapeStepCodes
