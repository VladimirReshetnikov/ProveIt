import ConfigurationStep

/-! Explicit packed PA194 configuration iterator. The decoder is a concrete
integer-square-root algorithm for the square pairing used by `pairCode`.
The theorems here establish its actual defining recurrence in all candidate
PRA models; they do NOT yet establish pairing/decoder inversion or identify
the resulting clock with literal PA194 halting.
-/
set_option autoImplicit false
namespace PackedClock
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRASelectCode PRAIsZero
open ConfigurationStep

/-- Apply unary code to a code of any arity. -/
def unary {n : Nat} (f : Code 1) (x : Code n) : Code n := .comp f (.cons x (.nil n))
def inc {n : Nat} (x : Code n) : Code n := unary .succ x

/-- Candidate floor square root: after index i, increment the accumulator
when its next square is at most i+1. -/
def rootStep : Code 2 :=
  let k : Code 2 := .proj 0
  let s : Code 2 := .proj 1
  let next := inc s
  selectAmong (bin ltBitCode (bin mulCode next next) (inc (inc k))) next s

def rootCode : Code 1 := .prec (.zero 0) rootStep

def squareRoot : Code 1 := rootCode
def remainder : Code 1 := bin subCode (.proj 0) (bin mulCode squareRoot squareRoot)
def lowSide : Code 1 := bin ltBitCode remainder squareRoot
/-- Candidate left projection for the square pairing. -/
def decodeLeft : Code 1 := selectAmong lowSide remainder squareRoot
/-- Candidate right projection for the square pairing. -/
def decodeRight : Code 1 := selectAmong lowSide squareRoot (bin subCode remainder squareRoot)

def packedQ : Code 1 := decodeLeft
def packedL : Code 1 := unary decodeLeft decodeRight
def packedR : Code 1 := unary decodeRight decodeRight

def inject3 (f : Code 3) : Code 1 := .comp f (.cons packedQ (.cons packedL (.cons packedR (.nil 1))))
def encodedStep : Code 1 := bin pairCode (inject3 nextQ)
  (bin pairCode (inject3 nextL) (inject3 nextR))

/-- Starting configuration is the packed zero triple. -/
def clockStep : Code 2 := unary encodedStep (.proj 1)
def clock : Code 1 := .prec (.zero 0) clockStep

def clockState : Code 1 := unary decodeLeft clock
def const194 : Code 1 := TableDispatch.constantCode 194
/-- Intended halting indicator for the totalized encoded run. -/
def haltIndicator : Code 1 := unary isZeroCode (bin ltBitCode clockState const194)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelRootZero : Structure.func (L := language) (M := M) rootCode
    (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0) =
    Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have h := modelBase (M := M) (Code.zero 0) rootStep (Fin.elim0 : Fin 0 → M)
  simpa [rootCode, Matrix.fun_eq_vec_one, PRAMultiplication.modelZero] using h

theorem modelRootSucc (i : M) : Structure.func (L := language) rootCode
    (fun _ => Structure.func (L := language) Code.succ (fun _ => i)) =
    Structure.func (L := language) rootStep
      ![i, Structure.func (L := language) rootCode (fun _ => i)] := by
  have h := modelStep (M := M) (Code.zero 0) rootStep (fun _ : Fin 1 => i)
  have hy : (fun _ : Fin 0 => i) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hy] at h
  have hs : Fin.cases (Structure.func (L := language) Code.succ (fun _ => i))
      (Fin.elim0 : Fin 0 → M) = (fun _ : Fin 1 => Structure.func (L := language) Code.succ (fun _ => i)) := by
    funext j
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  convert h using 1 <;> rfl

theorem modelClockZero : Structure.func (L := language) (M := M) clock
    (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0) =
    Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have h := modelBase (M := M) (Code.zero 0) clockStep (Fin.elim0 : Fin 0 → M)
  simpa [clock, Matrix.fun_eq_vec_one, PRAMultiplication.modelZero] using h

theorem modelClockSucc (i : M) : Structure.func (L := language) clock
    (fun _ => Structure.func (L := language) Code.succ (fun _ => i)) =
    Structure.func (L := language) encodedStep
      (fun _ => Structure.func (L := language) clock (fun _ => i)) := by
  have h := modelStep (M := M) (Code.zero 0) clockStep (fun _ : Fin 1 => i)
  have hy : (fun _ : Fin 0 => i) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hy] at h
  have hs : Fin.cases (Structure.func (L := language) Code.succ (fun _ => i))
      (Fin.elim0 : Fin 0 → M) = (fun _ : Fin 1 => Structure.func (L := language) Code.succ (fun _ => i)) := by
    funext j
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  change Structure.func (L := language) clock
    (fun _ => Structure.func (L := language) Code.succ (fun _ => i)) =
    Structure.func (L := language) clockStep
      (Fin.cases i (Fin.cases (Structure.func (L := language) clock (fun _ => i)) (Fin.elim0 : Fin 0 → M))) at h
  rw [h, clockStep, unary, modelComposition]
  congr 1
  funext j
  refine Fin.cases ?_ (fun k => Fin.elim0 k) j
  change Structure.func (L := language) (Code.proj 1)
      (Fin.cases i (Fin.cases (Structure.func (L := language) clock (fun _ => i)) (Fin.elim0 : Fin 0 → M))) = _
  rw [modelProjection]
  rfl
end models
#print axioms modelRootZero
#print axioms modelRootSucc
#print axioms modelClockZero
#print axioms modelClockSucc
end PackedClock
