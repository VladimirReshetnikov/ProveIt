import TableModelSemantics

/-! Explicit `Code 3` components of one totalized PA194 step. The three
arguments are state, left tape, and right tape; the latter includes the head
cell as its low bit, as in PA194Bounded. Halting and higher state labels stutter.
-/
set_option autoImplicit false
namespace ConfigurationStep
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRASelectCode PRAIsZero PRAExhaustion
open TableDispatch TableModelSemantics BinaryTapeCodes

/-- Unary substitution into three configuration arguments. -/
def app1 (f : Code 1) (a : Code 3) : Code 3 := .comp f (.cons a (.nil 3))
def q : Code 3 := .proj 0
def l : Code 3 := .proj 1
def r : Code 3 := .proj 2
def c194 : Code 3 := app1 (constantCode 194) q
def readBit : Code 3 := app1 parityCode r
def tail : Code 3 := app1 halfCode r
def address : Code 3 := bin addCode (bin addCode q q) readBit
def wr : Code 3 := app1 writeCode address
def dir : Code 3 := app1 directionCode address
def dest : Code 3 := app1 targetCode address
def live : Code 3 := bin ltBitCode q c194
def leftIfRight : Code 3 := bin addCode (bin addCode l l) wr
def leftIfLeft : Code 3 := app1 halfCode l
def rightIfLeft : Code 3 := bin addCode (app1 parityCode l)
    (bin addCode (bin addCode wr wr) (bin addCode (bin addCode tail tail) (bin addCode tail tail)))
def nextQ : Code 3 := selectAmong live dest q
def nextL : Code 3 := selectAmong live (selectAmong dir leftIfRight leftIfLeft) l
def nextR : Code 3 := selectAmong live (selectAmong dir tail rightIfLeft) r

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
noncomputable local instance : DecidableEq M := Classical.decEq M

local notation "F" => Structure.func (L := language)
local notation "Z" => (Structure.func (L := language) (Code.zero 0) Fin.elim0)

theorem modelApp1 (f : Code 1) (a : Code 3) (e : Fin 3 → M) :
    F (app1 f a) e = F f (fun _ => F a e) := by
  rw [app1, modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  rfl

theorem modelSelectAll (x a b : M) : F selectCode ![x,a,b] = if x = Z then b else a := by
  classical
  by_cases h : x = Z
  · subst x
    simp only [ite_true]
    exact modelSelectZero _ _
  · simp only [h, ite_false]
    have hx := (modelZeroOrSuccPred x).resolve_left h
    conv_lhs => rw [← hx]
    exact modelSelectSucc _ _ _

/-- Model-side reference: arithmetic operations and finite table lookup are
interpreted in the given structure, including all nonstandard arguments. -/
noncomputable def stepSem (q l r : M) : M × M × M :=
  let add := fun a b : M => F addCode ![a,b]
  let parity := fun a : M => F parityCode (fun _ => a)
  let half := fun a : M => F halfCode (fun _ => a)
  let address := add (add q q) (parity r)
  let w := lookupSem 0 writes address
  let d := lookupSem 0 directions address
  let t := lookupSem 194 targets address
  let active := F ltBitCode ![q, modelNumeral M 194]
  if active = Z then (q,l,r)
  else if d = Z then (t,half l,add (parity l) (add (add w w) (add (add (half r) (half r)) (add (half r) (half r)))))
  else (t,add (add l l) w,half r)

theorem modelNext (e : Fin 3 → M) :
    (F nextQ e, F nextL e, F nextR e) = stepSem (e 0) (e 1) (e 2) := by
  classical
  simp only [nextQ, nextL, nextR, live, dest, dir, wr, leftIfRight, leftIfLeft,
    rightIfLeft, tail, address, readBit, c194, q, l, r,
    modelSelectAmong, modelBin, modelApp1, modelProjection, modelSelectAll,
    modelConstant, writeCode, directionCode, targetCode, modelLookupAll, stepSem]
  split_ifs <;> rfl
end models
#print axioms modelApp1
#print axioms modelSelectAll
#print axioms modelNext
end ConfigurationStep
