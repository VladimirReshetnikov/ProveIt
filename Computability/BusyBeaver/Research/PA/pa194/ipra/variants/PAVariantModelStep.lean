import PAVariantRowDispatch
import ConfigurationStep
set_option autoImplicit false
namespace PAVariantModelStep
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRASelectCode
open TableDispatch TableModelSemantics ConfigurationStep BinaryTapeCodes

abbrev Action := PAVariantRowDispatch.Action
def wr (rows : List Action) : Code 3 := app1 (PAVariantRowDispatch.writeCode rows) address
def dir (rows : List Action) : Code 3 := app1 (PAVariantRowDispatch.directionCode rows) address
def dest (halt : Nat) (rows : List Action) : Code 3 := app1 (PAVariantRowDispatch.targetCode halt rows) address
def live (states : Nat) : Code 3 := bin ltBitCode q (app1 (constantCode states) q)
def leftIfRight (rows : List Action) : Code 3 := bin addCode (bin addCode l l) (wr rows)
def rightIfLeft (rows : List Action) : Code 3 := bin addCode (app1 parityCode l)
    (bin addCode (bin addCode (wr rows) (wr rows)) (bin addCode (bin addCode tail tail) (bin addCode tail tail)))
def nextQ (states halt : Nat) (rows : List Action) : Code 3 := selectAmong (live states) (dest halt rows) q
def nextL (states : Nat) (rows : List Action) : Code 3 :=
  selectAmong (live states) (selectAmong (dir rows) (leftIfRight rows) leftIfLeft) l
def nextR (states : Nat) (rows : List Action) : Code 3 :=
  selectAmong (live states) (selectAmong (dir rows) tail (rightIfLeft rows)) r

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
noncomputable local instance : DecidableEq M := Classical.decEq M
local notation "F" => Structure.func (L := language) (M := M)
local notation "Z" => (F (Code.zero 0) Fin.elim0)

noncomputable def stepSem (states halt : Nat) (rows : List Action) (q l r : M) : M × M × M :=
  let add := fun a b : M => F addCode ![a,b]
  let parity := fun a : M => F parityCode (fun _ => a)
  let half := fun a : M => F halfCode (fun _ => a)
  let address := add (add q q) (parity r)
  let w := lookupSem 0 (PAVariantRowDispatch.writes rows) address
  let d := lookupSem 0 (PAVariantRowDispatch.directions rows) address
  let t := lookupSem halt (PAVariantRowDispatch.targets rows) address
  let active := F ltBitCode ![q, modelNumeral M states]
  if active = Z then (q,l,r)
  else if d = Z then (t,half l,add (parity l) (add (add w w) (add (add (half r) (half r)) (add (half r) (half r)))))
  else (t,add (add l l) w,half r)

theorem modelNext (states halt : Nat) (rows : List Action) (e : Fin 3 → M) :
    (F (nextQ states halt rows) e, F (nextL states rows) e, F (nextR states rows) e) =
      stepSem states halt rows (e 0) (e 1) (e 2) := by
  classical
  simp only [nextQ, nextL, nextR, live, dest, dir, wr, leftIfRight, leftIfLeft,
    rightIfLeft, tail, address, readBit, q, l, r,
    modelSelectAmong, modelBin, modelApp1, modelProjection, modelSelectAll,
    modelConstant, PAVariantRowDispatch.writeCode, PAVariantRowDispatch.directionCode,
    PAVariantRowDispatch.targetCode, modelLookupAll, stepSem]
  split_ifs <;> rfl

#print axioms modelNext
end models
end PAVariantModelStep
