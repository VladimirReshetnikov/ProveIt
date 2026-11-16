import PA194RegisterSplit
import PA194RegisterUpdate
set_option autoImplicit false
namespace PA194DecrementSource
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PRAModelIOpenPairing PA194RegisterFile PA194MarkedFile PA194CarryFile PA194ReturnFile PA194DecrementChoice PA194RegisterPermutation PA194RegisterUpdate PA194RegisterSplit
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
def slot (r : Fin 9) : Fin 9 := ⟨M6.Source.physicalRegister r,M6.Source.physicalRegister_lt r⟩
/-- The marked physical decrement box agrees with a logical source-register
update for every fixed register and every model of PRA. -/
theorem modelSourceDecrement (r : Fin 9) (e : Fin 11 → M) (l : M) :
    letI : DecidableEq M := Classical.decEq M
    let p := slot r
    let a := physicalArgs e
    let v := e (logicalIndex r)
    let rest := tailArgs p a
    let mark := F markedBlock ![v,F (fileCode (8-p.val+1)) rest]
    let ep := frontArgs p a mark
    let c := F (costCode p.val) ep
    let out := F sourceFileCode (Function.update e (logicalIndex r) (F predCode (fun _ => v)))
    F PA194Stepper.stepper ![(c+(if v = (0 : M) then TableDispatch.modelNumeral M 7 else TableDispatch.modelNumeral M 4))+c,
      F pairCode ![(1 : M),F pairCode ![l,F (fileCode p.val) ep]]] =
    if v = (0 : M) then F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(F sourceFileCode e)+(F sourceFileCode e)]]
    else F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![l,out+out+1]] := by
  classical
  let p := slot r
  let a := physicalArgs e
  let v := e (logicalIndex r)
  let rest := tailArgs p a
  let mark := F markedBlock ![v,F (fileCode (8-p.val+1)) rest]
  let ep := frontArgs p a mark
  have hp : ep (Fin.last p.val) = F markedBlock ![v,F (fileCode (8-p.val+1)) rest] := by simp [ep,frontArgs,mark]
  have h := modelDecrementChoice p.val (8-p.val) ep rest v l hp
  have ha : a ⟨p.val,by have := p.isLt; omega⟩ = v := by
    exact sourceRegisterAt e r
  have hout := splitFile p a (F predCode (fun _ => v)) mark
  change _ = F (fileCode 10) (Function.update a (physicalIndex r) (F predCode (fun _ => v))) at hout
  rw [←modelSourceWrite e r] at hout
  have hwhole := splitFile p a v mark
  have hu : Function.update a ⟨p.val,by have := p.isLt; omega⟩ v = a := by
    rw [←ha]
    funext i
    by_cases hi : i = ⟨p.val,by have := p.isLt; omega⟩
    · subst i; simp
    · simp [hi]
  rw [hu,←modelSourceFile] at hwhole
  dsimp only at h ⊢
  rw [hout] at h
  by_cases hv : e (logicalIndex r) = (0 : M)
  · have hvv : v = (0 : M) := hv
    simp only [hvv,if_true] at h
    simp only [hv,if_true]
    rw [hvv] at hwhole
    rw [hwhole] at h
    dsimp [p,a,v,rest,mark,ep] at h
    simp only [hv] at h
    exact h
  · have hvv : v ≠ (0 : M) := hv
    simp only [hvv,if_false] at h
    simp only [hv,if_false]
    exact h
#print axioms modelSourceDecrement
end models
end PA194DecrementSource
