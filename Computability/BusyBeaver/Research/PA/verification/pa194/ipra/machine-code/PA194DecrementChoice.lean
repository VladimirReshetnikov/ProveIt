import PA194DecrementPositive
import PA194DecrementZeroFile
set_option autoImplicit false
namespace PA194DecrementChoice
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PRAExhaustion PA194RegisterFile PA194MarkedFile PA194CarryFile PA194ReturnFile PA194DecrementPositive PA194DecrementZeroFile
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelDecrementChoice (p n : Nat) (ep : Fin (p+1) → M) (e : Fin (n+2) → M) (v l : M)
    (hp : ep (Fin.last p) = F markedBlock ![v,F (fileCode (n+1)) e]) :
    letI : DecidableEq M := Classical.decEq M
    let cost := F (costCode p) ep
    let pred := F predCode (fun _ => v)
    let positive := F (returnCode p) (Fin.cases (F block ![pred,F (fileCode (n+1)) e]) ep)
    let zero := F (returnCode p) (Fin.cases (F block ![(0 : M),F (fileCode (n+1)) e]) ep)
    let isZero := v = (0 : M)
    F PA194Stepper.stepper ![(cost+(if isZero then TableDispatch.modelNumeral M 7 else TableDispatch.modelNumeral M 4))+cost,
      F pairCode ![(1 : M),F pairCode ![l,F (fileCode p) ep]]] =
    if isZero then F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+zero+zero]]
    else F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![l,positive+positive+1]] := by
  classical
  by_cases hv : v = (0 : M)
  · subst v
    simp only [ite_true]
    exact modelZeroDecrementFile p n ep e l hp
  · simp only [hv,ite_false]
    have he := (modelZeroOrSuccPred v).resolve_left hv
    have hs : F Code.succ (fun _ => F predCode (fun _ => v)) = F predCode (fun _ => v)+1 := (modelAddOne _).symm
    rw [hs] at he
    have hp' : ep (Fin.last p) = F markedBlock ![F predCode (fun _ => v)+1,F (fileCode (n+1)) e] := by
      rw [he]
      exact hp
    exact modelPositiveDecrement p (n+1) ep e (F predCode (fun _ => v)) l hp'
#print axioms modelDecrementChoice
end models
end PA194DecrementChoice
