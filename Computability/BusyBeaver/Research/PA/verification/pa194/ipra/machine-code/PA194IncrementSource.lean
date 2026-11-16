import PA194DecrementSource
import PA194IncrementAnywhere
set_option autoImplicit false
set_option maxRecDepth 2048
namespace PA194IncrementSource
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PRAModelIOpenPairing PA194RegisterFile PA194MarkedFile PA194CarryFile PA194ReturnFile PA194ReturnFileMeaning PA194RegisterPermutation PA194RegisterUpdate PA194DecrementSource PA194RegisterSplit PA194IncrementAnywhere
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

def inputArgs (p : Fin 9) (a : Fin 11 → M) : Fin (8-p.val+2) → M :=
  Fin.lastCases 0 (fun i => a ⟨p.val+i.val,by have := p.isLt; have := i.isLt; omega⟩)

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem inputLast (p : Fin 9) (a : Fin 11 → M) : inputArgs p a (Fin.last (8-p.val+1)) = (0 : M) := by
  simp [inputArgs]
omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem inputNonlast (p : Fin 9) (a : Fin 11 → M) (i : Fin (8-p.val+2)) (hi : i.val < 8-p.val+1) :
    inputArgs p a i = a ⟨p.val+i.val,by have := p.isLt; omega⟩ := by
  unfold inputArgs
  have heq : i = Fin.castSucc ⟨i.val,hi⟩ := Fin.ext rfl
  conv_lhs => rw [heq,Fin.lastCases_castSucc]

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem inputFirst (p : Fin 9) (a : Fin 11 → M) : inputArgs p a 0 = a ⟨p.val,by have := p.isLt; omega⟩ := by
  have h : 0 < 8-p.val+1 := by omega
  simpa using inputNonlast p a 0 h

/-- The increment output is the updated source file with an appended
one-valued spare and blank suffix. -/
theorem outputFile (p : Fin 9) (a : Fin 11 → M) (z marked : M) :
    let x := inputArgs p a
    let ep := frontArgs p a marked
    let six := (((1 : M)+1)+1)+(((1 : M)+1)+1)
    F (returnCode p.val) (Fin.cases (F block ![z,F (fileCode (8-p.val)) (replaceLast (8-p.val) (fun i => x i.succ) six)]) ep) =
    F (fileCode 10) (Function.update (Function.update (Function.update a ⟨p.val,by have := p.isLt; omega⟩ z) 9 1) 10 0) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  rw [modelReturnMeaning,←modelSpareOne]
  rcases p with ⟨p,hp⟩
  have hs : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 := by omega
  rcases hs with h | h | h | h | h | h | h | h | h <;> subst p <;>
    simp only [modelFileSucc] <;>
    simp [inputNonlast,frontArgs,replaceLast,Fin.snoc,Function.update,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
omit [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem physicalUpdate (e : Fin 11 → M) (i : Fin 11) (v : M) :
    physicalArgs (Function.update e (inputOrder i) v) = Function.update (physicalArgs e) i v := by
  funext j
  by_cases h : j = i
  · subst j; simp [physicalArgs]
  · have hne : inputOrder j ≠ inputOrder i := fun eq => h (order_injective eq)
    simp [physicalArgs,h,hne]

/-- The marked physical increment box agrees with a logical source-register
update for every fixed register and every model of PRA. -/
theorem modelSourceIncrement (r : Fin 9) (e : Fin 11 → M) (l : M) :
    let p := slot r
    let a := physicalArgs e
    let inp := inputArgs p a
    let ep := frontArgs p a (F (markedFile (8-p.val)) inp)
    let prefixCost := F (costCode p.val) ep
    let front := (((1 : M)+1)+inp 0)+F (costCode (8-p.val)) (fun i => inp i.succ)
    let incrementCost := ((front+TableDispatch.modelNumeral M 6)+F (costCode (8-p.val)) (fun i => inp i.succ))+((inp 0+1)+1+1)
    let changed := Function.update (Function.update (Function.update e (logicalIndex r) (inp 0+1)) 9 1) 10 0
    let out := F sourceFileCode changed
    F PA194Stepper.stepper ![(prefixCost+incrementCost)+prefixCost,
      F pairCode ![TableDispatch.modelNumeral M 2,F pairCode ![l,F (fileCode p.val) ep]]] =
    F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(out+out)]] := by
  let p := slot r
  let a := physicalArgs e
  let inp := inputArgs p a
  let mark := F (markedFile (8-p.val)) inp
  let ep := frontArgs p a mark
  have hp : ep (Fin.last p.val) = F (markedFile (8-p.val)) inp := by simp [ep,frontArgs,mark]
  have h := modelIncrementAnywhere p.val (8-p.val) ep inp l hp (inputLast p a)
  have hout := outputFile p a (inp 0+1) mark
  have heq : physicalArgs (Function.update (Function.update (Function.update e (logicalIndex r) (inp 0+1)) 9 1) 10 0) =
      Function.update (Function.update (Function.update a ⟨p.val,by have := p.isLt; omega⟩ (inp 0+1)) 9 1) 10 0 := by
    change physicalArgs (Function.update _ (inputOrder 10) 0) = _
    rw [physicalUpdate]
    change Function.update (physicalArgs (Function.update _ (inputOrder 9) 1)) 10 0 = _
    rw [physicalUpdate,update_commutes]
    rfl
  rw [←heq,←modelSourceFile] at hout
  dsimp only at h ⊢
  rw [hout] at h
  exact h
#print axioms outputFile
#print axioms modelSourceIncrement
end models
end PA194IncrementSource
