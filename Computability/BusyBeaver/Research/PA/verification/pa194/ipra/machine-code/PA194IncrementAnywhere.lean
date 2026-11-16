import PA194PrefixFile
import PA194PrefixReturn
import PA194IncrementReturn
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PA194IncrementAnywhere
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194UnaryRuns PA194BinaryDouble PA194StateOne PA194CarryFile PA194ReturnFile PA194ReturnFileMeaning PA194RegisterFile PA194IncrementReturn PA194PrefixReturn
open BinaryTapeCodes
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelIncrementAnywhere (p n : Nat) (ep : Fin (p+1) → M) (e : Fin (n+2) → M) (l : M)
    (hp : ep (Fin.last p) = F (PA194MarkedFile.markedFile n) e)
    (he : e (Fin.last (n+1)) = (0 : M)) :
    let prefixCost := F (costCode p) ep
    let left := F (PA194PrefixFile.leftCode p) (Fin.cases l ep)
    let front := (((1 : M)+1)+e 0)+F (costCode n) (fun i => e i.succ)
    let incrementCost := ((front+TableDispatch.modelNumeral M 6)+F (costCode n) (fun i => e i.succ))+((e 0+1)+1+1)
    let c3 := ((1 : M)+1)+1
    let six := c3+c3
    let rest := F (fileCode n) (replaceLast n (fun i => e i.succ) six)
    let result := F block ![e 0+1,rest]
    let out := F (returnCode p) (Fin.cases result ep)
    F PA194Stepper.stepper ![(prefixCost+incrementCost)+prefixCost,
      F pairCode ![TableDispatch.modelNumeral M 2,F pairCode ![l,F (fileCode p) ep]]] =
    F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(out+out)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  change F PA194Stepper.stepper ![F addCode ![F addCode ![_,_],_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose]
  rw [PA194PrefixFile.modelPrefixFile,hp,modelFirstMarkedIncrementFile n e _ he]
  have h := modelReturnPrefixFile p ep l (F block ![e 0+1,F (fileCode n) (replaceLast n (fun i => e i.succ) (((1 : M)+1)+1+(((1 : M)+1)+1)))])
  dsimp only at h
  simpa only [add_assoc] using h
theorem modelIncrementAnywhereRaw (p n : Nat) (ep : Fin (p+1) → M) (e : Fin (n+2) → M) (l : M)
    (hp : ep (Fin.last p) = F (PA194MarkedFile.markedFile n) e)
    (he : e (Fin.last (n+1)) = (0 : M)) :
    let prefixCost := F (costCode p) ep
    let left := F (PA194PrefixFile.leftCode p) (Fin.cases l ep)
    let front := (((1 : M)+1)+e 0)+F (costCode n) (fun i => e i.succ)
    let incrementCost := ((front+TableDispatch.modelNumeral M 6)+F (costCode n) (fun i => e i.succ))+((e 0+1)+1+1)
    let c3 := ((1 : M)+1)+1
    let six := c3+c3
    let rest := F (returnCode n) (Fin.cases six (fun i => e i.succ))
    let result := F block ![e 0+1,rest]
    let out := F (returnCode p) (Fin.cases result ep)
    F PA194Stepper.stepper ![(prefixCost+incrementCost)+prefixCost,
      F pairCode ![TableDispatch.modelNumeral M 2,F pairCode ![l,F (fileCode p) ep]]] =
    F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(out+out)]] := by
  have h := modelIncrementAnywhere p n ep e l hp he
  dsimp only at h ⊢
  rw [←modelReturnMeaning] at h
  exact h
#print axioms modelIncrementAnywhere
end models
end PA194IncrementAnywhere
