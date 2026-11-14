import PA194DecrementZero
import PA194MarkedFile
set_option autoImplicit false
namespace PA194DecrementZeroFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194MarkedFile PA194CarryFile PA194ReturnFile PA194DecrementZero
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelZeroDecrementFile (p n : Nat) (ep : Fin (p+1) → M) (e : Fin (n+2) → M) (l : M)
    (hp : ep (Fin.last p) = F markedBlock ![(0 : M),F (fileCode (n+1)) e]) :
    let plain := F block ![(0 : M),F (fileCode (n+1)) e]
    let cost := F (costCode p) ep
    let out := F (returnCode p) (Fin.cases plain ep)
    F PA194Stepper.stepper ![(cost+TableDispatch.modelNumeral M 7)+cost,
      F pairCode ![(1 : M),F pairCode ![l,F (fileCode p) ep]]] =
    F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+out+out]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let tail := F (fileCode n) (fun i => e i.succ)
  let t := F ones ![e 0,tail]
  let a := t+t+1
  let b := a+a
  let d := b+b
  let f := d+d
  have hn : F ones ![e 0+1,tail] = a := by
    change F ones ![F addCode ![e 0,F oneCode Fin.elim0],tail] = _
    rw [modelAddOne,modelOnesSucc]
  have hf : F (fileCode (n+1)) e = b := by
    rw [modelFileSucc,modelBlock,hn]
  have hm : F markedBlock ![(0 : M),F (fileCode (n+1)) e] = f := by
    rw [hf,modelMarkedBlock,modelOnesZero]
  have hu : F block ![(0 : M),F (fileCode (n+1)) e] = f+(1+1) := by
    rw [hf,modelBlock]
    have hone : F ones ![(0 : M)+1,b] = b+b+1 := by
      have h := modelOnesSucc (0 : M) b
      have hs : F Code.succ (fun _ => (0 : M)) = (0 : M)+1 := (modelAddOne (0 : M)).symm
      rw [hs,modelOnesZero] at h
      exact h
    rw [hone]
    dsimp [f,d]
    simp only [add_assoc,add_comm,add_left_comm]
  have hp' : ep (Fin.last p) = f := hp.trans hm
  have h := modelZeroDecrement p ep l t hp'
  dsimp only at h ⊢
  rw [hu]
  exact h
#print axioms modelZeroDecrementFile
end models
end PA194DecrementZeroFile
