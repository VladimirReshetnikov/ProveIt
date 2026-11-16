import PA194Site31IncrementReturn
import PA194Site31ReturnHeader
import PA194Path32Header
import PA194Site31ReturnPrefix
import PA194Site31Selected
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site31AfterSelectedTo32
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ZeroRuns PA194BinaryDouble PA194RegisterPermutation PA194RegisterFile PA194MarkedFile PA194CarryFile PA194UnaryRuns PA194OnesCommute PA194RightRows PA194StateOne PA194ReturnFile
open BinaryTapeCodes TableDispatch PA194OneSpareReturn
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- From the site-31 third-pass layout, traverse the six-register prefix,
increment logical register zero, and return to the prefix boundary. -/
theorem afterSelectedTo32 (k count : M) (args : Fin 11 → M)
    (he : physicalArgs args 10 = F repeatOutput ![count,(0 : M)]) :
    let v := physicalArgs args
    let h0 := (1 : M)+(1 : M)+1
    let h1 := h0+h0
    let h2 := h1+h1
    let h3 := h2+h2
    let h4 := h3+h3+1
    let h5 := h4+h4+1
    let h6 := h5+h5
    let h7 := h6+h6
    let e : Fin 5 → M := fun i => v ⟨i.val+6,by omega⟩
    let marked := F (markedFile 3) e
    let ep : Fin 7 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,marked]
    let file := F (fileCode 6) ep
    let pl := F (PA194PrefixFile.leftCode 6) (Fin.cases (F ones ![k+1,h7+h7]) ep)
    let c := F (costCode 3) (fun i => e i.succ)
    let front := (((1 : M)+1)+e 0)+c
    let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
    let tail := F repeatOutput ![count,six]
    let rest := F (returnCode 3) (Fin.cases tail (fun i => e i.succ))
    let result := F block ![e 0+1,rest]
    let out := F (returnCode 6) (Fin.cases result ep)
    let a := F ones ![k,(1 : M)+out+out]
    let z := F zeros ![k,(1 : M)+out+out]
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let outer : M → M := fun x =>
      F PA194Stepper.stepper ![modelNumeral M 3+rc,
        F PA194Stepper.stepper ![(1 : M),
          F PA194Stepper.stepper ![(1 : M),
            F PA194Stepper.stepper ![((1 : M)+k)+modelNumeral M 3,
              F PA194Stepper.stepper ![((modelNumeral M 2+1)+k)+1,
                F PA194Stepper.stepper ![modelNumeral M 2,x]]]]]]
    outer (
    F PA194Stepper.stepper ![(k+1)+1,
      F PA194Stepper.stepper ![F (costCode 6) ep,
    F PA194Stepper.stepper ![((e 0+1)+1+1),
      F PA194Stepper.stepper ![c,
        F PA194Stepper.stepper ![(count+count)+count,
          F PA194Stepper.stepper ![modelNumeral M 2,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![(count+count)+count,
                F PA194Stepper.stepper ![(1 : M),
                  F PA194Stepper.stepper ![front,
                    F PA194Stepper.stepper ![F (costCode 6) ep,
                      F PA194Stepper.stepper ![k+1,F pairCode ![modelNumeral M 2,
                        F pairCode ![h7+h7,F ones ![k,file+file+1]]]]]]]]]]]]]]]) =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),
      PA194Path27Header.modelWord (PA194SourceProgram.path 32) (z+z)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  dsimp only
  let v := physicalArgs args
  let e : Fin 5 → M := fun i => v ⟨i.val+6,by omega⟩
  let marked := F (markedFile 3) e
  let ep : Fin 7 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,marked]
  let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
  let tail := F repeatOutput ![count,six]
  let rest := F (returnCode 3) (Fin.cases tail (fun i => e i.succ))
  let result := F block ![e 0+1,rest]
  let out := F (returnCode 6) (Fin.cases result ep)
  let h0 := (1 : M)+(1 : M)+1
  let h1 := h0+h0
  let h2 := h1+h1
  let h3 := h2+h2
  let h4 := h3+h3+1
  let h5 := h4+h4+1
  let h6 := h5+h5
  let h7 := h6+h6
  let q := F (returnCode 5) (Fin.cases result (fun i => ep i.succ))
  let p := F ones ![ep 0,q+q+1]
  let z := F zeros ![k,(1 : M)+out+out]
  have hout : out=p+p := by
    dsimp only [out,p,q]
    rw [modelReturnCodeSucc]
    rfl
  have hi := PA194Site31IncrementReturn.incrementReturn k h7 count args he
  dsimp only at hi
  rw [(modelDouble h6).1,(modelDouble h6).2,zero_add] at hi
  change _ = F pairCode ![modelNumeral M 7,F pairCode ![h6,
    (F ones ![k,(1 : M)+out+out]+F ones ![k,(1 : M)+out+out])+
    (F ones ![k,(1 : M)+out+out]+F ones ![k,(1 : M)+out+out])]] at hi
  rw [hout] at hi
  have hh := PA194Site31ReturnHeader.headerTo24 k p
  dsimp only at hh
  have hw := PA194Path32Header.path32Word z
  dsimp only at hw
  have hz : z = F zeros ![k,(1 : M)+(p+p)+(p+p)] := by
    dsimp only [z]
    rw [hout]
  rw [hz] at hw
  rw [←hw] at hh
  rw [hi,hh]
  change _ = F pairCode ![modelNumeral M 24,F pairCode ![(1 : M), PA194Path27Header.modelWord (PA194SourceProgram.path 32) (z+z)]]
  rw [hz]
#print axioms afterSelectedTo32
end models
end PA194Site31AfterSelectedTo32
