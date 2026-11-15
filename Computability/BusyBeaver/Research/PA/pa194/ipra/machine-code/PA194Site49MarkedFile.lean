import PA194Site49To1
import PA194MarkedFile
import PA194ReturnFileMeaning
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site49MarkedFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194RegisterPermutation PA194RegisterFile PA194MarkedFile PA194ReturnFileMeaning PA194UnaryRuns TableDispatch PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

def selectedArgs (args : Fin 11 → M) : Fin 7 → M := fun i => physicalArgs args ⟨i.val+4,by omega⟩
noncomputable def prefixArgs (args : Fin 11 → M) : Fin 5 → M :=
  let v := physicalArgs args
  ![v 0,v 1,v 2,v 3,F (markedFile 5) (selectedArgs args)]

theorem markedInput (k : M) (args : Fin 11 → M) :
    let file := F (fileCode 4) (prefixArgs args)
    F halfCode (fun _ => PA194Site49SecondTo17.output k args) =
      F ones ![k,file+file+1] := by
  dsimp only
  let v := physicalArgs args
  let e := selectedArgs args
  let tail := F (fileCode 5) (fun i => e i.succ)
  let u := F ones ![e 0,tail]
  let r := (u+u)+(u+u)
  let w1 := F ones ![v 3,(1 : M)+r+r]
  let w2 := F ones ![v 2,(1 : M)+(w1+w1)+(w1+w1)]
  let w3 := F ones ![v 1,(1 : M)+(w2+w2)+(w2+w2)]
  let w4 := F ones ![v 0,(1 : M)+(w3+w3)+(w3+w3)]
  let t0 := F (markedFile 5) e
  let t1 := F block ![v 3,t0]
  let t2 := F block ![v 2,t1]
  let t3 := F block ![v 1,t2]
  let t4 := F block ![v 0,t3]
  have h0 : t0 = r := by dsimp only [t0,r,u,tail]; rw [modelMarkedFile,modelMarkedBlock]
  have hnext (a x y : M) (hy : y=x+x) : F block ![a,y] = F ones ![a,(1 : M)+(x+x)+(x+x)]+F ones ![a,(1 : M)+(x+x)+(x+x)] := by
    rw [hy]
    have hx : (1 : M)+(x+x)+(x+x) = (x+x)+(x+x)+1 := by ac_rfl
    rw [hx]
    exact (modelReturnBlock a (x+x)).symm
  have h1 : t1 = w1+w1 := hnext (v 3) (u+u) t0 h0
  have h2 : t2 = w2+w2 := hnext (v 2) w1 t1 h1
  have h3 : t3 = w3+w3 := hnext (v 1) w2 t2 h2
  have h4 : t4 = w4+w4 := hnext (v 0) w3 t3 h3
  have hf : F (fileCode 4) (prefixArgs args) = t4 := by
    rw [modelFileSucc,modelFileSucc,modelFileSucc,modelFileSucc]
    simp only [fileCode,modelProjection]
    rfl
  have ho : PA194Site49SecondTo17.output k args = F ones ![k+1,(1 : M)+(w4+w4)+(w4+w4)] := rfl
  have hsum : (1 : M)+(w4+w4)+(w4+w4) = (w4+w4)+(w4+w4)+1 := by ac_rfl
  rw [ho,show k+1 = F Code.succ (fun _ => k) from modelAddOne _,modelOnesSucc,(modelOdd _).2,hf,h4,←hsum]
#print axioms markedInput
end models
end PA194Site49MarkedFile
