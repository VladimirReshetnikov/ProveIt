import PA194Site29ReturnNormalized
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29ReturnFinalBlocks
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch PA194ReturnCell PA194UnaryRuns PA194BinaryDouble PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem returnOdd (n a t : M) :
    let left := a+a+1
    let right := F ones ![n,(1 : M)+(t+t)+(t+t)]
    F PA194Stepper.stepper ![(n+1)+1,F pairCode ![modelNumeral M 7,
      F pairCode ![F ones ![n,left+left],(1 : M)+(t+t)+(t+t)]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![a,(1 : M)+(right+right)+(right+right)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := modelReturnCell n (a+a+1) (t+t)
  dsimp only at h ⊢
  rw [(modelOdd a).1,(modelOdd a).2] at h
  simpa only [add_assoc,add_comm,add_left_comm] using h

theorem returnEven (n a t : M) :
    let right := F ones ![n,(1 : M)+(t+t)+(t+t)]
    F PA194Stepper.stepper ![(n+1)+1,F pairCode ![modelNumeral M 7,
      F pairCode ![F ones ![n,(a+a)+(a+a)],(1 : M)+(t+t)+(t+t)]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![a,(right+right)+(right+right)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := modelReturnCell n (a+a) (t+t)
  dsimp only at h ⊢
  rw [(modelDouble a).1,(modelDouble a).2,zero_add] at h
  simpa only [add_assoc,add_comm,add_left_comm] using h

theorem remainingReturn (n m k d t : M) :
    let a := F ones ![k,(d+d)+(d+d)]
    let a1 := a+a+1
    let z := F ones ![m,(a1+a1)+(a1+a1)+1]
    let r1 := F ones ![n,(1 : M)+(t+t)+(t+t)]
    let r2 := F ones ![m,(1 : M)+(r1+r1)+(r1+r1)]
    let r3 := F ones ![k,(1 : M)+(r2+r2)+(r2+r2)]
    F PA194Stepper.stepper ![(k+1)+1,
      F PA194Stepper.stepper ![(m+1)+1,
        F PA194Stepper.stepper ![(n+1)+1,
          F pairCode ![modelNumeral M 7,F pairCode ![F ones ![n,z+z],(1 : M)+(t+t)+(t+t)]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![d,(r3+r3)+(r3+r3)]] := by
  dsimp only
  let a := F ones ![k,(d+d)+(d+d)]
  let a1 := a+a+1
  let r1 := F ones ![n,(1 : M)+(t+t)+(t+t)]
  let r2 := F ones ![m,(1 : M)+(r1+r1)+(r1+r1)]
  have h1 := PA194Site29ReturnNormalized.returnPrevious n m a1 t
  dsimp only at h1
  have h2 := returnOdd m a r1
  dsimp only at h2
  have h3 := returnEven k d r2
  dsimp only at h3
  rw [h1,h2,h3]
#print axioms returnOdd
#print axioms returnEven
#print axioms remainingReturn
end models
end PA194Site29ReturnFinalBlocks
