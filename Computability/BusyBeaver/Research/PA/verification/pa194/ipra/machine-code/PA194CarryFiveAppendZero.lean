import PA194CarryFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194CarryFiveAppendZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194CarryFile PA194UnaryRuns
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem fiveThenZero (base a b c d e tail : M) :
    let v5 : Fin 6 → M := ![a,b,c,d,e,tail]
    let v6 : Fin 7 → M := ![a,b,c,d,e,0,tail]
    let carried := F (leftCode 5) (Fin.cases base v5)
    F (leftCode 6) (Fin.cases base v6) = (carried+carried+1)+(carried+carried+1) := by
  dsimp only
  let x0 := base
  let x1 := F ones ![a,(x0+x0+1)+(x0+x0+1)]
  let x2 := F ones ![b,(x1+x1+1)+(x1+x1+1)]
  let x3 := F ones ![c,(x2+x2+1)+(x2+x2+1)]
  let x4 := F ones ![d,(x3+x3+1)+(x3+x3+1)]
  let x5 := F ones ![e,(x4+x4+1)+(x4+x4+1)]
  have h5 : F (leftCode 5) (Fin.cases base (![a,b,c,d,e,tail] : Fin 6 → M)) = x5 := by
    dsimp only [x5,x4,x3,x2,x1,x0]
    simp only [modelLeftSucc,modelLeftZero,modelAdvance]
    rfl
  have h6 : F (leftCode 6) (Fin.cases base (![a,b,c,d,e,0,tail] : Fin 7 → M)) =
      F ones ![(0 : M),(x5+x5+1)+(x5+x5+1)] := by
    dsimp only [x5,x4,x3,x2,x1,x0]
    simp only [modelLeftSucc,modelLeftZero,modelAdvance]
    rfl
  rw [h5,h6,modelOnesZero]
#print axioms fiveThenZero
end models
end PA194CarryFiveAppendZero
