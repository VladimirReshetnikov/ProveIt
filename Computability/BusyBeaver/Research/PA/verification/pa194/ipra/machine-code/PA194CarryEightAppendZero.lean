import PA194CarryFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194CarryEightAppendZero
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

theorem eightThenZero (base a b c d e f g h tail : M) :
    let v8 : Fin 9 → M := ![a,b,c,d,e,f,g,h,tail]
    let v9 : Fin 10 → M := ![a,b,c,d,e,f,g,h,0,tail]
    let carried := F (leftCode 8) (Fin.cases base v8)
    F (leftCode 9) (Fin.cases base v9) = (carried+carried+1)+(carried+carried+1) := by
  dsimp only
  let x0 := base
  let x1 := F ones ![a,(x0+x0+1)+(x0+x0+1)]
  let x2 := F ones ![b,(x1+x1+1)+(x1+x1+1)]
  let x3 := F ones ![c,(x2+x2+1)+(x2+x2+1)]
  let x4 := F ones ![d,(x3+x3+1)+(x3+x3+1)]
  let x5 := F ones ![e,(x4+x4+1)+(x4+x4+1)]
  let x6 := F ones ![f,(x5+x5+1)+(x5+x5+1)]
  let x7 := F ones ![g,(x6+x6+1)+(x6+x6+1)]
  let x8 := F ones ![h,(x7+x7+1)+(x7+x7+1)]
  have h8 : F (leftCode 8) (Fin.cases base (![a,b,c,d,e,f,g,h,tail] : Fin 9 → M)) = x8 := by
    dsimp only [x8,x7,x6,x5,x4,x3,x2,x1,x0]
    simp only [modelLeftSucc,modelLeftZero,modelAdvance]
    rfl
  have h9 : F (leftCode 9) (Fin.cases base (![a,b,c,d,e,f,g,h,0,tail] : Fin 10 → M)) =
      F ones ![(0 : M),(x8+x8+1)+(x8+x8+1)] := by
    dsimp only [x8,x7,x6,x5,x4,x3,x2,x1,x0]
    simp only [modelLeftSucc,modelLeftZero,modelAdvance]
    rfl
  rw [h8,h9,modelOnesZero]
#print axioms eightThenZero
end models
end PA194CarryEightAppendZero
