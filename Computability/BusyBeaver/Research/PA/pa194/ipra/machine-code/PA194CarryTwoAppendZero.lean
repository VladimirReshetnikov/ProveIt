import PA194CarryFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194CarryTwoAppendZero
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

theorem twoThenZero (base a b tail : M) :
    let v2 : Fin 3 → M := ![a,b,tail]
    let v3 : Fin 4 → M := ![a,b,0,tail]
    let carried := F (leftCode 2) (Fin.cases base v2)
    F (leftCode 3) (Fin.cases base v3) = (carried+carried+1)+(carried+carried+1) := by
  dsimp only
  let x0 := base
  let x1 := F ones ![a,(x0+x0+1)+(x0+x0+1)]
  let x2 := F ones ![b,(x1+x1+1)+(x1+x1+1)]
  have h5 : F (leftCode 2) (Fin.cases base (![a,b,tail] : Fin 3 → M)) = x2 := by
    dsimp only [x2,x1,x0]
    simp only [modelLeftSucc,modelLeftZero,modelAdvance]
    rfl
  have h6 : F (leftCode 3) (Fin.cases base (![a,b,0,tail] : Fin 4 → M)) =
      F ones ![(0 : M),(x2+x2+1)+(x2+x2+1)] := by
    dsimp only [x2,x1,x0]
    simp only [modelLeftSucc,modelLeftZero,modelAdvance]
    rfl
  rw [h5,h6,modelOnesZero]
#print axioms twoThenZero
end models
end PA194CarryTwoAppendZero
