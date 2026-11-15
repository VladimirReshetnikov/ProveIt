import PA194CarryFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194CarryOneAppendZero
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

theorem oneThenZero (base a tail : M) :
    let v1 : Fin 2 → M := ![a,tail]
    let v2 : Fin 3 → M := ![a,0,tail]
    let carried := F (leftCode 1) (Fin.cases base v1)
    F (leftCode 2) (Fin.cases base v2) = (carried+carried+1)+(carried+carried+1) := by
  dsimp only
  let x := F ones ![a,(base+base+1)+(base+base+1)]
  have h1 : F (leftCode 1) (Fin.cases base (![a,tail] : Fin 2 → M)) = x := by
    dsimp only [x]
    simp only [modelLeftSucc,modelLeftZero,modelAdvance]
    rfl
  have h2 : F (leftCode 2) (Fin.cases base (![a,0,tail] : Fin 3 → M)) =
      F ones ![(0 : M),(x+x+1)+(x+x+1)] := by
    dsimp only [x]
    simp only [modelLeftSucc,modelLeftZero,modelAdvance]
    rfl
  rw [h1,h2,modelOnesZero]
#print axioms oneThenZero
end models
end PA194CarryOneAppendZero
