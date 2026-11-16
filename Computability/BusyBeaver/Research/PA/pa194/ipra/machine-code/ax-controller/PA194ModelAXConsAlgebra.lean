import PA194ModelAXCons
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelAXConsAlgebra
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194ModelCantorWalker PA194ModelMPTransfer
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem output (a : Fin 11 → M) (x y : M) :
    let popped := argsAt 2 a x y 0
    let restored := transferArgs popped 7 2
    let packed := PA194ModelMPPair.values restored 0 0 (cantor (restored 6) (restored 1))
    argsAfter packed 7 [1,1,1,1] (packed 7) =
      Function.update (Function.update (Function.update (Function.update a
        1 (modelNumeral M 4 * cantor x (a 1))) 2 y) 6 0) 7 0 := by
  funext i
  fin_cases i <;> simp [argsAt,write,transferArgs,PA194ModelMPPair.values,argsAfter,
    location,tally,subSelf,show modelNumeral M 0 = (0:M) from rfl]

#print axioms output
end models
end PA194ModelAXConsAlgebra
