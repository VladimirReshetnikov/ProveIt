import PA194ModelAXConsAlgebra
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelAXConsExecute
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194ModelCantorWalker PA194ModelMPTransfer PA194MachineProjections
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

theorem execute (base : Nat) (rows : PA194ModelAXCons.Rows base) (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    ReachesPositive (sourceState base a tail)
      (sourceState (base+27)
        (Function.update (Function.update (Function.update (Function.update a
          1 (modelNumeral M 4 * cantor (F fixedFirst ![a 2]) (a 1)))
          2 (F fixedSecond ![a 2])) 6 0) 7 0) tail) := by
  have h := PA194ModelAXCons.cons base rows a tail
  dsimp only at h
  have hz : cantor (0 : M) 0 = 0 := by simp [cantor,triangle]
  rw [hx,hy,hz,zero_add] at h
  rw [PA194ModelAXConsAlgebra.output] at h
  exact h

#print axioms execute
end models
end PA194ModelAXConsExecute
