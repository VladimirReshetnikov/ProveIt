import PA194AX11HThroughPrepValues
import PA194AX11HZeroGuard
import PA194AX11HCompareReturn
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HAXTail
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SchedulerFetchPositive PA194ModelMPPush PA194ModelMPField PA194IteratedSimulation PA194ControllerRunAdd
open PA194AX11HThroughPrep PA194AX11HThroughPrepValues PA194AX11HZeroGuard PA194TargetCantor PA194MachineProjections
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

noncomputable def compareInput (a : Fin 11 → M) : Fin 11 → M :=
  PA194PausedPrep.result (pushed (fieldArgs (pushed a))) 0 (cantor (a 1) (a 2))

/-- The revised AX fall-through returns with its exact full source file. -/
theorem ax_tail_returns (a : Fin 11 → M) (tail : M)
    (hcache : a 5 = 0) (hx : a 6 = 0) (hy : a 7 = 0) :
    ∃ n : M, F (iterate PA194AX11HSource.step) ![n,sourceState 3553 a tail] =
      sourceState 25 (PA194ModelMPCompare.values (compareInput a) 0 0) tail := by
  let r := compareInput a
  obtain ⟨m,hm⟩ := through_prep a tail hx hy
  change F (iterate PA194AX11HSource.step) ![m,sourceState 3553 a tail] = sourceState 3642 r tail at hm
  have hv := output_values a hx hy
  change r 1 = 0 ∧ r 2 = cantor (a 1) (a 2) ∧ r 3 = a 3 ∧
    r 4 = a 4 + F fixedFirst ![a 8] ∧ r 5 = a 5 ∧
    r 6 = impValue 0 (a 4 + F fixedFirst ![a 8]) ∧ r 7 = 0 ∧
    r 8 = F fixedSecond ![a 8] at hv
  obtain ⟨_,_,_,h4,h5,h6,_,_⟩ := hv
  have hzero : r 5 = r 6 → r 4 = 0 := by
    intro he
    rw [h5,hcache,h6] at he
    rw [h4]
    exact (zero_guard_iff _).mp he.symm
  have hc := PA194AX11HCompareReturn.compareAndReturn r tail hzero
  obtain ⟨n,hn⟩ := hc
  refine ⟨m+n,?_⟩
  rw [iterateAdd,hm,hn]

#print axioms ax_tail_returns
end models
end PA194AX11HAXTail
