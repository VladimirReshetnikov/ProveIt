import PA194SchedulerCode
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000
namespace PA194SchedulerHalt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetProofLeaf PA194MachineStack PA194MachineShiftMPCode PA194SchedulerCode
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sum_one (a b : M) (h : a+b=1) : a=1 ∨ b=1 := by
  rcases zero_or_succ a with (ha | ⟨a,ha⟩)
  · right; simpa [ha] using h
  · rcases zero_or_succ b with (hb | ⟨b,hb⟩)
    · left; simpa [hb] using h
    · have hh : (a+b+1)+1 = (0 : M)+1 := by simpa [ha,hb,add_assoc,add_comm,add_left_comm] using h
      have hx : a+b+1=0 := succ_inj hh
      exact False.elim (Arithmetic.succ_ne_zero (a+b) hx)

theorem halt_implies_provable {m : Nat} (n l t w h : Code m) (e : Fin m → M)
    (hs : SoundStore (F t e) (F w e) (F h e))
    (hh : F (halt n l t h) e = 1) : TargetProvable (1 : M) := by
  rw [halt,choose0_model] at hh
  by_cases hz : F (head n l) e = 0
  · rw [if_pos hz] at hh
    have hsum := (shiftHalt_correct t h e).mp hh
    rcases sum_one (F t e) (F h e) hsum with ht | hc
    · simpa [ht] using hs.1
    · simpa [hc] using hs.2.1
  · rw [if_neg hz, PRAMultiplication.modelZero] at hh
    exact False.elim (Arithmetic.one_ne_zero hh.symm)
#print axioms halt_implies_provable
end models
end PA194SchedulerHalt
