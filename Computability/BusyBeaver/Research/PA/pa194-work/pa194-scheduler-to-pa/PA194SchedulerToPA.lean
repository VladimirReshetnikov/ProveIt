import PA194SchedulerIteration
import PA194TargetSource
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194SchedulerToPA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PA194TargetCantor PA194TargetGate PA194TargetSource PA194SchedulerIteration PA194SourceLineSoundness
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

theorem modeled_halt_refutes_PA
    (hgate : ∀ a b c : M, c ≠ a → c ≠ b → good (oldBundleValue a b c))
    (k : M) (hh : F haltAt ![F run ![k,F initial Fin.elim0]] = 1) :
    Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : M) :=
  target_refutes_PA hgate (initial_run_halt_provable k hh)

theorem modeled_halt_refutes_PA_of_tail
    (htail : ∀ a b c : M, c ≠ a → c ≠ b →
      good (PA194SourceGateReduction.gateNeg (separationTailValue a b c)))
    (k : M) (hh : F haltAt ![F run ![k,F initial Fin.elim0]] = 1) :
    Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : M) :=
  modeled_halt_refutes_PA (gate_from_separation_tail htail) k hh

#print axioms modeled_halt_refutes_PA_of_tail
#print axioms modeled_halt_refutes_PA
end models
end PA194SchedulerToPA
