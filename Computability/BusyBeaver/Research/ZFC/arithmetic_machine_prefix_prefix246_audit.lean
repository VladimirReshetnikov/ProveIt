import BusyBeaver.ZFC.ArithmeticMachinePrefixPrefix246
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticMachineRunFromPrefix246
open ArithmeticMachineRunPrefix246 (run)
open ArithmeticBootstrapPrefix246 (bootCode)
open ArithmeticMachinePrefixPrefix246
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePrefixPrefix246.runFrom_commute
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePrefixPrefix246.halts_after_prefix_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePrefixPrefix246.blank_after_prefix_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePrefixPrefix246.boot_halts_iff

example (t u initial : V) : runFrom t (runFrom u initial) = runFrom u (runFrom t initial) := runFrom_commute t u initial
example (prefixTime initial : V) : (∃ time : V, first (runFrom time (runFrom prefixTime initial)) = 0) ↔ (∃ time : V, first (runFrom time initial) = 0) := halts_after_prefix_iff prefixTime initial
example (prefixTime : V) : (∃ time : V, first (runFrom time (run prefixTime)) = 0) ↔ (∃ time : V, first (run time) = 0) := blank_after_prefix_iff prefixTime
example : (∃ time : V, first (runFrom time (bootCode : V)) = 0) ↔ (∃ time : V, first (run time) = 0) := boot_halts_iff
example (time : V) (hh : first (runFrom time (bootCode : V)) = 0) : ∃ time : V, first (run time) = 0 := boot_halts_iff.mp ⟨time,hh⟩
example (time : V) (hh : first (run time) = 0) : ∃ time : V, first (runFrom time (bootCode : V)) = 0 := boot_halts_iff.mpr ⟨time,hh⟩
