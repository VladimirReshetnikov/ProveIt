import BusyBeaver.ZFC.ArithmeticStartupRotation240
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticMachineRunFromRotation240
open ArithmeticMachineRunRotation240 (run)
open ArithmeticBootstrapRotation240 (bootCode)
open ArithmeticStartupRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupRotation240.runFrom_commute
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupRotation240.halts_shift_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupRotation240.blank_shift_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupRotation240.blank_iff_seed_halts
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupRotation240.blankHaltingSentence_eval
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupRotation240.haltingFromSentence_eval
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupRotation240.seedHaltingSentence_eval
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupRotation240.blankSentence_iff_seedSentence
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupRotation240.seedHaltingSentence_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupRotation240.startupEquivalenceSentence_true
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupRotation240.isigma1_proves_startup_equivalence
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupRotation240.peano_proves_startup_equivalence

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (t u initial : V) :
    runFrom t (runFrom u initial) = runFrom u (runFrom t initial) :=
  runFrom_commute t u initial
example (offset initial : V) :
    (∃ t : V, first (runFrom t initial) = 0) ↔
      ∃ t : V, first (runFrom t (runFrom offset initial)) = 0 :=
  halts_shift_iff offset initial
example (offset initial t : V) (h : first (runFrom t initial) = 0) :
    ∃ u : V, first (runFrom u (runFrom offset initial)) = 0 :=
  (halts_shift_iff offset initial).mp ⟨t,h⟩
example (offset initial t : V) (h : first (runFrom t (runFrom offset initial)) = 0) :
    ∃ u : V, first (runFrom u initial) = 0 :=
  (halts_shift_iff offset initial).mpr ⟨t,h⟩
example (offset : V) :
    (∃ t : V, first (run t) = 0) ↔ ∃ t : V, first (runFrom t (run offset)) = 0 :=
  blank_shift_iff offset
example : (∃ t : V, first (run t) = 0) ↔
    ∃ t : V, first (runFrom t (bootCode : V)) = 0 := blank_iff_seed_halts
example : ArithmeticMachineRunRotation240.haltingSentence.val.Evalb (M := V) ![] ↔
    ∃ t : V, first (run t) = 0 := blankHaltingSentence_eval
example (initial : Nat) : (haltingFromSentence initial).val.Evalb (M := V) ![] ↔
    ∃ t : V, first (runFrom t (initial : V)) = 0 := haltingFromSentence_eval initial
example : seedHaltingSentence.val.Evalb (M := V) ![] ↔
    ∃ t : V, first (runFrom t (bootCode : V)) = 0 := seedHaltingSentence_eval
example : ArithmeticMachineRunRotation240.haltingSentence.val.Evalb (M := V) ![] ↔
    seedHaltingSentence.val.Evalb (M := V) ![] := blankSentence_iff_seedSentence
example : startupEquivalenceSentence.Evalb (M := V) ![] := startupEquivalenceSentence_true
end Internal

example : seedHaltingSentence.val.Evalb (M := Nat) ![] ↔
    ∃ time, (machineRotation240.run time).state = none := seedHaltingSentence_nat
example : 𝗜𝚺₁ ⊢ startupEquivalenceSentence := isigma1_proves_startup_equivalence
example : Peano ⊢ startupEquivalenceSentence := peano_proves_startup_equivalence
