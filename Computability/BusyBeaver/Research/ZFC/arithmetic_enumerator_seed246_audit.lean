import BusyBeaver.ZFC.ArithmeticEnumeratorSeed246

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticEnumeratorStep254 ArithmeticEnumeratorRun254
open ArithmeticCommandStep254 ArithmeticRefutationWord254
open ArithmeticStackCertificate254 ArithmeticEnumeratorSeed246

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSeed246.reach_from
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSeed246.halts_of_word_from
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSeed246.refutationWord_raw_bound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSeed246.halts_of_accepted_from_three
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSeed246.certified_seed_work
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSeed246.seed_projections
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSeed246.accepted_iff_seed_halts
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSeed246.equivalenceSentence_true
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSeed246.isigma1_proves_equivalence
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSeed246.peano_proves_equivalence

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (base offset initialWork : V) : ∃ time,
    run time (liveValue 0 base initialWork) = 0 ∨
    ∃ w, run time (liveValue 0 base initialWork) = liveValue 0 (base+offset) w :=
  reach_from base offset initialWork
example (base word initialWork : V) (hp : word ≠ 0) (hb : base ≤ word-1)
    (hall : ∀ w, ArithmeticCommandRun254.evalValue word w = 0) :
    ∃ time, run time (liveValue 0 base initialWork) = 0 :=
  halts_of_word_from base word initialWork hp hb hall
example (code : V) : 3 ≤ refutationWord code-1 := refutationWord_raw_bound code
example (code initialWork : V) (hv : ArithmeticHistory254.value code = 2) :
    ∃ time, run time (liveValue 0 3 initialWork) = 0 :=
  halts_of_accepted_from_three code initialWork hv
example (d : V) : CertifiedWorking (stateValue 0 0 d 0) := certified_seed_work d
example : pointer (seedValue (V := V)) = 0 ∧ candidate (seedValue (V := V)) = 3 ∧
    working (seedValue (V := V)) = stateValue 0 0 3 0 := seed_projections
example : (∃ code : V, ArithmeticHistory254.value code = 2) ↔
    (∃ time : V, run time (seedValue (V := V)) = 0) := accepted_iff_seed_halts
example (time : V) (ht : run time (liveValue 0 3 (stateValue 0 0 3 0)) = 0) :
    ∃ code : V, ArithmeticHistory254.value code = 2 :=
  accepted_iff_seed_halts.mpr ⟨time, ht⟩
example : equivalenceSentence.Evalb (M := V) ![] := equivalenceSentence_true
example : 𝗜𝚺₁ ⊢ equivalenceSentence := isigma1_proves_equivalence
example : Peano ⊢ equivalenceSentence := peano_proves_equivalence
