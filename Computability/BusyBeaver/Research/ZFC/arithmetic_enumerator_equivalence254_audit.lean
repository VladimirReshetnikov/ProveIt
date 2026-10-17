import BusyBeaver.ZFC.ArithmeticEnumeratorEquivalence254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticHistory254 ArithmeticEnumeratorStep254 ArithmeticEnumeratorRun254
open ArithmeticEnumeratorEquivalence254
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorEquivalence254.blank_live
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorEquivalence254.accepted_iff_blank_halts
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorEquivalence254.equivalenceSentence_true
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorEquivalence254.isigma1_proves_equivalence
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorEquivalence254.peano_proves_equivalence
example : liveValue (0 : V) 0 0 = 1 := blank_live
example : (∃ code : V, value code = 2) ↔ (∃ time : V, run time 1 = 0) := accepted_iff_blank_halts
example (code : V) (hv : value code = 2) : ∃ time : V, run time 1 = 0 := accepted_iff_blank_halts.mp ⟨code,hv⟩
example (time : V) (ht : run time 1 = 0) : ∃ code : V, value code = 2 := accepted_iff_blank_halts.mpr ⟨time,ht⟩
example : equivalenceSentence.Evalb (M := V) ![] := equivalenceSentence_true
example : 𝗜𝚺₁ ⊢ equivalenceSentence := isigma1_proves_equivalence
example : Peano ⊢ equivalenceSentence := peano_proves_equivalence
