import DiophantineConsistency.TemporalSourcePredecessor
import DiophantineConsistency.TemporalCleanNumerics
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TemporalSafeDigit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem safe (X n E t : V) (hn : 0<n) (ht : t<n) (hX : X<Exp.exp (67*n))
    (hz : dig 67 X (cyc n t ((E/67)%n))=0)
    (h1 : dig 67 X (cyc n (cyc n t ((E/67)%n)) 1)≤1)
    (h2 : dig 67 X (cyc n (cyc n (cyc n t ((E/67)%n)) 1) 1)≤1) :
    let T := rot 1 (67*n) X (E%(67*n))
    dig 67 T t=0 ∧ dig 67 T (cyc n t 1)≤Exp.exp 66 := by
  let r := E%67
  let j := cyc n t ((E/67)%n)
  let T := rot 1 (67*n) X (E%(67*n))
  have hr : r<67 := mod_lt _ (by norm_num)
  have htarget := TemporalSourceUnified.digit X n E t hn ht hX
  have hpred := TemporalSourcePredecessor.predecessor X n E t hn hX
  apply TemporalCleanNumerics.clean_of_formulas r (dig 67 X (cyc n j 1))
    (dig 67 X (cyc n (cyc n j 1) 1)) (dig 67 T t) (dig 67 T (cyc n t 1)) hr h1 h2
  · simpa only [hz] using htarget
  · exact hpred
#print axioms TemporalSafeDigit.safe
end TemporalSafeDigit
