import DiophantineConsistency.Mixed121.W121.TemporalSourcePredecessor
import DiophantineConsistency.Mixed121.W121.TemporalCleanNumerics
/-! Width-121 port of `Compact44/TemporalSafeDigit` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.TemporalSafeDigit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem safe (X n E t : V) (hn : 0<n) (ht : t<n) (hX : X<Exp.exp (121*n))
    (hz : dig 121 X (cyc n t ((E/121)%n))=0)
    (h1 : dig 121 X (cyc n (cyc n t ((E/121)%n)) 1)≤1)
    (h2 : dig 121 X (cyc n (cyc n (cyc n t ((E/121)%n)) 1) 1)≤1) :
    let T := rot 1 (121*n) X (E%(121*n))
    dig 121 T t=0 ∧ dig 121 T (cyc n t 1)≤Exp.exp 120 := by
  let r := E%121
  let j := cyc n t ((E/121)%n)
  let T := rot 1 (121*n) X (E%(121*n))
  have hr : r<121 := mod_lt _ (by norm_num)
  have htarget := W121.TemporalSourceUnified.digit X n E t hn ht hX
  have hpred := W121.TemporalSourcePredecessor.predecessor X n E t hn hX
  apply W121.TemporalCleanNumerics.clean_of_formulas r (dig 121 X (cyc n j 1))
    (dig 121 X (cyc n (cyc n j 1) 1)) (dig 121 T t) (dig 121 T (cyc n t 1)) hr h1 h2
  · simpa only [hz] using htarget
  · exact hpred
#print axioms W121.TemporalSafeDigit.safe
end W121.TemporalSafeDigit
