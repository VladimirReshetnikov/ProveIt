import DiophantineConsistency.Mixed121.W121.TemporalSourceUnified
import DiophantineConsistency.ArithmeticModularCancellation
/-! Width-121 port of `Compact44/TemporalSourcePredecessor` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.TemporalSourcePredecessor
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem mod_add_mod' {n : V} (hn : 0<n) (x y : V) : (x%n+y)%n=(x+y)%n := by
  rw [mod_add hn,mod_eq_self_of_lt (mod_lt x hn),←mod_add hn]
private theorem cyc_add_mod {n : V} (hn : 0<n) (k e : V) : (cyc n k e+e)%n=k%n := by
  unfold cyc
  rw [mod_add_mod' hn]
  have hle : e%n≤k+n := le_trans (le_of_lt (mod_lt e hn)) le_add_self
  have he : k+n-e%n+e=(k+n)+n*(e/n) := by
    calc
      _ = k+n-e%n+(n*(e/n)+e%n) := by rw [div_add_mod]
      _ = (k+n-e%n+e%n)+n*(e/n) := by ring
      _ = _ := by rw [tsub_add_cancel_of_le hle]
  rw [he,mod_add_mul' _ _ hn,mod_add_remove_right hn]

theorem cyclic_commute (n t a b : V) (hn : 0<n) :
    cyc n (cyc n t a) b = cyc n (cyc n t b) a := by
  have hleft : (cyc n (cyc n t a) b + (a+b))%n=t%n := by
    calc
      _ = ((cyc n (cyc n t a) b+b)+a)%n := by congr 1; ring
      _ = (((cyc n (cyc n t a) b+b)%n)+a)%n := (mod_add_mod' hn _ _).symm
      _ = (cyc n t a+a)%n := by rw [cyc_add_mod hn, mod_eq_self_of_lt (cyc_lt hn _ _)]
      _ = t%n := cyc_add_mod hn _ _
  have hright : (cyc n (cyc n t b) a + (a+b))%n=t%n := by
    calc
      _ = ((cyc n (cyc n t b) a+a)+b)%n := by congr 1; ring
      _ = (((cyc n (cyc n t b) a+a)%n)+b)%n := (mod_add_mod' hn _ _).symm
      _ = (cyc n t b+b)%n := by rw [cyc_add_mod hn, mod_eq_self_of_lt (cyc_lt hn _ _)]
      _ = t%n := cyc_add_mod hn _ _
  have he := ArithmeticModularCancellation.add_cancel hn (hleft.trans hright.symm)
  simpa only [mod_eq_self_of_lt (cyc_lt hn _ _)] using he

theorem predecessor (X n E t : V) (hn : 0<n) (hX : X<Exp.exp (121*n)) :
    let q := (E/121)%n
    let r := E%121
    let j := cyc n t q
    dig 121 (rot 1 (121*n) X (E%(121*n))) (cyc n t 1) =
      (dig 121 X (cyc n j 1)*Exp.exp r)%Exp.exp 121 +
        dig 121 X (cyc n (cyc n j 1) 1)/Exp.exp (121-r) := by
  have h := W121.TemporalSourceUnified.digit X n E (cyc n t 1) hn (cyc_lt hn _ _) hX
  have hc := cyclic_commute n t 1 ((E/121)%n) hn
  simpa only [hc] using h
#print axioms W121.TemporalSourcePredecessor.cyclic_commute
#print axioms W121.TemporalSourcePredecessor.predecessor
end W121.TemporalSourcePredecessor
