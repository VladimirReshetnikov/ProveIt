import DiophantineConsistency.TemporalSourceUnified
import DiophantineConsistency.ArithmeticModularCancellation
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TemporalSourcePredecessor
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

theorem predecessor (X n E t : V) (hn : 0<n) (hX : X<Exp.exp (67*n)) :
    let q := (E/67)%n
    let r := E%67
    let j := cyc n t q
    dig 67 (rot 1 (67*n) X (E%(67*n))) (cyc n t 1) =
      (dig 67 X (cyc n j 1)*Exp.exp r)%Exp.exp 67 +
        dig 67 X (cyc n (cyc n j 1) 1)/Exp.exp (67-r) := by
  have h := TemporalSourceUnified.digit X n E (cyc n t 1) hn (cyc_lt hn _ _) hX
  have hc := cyclic_commute n t 1 ((E/67)%n) hn
  simpa only [hc] using h
#print axioms TemporalSourcePredecessor.cyclic_commute
#print axioms TemporalSourcePredecessor.predecessor
end TemporalSourcePredecessor
