import DiophantineConsistency.Compact44.TemporalSafeDigit
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TemporalSafeCyclic
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

theorem cyc_nested (n k a b : V) (hn : 0<n) : cyc n (cyc n k a) b=cyc n k (a+b) := by
  have hleft : (cyc n (cyc n k a) b+(a+b))%n=k%n := by
    calc
      _ = ((cyc n (cyc n k a) b+b)+a)%n := by congr 1; ring
      _ = (((cyc n (cyc n k a) b+b)%n)+a)%n := (mod_add_mod' hn _ _).symm
      _ = (cyc n k a+a)%n := by rw [cyc_add_mod hn,mod_eq_self_of_lt (cyc_lt hn _ _)]
      _ = k%n := cyc_add_mod hn _ _
  have hright := cyc_add_mod hn k (a+b)
  have he := ArithmeticModularCancellation.add_cancel hn (hleft.trans hright.symm)
  simpa only [mod_eq_self_of_lt (cyc_lt hn _ _)] using he

theorem safe (X n E t : V) (hn : 0<n) (ht : t<n) (hX : X<Exp.exp (67*n))
    (hz : dig 67 X (cyc n t ((E/67)%n))=0)
    (h1 : dig 67 X (cyc n (cyc n t ((E/67)%n)) 1)≤1)
    (h2 : dig 67 X (cyc n (cyc n t ((E/67)%n)) 2)≤1) :
    let T := rot 1 (67*n) X (E%(67*n))
    dig 67 T t=0 ∧ dig 67 T (cyc n t 1)≤Exp.exp 66 := by
  apply TemporalSafeDigit.safe X n E t hn ht hX hz h1
  rw [cyc_nested n (cyc n t ((E/67)%n)) 1 1 hn]
  simpa only [show (1:V)+1=2 by norm_num] using h2
#print axioms TemporalSafeCyclic.cyc_nested
#print axioms TemporalSafeCyclic.safe
end TemporalSafeCyclic
