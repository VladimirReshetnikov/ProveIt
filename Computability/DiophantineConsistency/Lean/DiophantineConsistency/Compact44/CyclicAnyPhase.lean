import DiophantineConsistency.Compact44.CyclicPhaseTransport
import DiophantineConsistency.ArithmeticModularCancellation
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CyclicAnyPhase
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem mod_add_mod' {n : V} (hn : 0<n) (x y : V) : (x%n+y)%n=(x+y)%n := by
  rw [mod_add hn, mod_eq_self_of_lt (mod_lt x hn), ← mod_add hn]

private theorem cyc_add_mod {n : V} (hn : 0<n) (k e : V) : (cyc n k e + e)%n=k%n := by
  unfold cyc
  rw [mod_add_mod' hn]
  have hle : e%n≤k+n := le_trans (le_of_lt (mod_lt e hn)) le_add_self
  have he : k+n-e%n+e=(k+n)+n*(e/n) := by
    calc
      _ = k+n-e%n+(n*(e/n)+e%n) := by rw [div_add_mod]
      _ = (k+n-e%n+e%n)+n*(e/n) := by ring
      _ = _ := by rw [tsub_add_cancel_of_le hle]
  rw [he,mod_add_mul' _ _ hn,mod_add_remove_right hn]

private theorem cyc_unique {n r k e : V} (hr : r<n) (h : (r+e)%n=k%n) : cyc n k e=r := by
  have hn : 0<n := lt_of_le_of_lt (Arithmetic.zero_le r) hr
  have he : cyc n k e % n = r % n := by
    apply ArithmeticModularCancellation.add_cancel hn
    rw [cyc_add_mod hn, h]
  simpa only [mod_eq_self_of_lt (cyc_lt hn k e),mod_eq_self_of_lt hr] using he

theorem cyc_period (m N k d : V) (hm : 0<m) (hN : 0<N) :
    cyc (m*N) k d % m = cyc m (k%m) d := by
  have hn : 0<m*N := mul_pos hm hN
  have hmod (x : V) : x%(m*N)%m=x%m := by
    have he := div_add_mod x (m*N)
    conv_rhs => rw [← he]
    rw [show (m*N)*(x/(m*N))+x%(m*N) = x%(m*N)+(N*(x/(m*N)))*m by ring,
      mod_add_mul _ _ hm]
  apply (cyc_unique (mod_lt _ hm) ?_).symm
  have he := congrArg (· % m) (cyc_add_mod hn k d)
  rw [hmod,hmod] at he
  simpa only [mod_add_mod' hm,mod_mod_self _ _ hm] using he
#print axioms CyclicAnyPhase.cyc_period
end CyclicAnyPhase
