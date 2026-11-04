import DiophantineConsistency.Compact44.ParityAdjacentPhase
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ParityPreviousPhase
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

theorem previous_ordinary (N j : V) (hN : 0<N) (hphase : j%8807≠1064) :
    (cyc (8807*N) j 1)%8807≠1063 := by
  intro hprev
  have hp := CyclicAnyPhase.cyc_period 8807 N j 1 (by norm_num) hN
  rw [hprev] at hp
  have h := cyc_add_mod (by norm_num : (0:V)<8807) (j%8807) 1
  rw [←hp] at h
  have hleft : ((1063:V)+1)%8807=1064 := by
    rw [show (1063:V)+1=1064 by norm_num,mod_eq_self_of_lt (by norm_num)]
  rw [hleft, mod_eq_self_of_lt (mod_lt _ (by norm_num : (0:V)<8807))] at h
  exact hphase h.symm
#print axioms ParityPreviousPhase.previous_ordinary
end ParityPreviousPhase
