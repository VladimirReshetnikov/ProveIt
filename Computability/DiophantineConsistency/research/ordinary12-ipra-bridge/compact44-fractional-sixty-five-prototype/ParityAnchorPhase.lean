import DiophantineConsistency.FractionalBooleanHalf
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ParityAnchorPhase
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem mod_add_mod' {n : V} (hn : 0<n) (x y : V) : (x%n+y)%n=(x+y)%n := by
  rw [mod_add hn, mod_eq_self_of_lt (mod_lt x hn), ← mod_add hn]
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

theorem different (D : V) :
    cyc 8807 2194 D≠cyc 8807 3295 D := by
  intro heq
  have h1 := cyc_add_mod (by norm_num : (0:V)<8807) 2194 D
  have h2 := cyc_add_mod (by norm_num : (0:V)<8807) 3295 D
  rw [heq] at h1
  have he : (2194:V)%8807=(3295:V)%8807 := h1.symm.trans h2
  have hbad : (2194:V)=3295 := by
    simpa only [mod_eq_self_of_lt (by norm_num : (2194:V)<8807),
      mod_eq_self_of_lt (by norm_num : (3295:V)<8807)] using he
  norm_num at hbad

theorem choose_ordinary (N D : V) (hN : 0<N) :
    (cyc (8807*N) 2194 D)%8807≠1063 ∨ (cyc (8807*N) 3295 D)%8807≠1063 := by
  have h1 := CyclicAnyPhase.cyc_period 8807 N 2194 D (by norm_num) hN
  have h2 := CyclicAnyPhase.cyc_period 8807 N 3295 D (by norm_num) hN
  rw [mod_eq_self_of_lt (by norm_num : (2194:V)<8807)] at h1
  rw [mod_eq_self_of_lt (by norm_num : (3295:V)<8807)] at h2
  by_contra hn
  push Not at hn
  apply different D
  rw [←h1,←h2,hn.1,hn.2]
#print axioms ParityAnchorPhase.different
#print axioms ParityAnchorPhase.choose_ordinary
end ParityAnchorPhase
