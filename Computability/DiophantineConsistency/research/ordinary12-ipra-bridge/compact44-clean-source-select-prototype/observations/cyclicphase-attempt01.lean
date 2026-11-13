import DiophantineConsistency.CleanPhaseNeighbors
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CyclicPhaseTransport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cyc_period (m N k d : V) (hm : 0<m) (hN : 0<N) (hd : d<m) :
    cyc (m*N) k d % m = cyc m (k%m) d := by
  have hN1 : 1≤N := pos_iff_one_le.mp hN
  have hmN : m≤m*N := by
    have h := mul_le_mul_of_nonneg_left hN1 (by simp : (0:V)≤m)
    simpa only [mul_one] using h
  have hdN : d<m*N := lt_of_lt_of_le hd hmN
  have hnm : m*N=m+m*(N-1) := by
    have hN' : 1+(N-1)=N := add_tsub_cancel_of_le hN1
    conv_lhs => rw [←hN']
    ring
  have hdm : d≤k+m := le_trans (le_of_lt hd) (le_add_of_nonneg_left (by simp))
  have hdr : d≤k%m+m := le_trans (le_of_lt hd) (le_add_of_nonneg_left (by simp))
  have hmain : k+m*N-d = (k+m-d)+m*(N-1) := by
    rw [hnm, ←add_assoc]
    exact (tsub_add_eq_add_tsub hdm).symm
  have hkw : k+m=(k%m+m)+(k/m)*m := by
    calc
      _ = (m*(k/m)+k%m)+m := by rw [div_add_mod]
      _ = _ := by ring
  have hreplace : k+m-d=(k%m+m-d)+(k/m)*m := by
    rw [hkw]
    exact (tsub_add_eq_add_tsub hdr).symm
  unfold cyc
  rw [mod_eq_self_of_lt hdN, mod_eq_self_of_lt hd,
    mod_mod_of_dvd' hm (dvd_mul_right _ _), hmain]
  rw [show (k+m-d)+m*(N-1) = (k+m-d)+(N-1)*m by ring,
    mod_add_mul _ _ hm, hreplace, mod_add_mul _ _ hm]
#print axioms CyclicPhaseTransport.cyc_period
end CyclicPhaseTransport
