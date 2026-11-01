import DiophantineConsistency.ArithmeticAdaptiveTransport2011
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ32Bound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem main_positive_bound (q y a c k phi : V)
    (hq : (3:V) ≤ q) (hy : (1:V) ≤ y) (ha : (1:V) ≤ a) (hk : 0 < k)
    (hphi : phi = y*(q*q)) (hc : y*k ≤ c) :
    (3+4*a)*k < phi*(a*c) := by
  have hq2 : (9:V) ≤ q*q := by
    have h := mul_le_mul hq hq (by simp : (0:V) ≤ (3:V)) (by simp : (0:V) ≤ q)
    norm_num at h ⊢
    exact h
  have hy2 : (1:V) ≤ y*y := by simpa using one_le_mul hy hy
  have hphiY : (9:V) ≤ phi*y := calc
    _ = (1:V)*9 := by simp
    _ ≤ (y*y)*(q*q) := mul_le_mul hy2 hq2 (by simp) (by simp)
    _ = phi*y := by rw [hphi]; ring
  have hfive : (5:V) ≤ 5*a := by simpa using mul_le_mul_of_nonneg_left ha (show (0:V) ≤ 5 by simp)
  have hlt : (3:V)+4*a < 9*a := calc
    _ < 5*a+4*a := by simpa only [add_comm] using add_lt_add_right (lt_of_lt_of_le (by norm_num : (3:V)<5) hfive) (4*a)
    _ = _ := by ring
  have hltK : (3+4*a)*k < (9*a)*k := mul_lt_mul_of_pos_right hlt hk
  have hle : (9*a)*k ≤ phi*(a*c) := calc
    _ ≤ ((phi*y)*a)*k := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hphiY (by simp)) (by simp)
    _ = (phi*a)*(y*k) := by ring
    _ ≤ (phi*a)*c := mul_le_mul_of_nonneg_left hc (by simp)
    _ = _ := by ring
  exact lt_of_lt_of_le hltK hle
#print axioms main_positive_bound
end DiophantineConsistency.AdaptiveAQ32Bound
