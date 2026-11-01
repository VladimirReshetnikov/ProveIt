import DiophantineConsistency.AdaptiveAQ32Facts
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ32Positive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveAQ32Facts AdaptiveAQ32Bound
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem signed_d_positive (p : Fin 4 → ℕ) (v : Fin 33 → V)
    (hb : (2:V) ≤ (p 0:V)) (hv : ∀ i,0<v i)
    (hz : InternalZero (AdaptiveAQ33Literal.literal (fun j => (p j:ℤ))) v) : v 23 < v 22 := by
  obtain ⟨hq2,hphi,hc,hroot⟩ := facts p v hz
  have hJ : (1:V) ≤ v 0 := pos_iff_one_le.mp (hv 0)
  have hY : (1:V) ≤ v 7 := pos_iff_one_le.mp (hv 7)
  have hA : (1:V) ≤ v 28+v 7 := pos_iff_one_le.mp (add_pos (hv 28) (hv 7))
  have hk : 0 < v 9+v 10 := add_pos (hv 9) (hv 10)
  have hmul : (2:V) ≤ v 0*(p 0:V) := calc
    _ = (1:V)*2 := by simp
    _ ≤ v 0*(p 0:V) := mul_le_mul hJ hb (by simp) (by simp)
  have hq : (3:V) ≤ 1+v 0*(p 0:V) := by
    have hh := add_le_add_left hmul (1:V)
    norm_num at hh ⊢
    simpa only [add_comm] using hh
  have hc' : v 7*(v 9+v 10) ≤ v 16 := by rw [hc]; simp
  have hphi' : v 14 = v 7*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))) := by rw [hphi,hq2]
  have hbound := main_positive_bound (1+v 0*(p 0:V)) (v 7) (v 28+v 7) (v 16) (v 9+v 10) (v 14) hq hY hA hk hphi' hc'
  have hPbound : (3+4*(v 28+v 7))*(v 9+v 10) < v 14*(v 6+(v 28+v 7)*v 16) := by
    apply lt_of_lt_of_le hbound
    have hp : (v 28+v 7)*v 16 ≤ v 6+(v 28+v 7)*v 16 := by simp
    exact mul_le_mul_of_nonneg_left hp (Arithmetic.zero_le _)
  by_contra hn
  have hle : v 22 ≤ v 23 := le_of_not_gt hn
  have hlt : v 22+(3+4*(v 28+v 7))*(v 9+v 10) < v 23+v 14*(v 6+(v 28+v 7)*v 16) :=
    add_lt_add_of_le_of_lt hle hPbound
  have hle' : v 23+v 14*(v 6+(v 28+v 7)*v 16) ≤ v 23+v 14*(v 6+(v 28+v 7)*v 16)+(3+4*(v 28+v 7))*(v 14*v 12+v 28*(1+v 0*(p 0:V))+v 15+1) := by simp
  have hbad := lt_of_lt_of_le hlt hle'
  rw [hroot] at hbad
  exact (_root_.lt_irrefl _) hbad
#print axioms signed_d_positive
end DiophantineConsistency.AdaptiveAQ32Positive
