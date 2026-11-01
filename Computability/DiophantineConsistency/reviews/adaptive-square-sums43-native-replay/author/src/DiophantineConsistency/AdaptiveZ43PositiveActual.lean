import DiophantineConsistency.AdaptiveZ43Facts
import DiophantineConsistency.AdaptiveZ43Inequality
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveZ43PositiveActual
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveZ44Context AdaptiveZ43Facts AdaptiveZ43Inequality
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem signed_d_positive (p : Fin 4 → ℕ) (v : Fin 44 → V)
    (hb : (2:V) ≤ (p 0:V)) (hv : ∀ i,0<v i)
    (hz : InternalZero (literal (fun j => (p j:ℤ))) v) : v 25 < v 24 := by
  obtain ⟨hq2,hphi,hO,hP,hroot⟩ := facts p v hz
  have hJ : (1:V) ≤ v 0 := pos_iff_one_le.mp (hv 0)
  have hY : (1:V) ≤ v 7 := pos_iff_one_le.mp (hv 7)
  have hA : (1:V) ≤ v 30+v 7 := pos_iff_one_le.mp (add_pos (hv 30) (hv 7))
  have hk : 0 < v 9+v 10 := add_pos (hv 9) (hv 10)
  have hmul : (2:V) ≤ v 0*(p 0:V) := calc
    _ = (1:V)*2 := by simp
    _ ≤ v 0*(p 0:V) := mul_le_mul hJ hb (by simp) (by simp)
  have hq : (3:V) ≤ 1+v 0*(p 0:V) := by
    have hh := add_le_add_left hmul (1:V)
    norm_num at hh ⊢
    simpa only [add_comm] using hh
  have hc : v 7*(v 9+v 10) ≤ v 9+v 38 := by rw [hO]; simp
  have hphi' : v 15 = v 7*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))) := by rw [hphi,hq2]
  have hbound := main_positive_bound (1+v 0*(p 0:V)) (v 7) (v 30+v 7) (v 9+v 38) (v 9+v 10) (v 15) hq hY hA hk hphi' hc
  have hPbound : (3+4*(v 30+v 7))*(v 9+v 10) < v 15*v 39 := by
    apply lt_of_lt_of_le hbound
    rw [hP]
    have hp : (v 30+v 7)*(v 9+v 38) ≤ v 6+(v 30+v 7)*(v 9+v 38) := by simp
    exact mul_le_mul_of_nonneg_left hp (Arithmetic.zero_le _)
  by_contra hn
  have hle : v 24 ≤ v 25 := le_of_not_gt hn
  have hlt : v 24+(3+4*(v 30+v 7))*(v 9+v 10) < v 25+v 15*v 39 :=
    add_lt_add_of_le_of_lt hle hPbound
  have hle' : v 25+v 15*v 39 ≤ v 25+v 15*v 39+(3+4*(v 30+v 7))*(v 40+v 20+v 16+1) := by simp
  have hbad := lt_of_lt_of_le hlt hle'
  rw [hroot] at hbad
  exact (_root_.lt_irrefl _) hbad
#print axioms signed_d_positive
end DiophantineConsistency.AdaptiveZ43PositiveActual
