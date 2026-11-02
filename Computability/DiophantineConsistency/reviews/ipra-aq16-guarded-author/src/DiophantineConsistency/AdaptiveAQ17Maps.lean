import DiophantineConsistency.AdaptiveAQ17Zeros
import DiophantineConsistency.AdaptiveAQ22Zeros
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ17Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def project (v : Fin 22 → V) : Fin 17 → V :=
  ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 15,v 18,v 19,v 20]

def extend (p : Fin 4 → ℕ) (v : Fin 17 → V) : Fin 22 → V :=
  let qm := v 0 * (p 0 : V)
  let q := 1 + qm
  let e := v 6 * v 7
  let ky := v 7 * (v 9 + v 10)
  let c := v 9 + ky
  let a := e + v 7
  ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,
    (q*(q*q))*qm, v 7*(q*q),v 13,e*ky,c*c,v 14,v 15,v 16,3+4*a+a*a]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem project_pos (v : Fin 22 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < project v i := by
  intro i
  fin_cases i <;> exact hv _

theorem extend_pos (p : Fin 4 → ℕ) (hp : 0 < p 0) (v : Fin 17 → V)
    (hv : ∀ i, 0 < v i) : ∀ i, 0 < extend p v i := by
  have hp' : 0 < (p 0 : V) := by exact_mod_cast hp
  have hm : 0 < v 0 * (p 0 : V) := mul_pos (hv 0) hp'
  have hq : 0 < 1 + v 0 * (p 0 : V) := by
    simpa only [add_comm] using (lt_of_le_of_lt (Arithmetic.zero_le (v 0 * (p 0 : V))) (lt_add_one (v 0 * (p 0 : V))))
  have he : 0 < v 6 * v 7 := mul_pos (hv 6) (hv 7)
  have hk : 0 < v 9 + v 10 := lt_of_lt_of_le (hv 9) (le_add_of_nonneg_right (Arithmetic.zero_le _))
  have hy : 0 < v 7 * (v 9 + v 10) := mul_pos (hv 7) hk
  have hc : 0 < v 9 + v 7 * (v 9 + v 10) := lt_of_lt_of_le (hv 9) (le_add_of_nonneg_right (Arithmetic.zero_le _))
  have hd : 0 < 3 + 4 * (v 6 * v 7 + v 7) + (v 6 * v 7 + v 7) * (v 6 * v 7 + v 7) := by
    have h3 : (0 : V) < 3 := by norm_num
    exact lt_of_lt_of_le h3 (le_trans (le_add_of_nonneg_right (Arithmetic.zero_le _)) (le_add_of_nonneg_right (Arithmetic.zero_le _)))
  intro i
  fin_cases i <;> dsimp [extend] <;> first | exact hv _ | exact mul_pos (mul_pos hq (mul_pos hq hq)) hm | exact mul_pos (hv 7) (mul_pos hq hq) | exact mul_pos he hy | exact mul_pos hc hc | exact hd
#print axioms project_pos
#print axioms extend_pos
end DiophantineConsistency.AdaptiveAQ17Maps
