import DiophantineConsistency.AdaptiveAQ16Positive
import DiophantineConsistency.AdaptiveAQ17Zeros
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ16Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveAQ16Positive
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def project (v : Fin 17 → V) : Fin 16 → V :=
  ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 16]

def positivePart (p : Fin 4 → ℕ) (v : Fin 16 → V) : V :=
  let q := 1+v 0*(p 0:V)
  let U := v 7*(q*q)
  let E := v 6*v 7
  let a := E+v 7
  let k := v 9+v 10
  let c := v 9+v 7*k
  let H := 3+4*a
  U*(v 6+a*c)+H*(U*v 12+E*q+v 13+1)

def negativePart (_p : Fin 4 → ℕ) (v : Fin 16 → V) : V :=
  let a := v 6*v 7+v 7
  (3+4*a)*(v 9+v 10)

def extend (p : Fin 4 → ℕ) (v : Fin 16 → V) : Fin 17 → V :=
  ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,
    positivePart p v-negativePart p v,v 15]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem project_pos (v : Fin 17 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < project v i := by
  intro i
  fin_cases i <;> exact hv _

theorem parts_pos (p : Fin 4 → ℕ) (hp : 2 ≤ p 0) (v : Fin 16 → V)
    (hv : ∀ i, 0 < v i) : negativePart p v < positivePart p v := by
  have hU := scale_at_least_eight (v 0) (v 7) (p 0) (hv 0) (hv 7) hp
  have hk : 0 < v 9+v 10 := lt_of_lt_of_le (hv 9) (le_add_of_nonneg_right (Arithmetic.zero_le _))
  simpa [positivePart,negativePart] using
    (positive_part_dominates (v 7*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))) (v 6) (v 7)
      (v 9+v 10) (v 9) (v 12) (1+v 0*(p 0:V)) (v 13) hU (hv 7) hk)

theorem extend_pos (p : Fin 4 → ℕ) (hp : 2 ≤ p 0) (v : Fin 16 → V)
    (hv : ∀ i, 0 < v i) : ∀ i, 0 < extend p v i := by
  have hd : 0 < positivePart p v-negativePart p v := tsub_pos_iff_lt.mpr (parts_pos p hp v hv)
  intro i
  fin_cases i <;> dsimp [extend] <;> first | exact hv _ | exact hd
#print axioms project_pos
#print axioms parts_pos
#print axioms extend_pos
end DiophantineConsistency.AdaptiveAQ16Maps
