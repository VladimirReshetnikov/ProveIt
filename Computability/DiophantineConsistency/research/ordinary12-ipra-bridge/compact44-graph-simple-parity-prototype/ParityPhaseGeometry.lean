import DiophantineConsistency.FixedGraphBandParity
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ParityPhaseGeometry
open CleanGeometry

def phase (t e : ℕ) : ℕ := (t+8807-e%8807)%8807

theorem selectors (j : ℕ) (hj : j<943) :
    ¬BadNat (phase 2195 (4393-j)) ∧ ¬BadNat (phase 2195 (5495-j)) ∧
    ¬BadNat (phase 3296 (4393-j)) ∧ ¬BadNat (phase 3296 (5495-j)) := by
  unfold phase BadNat
  omega

theorem bare2195 (j : Fin 5) (hj : j≠⟨2, by decide⟩) :
    ¬BadNat (phase 2195 (![30,62,1100,2201,8849] j)) := by
  fin_cases j <;> norm_num [phase,BadNat] at *

theorem bare3296 (j : Fin 5) (hj : j≠⟨3, by decide⟩) :
    ¬BadNat (phase 3296 (![30,62,1100,2201,8849] j)) := by
  fin_cases j <;> norm_num [phase,BadNat] at *
#print axioms ParityPhaseGeometry.selectors
#print axioms ParityPhaseGeometry.bare2195
#print axioms ParityPhaseGeometry.bare3296
end ParityPhaseGeometry
