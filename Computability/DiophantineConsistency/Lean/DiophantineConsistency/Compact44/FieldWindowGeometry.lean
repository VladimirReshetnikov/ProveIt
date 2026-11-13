import DiophantineConsistency.Compact44.FixedGraphUniformDecoder
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FieldWindowGeometry
open CompactConcreteMask

def phase (t e : ℕ) : ℕ := (t+8807-e%8807)%8807
def absent (j : ℕ) : Prop := j ∉ support ∧ j≠1063

theorem vertical_selectors (u j : ℕ) (hu : u<9) (hj : j<943) :
    absent (phase (1013+u) (4393-j)) ∧ absent (phase (1013+u) (5495-j)) := by
  simp only [absent,phase,support,Finset.mem_sdiff,Finset.mem_union,Finset.mem_range,
    Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem horizontal_selectors (u j : ℕ) (hu : u<8) (hj : j<943) :
    absent (phase (1065+u) (4393-j)) ∧ absent (phase (1065+u) (5495-j)) := by
  simp only [absent,phase,support,Finset.mem_sdiff,Finset.mem_union,Finset.mem_range,
    Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem vertical_bare (u : ℕ) (hu : u<9) (j : Fin 5) (hj : j≠⟨0,by decide⟩) :
    absent (phase (1013+u) (![30,62,1100,2201,8849] j)) := by
  fin_cases j <;> simp_all [absent,phase,support,Finset.mem_sdiff,Finset.mem_union,Finset.mem_range,
    Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton] <;> omega

theorem horizontal_bare (u : ℕ) (hu : u<8) (j : Fin 5)
    (h1 : j≠⟨1,by decide⟩) (h4 : j≠⟨4,by decide⟩) :
    absent (phase (1065+u) (![30,62,1100,2201,8849] j)) := by
  fin_cases j <;> simp_all [absent,phase,support,Finset.mem_sdiff,Finset.mem_union,Finset.mem_range,
    Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton] <;> omega

theorem horizontal_temporal (u : ℕ) (hu : u<8) : absent (1065+u) := by
  simp only [absent,support,Finset.mem_sdiff,Finset.mem_union,Finset.mem_range,
    Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton]
  omega
#print axioms FieldWindowGeometry.vertical_selectors
#print axioms FieldWindowGeometry.horizontal_selectors
#print axioms FieldWindowGeometry.vertical_bare
#print axioms FieldWindowGeometry.horizontal_bare
#print axioms FieldWindowGeometry.horizontal_temporal
end FieldWindowGeometry
