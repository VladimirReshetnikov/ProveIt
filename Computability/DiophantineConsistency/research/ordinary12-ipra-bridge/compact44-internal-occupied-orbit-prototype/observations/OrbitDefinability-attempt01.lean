import DiophantineConsistency.FixedGraphOccupiedOrbit
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace OrbitDefinability
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def selPos (C : V) : ℕ → V → V
  | 0, _ => 0
  | m+1, h => selPos C m h + (m:V)*dig 67 C (8807*h+(m:V))

instance selPos_definable (C : V) (m : ℕ) : 𝚺₁-Function₁ (selPos C m) := by
  induction m with
  | zero =>
    change 𝚺₁-Function₁ (fun _ : V => (0:V))
    definability
  | succ m ih =>
    change 𝚺₁-Function₁ (fun h : V => selPos C m h + (m:V)*dig 67 C (8807*h+(m:V)))
    definability

def orbit (N s t : V) : V := (t*s)%N
instance orbit_definable (N s : V) : 𝚺₁-Function₁ (orbit N s) := by
  unfold orbit
  definability

def Occupied (C N s t : V) : Prop := ∃ j<943, dig 67 C (8807*orbit N s t+j)=1
instance occupied_definable (C N s : V) : 𝚺₁-Relation (Occupied C N s) := by
  unfold Occupied orbit
  definability
#print axioms OrbitDefinability.selPos_definable
#print axioms OrbitDefinability.orbit_definable
#print axioms OrbitDefinability.occupied_definable
end OrbitDefinability
