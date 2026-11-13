import DiophantineConsistency.ArithmeticWindowDigits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CleanGeometry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

def BadNat (x : ℕ) : Prop := x≤1065 ∨ x=1095 ∨ x=2195 ∨ x=3296

theorem finite_disjoint (x : ℕ) (hx : x<8807) :
    ¬ (BadNat x ∧ BadNat ((x+1102)%8807)) := by
  unfold BadNat
  omega

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def Bad (x : V) : Prop := x≤1065 ∨ x=1095 ∨ x=2195 ∨ x=3296

theorem model_disjoint (x : V) (hx : x<8807) :
    ¬ (Bad x ∧ Bad ((x+1102)%8807)) := by
  unfold Bad
  omega
#print axioms CleanGeometry.finite_disjoint
#print axioms CleanGeometry.model_disjoint
end CleanGeometry
