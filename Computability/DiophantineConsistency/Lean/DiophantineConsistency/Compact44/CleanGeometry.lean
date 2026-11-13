import DiophantineConsistency.ArithmeticStandardCasts
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

theorem bounded_standard (n : ℕ) (x : V) (hx : x<(n:V)) : ∃ j : ℕ, j<n ∧ x=(j:V) := by
  induction n with
  | zero => simp at hx
  | succ n ih =>
    have hx' : x<(n:V)+1 := by simpa only [Nat.cast_succ] using hx
    have hle : x≤(n:V) := (add_le_add_iff_right (1:V)).mp (lt_iff_succ_le.mp hx')
    rcases lt_or_eq_of_le hle with hlt | heq
    · obtain ⟨j,hj,hxj⟩ := ih hlt
      exact ⟨j,Nat.lt_succ_of_lt hj,hxj⟩
    · exact ⟨n,Nat.lt_succ_self n,heq⟩

theorem bad_cast (j : ℕ) : Bad (j:V) ↔ BadNat j := by
  unfold Bad BadNat
  exact_mod_cast (Iff.rfl : (j≤1065 ∨ j=1095 ∨ j=2195 ∨ j=3296) ↔ _)

theorem model_disjoint (x : V) (hx : x<8807) :
    ¬ (Bad x ∧ Bad ((x+1102)%8807)) := by
  obtain ⟨j,hj,rfl⟩ := bounded_standard 8807 x hx
  have hc : (((j+1102)%8807 : ℕ):V) = ((j:V)+1102)%8807 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (DiophantineConsistency.ArithmeticStandardCasts.cast_mod (V:=V) (j+1102) 8807)
  rw [← hc, bad_cast, bad_cast]
  exact finite_disjoint j hj
#print axioms CleanGeometry.finite_disjoint
#print axioms CleanGeometry.bounded_standard
#print axioms CleanGeometry.bad_cast
#print axioms CleanGeometry.model_disjoint
end CleanGeometry
