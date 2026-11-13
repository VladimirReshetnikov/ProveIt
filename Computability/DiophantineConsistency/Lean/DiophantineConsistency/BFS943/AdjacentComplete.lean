import DiophantineConsistency.BFS943.AdjacentStep

/-! An internal least-number descent for the rational adjacent-Pell norm. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositiveAdjacentComplete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticGcdNormalization
open TenPositiveAdjacentStep
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A reduced positive rational solution of the adjacent-Pell norm has
unit denominator in every IΣ₁ model. The norm is cross-multiplied. -/
theorem denominator_one (B m v r : V) (hB : 0<B) (hm : 0<m) (hv : 0<v)
    (hu : Bez r m 1) (h : (1+B)*((m*v)*(m*v))=m*m+B*(r*r)) : m=1 := by
  let P : V → Prop := fun w => 0<w ∧ ∃ s : V, Bez s m 1 ∧
    (1+B)*((m*w)*(m*w))=m*m+B*(s*s)
  have hP : 𝚺₁-Predicate P := by dsimp [P,Bez]; definability
  have hex : P v := ⟨hv,r,hu,h⟩
  obtain ⟨w,⟨hwpos,s,hsbez,hsnorm⟩,hmin⟩ := InductionOnHierarchy.least_number 𝚺 1 hP hex
  have hwone : w=1 := by
    by_contra hn
    have hbig : 1<w := lt_of_le_of_ne (pos_iff_one_le.mp hwpos) (Ne.symm hn)
    obtain ⟨w',s',hwpos',hwlt,hsbez',hsnorm'⟩ := adjacent_step B m w s hB hm hbig hsbez hsnorm
    exact hmin w' hwlt ⟨hwpos',s',hsbez',hsnorm'⟩
  rw [hwone] at hsnorm
  simp only [mul_one] at hsnorm
  have hmul : B*(m*m)=B*(s*s) := by
    apply add_left_cancel (a:=m*m)
    calc
      m*m+B*(m*m)=(1+B)*(m*m) := by ring
      _=m*m+B*(s*s) := hsnorm
  have hsquare : m*m=s*s := mul_left_cancel₀ (ne_of_gt hB) hmul
  have hms : m=s := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hslt : m*m<s*s := mul_self_lt_mul_self (by simp) hlt
      rw [hsquare] at hslt
      exact (_root_.lt_irrefl _) hslt
    · have hslt : s*s<m*m := mul_self_lt_mul_self (by simp) hlt
      rw [hsquare] at hslt
      exact (_root_.lt_irrefl _) hslt
  have hmdiv : m∣(1:V) := bez_divisor hsbez (by simp [hms]) (dvd_refl m)
  exact le_antisymm (le_of_dvd (by simp : (0:V)<1) hmdiv) (pos_iff_one_le.mp hm)

#print axioms TenPositiveAdjacentComplete.denominator_one
end TenPositiveAdjacentComplete
