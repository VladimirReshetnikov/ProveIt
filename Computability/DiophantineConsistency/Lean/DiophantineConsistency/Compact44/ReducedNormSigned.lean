import DiophantineConsistency.Compact44.ReducedNormNormalization
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ReducedNormSigned
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ModelDifferenceRing
open ReducedNormNormalization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem natural_magnitude_square (x : DiffRing V) :
    ∃ a : V, (x=ι a ∨ x= -ι a) ∧ x*x=ι (a*a) := by
  rcases nonneg_or_nonpos x with ⟨a,ha⟩ | ⟨a,ha⟩
  · refine ⟨a,Or.inl ha,?_⟩
    rw [ha,map_mul]
  · refine ⟨a,Or.inr ha,?_⟩
    rw [ha,map_mul]
    ring

theorem signed_denominator_divides (r : V) (z y d : DiffRing V) (hr : 0<r) (hd : d≠0)
    (hn : (ι r+1)*z*z*d*d=ι r*y*y+d*d) : d∣y := by
  obtain ⟨v,hvs,hv2⟩ := natural_magnitude_square z
  obtain ⟨a,has,ha2⟩ := natural_magnitude_square y
  obtain ⟨b,hbs,hb2⟩ := natural_magnitude_square d
  have hbpos : 0<b := by
    by_contra h
    have hb0 : b=0 := le_antisymm (le_of_not_gt h) (Arithmetic.zero_le b)
    apply hd
    rcases hbs with hs | hs <;> simpa only [hb0,map_zero,neg_zero] using hs
  have hnat : (r+1)*(v*b)*(v*b)=r*(a*a)+b*b := by
    apply ι_injective
    simp only [map_add,map_mul,map_one]
    calc
      (ι r+1)*(ι v*ι b)*(ι v*ι b)=(ι r+1)*(ι v*ι v)*(ι b*ι b) := by ring
      _=(ι r+1)*(z*z)*(d*d) := by rw [hv2,hb2]; simp only [map_mul]
      _=(ι r+1)*z*z*d*d := by ring
      _=ι r*y*y+d*d := hn
      _=ι r*(y*y)+d*d := by ring
      _=ι r*(ι a*ι a)+ι b*ι b := by rw [ha2,hb2]; simp only [map_mul]
  obtain ⟨k,hk⟩ := denominator_divides hr hbpos hnat
  rcases hbs with hdpos | hdneg <;> rcases has with hypos | hyneg
  · refine ⟨ι k,?_⟩
    rw [hdpos,hypos,hk,map_mul]
  · refine ⟨-ι k,?_⟩
    rw [hdpos,hyneg,hk,map_mul]
    ring
  · refine ⟨-ι k,?_⟩
    rw [hdneg,hypos,hk,map_mul]
    ring
  · refine ⟨ι k,?_⟩
    rw [hdneg,hyneg,hk,map_mul]
    ring
end ReducedNormSigned
#print axioms ReducedNormSigned.natural_magnitude_square
#print axioms ReducedNormSigned.signed_denominator_divides
