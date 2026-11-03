import DiophantineConsistency.ModelDifferenceRing
import Trace74DirectFourBlock

/-! UNCHECKED DRAFT. Naturalize the four-block identity once the signed rank
has a natural representative and the individual digit bounds are supplied.
No positive graph zero, population bound, or reverse guard is inferred. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74NaturalBlock
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem cast_tsub (a b : V) (h : b≤a) :
    ι (a-b) = (ι a : DiffRing V) - ι b := by
  apply eq_sub_iff_add_eq.mpr
  rw [←map_add,tsub_add_cancel_of_le h]

/-- The natural block equation follows from a natural representative of the
signed rank, separately bounded digits, and the explicit product bounds. -/
theorem natural_block (q beta J F C MC HP R : V)
    (hq : q=beta*J+1) (hCpos : 0<C) (hC : C≤q) (hF : F<q)
    (hHP : 1≤HP*J)
    (hrank : (ι R : DiffRing V) =
      ((ι q)*((ι q)-(ι F))-(ι C))*((ι q)^2-1)+
        ((ι MC)+(ι q)*((ι beta)+(ι HP)))*(ι J)) :
    R=(C-1)+(MC*J+1)+q*(F+(HP*J-1))+
      q^2*(q-1-(C-1))+q^3*(q-1-F) := by
  have hqpos : 0<q := lt_of_lt_of_le hCpos hC
  have hq1 : 1≤q := pos_iff_one_le.mp hqpos
  have hC1 : 1≤C := pos_iff_one_le.mp hCpos
  have hCpred : C-1≤q-1 := tsub_le_tsub_right hC 1
  have hFpred : F≤q-1 := (le_tsub_iff_right hq1).mpr (lt_iff_succ_le.mp hF)
  have hqcast : (ι q : DiffRing V)=(ι beta)*(ι J)+1 := by
    rw [hq]
    simp only [map_add,map_mul,map_one]
  apply ι_injective
  rw [hrank, Trace74DirectFourBlock.rank_identity _ _ _ _ _ _ _ hqcast]
  simp only [map_add,map_mul,map_pow,map_one,
    cast_tsub C 1 hC1, cast_tsub (HP*J) 1 hHP,
    cast_tsub q 1 hq1, cast_tsub (q-1) (C-1) hCpred,
    cast_tsub (q-1) F hFpred]
  ring

#print axioms Trace74NaturalBlock.natural_block
end Trace74NaturalBlock
