import Trace74R9GraphProjection
import Trace74R9QuotientSize
import Trace74AtLeastSevenR9ModelGrowth
import Trace74Pell

/-! UNCHECKED DRAFT: same 74 zero, explicit q≥64 and first n≥7
exclude the main r=9 branch. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74AtLeastSevenR9GraphExclusion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence Trace75Factors Trace74Pell
open Trace74R9GraphProjection Trace74R9QuotientSize Trace74AtLeastSevenR9ModelGrowth
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_r9_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hqbig : (64:V)≤q p v)
    (hn : 7≤n)
    (hfirst : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hmain : c p v=ycoord 9 (A p v-1)) : False := by
  have hq64 : (64:V)≤q p v := hqbig
  have hs1 : 1≤v 6 := pos_iff_one_le.mp (hv 6)
  have hYq : (q p v)^3≤Y p v := by
    have hh := mul_le_mul_of_nonneg_left hs1 (show (0:V)≤(q p v)^3 by simp)
    simpa only [mul_one,Y,pow_succ,pow_zero,one_mul,mul_assoc] using hh
  have hbq : (ι (q p v):DiffRing V)-1=ι (b p v) := by
    simp only [q,map_add,map_one]
    ring
  have hsize := same_tuple_growth p v n hqbig hv hn hfirst hmain
  have hdiv := graph_r9_reduced p v hb hv hz hmain
  rw [←hbq] at hsize hdiv
  apply Trace74R9QuotientSize.impossible (ι (q p v)) (ι (X p v)) (ι (Y p v))
  · intro z hz'
    exact ModelDifferenceRing.one_le_of_pos (fun a ha => pos_iff_one_le.mp ha) hz'
  · simpa only [map_ofNat] using (ι_le_ι.mpr hq64)
  · simpa only [map_pow] using (ι_le_ι.mpr hYq)
  · exact hsize
  · exact hdiv

#print axioms Trace74AtLeastSevenR9GraphExclusion.graph_r9_impossible
end Trace74AtLeastSevenR9GraphExclusion
