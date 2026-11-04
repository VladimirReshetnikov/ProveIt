import Trace74FCResidue

/-! UNCHECKED DRAFT. Transfer signed q² congruence to model remainders. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74FCModelRemainder
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74FCResidue
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem mod_eq_of_signed_dvd (x y d : V) (hd : 0<d)
    (h : (ι d:DiffRing V)∣ι x-ι y) : x%d=y%d := by
  obtain ⟨z,hz⟩ := h
  rcases nonneg_or_nonpos z with ⟨t,ht⟩ | ⟨t,ht⟩
  · rw [ht] at hz
    have hxyR : (ι x:DiffRing V)=ι (y+d*t) := by
      simp only [map_add,map_mul]
      linear_combination hz
    have hxy : x=y+d*t := ι_injective hxyR
    rw [hxy,mod_add_mul' y t hd]
  · rw [ht] at hz
    have hyxR : (ι y:DiffRing V)=ι (x+d*t) := by
      simp only [map_add,map_mul]
      linear_combination -hz
    have hyx : y=x+d*t := ι_injective hyxR
    rw [hyx,mod_add_mul' x t hd]

theorem graph_FC_model_remainder (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hq4 : 4≤q p v) :
    ∃ n : V, 3≤n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      (v 2+(p 2:V)*v 0+q p v*(v 1+(p 3:V)*v 0)+1)%(q p v)^2 =
        (2*n)%(q p v)^2 := by
  obtain ⟨n,hn,hcoord,hdiv⟩ := graph_FC_residue p v hb hv hz hq4
  refine ⟨n,hn,hcoord,?_⟩
  have hd : 0<(q p v)^2 := pow_pos (add_pos (mul_pos hb (hv 0)) (by simp)) _
  apply mod_eq_of_signed_dvd _ _ _ hd
  simp only [map_add,map_mul,map_pow,map_one,map_natCast]
  exact hdiv

#print axioms Trace74FCModelRemainder.mod_eq_of_signed_dvd
#print axioms Trace74FCModelRemainder.graph_FC_model_remainder
end Trace74FCModelRemainder
