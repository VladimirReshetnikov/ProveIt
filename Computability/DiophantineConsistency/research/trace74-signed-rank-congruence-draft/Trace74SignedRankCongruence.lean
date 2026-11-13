import Trace74OffsetDiv
import Trace74FirstIndexResidue

/-! UNCHECKED DRAFT. The same positive 74 zero gives a first Pell index whose
triple relation to the signed graph rank holds in the difference ring. No
natural representative or rank bound is assumed or derived. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74SignedRankCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence Trace75Factors Trace74Representatives Trace74Pell
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem signed_dvd_of_mod_eq (x y d : V) (h : x%d=y%d) :
    (ι d:DiffRing V) ∣ ι x-ι y := by
  refine ⟨ι (x/d)-ι (y/d),?_⟩
  have hx := congrArg (ι (V := V)) (div_add_mod x d)
  have hy := congrArg (ι (V := V)) (div_add_mod y d)
  simp only [map_add,map_mul] at hx hy
  rw [h] at hx
  linear_combination hy-hx

theorem graph_signed_rank_congruence (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    ∃ n : V, 0<n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      (ι (q p v):DiffRing V)^4 ∣
        (regs (ports p) (masked p v)).rank+1-ι (2*n) := by
  obtain ⟨n,hn,hcoord,hmod⟩ := Trace74FirstIndexResidue.graph_first_index_residue p v hb hv hz
  have hdiv := signed_dvd_of_mod_eq (k v) (2*n) ((q p v)^4) hmod
  rw [map_pow] at hdiv
  obtain ⟨a,ha⟩ := hdiv
  have hediv := Trace74OffsetDiv.graph_offset_divisible p v hb hv hz
  obtain ⟨b,hb'⟩ := hediv
  have hk : (regs (ports p) (masked p v)).k = ι (k v) := by
    change (regs (ports p) (fun j => ι (v j))).k=ι (k v)
    simp only [k_def,k,map_add]
  have he : (regs (ports p) (masked p v)).e =
      ι (k v)-(regs (ports p) (masked p v)).rank-1 := by
    rw [e_def,hk]
  rw [he] at hb'
  refine ⟨n,hn,hcoord,?_⟩
  refine ⟨a-b,?_⟩
  linear_combination ha-hb'

#print axioms Trace74SignedRankCongruence.signed_dvd_of_mod_eq
#print axioms Trace74SignedRankCongruence.graph_signed_rank_congruence
end Trace74SignedRankCongruence
