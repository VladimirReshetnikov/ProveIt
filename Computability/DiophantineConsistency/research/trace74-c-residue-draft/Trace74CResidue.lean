import Trace74SignedRankCongruence
import Trace74RankBinding
import Trace74FirstIndexThree

/-! UNCHECKED DRAFT. A same-witness C residue forced by the 74 graph zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74Representatives Trace74SignedRankCongruence
open Trace74RankBinding Trace74FirstIndexThree
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem rank_mod_q {R : Type*} [CommRing R] (q F C MC MF J : R) :
    q ∣ ((q*(q-F)-C)*(q^2-1)+(MC+q*MF)*J)-(C+MC*J) := by
  refine ⟨(q-F)*(q^2-1)-C*q+MF*J,?_⟩
  ring

theorem graph_C_residue (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hq4 : 4≤q p v) :
    ∃ n : V, 3≤n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      (ι (q p v):DiffRing V) ∣
        ι (v 2)+ι (p 2:V)*ι (v 0)+1-ι (2*n) := by
  let rr := regs (ports p) (masked p v)
  let qq : DiffRing V := ι (q p v)
  obtain ⟨n,hn,hcoord,hdiv⟩ := graph_signed_rank_congruence p v hb hv hz
  have hn3 : 3≤n := graph_first_index_ge_three p v n hb hv hz hq4 hcoord
  have hrank : rr.rank =
      (qq*(qq-ι (v 1))-ι (v 2))*(qq^2-1)+
        (ι (p 2:V)+qq*ι (p 3:V))*ι (v 0) := by
    have hr := ring_rank_shape (ports p) (fun j => ι (v j))
    change rr.rank = _ at hr
    dsimp [qq,q,b]
    simpa only [ports,map_add,map_mul,map_natCast,map_one] using hr
  have hshape : qq ∣ rr.rank-(ι (v 2)+ι (p 2:V)*ι (v 0)) := by
    rw [hrank]
    exact rank_mod_q qq (ι (v 1)) (ι (v 2)) (ι (p 2:V)) (ι (p 3:V)) (ι (v 0))
  have hqpow : qq∣qq^4 := ⟨qq^3,by ring⟩
  have hmain : qq∣rr.rank+1-ι (2*n) := dvd_trans hqpow hdiv
  refine ⟨n,hn3,hcoord,?_⟩
  have hsub := dvd_sub hmain hshape
  convert hsub using 1
  ring

#print axioms Trace74CResidue.rank_mod_q
#print axioms Trace74CResidue.graph_C_residue
end Trace74CResidue
