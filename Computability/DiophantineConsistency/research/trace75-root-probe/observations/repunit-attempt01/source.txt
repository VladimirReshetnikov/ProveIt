import Trace75RadixAlignment
import DiophantineConsistency.ArithmeticRepunit

/-! Bind the positive graph's radix exponent to its actual repunit witness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75Repunit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticRepunit
open Trace75Factors Trace75Rank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_repunit (p : Fin 4 → ℕ) (v : Fin 10 → V) (d : V)
    (hbeta31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value75 (ports p) (fun j => ι (v j)) = 0)
    (hd : 2≤d)
    (hbeta : (p 0:V)+1=Exp.exp d) :
    ∃ N : V, 0<N ∧ v 0=rep d N ∧ q p v=Exp.exp (d*N) ∧ d*N≤rankNat p v ∧
      v 5=Exp.exp (rankNat p v-d*N) := by
  obtain ⟨N,hN,hq,hbound,hrest⟩ :=
    Trace75RadixAlignment.graph_radix_alignment p v d hbeta31 hl hh hv hz hd hbeta
  have hpred : Exp.exp d-1=(p 0:V) := by rw [←hbeta]; simp
  have hidentity : (Exp.exp d-1)*v 0+1=Exp.exp (d*N) := by
    rw [hpred]
    exact hq
  have hj : v 0=rep d N := eq_rep_of_identity (lt_of_lt_of_le (by norm_num : (0:V)<2) hd) hidentity
  exact ⟨N,hN,hj,hq,hbound,hrest⟩

#print axioms Trace75Repunit.graph_repunit
end Trace75Repunit
