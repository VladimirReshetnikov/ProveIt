import Trace75GraphPower
import DiophantineConsistency.ArithmeticRadixAlignment

/-! Internal radix/block alignment from the recovered trace75 power. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75RadixAlignment
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticRadixAlignment
open Trace75Factors Trace75Rank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_radix_alignment (p : Fin 4 → ℕ) (v : Fin 10 → V) (d : V)
    (hbeta31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value75 (ports p) (fun j => ι (v j)) = 0)
    (hd : 2≤d)
    (hbeta : (p 0:V)+1=Exp.exp d) :
    ∃ N : V, 0<N ∧ q p v=Exp.exp (d*N) ∧ d*N≤rankNat p v ∧
      v 5=Exp.exp (rankNat p v-d*N) := by
  have hx := Trace75GraphPower.graph_power p v hbeta31 hl hh hv hz
  have hpred : Exp.exp d-1=(p 0:V) := by rw [←hbeta]; simp
  have he : Exp.exp (rankNat p v)=v 5*((Exp.exp d-1)*v 0+1) := by
    rw [hpred,←hx]
    rfl
  obtain ⟨_,N,hN,hq,hbound,hrest⟩ := factor_alignment d (v 0) (rankNat p v) (v 5) hd (hv 0) he
  have hqdef : q p v=(Exp.exp d-1)*v 0+1 := by rw [hpred]; rfl
  refine ⟨N,hN,?_,hbound,hrest⟩
  rw [hqdef]
  exact hq

#print axioms Trace75RadixAlignment.graph_radix_alignment
end Trace75RadixAlignment
