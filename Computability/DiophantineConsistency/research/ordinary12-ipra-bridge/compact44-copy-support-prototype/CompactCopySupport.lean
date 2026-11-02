import DiophantineConsistency.CompactSupportSlot
import DiophantineConsistency.CompactSymbolicKernel
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace CompactCopySupport
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits CompactSymbolicPorts
open CompactSymbolicKernel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem position_good (i : Fin 41) : position i ∈ CompactConcreteMask.support ∧ position i ≠ 1063 := by
  have hm : position i ∈ slots := List.get_mem slots _
  simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hm
  simp only [CompactConcreteMask.support, Finset.mem_sdiff, Finset.mem_union, Finset.mem_range,
    Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> norm_num

theorem fixed_graph_copy_bounds (K : ℕ) (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat K lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat K lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      v 5=q*w ∧ (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧ dig 67 C 0=1 ∧
      (∀ (i : Fin 41) (k : V), k<8807*N → 0<k → k%8807=(position i:V) → dig 67 C k≤1) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) := by
  obtain ⟨N,w,hN,hq,hJ,hv5,hcongr,h0,hslots,hhigh⟩ := CompactSupportSlot.fixed_graph_support_bounds K v hv hz
  refine ⟨N,w,hN,hq,hJ,hv5,hcongr,h0,?_,hhigh⟩
  intro i k hk hk0 hm
  have hgood := position_good i
  exact hslots (position i) (lt_trans (position_lt_target i) (by norm_num)) hgood.1 hgood.2 k hk hk0 hm
end CompactCopySupport
#print axioms CompactCopySupport.position_good
#print axioms CompactCopySupport.fixed_graph_copy_bounds
