import DiophantineConsistency.CompactCopySupport
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactPeriodCopy
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits CompactSymbolicPorts
open CompactSymbolicKernel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Generic model period arithmetic: no graph, digit or carry premise. -/
theorem period_index (N t j : V) (ht : t<N) (hj0 : 0<j) (hj : j<8807) :
    0<8807*t+j ∧ 8807*t+j<8807*N ∧ (8807*t+j)%8807=j := by
  refine ⟨?_,?_,?_⟩
  · exact add_pos_of_nonneg_of_pos (by simp) hj0
  · calc
      8807*t+j < 8807*t+8807 := add_lt_add_left hj _
      _ = 8807*(t+1) := by ring
      _ ≤ 8807*N := mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp ht) (by simp)
  · rw [mod_mul_add' _ _ (by norm_num : (0:V)<8807)]
    exact mod_eq_self_of_lt hj

theorem position_pos (i : Fin 41) : 0<position i := by
  have hall : slots.all (fun n => decide (0<n)) = true := by decide
  have hm : position i ∈ slots := List.get_mem slots _
  exact of_decide_eq_true ((List.all_eq_true.mp hall) _ hm)

/-- Same graph witnesses; every full period and every copy position. -/
theorem fixed_graph_period_copies (K : ℕ) (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat K lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat K lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      v 5=q*w ∧ (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧ dig 67 C 0=1 ∧
      (∀ (i : Fin 41) (t : V), t<N → dig 67 C (8807*t+(position i:V))≤1) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) := by
  obtain ⟨N,w,hN,hq,hJ,hv5,hcongr,h0,hslots,hhigh⟩ := CompactCopySupport.fixed_graph_copy_bounds K v hv hz
  refine ⟨N,w,hN,hq,hJ,hv5,hcongr,h0,?_,hhigh⟩
  intro i t ht
  have hp : 0 < (position i:V) := by exact_mod_cast position_pos i
  have hn : position i < 8807 := lt_trans (position_lt_target i) (by norm_num)
  have hj : (position i:V) < 8807 := by exact_mod_cast hn
  obtain ⟨hk0,hk,hmod⟩ := period_index N t (position i:V) ht hp hj
  exact hslots i _ hk hk0 hmod
end CompactPeriodCopy
#print axioms CompactPeriodCopy.period_index
#print axioms CompactPeriodCopy.position_pos
#print axioms CompactPeriodCopy.fixed_graph_period_copies
