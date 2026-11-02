import DiophantineConsistency.CompactSelectorGraph
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSelectorPeriod
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits CompactSymbolicPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Unlike the positive-slot version, the generic index may be zero. -/
theorem period_index_zero_allowed (N t j : V) (ht : t<N) (hj : j<8807) :
    8807*t+j<8807*N ∧ (8807*t+j)%8807=j := by
  constructor
  · calc
      8807*t+j < 8807*t+8807 := add_lt_add_right hj _
      _ = 8807*(t+1) := by ring
      _ ≤ 8807*N := mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp ht) (by simp)
  · rw [mod_mul_add' _ _ (by norm_num : (0:V)<8807)]
    exact mod_eq_self_of_lt hj

/-- Explicit origin split: the origin is already 1, while all other indices use the slot theorem. -/
theorem fixed_graph_period_selectors (K : ℕ) (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat K lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat K lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      v 5=q*w ∧ (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧ dig 67 C 0=1 ∧
      (∀ (i : Fin 943) (t : V), t<N → i.val≠1 → dig 67 C (8807*t+(i.val:V))≤1) ∧
      (∀ (t : V), t<N → dig 67 C (8807*t+1)=0) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) := by
  obtain ⟨N,w,hN,hq,hJ,hv5,hcongr,h0,hslots,hexcluded,hhigh⟩ :=
    CompactSelectorGraph.fixed_graph_selector_bounds K v hv hz
  refine ⟨N,w,hN,hq,hJ,hv5,hcongr,h0,?_,?_,hhigh⟩
  · intro i t ht hne
    have hjNat : i.val<8807 := lt_trans i.isLt (by norm_num)
    have hj : (i.val:V)<8807 := by exact_mod_cast hjNat
    obtain ⟨hk,hmod⟩ := period_index_zero_allowed N t (i.val:V) ht hj
    by_cases horigin : 8807*t+(i.val:V)=0
    · rw [horigin,h0]
    · exact hslots i.val i.isLt hne _ hk (pos_iff_ne_zero.mpr horigin) hmod
  · intro t ht
    obtain ⟨hk,hmod⟩ := period_index_zero_allowed N t (1:V) ht (by norm_num)
    have hk0 : 0<8807*t+1 := add_pos_of_nonneg_of_pos (by simp) (by norm_num)
    exact hexcluded _ hk hk0 hmod
end CompactSelectorPeriod
#print axioms CompactSelectorPeriod.period_index_zero_allowed
#print axioms CompactSelectorPeriod.fixed_graph_period_selectors
