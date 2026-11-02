import DiophantineConsistency.CompactPeriodCopy
import DiophantineConsistency.CompactSelectorPeriod
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactCommonPeriodBits
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits CompactSymbolicPorts
open CompactSymbolicKernel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- One graph-derived N,w simultaneously serves selector and copy periods. -/
theorem fixed_graph_common_period_bits (K : ℕ) (v : Fin 12 → V)
    (hv : ∀ j, 0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat K lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat K lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      v 5=q*w ∧ (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧ dig 67 C 0=1 ∧
      (∀ (i : Fin 943) (t : V), t<N → i.val≠1 → dig 67 C (8807*t+(i.val:V))≤1) ∧
      (∀ (t : V), t<N → dig 67 C (8807*t+1)=0) ∧
      (∀ (i : Fin 41) (t : V), t<N → dig 67 C (8807*t+(position i:V))≤1) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) := by
  obtain ⟨N,w,hN,hq,hJ,hv5,hcongr,h0,hslots,hhigh⟩ :=
    CompactPositionCarry.fixed_position_noCarry K v hv hz
  refine ⟨N,w,hN,hq,hJ,hv5,hcongr,h0,?_,?_,?_,hhigh⟩
  · intro i t ht hne
    have hjNat : i.val<8807 := lt_trans i.isLt (by norm_num)
    have hj : (i.val:V)<8807 := by exact_mod_cast hjNat
    obtain ⟨hk,hmod⟩ := CompactSelectorPeriod.period_index_zero_allowed N t (i.val:V) ht hj
    by_cases horigin : 8807*t+(i.val:V)=0
    · rw [horigin,h0]
    · exact CompactSelectorGraph.selector_slot N _ _ i.val i.isLt hne hk
        (pos_iff_ne_zero.mpr horigin) hmod hslots
  · intro t ht
    obtain ⟨hk,hmod⟩ := CompactSelectorPeriod.period_index_zero_allowed N t (1:V) ht (by norm_num)
    have hk0 : 0<8807*t+1 := add_pos_of_nonneg_of_pos (by simp) (by norm_num)
    exact CompactSelectorGraph.excluded_slot N _ _ hk hk0 hmod hslots
  · intro i t ht
    have hp : 0<(position i:V) := by exact_mod_cast CompactPeriodCopy.position_pos i
    have hn : position i<8807 := lt_trans (position_lt_target i) (by norm_num)
    have hj : (position i:V)<8807 := by exact_mod_cast hn
    obtain ⟨hk0,hk,hmod⟩ := CompactPeriodCopy.period_index N t (position i:V) ht hp hj
    have hg := CompactCopySupport.position_good i
    exact CompactSupportSlot.support_slot N _ _ (position i) hn hg.1 hg.2 hk hk0 hmod hslots
end CompactCommonPeriodBits
#print axioms CompactCommonPeriodBits.fixed_graph_common_period_bits
