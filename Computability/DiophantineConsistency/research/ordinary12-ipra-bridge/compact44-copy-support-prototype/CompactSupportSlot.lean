import DiophantineConsistency.CompactSelectorGraph
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSupportSlot
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits CompactSymbolicPorts
open CompactListMask
open DiophantineConsistency.ArithmeticMaskConstants
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem sub_cast (r : ℕ) (hr : r ≤ 2^67) :
    ((2^67-r : ℕ):V)=Exp.exp (67:V)-(r:V) := by
  have h1 : 2^67-r+r=2^67 := Nat.sub_add_cancel hr
  have h2 : ((2^67-r : ℕ):V)+(r:V)=((2^67:ℕ):V) := by exact_mod_cast h1
  have h3 : ((2^67:ℕ):V)=Exp.exp (67:V) := by simpa using (ArithmeticStandardCasts.cast_exp (V:=V) 67).symm
  rw [h3] at h2
  exact eq_tsub_of_add_eq h2

theorem support_mask_digit (j : ℕ) (hj : j<8807)
    (hmem : j∈CompactConcreteMask.support) (hspecial : j≠1063) :
    dig 67 (lowNat:V) (j:V)=Exp.exp 67-2 := by
  have hd := dig_ofDigits (V:=V) 67 (digits (2^67) 8807 1063 CompactConcreteMask.support)
    (digits_lt _ _ _ _ (by norm_num)) j
  rw [digits_getD _ _ _ _ hj] at hd
  simp only [digit, if_neg hspecial, if_pos hmem] at hd
  rw [sub_cast 2 (by norm_num)] at hd
  exact hd

theorem support_slot (N C k : V) (j : ℕ)
    (hj : j<8807) (hmem : j∈CompactConcreteMask.support) (hspecial : j≠1063)
    (hk : k<8807*N) (hk0 : 0<k) (hmod : k%8807=(j:V))
    (hslots : ∀ k<8807*N, 0<k → NoCarry (dig 67 C k) (dig 67 (lowNat:V) (k%8807))) :
    dig 67 C k ≤ 1 := by
  have h := hslots k hk hk0
  rw [hmod,support_mask_digit j hj hmem hspecial] at h
  exact CompactDummyBound.ordinary_le_one _ (dig_lt 67 C k) h

theorem fixed_graph_support_bounds (K : ℕ) (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat K lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat K lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      v 5=q*w ∧ (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧ dig 67 C 0=1 ∧
      (∀ (j : ℕ), j<8807 → j∈CompactConcreteMask.support → j≠1063 →
        ∀ k : V, k<8807*N → 0<k → k%8807=(j:V) → dig 67 C k≤1) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) := by
  obtain ⟨N,w,hN,hq,hJ,hv5,hcongr,h0,hslots,hhigh⟩ := CompactPositionCarry.fixed_position_noCarry K v hv hz
  refine ⟨N,w,hN,hq,hJ,hv5,hcongr,h0,?_,hhigh⟩
  intro j hj hmem hspecial k hk hk0 hm
  exact support_slot N _ k j hj hmem hspecial hk hk0 hm hslots
end CompactSupportSlot
#print axioms CompactSupportSlot.support_mask_digit
#print axioms CompactSupportSlot.support_slot
#print axioms CompactSupportSlot.fixed_graph_support_bounds
