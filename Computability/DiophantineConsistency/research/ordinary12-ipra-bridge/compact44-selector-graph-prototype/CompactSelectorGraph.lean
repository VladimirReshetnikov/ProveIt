import DiophantineConsistency.CompactSelectorMask
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSelectorGraph
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits CompactSymbolicPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem selector_slot (N C k : V) (j : ℕ)
    (hj : j<943) (hne : j≠1) (hk : k<8807*N) (hk0 : 0<k)
    (hmod : k%8807=(j:V))
    (hslots : ∀ k<8807*N, 0<k → NoCarry (dig 67 C k) (dig 67 (lowNat:V) (k%8807))) :
    dig 67 C k ≤ 1 := by
  have h := hslots k hk hk0
  rw [hmod,CompactSelectorMask.selector_mask_digit j hj hne] at h
  exact CompactDummyBound.ordinary_le_one _ (dig_lt 67 C k) h

theorem excluded_slot (N C k : V)
    (hk : k<8807*N) (hk0 : 0<k) (hmod : k%8807=(1:V))
    (hslots : ∀ k<8807*N, 0<k → NoCarry (dig 67 C k) (dig 67 (lowNat:V) (k%8807))) :
    dig 67 C k = 0 := by
  have h := hslots k hk hk0
  rw [hmod] at h
  have hmask := CompactSelectorMask.absent_mask_digit (V:=V) 1 (by norm_num)
    (by simp [CompactConcreteMask.support]) (by norm_num)
  simp only [Nat.cast_one] at hmask
  rw [hmask] at h
  exact CompactDummyBound.forbidden_zero _ (dig_lt 67 C k) h

theorem fixed_graph_selector_bounds (K : ℕ) (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat K lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat K lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      v 5=q*w ∧ (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧ dig 67 C 0=1 ∧
      (∀ (j : ℕ), j<943 → j≠1 → ∀ k : V, k<8807*N → 0<k → k%8807=(j:V) → dig 67 C k≤1) ∧
      (∀ k : V, k<8807*N → 0<k → k%8807=(1:V) → dig 67 C k=0) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) := by
  obtain ⟨N,w,hN,hq,hJ,hv5,hcongr,h0,hslots,hhigh⟩ := CompactPositionCarry.fixed_position_noCarry K v hv hz
  refine ⟨N,w,hN,hq,hJ,hv5,hcongr,h0,?_,?_,hhigh⟩
  · intro j hj hne k hk hk0 hm
    exact selector_slot N _ k j hj hne hk hk0 hm hslots
  · intro k hk hk0 hm
    exact excluded_slot N _ k hk hk0 hm hslots
end CompactSelectorGraph
#print axioms CompactSelectorGraph.selector_slot
#print axioms CompactSelectorGraph.excluded_slot
#print axioms CompactSelectorGraph.fixed_graph_selector_bounds
