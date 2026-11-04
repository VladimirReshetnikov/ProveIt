import DiophantineConsistency.Compact44.CompactSameWitnessSaturation2
import DiophantineConsistency.Compact44.CompactPositionIncrement
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactPositionCarry
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits CompactSymbolicPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem generic_position_noCarry (B K L H : ℕ) (v : Fin 12 → V)
    (hB : (B:V)+1=Exp.exp ((67:V)*8807)) (hL : L=lowNat) (hH : H=highNat)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports B K L H j:ℤ))) v) :
    let p := ports B K L H
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      v 5=q*w ∧ (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧ dig 67 C 0=1 ∧
      (∀ k<8807*N, 0<k → NoCarry (dig 67 C k) (dig 67 (L:V) (k%8807))) ∧
      NoCarry (v 1) ((H:V)*v 0-1) := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hcongr,h0,hlim,hlow,hhigh⟩ :=
    CompactSameWitnessSaturation.generic_graph_saturation B K L H v hB hL hH hv hz
  let p := ports B K L H
  let q : V := 1+v 0*(p 0:V)
  let C : V := q-v 1-v 2
  have hC : 1≤C := by
    have h := mod_le C (Exp.exp (67:V))
    rw [←dig_zero_index 67 C,h0] at h
    exact h
  have hmask : (L:V)<Exp.exp (67*8807) := by rw [hL]; exact CompactConcreteMask.model_lt
  have hmask0 : dig 67 (L:V) 0=Exp.exp 67-2 := by rw [hL]; exact CompactConcreteMask.model_origin
  have hn : NoCarry (C-1) ((L:V)*rep (67*8807) N+1) := by
    change NoCarry (C-1) ((L:V)*v 0+1) at hlow
    simpa only [hJ] using hlow
  have hextract := increment_digits 8807 N C (L:V) (by norm_num) hN hmask hmask0 hC hn
  exact ⟨N,w,hN,hq,hJ,hv5,hcongr,h0,hextract.2,hhigh⟩

theorem fixed_position_noCarry (K : ℕ) (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat K lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat K lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      v 5=q*w ∧ (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧ dig 67 C 0=1 ∧
      (∀ k<8807*N, 0<k → NoCarry (dig 67 C k) (dig 67 (lowNat:V) (k%8807))) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) := by
  exact generic_position_noCarry CompactFixedBeta.betaNat K lowNat highNat v CompactFixedBeta.beta_identity rfl rfl hv hz
end CompactPositionCarry
#print axioms CompactPositionCarry.generic_position_noCarry
#print axioms CompactPositionCarry.fixed_position_noCarry
