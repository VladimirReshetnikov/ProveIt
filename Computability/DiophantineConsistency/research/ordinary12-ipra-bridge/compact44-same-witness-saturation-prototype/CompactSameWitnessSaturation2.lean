import DiophantineConsistency.FreeJGraphCongruenceExplore
import DiophantineConsistency.CompactSymbolicGraphSaturation
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSameWitnessSaturation
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits CompactSymbolicPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem generic_graph_saturation (B K L H : ℕ) (v : Fin 12 → V)
    (hB : (B:V)+1=Exp.exp ((67:V)*8807)) (hL : L=lowNat) (hH : H=highNat)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports B K L H j:ℤ))) v) :
    let p := ports B K L H
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      0<v 0*(p 0:V) ∧ v 1<v 0*(p 0:V) ∧
      (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧
      dig 67 C 0=1 ∧ (∀ k<8807*N, dig 67 C k≤3) ∧
      NoCarry (C-1) ((p 2:V)*v 0+1) ∧
      NoCarry (v 1) ((H:V)*v 0-1) := by
  let p := ports B K L H
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hcongr,h0,hlim⟩ :=
    FreeJGraphCongruenceExplore.symbolic_aligned B K L H v hB hL hH hv hz
  obtain ⟨hb',hl',hh',hHPJ⟩ := CompactMaskBoundFinish.bounds (B:V) (v 0) hB (hv 0)
  have hb : 0<(p 0:V) := by change 0<(B:V); exact hb'
  have hl : (p 2:V)<(p 0:V) := by change (L:V)<(B:V); rw [hL]; exact hl'
  have hh : (p 3:V)<2*(p 0:V) := by
    change ((B+H:ℕ):V)<2*(B:V)
    rw [Nat.cast_add,hH]
    exact hh'
  have h64 : (64:V)=Exp.exp (6:V) := by
    have h := ArithmeticStandardCasts.cast_exp (V:=V) 6
    norm_num at h
    exact h.symm
  have hbig : (64:V)≤(B:V)+1 := by
    rw [hB,h64]
    exact exp_monotone_le.mpr (by norm_num)
  have hbeta : (46:V)≤(p 0:V) := by
    change (46:V)≤(B:V)
    apply le_iff_lt_succ.mpr
    exact lt_of_lt_of_le (by norm_num : (46:V)<64) hbig
  have hlow : (p 2:V)=CompactConcreteIncrement.mask := by
    change (L:V)=CompactConcreteIncrement.mask
    rw [hL]
    rfl
  have hhigh : (H:V)=((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V) := by
    rw [hH]
    rfl
  have hport : (p 3:V)=(H:V)+(p 0:V) := by
    change ((B+H:ℕ):V)=(H:V)+(B:V)
    rw [Nat.cast_add,add_comm]
  have hs := CompactSymbolicGraphSaturation.graph_saturation p v N (H:V)
    hb hl hh hv hz hbeta hN hq hJ hlow hhigh hport (by rw [hH]; exact hHPJ)
  exact ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hcongr,h0,hlim,hs.1,hs.2⟩
theorem fixed_graph_saturation (K : ℕ) (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat K lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat K lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      0<v 0*(p 0:V) ∧ v 1<v 0*(p 0:V) ∧
      (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧
      dig 67 C 0=1 ∧ (∀ k<8807*N, dig 67 C k≤3) ∧
      NoCarry (C-1) ((p 2:V)*v 0+1) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) := by
  exact generic_graph_saturation CompactFixedBeta.betaNat K lowNat highNat v CompactFixedBeta.beta_identity rfl rfl hv hz
end CompactSameWitnessSaturation
#print axioms CompactSameWitnessSaturation.fixed_graph_saturation
#print axioms CompactSameWitnessSaturation.generic_graph_saturation
