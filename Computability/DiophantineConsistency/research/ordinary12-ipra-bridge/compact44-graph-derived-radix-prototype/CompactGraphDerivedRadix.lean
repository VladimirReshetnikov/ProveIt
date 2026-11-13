import DiophantineConsistency.CompactGenericGraphDigits
import DiophantineConsistency.FreeJRadixAlignment
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactGraphDerivedRadix
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits
open CompactSymbolicPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The graph supplies the positive internal block count and repunit equation;
    model beta and symbolic-mask identities remain explicit. -/
theorem graph_digits (B K L H : ℕ) (v : Fin 12 → V)
    (hB : (B:V)+1=Exp.exp ((67:V)*8807)) (hL : L=lowNat) (hH : H=highNat)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports B K L H j:ℤ))) v) :
    ∃ N : V, 0<N ∧
      (let q : V := 1+v 0*(ports B K L H 0:V)
       let C : V := q-v 1-v 2
       q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
         dig 67 C 0=1 ∧ ∀ k < 8807*N, dig 67 C k≤3) := by
  let d : V := 67*8807
  obtain ⟨hb',hl',hh',_⟩ := CompactMaskBoundFinish.bounds (B:V) (v 0) hB (hv 0)
  have hb : 0<(ports B K L H 0:V) := by change 0<(B:V); exact hb'
  have hl : (ports B K L H 2:V)<(ports B K L H 0:V) := by
    change (L:V)<(B:V)
    rw [hL]
    exact hl'
  have hh : (ports B K L H 3:V)<2*(ports B K L H 0:V) := by
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
  have hbeta : (46:V)≤(ports B K L H 0:V) := by
    change (46:V)≤(B:V)
    apply le_iff_lt_succ.mpr
    exact lt_of_lt_of_le (by norm_num : (46:V)<64) hbig
  have hport : (ports B K L H 0:V)=Exp.exp d-1 := by
    change (B:V)=Exp.exp d-1
    rw [←hB,add_tsub_cancel_right]
  obtain ⟨N,w,hN,hq,_,_,_⟩ := FreeJRadixAlignment.graph_alignment (ports B K L H) v d
    hb hl hh hv hz hbeta (by dsimp [d]; norm_num) hport
  have hJ : v 0=rep d N := by
    apply ArithmeticRepunit.eq_rep_of_identity (by dsimp [d]; norm_num)
    calc (Exp.exp d-1)*v 0+1 = 1+v 0*(ports B K L H 0:V) := by rw [←hport]; ring
      _ = Exp.exp (d*N) := hq
  refine ⟨N,hN,hq,hJ,?_⟩
  exact CompactGenericGraphDigits.graph_digits B K L H v N hB hL hH hv hz hN hq hJ

/-- Fixed symbolic beta/masks; K is an arbitrary natural parameter. -/
theorem fixed_graph_digits (K : ℕ) (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat K lowNat highNat j:ℤ))) v) :
    ∃ N : V, 0<N ∧
      (let q : V := 1+v 0*(ports CompactFixedBeta.betaNat K lowNat highNat 0:V)
       let C : V := q-v 1-v 2
       q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
         dig 67 C 0=1 ∧ ∀ k < 8807*N, dig 67 C k≤3) := by
  exact graph_digits CompactFixedBeta.betaNat K lowNat highNat v
    CompactFixedBeta.beta_identity rfl rfl hv hz

end CompactGraphDerivedRadix
#print axioms CompactGraphDerivedRadix.graph_digits
#print axioms CompactGraphDerivedRadix.fixed_graph_digits
