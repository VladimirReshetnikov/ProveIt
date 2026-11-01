import DiophantineConsistency.ArithmeticAdaptiveOrientedWitness2011
import DiophantineConsistency.AdaptiveDirectOrdinate86SignedV
import DiophantineConsistency.ArithmeticAdaptiveTransport2011
/-! The constructed halting witness has a strictly positive signed auxiliary expression. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptivePositiveAuxPair2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
  ArithmeticAdaptiveConstructionWitness2011 ArithmeticAdaptiveScaledNorms2011
  ArithmeticCarrierRadix2011 AdaptiveDirectOrdinate86SignedV AdaptiveDirectOrdinate86AuxNorm
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem pair_positive (p : Pair V) (L M : V) (h : Equivalent p (L,M))
    (hpos : M<L) : p.2<p.1 := by
  apply (add_lt_add_iff_right M).mp
  calc p.2+M < p.2+L := by simpa only [add_comm] using add_lt_add_left hpos p.2
    _ = p.1+M := h.symm

theorem witness_pair_positive (v : Fin 14 → V) (r aux gamma : V)
    (hf : v 1≤q v)
    (hs : let Y := v 7*(q v)^3
      let c := (v 10+v 11)*Y+v 10
      v 4*v 4*rank v+c < v 4*v 4*c*v 6) :
    let w := witness v r aux gamma
    (pairEval (eV CurrentWindowCarry2011.ports) w).2 <
      (pairEval (eV CurrentWindowCarry2011.ports) w).1 := by
  let w := witness v r aux gamma
  have hq : 1+w 0*(currentPorts 0:V)=q v := by
    change 1+v 0*(CurrentMasks2011.beta:V)=(CurrentMasks2011.beta:V)*v 0+1
    ring
  have hf' : w 1≤1+w 0*(currentPorts 0:V) := by
    rw [hq]
    exact hf
  have hr := signedV_rep currentPorts w hf'
  dsimp only at hr
  rw [hq] at hr
  have hrank : ((q v-1)*(q v-w 1)+w 2)*((q v)^2-1)+
      ((currentPorts 2:V)+q v*(currentPorts 3:V))*w 0=rank v := by
    change ((q v-1)*(q v-v 1)+v 2)*((q v)^2-1)+
      ((CurrentMasks2011.lowPort:V)+q v*((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V))*v 0=rank v
    rfl
  rw [hrank] at hr
  have hc : w 9+w 7*(w 9+w 10)=(v 10+v 11)*(v 7*(q v)^3)+v 10 := by
    change v 10+(v 7*(q v)^3)*(v 10+v 11)=_
    ring
  rw [hc] at hr
  change Equivalent (pairEval (eV (fun j => (currentPorts j:ℤ))) w)
    (v 4*v 4*v 6*((v 10+v 11)*(v 7*(q v)^3)+v 10),
      v 4*v 4*rank v+((v 10+v 11)*(v 7*(q v)^3)+v 10)) at hr
  rw [currentPorts_cast] at hr
  apply pair_positive _ _ _ hr
  dsimp only at hs
  calc v 4*v 4*rank v+((v 10+v 11)*(v 7*(q v)^3)+v 10)
      < v 4*v 4*((v 10+v 11)*(v 7*(q v)^3)+v 10)*v 6 := hs
    _ = _ := by ring
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticCantor (first)

theorem oriented_pair_witness_of_run (T : V)
    (hT : first (ArithmeticMachineRun215.run T)=0) :
    ∃ w : Fin 13 → V, (∀ j, 0<w j) ∧ InternalZero expression w ∧
      (pairEval (eV CurrentWindowCarry2011.ports) w).2 <
        (pairEval (eV CurrentWindowCarry2011.ports) w).1 := by
  obtain ⟨v,r,aux,gamma,hpos,hzero,hstrict⟩ :=
    ArithmeticAdaptiveOrientedWitness2011.oriented_witness_of_run T hT
  let w := witness v r aux gamma
  have hg := ArithmeticAdaptiveTransport2011.current_transport_positive w hpos hzero
  have hgap : w 1+w 2<1+w 0*(currentPorts 0:V) := tsub_pos_iff_lt.mp hg.2
  have hf' : w 1≤1+w 0*(currentPorts 0:V) :=
    le_trans (by simp : w 1≤w 1+w 2) (le_of_lt hgap)
  have hf : v 1≤q v := by
    change v 1≤1+v 0*(CurrentMasks2011.beta:V) at hf'
    change v 1≤(CurrentMasks2011.beta:V)*v 0+1
    simpa only [mul_comm,add_comm] using hf'
  exact ⟨w,hpos,hzero,witness_pair_positive v r aux gamma hf hstrict⟩

end DiophantineConsistency.ArithmeticAdaptivePositiveAuxPair2011
