import DiophantineConsistency.BFS943.Trace87Source
import DiophantineConsistency.BFS943.Trace87ShiftIntegral
import DiophantineConsistency.BFS943.Trace87ShiftSandwich

/-! # A shifted 87 zero is a `FixedSource`

`Trace87Source.source_of_zero` under `Trace87ShiftTransport.ShiftZero p v ws`:
the same source coordinates `Trace87Source.sourceVal p v =
![J, F, α, 1, 1, w, 1, 1, 1, 1]` and the same proof, reading `X = 2^R`, the
mask, the transport, `q³ ∣ s` and both sandwiches from the `Trace87Shift*`
copies. None of `i, T, n, η, ζ`, nor the shift `ws`, enters the source. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace87ShiftSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace87
open ArithmeticPow ArithmeticBinaryPopulation ArithmeticRadixAlignment
open Trace87Source (sourceVal source_X source_rank source_q source_b)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {ws : DiffRing V}

theorem source_of_zero (p : Fin 4 → ℕ) (v : Fin 10 → V) (d : V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : Trace87ShiftTransport.ShiftZero p v ws)
    (hd : 2≤d) (hbeta : (p 0:V)+1=Exp.exp d) :
    BFS943FixedSource.FixedSource p (sourceVal p v) := by
  obtain ⟨hpow,hmask,⟨t,ht⟩,⟨s',_hs',hs⟩⟩ :=
    Trace87ShiftIntegral.graph_source_parts p v hb31 hl hh hv hz
  refine ⟨?_,?_,?_,?_⟩
  · rw [source_X,source_rank]; exact hpow
  · rw [source_q]; exact hmask
  · refine ⟨t,?_⟩
    rw [source_b]
    change ((p 1:V)+v 5)*
      (Trace87Factors.q p v-v 1-v 2)=v 1+Trace87Factors.b p v*t
    exact ht
  · rw [source_q,source_rank]
    -- `q = 2^ℓ`
    have hpred : Exp.exp d-1=(p 0:V) := by rw [←hbeta]; simp
    have he : Exp.exp (Trace87NormRank.rankNat p v)=
        v 5*((Exp.exp d-1)*v 0+1) := by
      rw [hpred,←hpow]
      change Trace87Factors.q p v*v 5=v 5*Trace87Factors.q p v
      ring
    obtain ⟨_,N,_hN,hqN,_,_⟩ := factor_alignment d (v 0) (Trace87NormRank.rankNat p v)
      (v 5) hd (hv 0) he
    have hq : Trace87Factors.q p v=Exp.exp (d*N) := by
      rw [←hqN,hpred]; rfl
    refine ⟨d*N,hq,?_⟩
    -- the half-binomial population bound
    obtain ⟨r,hr,hR,hX,hlow,hup⟩ := Trace87ShiftSandwich.graph_sandwich_both p v hb31 hl hh hv hz
    obtain ⟨z,hbin⟩ := ScaledPellRounding.extract (Trace87Factors.X p v) (v 6) r (v 8) (v 9)
      (Trace87Factors.k v) (Trace87Factors.c p v) hr hX rfl rfl (hv 8) (hv 9) hlow hup
    have hdvd : Exp.exp (3*(d*N))∣v 6 := by
      refine ⟨s',?_⟩
      rw [hs,hq,show 3*(d*N)=(d*N)+(d*N)+(d*N) by ring,exp_add,exp_add]
    have hzn := (Trace87ShiftProjection.zero_norm_data p v hb31 hv hz)
    have hrank := (Trace87NormRank.graph_rank_exact p v _ hb31 hl hh hv hzn.1 hzn.2.1).2.1
    have hlt : d*N<Trace87Factors.q p v := by rw [hq]; exact lt_exp (d*N)
    have h3 : 3*(d*N)<2*r+1 := by
      rw [←hR]
      calc
        3*(d*N)<3*Trace87Factors.q p v := mul_lt_mul_of_pos_left hlt (by norm_num)
        _<Trace87NormRank.rankNat p v := hrank
    have hpop := ArithmeticHalfBinomial.population_lower (Trace87Factors.X p v) (v 6) r z (d*N)
      hX hbin hdvd (lt_iff_succ_le.mp h3)
    rw [hR]
    exact hpop

/-- At the direct-BFS943 ports, a shifted 87 zero is a `FixedSource`. -/
theorem source_of_fixed_zero (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=CompactFixedBeta.betaNat) (hp2 : p 2=CompactSymbolicPorts.lowNat)
    (hp3 : p 3=CompactFixedBeta.betaNat+CompactSymbolicPorts.highNat)
    (hv : ∀j,0<v j) (hz : Trace87ShiftTransport.ShiftZero p v ws) :
    BFS943FixedSource.FixedSource p (sourceVal p v) := by
  obtain ⟨h31,hl,hh⟩ := Trace75FixedBounds.fixed_bounds (V:=V) p hp0 hp2 hp3
  have hb : (p 0:V)+1=Exp.exp ((67:V)*8807) := by rw [hp0]; exact CompactFixedBeta.beta_identity
  exact source_of_zero p v ((67:V)*8807) h31 hl hh hv hz (by norm_num) hb

#print axioms Trace87ShiftSource.source_of_zero
#print axioms Trace87ShiftSource.source_of_fixed_zero
end Trace87ShiftSource
