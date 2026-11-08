import DiophantineConsistency.BFS943.Trace104Integral
import DiophantineConsistency.BFS943.Trace104Sandwich
import DiophantineConsistency.BFS943.ScaledPellRounding
import DiophantineConsistency.BFS943.FixedSourceInterface
import DiophantineConsistency.BFS943.Trace75FixedBounds

/-! # A positive 104/174 zero is a `FixedSource`

At a positive zero `v` of `valueC`, the source coordinates are
`sourceVal p v = ![J, F, α, 1, 1, w, 1, 1, 1, 1]`: the transport base of the
constant-dilation chart is `W = w`, and `X = q w = W q`. The four fields of
`BFS943FixedSource.FixedSource`:

* `power`: `X = 2^R` (`Trace104GraphPower.graph_power`);
* `mask`, `transport`: `Trace104Integral.graph_source_parts`
  (`(K0 + w) C = F + h t`);
* `population`: with `β + 1 = 2^d`, the radix alignment gives `q = 2^ℓ`
  (`ℓ = d N`); `Trace104Integral` gives `q³ ∣ s`, so `2^{3ℓ} ∣ s`; the two
  Pell sandwiches (`Trace104Sandwich`) and `ScaledPellRounding.extract` at the
  free strip `c = k s + η` give `2 s = C(2r, r) + z X`, and
  `ArithmeticHalfBinomial.population_lower` gives `3 ℓ + 2 ≤ population R`
  (`3 ℓ < 3 q < R`).

None of the coordinates `i, T, n, η, ζ` (nor `s`) enters the source. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace104Source
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace104
open ArithmeticPow ArithmeticBinaryPopulation ArithmeticRadixAlignment
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The source coordinates of a 104 core zero: `J, F, α` and the transport base `w`. -/
def sourceVal (p : Fin 4 → ℕ) (v : Fin 10 → V) : Fin 10 → V :=
  ![v 0,v 1,v 2,1,1,v 5,1,1,1,1]

theorem source_pos (p : Fin 4 → ℕ) (v : Fin 10 → V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j) :
    ∀ j, 0<sourceVal p v j := by
  have hq : 0<Trace104Factors.q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  intro j
  fin_cases j <;> simp [sourceVal,hv]

theorem source_b (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    Trace75Factors.b p (sourceVal p v)=Trace104Factors.b p v := rfl
theorem source_q (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    Trace75Factors.q p (sourceVal p v)=Trace104Factors.q p v := rfl
theorem source_rank (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    Trace75Rank.rankNat p (sourceVal p v)=Trace104NormRank.rankNat p v := rfl
theorem source_X (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    Trace75Factors.X p (sourceVal p v)=Trace104Factors.X p v := by
  change v 5*Trace104Factors.q p v=Trace104Factors.q p v*v 5
  ring

theorem source_of_zero (p : Fin 4 → ℕ) (v : Fin 10 → V) (d : V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : valueC (Trace104Factors.ports p) (fun j => ι (v j)) = 0)
    (hHK : (regs (Trace104Factors.ports p) (fun j => ι (v j))).H∣
      (regs (Trace104Factors.ports p) (fun j => ι (v j))).K)
    (hd : 2≤d) (hbeta : (p 0:V)+1=Exp.exp d) :
    BFS943FixedSource.FixedSource p (sourceVal p v) := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  obtain ⟨hpow,hmask,⟨t,ht⟩,⟨s',_hs',hs⟩⟩ :=
    Trace104Integral.graph_source_parts p v hb31 hl hh hv hz hHK
  refine ⟨?_,?_,?_,?_⟩
  · rw [source_X,source_rank]; exact hpow
  · rw [source_q]; exact hmask
  · refine ⟨t,?_⟩
    rw [source_b]
    change ((p 1:V)+v 5)*
      (Trace104Factors.q p v-v 1-v 2)=v 1+Trace104Factors.b p v*t
    exact ht
  · rw [source_q,source_rank]
    -- `q = 2^ℓ`
    have hpred : Exp.exp d-1=(p 0:V) := by rw [←hbeta]; simp
    have he : Exp.exp (Trace104NormRank.rankNat p v)=
        v 5*((Exp.exp d-1)*v 0+1) := by
      rw [hpred,←hpow]
      change Trace104Factors.q p v*v 5=v 5*Trace104Factors.q p v
      ring
    obtain ⟨_,N,_hN,hqN,_,_⟩ := factor_alignment d (v 0) (Trace104NormRank.rankNat p v)
      (v 5) hd (hv 0) he
    have hq : Trace104Factors.q p v=Exp.exp (d*N) := by
      rw [←hqN,hpred]; rfl
    refine ⟨d*N,hq,?_⟩
    -- the half-binomial population bound
    obtain ⟨r,hr,hR,hX,hlow,hup⟩ := Trace104Sandwich.graph_sandwich_both p v hb31 hl hh hv hz hHK
    obtain ⟨z,hbin⟩ := ScaledPellRounding.extract (Trace104Factors.X p v) (v 6) r (v 8) (v 9)
      (Trace104Factors.k v) (Trace104Factors.c p v) hr hX rfl rfl (hv 8) (hv 9) hlow hup
    have hdvd : Exp.exp (3*(d*N))∣v 6 := by
      refine ⟨s',?_⟩
      rw [hs,hq,show 3*(d*N)=(d*N)+(d*N)+(d*N) by ring,exp_add,exp_add]
    have hzn := (Trace104Projection.zero_norm_data p v hb31 hv hz hHK)
    have hrank := (Trace104NormRank.graph_rank_exact p v _ hb31 hl hh hv hzn.1 hzn.2.1).2.1
    have hlt : d*N<Trace104Factors.q p v := by rw [hq]; exact lt_exp (d*N)
    have h3 : 3*(d*N)<2*r+1 := by
      rw [←hR]
      calc
        3*(d*N)<3*Trace104Factors.q p v := mul_lt_mul_of_pos_left hlt (by norm_num)
        _<Trace104NormRank.rankNat p v := hrank
    have hpop := ArithmeticHalfBinomial.population_lower (Trace104Factors.X p v) (v 6) r z (d*N)
      hX hbin hdvd (lt_iff_succ_le.mp h3)
    rw [hR]
    exact hpop

/-- At the direct-BFS943 ports, a positive 104 core zero is a `FixedSource`. -/
theorem source_of_fixed_zero (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=CompactFixedBeta.betaNat) (hp2 : p 2=CompactSymbolicPorts.lowNat)
    (hp3 : p 3=CompactFixedBeta.betaNat+CompactSymbolicPorts.highNat)
    (hv : ∀j,0<v j) (hz : valueC (Trace104Factors.ports p) (fun j => ι (v j)) = 0)
    (hHK : (regs (Trace104Factors.ports p) (fun j => ι (v j))).H∣
      (regs (Trace104Factors.ports p) (fun j => ι (v j))).K) :
    BFS943FixedSource.FixedSource p (sourceVal p v) := by
  obtain ⟨h31,hl,hh⟩ := Trace75FixedBounds.fixed_bounds (V:=V) p hp0 hp2 hp3
  have hb : (p 0:V)+1=Exp.exp ((67:V)*8807) := by rw [hp0]; exact CompactFixedBeta.beta_identity
  exact source_of_zero p v ((67:V)*8807) h31 hl hh hv hz hHK (by norm_num) hb

#print axioms Trace104Source.source_of_zero
#print axioms Trace104Source.source_of_fixed_zero
end Trace104Source
