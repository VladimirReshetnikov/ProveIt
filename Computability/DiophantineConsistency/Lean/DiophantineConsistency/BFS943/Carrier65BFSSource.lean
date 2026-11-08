import DiophantineConsistency.BFS943.FixedSourceHalt
import DiophantineConsistency.BFS943.Trace75FixedBounds
import DiophantineConsistency.ArithmeticCarrierSoundness2011
import DiophantineConsistency.ArithmeticPellPowerRecovery
import DiophantineConsistency.ArithmeticHalfBinomial
import DiophantineConsistency.ArithmeticRadixAlignment

/-! # A positive Carrier65 zero is a `FixedSource`

The Carrier65 polynomial `ObjectCurrentEquation2011.expressionAt` has fourteen
positive unknowns `J, F, α, z, f, i, T, s, w, n, η, ζ, y, γ`. At ports with
`31 ≤ β`, `MC < β`, `MF < 2β` and `β + 1 = 2^d` (`d ≥ 2`), the five additive
equations of a positive zero (`ArithmeticCarrierSoundness2011.Equations`, from
the port-generic `expressionAt_equations`) give the four fields of
`BFS943FixedSource.FixedSource` at the source coordinates
`sourceVal u = ![J, F, α, 1, 1, w, 1, 1, 1, 1]`:

* `power`: `w q = 2^R` (`ArithmeticPellPowerRecovery.maintained_power`);
* `mask`: `F + α < q` (`ArithmeticPellFirstIndex.scalar_window`);
* `transport`: `(K0 + w) C = F + h (z - 1)`, from the transport unit;
* `population`: `q = 2^ℓ` (`ArithmeticRadixAlignment.factor_alignment`) and
  `3 ℓ + 2 ≤ population R`, by the port-generic half-binomial lemmas
  (the body of `Bm2963HalfBinomial.population_of_equations`, restated over
  arbitrary ports).

At the direct-BFS943 ports, `FixedSourceHalt.source_halts` then gives halting
(`zero_halts`). The coordinates `f, i, T, n, η, ζ, y, γ, s` do not enter the
source. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Carrier65BFSSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticBinaryPopulation
  ArithmeticHalfBinomial ArithmeticRadixAlignment
open ArithmeticCarrierSoundness2011 (Equations)
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat
  lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The source coordinates of a Carrier65 zero: `J, F, α` and the transport base `w`. -/
def sourceVal (u : Fin 14 → V) : Fin 10 → V := ![u 0,u 1,u 2,1,1,u 8,1,1,1,1]

theorem source_pos (u : Fin 14 → V) (hu : ∀ j, 0<u j) : ∀ j, 0<sourceVal u j := by
  intro j
  fin_cases j <;> simp [sourceVal,hu]

/-- The five equations of a positive Carrier65 solution give the source fields. -/
theorem source_of_equations (p : Fin 4 → ℕ) (u : Fin 14 → V) (d : V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hu : ∀ j, 0<u j) (he : Equations (p 0:V) (p 1:V) (p 2:V) (p 3:V) u)
    (hd : 2≤d) (hbeta : (p 0:V)+1=Exp.exp d) :
    BFS943FixedSource.FixedSource p (sourceVal u) := by
  have hb0 : (0:V)<(p 0:V) := lt_of_lt_of_le (by norm_num) hb31
  have hb15 : (15:V)≤(p 0:V) := le_trans (by norm_num) hb31
  obtain ⟨ht,hn,hm,hf,hU⟩ := he
  let b : V := (p 0:V)*u 0
  let q : V := b+1
  let X : V := u 8*q
  let Y : V := u 7*q^3
  let R : V := ((q-1)*(q-u 1)+u 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*u 0
  obtain ⟨hX,-,-⟩ := ArithmeticPellPowerRecovery.maintained_power (p 0:V) (p 1:V) (p 2:V)
    (p 3:V) (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) (u 6) (u 7) (u 8) (u 9) (u 10) (u 11)
    (u 12) (u 13) hb15 hl hh (hu 0) (hu 1) (hu 2) (hu 3) (hu 4) (hu 5) (hu 6) (hu 7)
    (hu 8) (hu 9) (hu 10) (hu 11) (hu 12) (hu 13) ht hn hm hf hU
  change X=Exp.exp R at hX
  change ((p 1:V)+u 8)*q+q=((p 1:V)+u 8)*(u 1+u 2)+u 1+u 3*(q-1)+1 at ht
  obtain ⟨hgap,-,-⟩ := ArithmeticPellFirstIndex.scalar_window q (p 0:V) (p 1:V) (p 2:V)
    (p 3:V) (u 0) (u 1) (u 2) (u 3) (u 8) (u 7) hb0 (hu 0) (hu 1) (hu 2) (hu 3) (hu 8)
    (hu 7) hl hh rfl ht
  have hqb : q-1=b := add_tsub_cancel_right b 1
  have hmask : u 1+u 2<q := by
    have h := tsub_pos_iff_lt.mp (by simpa only [tsub_tsub] using hgap)
    exact h
  have hrank : Trace75Rank.rankNat p (sourceVal u)=R := by
    change (b*(q-u 1)+u 2)*(q*q-1)+((p 2:V)+q*(p 3:V))*u 0=R
    dsimp only [R]
    rw [hqb,pow_two]
  refine ⟨?_,?_,?_,?_⟩
  · rw [hrank]
    change u 8*q=Exp.exp R
    exact hX
  · exact hmask
  · -- `(K0 + w) C + q = F + z b + 1`, so `(K0 + w) C = F + (z - 1) b`
    refine ⟨u 3-1,?_⟩
    change ((p 1:V)+u 8)*(q-u 1-u 2)=u 1+b*(u 3-1)
    let C : V := q-u 1-u 2
    have hC : C+(u 1+u 2)=q := by
      dsimp only [C]
      rw [tsub_tsub]
      exact tsub_add_cancel_of_le (le_of_lt hmask)
    have hz : u 3-1+1=u 3 := tsub_add_cancel_of_le (pos_iff_one_le.mp (hu 3))
    rw [hqb] at ht
    apply add_right_cancel (b:=((p 1:V)+u 8)*(u 1+u 2)+q)
    calc
      ((p 1:V)+u 8)*C+(((p 1:V)+u 8)*(u 1+u 2)+q)=((p 1:V)+u 8)*(C+(u 1+u 2))+q := by ring
      _=((p 1:V)+u 8)*q+q := by rw [hC]
      _=((p 1:V)+u 8)*(u 1+u 2)+u 1+u 3*b+1 := ht
      _=((p 1:V)+u 8)*(u 1+u 2)+u 1+(u 3-1+1)*b+1 := by rw [hz]
      _=u 1+b*(u 3-1)+(((p 1:V)+u 8)*(u 1+u 2)+(b+1)) := by ring
  · -- the radix `q = 2^(d N)` and the half-binomial population bound
    rw [hrank]
    have hpred : Exp.exp d-1=(p 0:V) := by rw [←hbeta]; simp
    have he' : Exp.exp R=u 8*((Exp.exp d-1)*u 0+1) := by
      rw [hpred,←hX]
    obtain ⟨_,N,_hN,hqN,_,_⟩ := factor_alignment d (u 0) R (u 8) hd (hu 0) he'
    have hq : q=Exp.exp (d*N) := by rw [←hqN,hpred]
    refine ⟨d*N,hq,?_⟩
    obtain ⟨nn,_,hn5,_,hnR,_,hk,_,hc,_,_,_,_⟩ :=
      ArithmeticPellFirstIndex.maintained_first_indices (p 0:V) (p 1:V) (p 2:V) (p 3:V)
        (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) (u 6) (u 7) (u 8) (u 9) (u 10) (u 11) (u 12) (u 13)
        hb0 hl hh (hu 0) (hu 1) (hu 2) (hu 3) (hu 4) (hu 5) (hu 6) (hu 7) (hu 8) (hu 9)
        (hu 10) (hu 11) (hu 12) (hu 13) ht hn hm hf hU
    change u 10+u 11=2*ycoord nn (2*(X*Y*Y-1)+1) at hk
    change (u 10+u 11)*Y+u 10=ycoord R (X*Y+Y) at hc
    change 2*nn=R+1 at hnR
    obtain ⟨r,hrn,hr4,hR⟩ := half_index_of_ge_five nn R hn5 hnR
    have hXe : X=Exp.exp (2*r+1) := by rw [hX,hR]
    have hq1 : 1≤q := le_add_of_nonneg_left (by simp)
    have hY : 1≤Y := one_le_mul (pos_iff_one_le.mp (hu 7)) (by
      simpa only [show q^3=q*q*q by ring] using one_le_mul (one_le_mul hq1 hq1) hq1)
    have hck : ycoord (2*r+1) (Y*(X+1))=2*ycoord (r+1) (2*(X*Y*Y-1)+1)*Y+u 10 := by
      rw [show Y*(X+1)=X*Y+Y by ring,←hR,←hc,hrn,←hk]
    obtain ⟨w,hw⟩ := half_binomial X Y r (u 10) (u 11) hr4 hXe hY hck
      (by rw [hrn,←hk]) (hu 10) (hu 11)
    have hYq : Exp.exp (3*(d*N))∣Y := by
      refine ⟨u 7,?_⟩
      change u 7*q^3=_
      rw [hq,show 3*(d*N)=d*N+d*N+d*N by ring,exp_add,exp_add]
      ring
    have hq16 : (16:V)≤q := by
      change (16:V)≤(p 0:V)*u 0+1
      calc
        (16:V)=15*1+1 := by ring
        _≤(p 0:V)*u 0+1 :=
          add_le_add (mul_le_mul hb15 (pos_iff_one_le.mp (hu 0)) (by simp) (by simp)) le_rfl
    have h3 : 3*(d*N)+1≤R :=
      rank_lower_of_radix q (u 1) (u 2) (u 0) (p 2:V) (p 3:V) (d*N) hq16 (hu 2) hq
    rw [hR] at h3 ⊢
    exact population_lower X Y r w (d*N) hXe hw hYq h3

/-- The literal positive Carrier65 zero at generic ports gives the source fields. -/
theorem source_of_zero (p : Fin 4 → ℕ) (u : Fin 14 → V) (d : V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hu : ∀ j, 0<u j)
    (hz : (ObjectCurrentEquation2011.expressionAt (fun j => (p j:ℤ))).splitNatural.1.evalSemiring u=
      (ObjectCurrentEquation2011.expressionAt (fun j => (p j:ℤ))).splitNatural.2.evalSemiring u)
    (hd : 2≤d) (hbeta : (p 0:V)+1=Exp.exp d) :
    BFS943FixedSource.FixedSource p (sourceVal u) := by
  have hb0 : (0:V)<(p 0:V) := lt_of_lt_of_le (by norm_num) hb31
  exact source_of_equations p u d hb31 hl hh hu
    (ArithmeticCarrierSoundness2011.expressionAt_equations p u hb0 hl hh hu hz) hd hbeta

/-- At the direct-BFS943 ports, a solution of the five equations makes machine 215 halt. -/
theorem equations_halt (p : Fin 4 → ℕ) (u : Fin 14 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hu : ∀ j, 0<u j)
    (he : Equations (p 0:V) (p 1:V) (p 2:V) (p 3:V) u) :
    ∃ t : V, ArithmeticCantor.first (ArithmeticMachineRun215.run t)=0 := by
  obtain ⟨h31,hl,hh⟩ := Trace75FixedBounds.fixed_bounds (V:=V) p hp0 hp2 hp3
  have hb : (p 0:V)+1=Exp.exp ((67:V)*8807) := by rw [hp0]; exact beta_identity
  exact FixedSourceHalt.source_halts p (sourceVal u) hp0 hp1 hp2 hp3 (source_pos u hu)
    (source_of_equations p u ((67:V)*8807) h31 hl hh hu he (by norm_num) hb)

/-- **Zero ⇒ halt** for Carrier65 at the direct-BFS943 ports. -/
theorem zero_halts (p : Fin 4 → ℕ) (u : Fin 14 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hu : ∀ j, 0<u j)
    (hz : (ObjectCurrentEquation2011.expressionAt (fun j => (p j:ℤ))).splitNatural.1.evalSemiring u=
      (ObjectCurrentEquation2011.expressionAt (fun j => (p j:ℤ))).splitNatural.2.evalSemiring u) :
    ∃ t : V, ArithmeticCantor.first (ArithmeticMachineRun215.run t)=0 := by
  obtain ⟨h31,hl,hh⟩ := Trace75FixedBounds.fixed_bounds (V:=V) p hp0 hp2 hp3
  have hb0 : (0:V)<(p 0:V) := lt_of_lt_of_le (by norm_num) h31
  exact equations_halt p u hp0 hp1 hp2 hp3 hu
    (ArithmeticCarrierSoundness2011.expressionAt_equations p u hb0 hl hh hu hz)

#print axioms Carrier65BFSSource.source_of_equations
#print axioms Carrier65BFSSource.source_of_zero
#print axioms Carrier65BFSSource.equations_halt
#print axioms Carrier65BFSSource.zero_halts
end Carrier65BFSSource
