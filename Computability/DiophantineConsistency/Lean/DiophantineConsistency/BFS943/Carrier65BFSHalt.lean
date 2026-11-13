import DiophantineConsistency.BFS943.DirectBFSHaltPellSeed
import DiophantineConsistency.BFS943.Trace75FixedBounds
import DiophantineConsistency.Compact44.CompactRankResidueJoin
import DiophantineConsistency.Compact44.CompactSymbolicBetaCast
import DiophantineConsistency.Compact44.CompactSymbolicMaskData
import DiophantineConsistency.ArithmeticConstructionAssembly
import DiophantineConsistency.ArithmeticConstructionZero
import DiophantineConsistency.ArithmeticPellAuxiliarySeed

/-! # Halting gives a positive Carrier65 zero at the direct-BFS943 ports

From an internal halting time, `DirectBFSHaltPellSeed.halt_seeds_transport`
supplies the direct-BFS943 packing with its rank, the outer Pell seed
(`ArithmeticOuterSeed.SeedRelations`), the derived multiplier
`w = 2^(R - d N)` with `q w = 2^R`, and the transport quotient `t`. In the
Carrier65 coordinates (`halt_outer`):

* `J = rep d N`, `F = Fw`, `α = alpha` of the packing, `q = 2^(d N)`
  (`d = 590069`), so `β J + 1 = q`;
* `R` is the packing rank, which is literally the Carrier65 rank formula at
  the ports `MC = low`, `MF_source = high + β`; `R ≡ 3 (mod 4)`;
* the transport unit holds with `z = t + 1`.

`halt_equations` adds the auxiliary seed
`ArithmeticPellAuxiliarySeed.auxiliary_seed` (strong index `R c`) and
assembles the five Carrier65 equations
(`ArithmeticConstructionAssembly.equations_of`); `halt_zero` turns them into a
zero of the literal split polynomial (`ArithmeticConstructionZero.equations_zero`).
`halt_outer` is stated separately because the quotient-carrier forms of
package 170 reuse the same outer data with a different strong multiplier. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Carrier65BFSHalt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow ArithmeticPacking ArithmeticRepunit
  ArithmeticPellRecurrence ArithmeticOuterSeed ArithmeticMaskPopulation
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel CompactConstructedRank
open DirectBFSConstructedWord DirectBFSFourFieldsPacking DirectBFSHaltCanonicalPacking
open ArithmeticCarrierSoundness2011 (Equations)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] DirectBFSFourFieldsPacking.kernel DirectBFSSymbolicKernel.paramKernel
  CompactSymbolicKernel.rho CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The model values of the direct-BFS943 ports. -/
structure PortValues (p : Fin 4 → ℕ) : Prop where
  p0 : (p 0:V)=Exp.exp (590069:V)-1
  p1 : (p 1:V)=(kernel:V)
  p2 : (p 2:V)=low
  p3 : (p 3:V)=high+(Exp.exp (590069:V)-1)

theorem port_values (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) : PortValues (V:=V) p := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [hp0]
    exact CompactSymbolicBetaCast.beta_model
  · unfold DirectBFSFourFieldsPacking.kernel
    exact congrArg (fun k : ℕ => (k:V)) hp1
  · rw [hp2]
    exact CompactSymbolicMaskData.low_eq
  · rw [hp3,Nat.cast_add,CompactSymbolicBetaCast.beta_model]
    have hh : (highNat:V)=high := CompactSymbolicMaskData.high_eq
    rw [hh,add_comm]

/-- **The outer data of a halting run**, in the Carrier65 coordinates. -/
theorem halt_outer (p : Fin 4 → ℕ) (time : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run time)=0)
    (hp : PortValues (V:=V) p) :
    ∃ J F alpha z w sY n eta zeta gamma u R : V,
      0<J ∧ 0<F ∧ 0<alpha ∧ 0<z ∧ 0<w ∧ 0<sY ∧ 0<n ∧ 0<eta ∧ 0<zeta ∧ 0<gamma ∧
      (p 0:V)*J+1=Exp.exp u ∧ w*Exp.exp u=Exp.exp R ∧
      ((Exp.exp u-1)*(Exp.exp u-F)+alpha)*(Exp.exp u^2-1)+
        ((p 2:V)+Exp.exp u*(p 3:V))*J=R ∧
      ((p 1:V)+w)*Exp.exp u+Exp.exp u=((p 1:V)+w)*(F+alpha)+F+z*(Exp.exp u-1)+1 ∧
      F+alpha<Exp.exp u ∧ R%4=3 ∧ 2*u<R ∧
      SeedRelations u R sY n eta zeta gamma := by
  obtain ⟨δ,_hd,_hbool,_hs,hpack,hx,hresult⟩ := DirectBFSHaltPellSeed.halt_seeds_transport time hT
  letI : 𝚺₁-Function₁ (cellWord (row time) δ) := hx
  let word := cellWord (row time) δ
  let N := length time
  let stride := DirectBFSHaltCanonicalPacking.stride time
  let K : V := kernel
  let R := rank K N stride word
  let w := Exp.exp (R-(590069:V)*N)
  have hpk : PackingInput 590069 K low high N stride word := by
    simpa only [word,N,stride,K,low,high,highNat] using hpack
  obtain ⟨_hcal,hbundle,t,ht,hpow,htransport⟩ := hresult
  obtain ⟨sY,n,eta,zeta,gamma,hsY,hn,heta,hzeta,hgamma,hseed,_hsize,_haux⟩ := hbundle
  have hprops := CompactRankResidueJoin.properties hpk
  let J : V := rep 590069 N
  let F : V := Fw 590069 K N stride word
  let alpha0 : V := alpha 590069 K N stride word
  let q0 : V := Exp.exp ((590069:V)*N)
  have hJ : 0<J := by
    obtain ⟨j,hj⟩ := rep_eight (590069:V) N (by norm_num) (N_pos hpk)
    dsimp [J]
    rw [hj]
    simp
  have hq : (p 0:V)*J+1=q0 := by
    rw [hp.p0]
    exact repunit_identity (590069:V) N
  have hsum : Cw 590069 N word+F+alpha0=q0 := (packing_alpha hpk).2
  have hmask : F+alpha0<q0 := by
    rw [←hsum]
    simpa only [add_assoc] using (lt_add_of_pos_left (F+alpha0) (C_pos hpk))
  have hq1 : q0-1+1=q0 := tsub_add_cancel_of_le (one_le_exp _)
  have htr : (K+w)*Cw 590069 N word=F+t*(q0-1) := htransport
  refine ⟨J,F,alpha0,t+1,w,sY,n,eta,zeta,gamma,(590069:V)*N,R,hJ,F_pos hpk,
    (packing_alpha hpk).1,by simp,lt_of_lt_of_le (by simp) (one_le_exp _),hsY,hn,heta,hzeta,
    hgamma,hq,?_,?_,?_,hmask,hprops.2.1,hprops.2.2,hseed⟩
  · rw [mul_comm]
    exact hpow
  · rw [hp.p2,hp.p3]
    rfl
  · rw [hp.p1]
    change (K+w)*q0+q0=(K+w)*(F+alpha0)+F+(t+1)*(q0-1)+1
    calc
      (K+w)*q0+q0=(K+w)*(Cw 590069 N word+F+alpha0)+(q0-1+1) := by rw [hsum,hq1]
      _=(K+w)*Cw 590069 N word+(K+w)*(F+alpha0)+(q0-1)+1 := by ring
      _=(F+t*(q0-1))+(K+w)*(F+alpha0)+(q0-1)+1 := by rw [htr]
      _=(K+w)*(F+alpha0)+F+(t+1)*(q0-1)+1 := by ring

/-- Halting gives a positive solution of the five Carrier65 equations. -/
theorem halt_equations (p : Fin 4 → ℕ) (time : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run time)=0)
    (hp : PortValues (V:=V) p) :
    ∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ v 1≤(p 0:V)*v 0+1 ∧
      Equations (p 0:V) (p 1:V) (p 2:V) (p 3:V) v := by
  obtain ⟨J,F,alpha0,z,w,sY,n,eta,zeta,gamma,u,R,hJ,hF,ha,hz,hw,hsY,hn,heta,hzeta,hgamma,
    hq,hX,hR,hW,hmask,hR4,_,hseed⟩ := halt_outer p time hT hp
  let q : V := Exp.exp u
  obtain ⟨hτ,hdn,hc,-,-⟩ := hseed
  obtain ⟨f,i,T',u',y,hf,hi,hT',-,hy,-,-,hfn,-,-,-,-,-,-,habs,hlast⟩ :=
    ArithmeticPellAuxiliarySeed.auxiliary_seed (Exp.exp R*(sY*q^3)+sY*q^3) R hR4
  rw [←hc] at hfn habs hlast
  rw [habs] at hlast
  refine ⟨![J,F,alpha0,z,f,i,T',sY,w,n,eta,zeta,y,gamma],?_,?_,?_⟩
  · intro j
    fin_cases j
    exacts [hJ,hF,ha,hz,hf,hi,hT',hsY,hw,hn,heta,hzeta,hy,hgamma]
  · show F≤(p 0:V)*J+1
    rw [hq]
    exact le_of_lt (lt_of_le_of_lt (le_add_of_nonneg_right (Arithmetic.zero_le alpha0)) hmask)
  · exact ArithmeticConstructionAssembly.equations_of _ _ _ _ _ q R hq hX hR hW hτ hdn hfn hlast

/-- **Halt ⇒ zero** for the literal Carrier65 polynomial at the direct-BFS943 ports. -/
theorem halt_zero (p : Fin 4 → ℕ) (time : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run time)=0)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) :
    ∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      (ObjectCurrentEquation2011.expressionAt (fun j => (p j:ℤ))).splitNatural.1.evalSemiring v=
        (ObjectCurrentEquation2011.expressionAt (fun j => (p j:ℤ))).splitNatural.2.evalSemiring v := by
  have hpv := port_values (V:=V) p hp0 hp1 hp2 hp3
  obtain ⟨v,hv,hF,heq⟩ := halt_equations p time hT hpv
  have hb1 : (1:V)≤(p 0:V) := by
    have h31 := (Trace75FixedBounds.fixed_bounds (V:=V) p hp0 hp2 hp3).1
    exact le_trans (by norm_num) h31
  exact ⟨v,hv,ArithmeticConstructionZero.equations_zero p v hv hb1 hF heq⟩

#print axioms Carrier65BFSHalt.port_values
#print axioms Carrier65BFSHalt.halt_outer
#print axioms Carrier65BFSHalt.halt_equations
#print axioms Carrier65BFSHalt.halt_zero
end Carrier65BFSHalt
