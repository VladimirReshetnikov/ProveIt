import DiophantineConsistency.BFS943.DirectBFSHaltPellSeed
import DiophantineConsistency.BFS943.Trace82ReverseGraph
import DiophantineConsistency.Compact44.CompactHaltFirstSeed
import DiophantineConsistency.Compact44.CompactRankResidueJoin
import DiophantineConsistency.BFS943.Direct80RankLower

/-! # A halting time of machine 215 gives a positive 82/240 zero

`Trace75PackingReverseGraph`/`Trace75BFSHaltGraph` for the free-plain chart.
`DirectBFSHaltPellSeed.halt_seeds_transport` supplies the canonical packing,
its rank `R = 2r + 1` (`R ≡ 3 mod 4`, `2 u N < R`, `u = 590069`), the
unscaled outer seed at `(2^R, s_Y q³)` (`SeedRelations`) and the transport at
base `w = 2^{R - uN}`. Since `2 u N < R`, `w = q w''` with
`w'' = 2^{R - 2uN}` (`q = 2^{uN}`), so `X = q² w'' = 2^R` and the 82 transport
base is `q w'' = w`. The free strip ordinate is `s = s_Y q³`, the unscaled
seed's `Y`; `Trace82ReverseGraph.graph_zero_of_source` gives the zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Trace82HaltGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace82
open ArithmeticPow ArithmeticPacking ArithmeticRepunit ArithmeticPellRecurrence ArithmeticOuterSeed
open ArithmeticHalfBinomial ArithmeticMaskPopulation
open CompactSymbolicPorts CompactConstructedRank CompactRankResidueJoin CompactHaltFirstSeed
open DirectBFSConstructedWord DirectBFSFourFieldsPacking DirectBFSHaltCanonicalPacking
open TenPositive80RankLower Trace82Factors Trace82NormRank Trace82ReverseGraph
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] DirectBFSFourFieldsPacking.kernel DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho CompactSymbolicPorts.highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem packing_seed_zero (p : Fin 4 → ℕ) (K N stride : V)
    (word : V → V) [𝚺₁-Function₁ word] (sY n eta zeta gamma w t r : V)
    (hp : PackingInput 590069 K low high N stride word)
    (hp0 : (p 0:V)=Exp.exp (590069:V)-1)
    (hp1 : (p 1:V)=K) (hp2 : (p 2:V)=low)
    (hp3 : (p 3:V)=high+(Exp.exp (590069:V)-1))
    (hb : 0<(p 0:V)) (hsY : 0<sY) (hw : 0<w)
    (heta : 0<eta) (hzeta : 0<zeta) (hr : 4≤r)
    (hphase : (2*r+1)%4=3)
    (hR : rank K N stride word=2*r+1)
    (hpow : Exp.exp ((590069:V)*N)*(Exp.exp ((590069:V)*N)*w)=Exp.exp (2*r+1))
    (htransport : (K+Exp.exp ((590069:V)*N)*w)*Cw 590069 N word =
      Fw 590069 K N stride word+t*(Exp.exp ((590069:V)*N)-1))
    (hseed : SeedRelations ((590069:V)*N) (2*r+1) sY n eta zeta gamma) :
    ∃ v : Fin 10 → V, (∀j,0<v j) ∧ value82 (ports p) (fun j => ι (v j))=0 := by
  let J : V := rep 590069 N
  let F : V := Fw 590069 K N stride word
  let alpha0 : V := alpha 590069 K N stride word
  let q0 : V := Exp.exp ((590069:V)*N)
  let v : Fin 10 → V := ![J,F,alpha0,1,1,w,q0*q0*q0*sY,1,1,1]
  have hJ : 0<J := by
    obtain ⟨j,hj⟩ := rep_eight (590069:V) N (by norm_num) (N_pos hp)
    dsimp [J]
    rw [hj]
    simp
  have hq0 : 0<q0 := exp_pos _
  have hv : ∀j,0<v j := by
    intro j
    fin_cases j <;> simp [v,J,F,alpha0,hJ,F_pos hp,(packing_alpha hp).1,hw,hsY,hq0]
  have hq : q p v=q0 := by
    dsimp [q,b,v,J,q0]
    rw [hp0]
    exact repunit_identity (590069:V) N
  have hbJ : b p v=q0-1 := by
    have he := hq
    dsimp [q] at he
    rw [←he]
    simp
  have hmask : v 1+v 2<q p v := by
    rw [hq]
    change F+alpha0<q0
    have hh := (packing_alpha hp).2
    have hc := C_pos hp
    change Cw 590069 N word+F+alpha0=q0 at hh
    rw [←hh]
    simpa only [add_assoc] using (lt_add_of_pos_left (F+alpha0) hc)
  have htransport' : ((p 1:V)+q p v*v 5)*(q p v-v 1-v 2)=v 1+b p v*t := by
    rw [hq,hbJ,hp1]
    change (K+q0*w)*(q0-F-alpha0)=F+(q0-1)*t
    have hh := (packing_alpha hp).2
    change Cw 590069 N word+F+alpha0=q0 at hh
    have hc : q0-F-alpha0=Cw 590069 N word := by
      rw [←hh,show Cw 590069 N word+F+alpha0=(Cw 590069 N word+alpha0)+F by ring]
      simp
    rw [hc]
    simpa only [F,q0,mul_comm] using htransport
  have hRank : rankNat p v=2*r+1 := by
    rw [←hR]
    dsimp [rankNat,CompactConstructedRank.rank]
    rw [hq,hbJ,hp2,hp3]
    change ((q0-1)*(q0-F)+alpha0)*(q0*q0-1)+
        (low+q0*(high+(Exp.exp (590069:V)-1)))*J =
      ((q0-1)*(q0-F)+alpha0)*(q0^2-1)+
        (low+q0*(high+(Exp.exp (590069:V)-1)))*J
    rw [pow_two]
  have hX : X p v=Exp.exp (2*r+1) := by
    dsimp [X,v]
    rw [hq]
    exact hpow
  have h72 : 72*r<X p v+1 := by
    rw [hX]
    exact lt_of_lt_of_le (seventy_two_lt_exp r hr) (by simp)
  have hs := hseed
  dsimp [SeedRelations] at hs
  obtain ⟨_,_,hC,_,r0,hr0,_,hk⟩ := hs
  have hr0eq : r0=r := by
    have hh : 2*r0+1=2*r+1 := hr0.symm
    apply mul_left_cancel₀ (by norm_num : (2:V)≠0)
    exact add_right_cancel hh
  subst r0
  have hv6 : v 6=sY*q0^3 := by dsimp [v]; ring
  have hck : ycoord (2*r+1) (v 6*(X p v+1))=
      2*ycoord (r+1) (2*(X p v*v 6*v 6-1)+1)*v 6+eta := by
    rw [hX,hv6]
    have he : sY*q0^3*(Exp.exp (2*r+1)+1)=Exp.exp (2*r+1)*(sY*q0^3)+sY*q0^3 := by ring
    rw [he]
    simpa only [q0] using hC.symm.trans (by rw [hk])
  have hk' : 2*ycoord (r+1) (2*(X p v*v 6*v 6-1)+1)=eta+zeta := by
    rw [hX,hv6]
    simpa only [q0] using hk.symm
  have hYs : v 6=q p v*q p v*q p v*sY := by rw [hq]; rfl
  exact graph_zero_of_source p v r eta zeta t sY hb hv (le_trans (by norm_num) hr)
    hmask htransport' hRank hphase hX h72 heta hzeta hck hk' hYs

theorem halt_zero_of_model_ports (p : Fin 4 → ℕ) (time : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run time)=0)
    (hp0 : (p 0:V)=Exp.exp (590069:V)-1)
    (hp1 : (p 1:V)=(kernel:V)) (hp2 : (p 2:V)=low)
    (hp3 : (p 3:V)=high+(Exp.exp (590069:V)-1)) :
    ∃ v : Fin 10 → V, (∀j,0<v j) ∧ value82 (ports p) (fun j => ι (v j))=0 := by
  obtain ⟨δ,hd,_hbool,_hs,hpack,hx,hresult⟩ := DirectBFSHaltPellSeed.halt_seeds_transport time hT
  letI : 𝚺₁-Function₁ (cellWord (row time) δ) := hx
  let word := cellWord (row time) δ
  let N := length time
  let stride := DirectBFSHaltCanonicalPacking.stride time
  let K : V := kernel
  let R := rank K N stride word
  let u : V := (590069:V)*N
  let w := Exp.exp (R-2*u)
  have hp : PackingInput 590069 K low high N stride word := by
    simpa only [word,N,stride,K,low,high,highNat] using hpack
  obtain ⟨_hcal,hbundle,t,_ht,hpow,htransport⟩ := hresult
  obtain ⟨sY,n,eta,zeta,gamma,hsY,_hn,heta,hzeta,_hgamma,hseed,_hsize,_haux⟩ := hbundle
  have hprops := CompactRankResidueJoin.properties hp
  have hseed' := hseed
  dsimp [SeedRelations] at hseed'
  obtain ⟨_,_,_,_,r,hr,_,_⟩ := hseed'
  have hN1 : 1≤N := pos_iff_one_le.mp (N_pos hp)
  have hU : (590069:V)≤590069*N := le_mul_of_one_le_right (by simp) hN1
  have h32 : (32:V)≤2*((590069:V)*N) := le_trans (by norm_num)
    (mul_le_mul_of_nonneg_left hU (by simp))
  have hR32 : 32≤R := le_trans h32 (le_of_lt hprops.2.2)
  have hr15 := half_rank_ge_fifteen R r hR32 hr
  have hr4 : 4≤r := le_trans (by norm_num) hr15
  have hphase : (2*r+1)%4=3 := by rw [←hr]; exact hprops.2.1
  have hb : 0<(p 0:V) := by
    rw [hp0]
    exact tsub_pos_of_lt (lt_of_lt_of_le (by norm_num) (two_le_B hp))
  have hw : 0<w := lt_of_lt_of_le (by simp) (one_le_exp _)
  -- `2 u N < R`: the 75 transport base `2^{R - uN}` is `q w`
  have h2u : 2*u≤R := le_of_lt hprops.2.2
  obtain ⟨d,hdR⟩ : ∃ d : V, R=2*u+d := ⟨R-2*u,(add_tsub_cancel_of_le h2u).symm⟩
  have hwd : w=Exp.exp d := by
    change Exp.exp (R-2*u)=Exp.exp d
    rw [hdR,add_tsub_cancel_left]
  have hsplit : Exp.exp (R-(590069:V)*N)=Exp.exp ((590069:V)*N)*w := by
    rw [hwd,←exp_add]
    congr 1
    change R-u=u+d
    rw [hdR,two_mul,add_assoc,add_tsub_cancel_left]
  apply packing_seed_zero p K N stride word sY n eta zeta gamma w t r hp hp0 hp1 hp2 hp3
    hb hsY hw heta hzeta hr4 hphase hr
  · rw [←hr,←hsplit]
    exact hpow
  · rw [←hsplit]
    exact htransport
  · simpa only [←hr] using hseed
#print axioms Trace82HaltGraph.packing_seed_zero
#print axioms Trace82HaltGraph.halt_zero_of_model_ports
end Trace82HaltGraph
