import DiophantineConsistency.BFS943.Trace76ReverseGraph
import DiophantineConsistency.Compact44.CompactHaltFirstSeed

/-! Conditional passage from the compact canonical packing to a positive 76/352 zero
(`Trace75PackingReverseGraph` with `Trace76ReverseGraph`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace76PackingReverseGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 TenPositiveTrace76
open ArithmeticPow ArithmeticPacking ArithmeticRepunit ArithmeticPellRecurrence ArithmeticOuterSeed
open ArithmeticHalfBinomial ArithmeticMaskPopulation
open CompactConstructedRank CompactHaltFirstSeed
open Trace75Factors Trace75Rank Trace76ReverseGraph
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
    (hpow : Exp.exp ((590069:V)*N)*w=Exp.exp (2*r+1))
    (htransport : (K+w)*Cw 590069 N word =
      Fw 590069 K N stride word+t*(Exp.exp ((590069:V)*N)-1))
    (hseed : SeedRelations ((590069:V)*N) (2*r+1) sY n eta zeta gamma) :
    ∃ v : Fin 10 → V, (∀j,0<v j) ∧ value76 (ports p) (fun j => ι (v j))=0 := by
  let J : V := rep 590069 N
  let F : V := Fw 590069 K N stride word
  let alpha0 : V := alpha 590069 K N stride word
  let q0 : V := Exp.exp ((590069:V)*N)
  let v : Fin 10 → V := ![J,F,alpha0,1,1,w,sY,1,1,1]
  have hJ : 0<J := by
    obtain ⟨j,hj⟩ := rep_eight (590069:V) N (by norm_num) (N_pos hp)
    dsimp [J]
    rw [hj]
    simp
  have hv : ∀j,0<v j := by
    intro j
    fin_cases j <;> simp [v,J,F,alpha0,hJ,F_pos hp,(packing_alpha hp).1,hw,hsY]
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
  have htransport' : ((p 1:V)+v 5)*(q p v-v 1-v 2)=v 1+b p v*t := by
    rw [hq,hbJ,hp1]
    change (K+w)*(q0-F-alpha0)=F+(q0-1)*t
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
    rw [hq,mul_comm]
    exact hpow
  have hY : Y p v=sY*q0^3 := by
    dsimp [Y,v]
    rw [hq]
    ring
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
  have hck : ycoord (2*r+1) (Y p v*(X p v+1))=
      2*ycoord (r+1) (2*(X p v*Y p v*Y p v-1)+1)*Y p v+eta := by
    rw [hX,hY]
    have he : sY*q0^3*(Exp.exp (2*r+1)+1)=Exp.exp (2*r+1)*(sY*q0^3)+sY*q0^3 := by ring
    rw [he]
    simpa only [q0] using hC.symm.trans (by rw [hk])
  have hk' : 2*ycoord (r+1) (2*(X p v*Y p v*Y p v-1)+1)=eta+zeta := by
    rw [hX,hY]
    simpa only [q0] using hk.symm
  exact graph_zero_of_source p v r eta zeta t hb hv (lt_of_lt_of_le (by norm_num) hr)
    hmask htransport' hRank hphase hX h72 heta hzeta hck hk'

#print axioms Trace76PackingReverseGraph.packing_seed_zero
end Trace76PackingReverseGraph
