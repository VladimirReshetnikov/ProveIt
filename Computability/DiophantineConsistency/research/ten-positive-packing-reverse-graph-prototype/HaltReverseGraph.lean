import PackingReverseGraph
import CompactRankResidueJoin
import Direct80RankLower

/-! One symbolic-port machine halt supplies the same packing and 80 graph zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositiveHaltReverseGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open ArithmeticPow ArithmeticPacking ArithmeticRepunit ArithmeticPellRecurrence ArithmeticOuterSeed
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactWordLowFields CompactCanonicalPerturbation CompactHaltPackedWord
open CompactConstructedRank CompactRankResidueJoin CompactHaltFirstSeed
open TenPositive80Graph TenPositive80Factors TenPositive80RankLower TenPositivePackingReverseGraph
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem halt_zero_of_model_ports (p : Fin 4 → ℕ) (time : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run time)=0)
    (hp0 : (p 0:V)=Exp.exp (590069:V)-1)
    (hp1 : (p 1:V)=paramKernel rho)
    (hp2 : (p 2:V)=low)
    (hp3 : (p 3:V)=high+(Exp.exp (590069:V)-1)) :
    ∃ v : Fin 10 → V, (∀j,0<v j) ∧ InternalZero (graph (integerPorts p)).output v := by
  obtain ⟨δ,hd,hbool,hs,hpack,hx,hresult⟩ := halt_first_seed time hT
  let word := perturb (baseCell (haltRow time)) δ
  letI : 𝚺₁-Function₁ word := hx
  let N := haltLength time
  let stride := haltStride time
  let K : V := paramKernel rho
  let R := rank K N stride word
  let q0 := Exp.exp ((590069:V)*N)
  let w := Exp.exp (R-(590069:V)*N)
  have hp : PackingInput 590069 K low high N stride word := by
    simpa only [word,N,stride,K,low,high,highNat] using hpack
  obtain ⟨_hcal,t,ht,hpow,htransport,sY,n,eta,zeta,gamma,hsY,hn,heta,hzeta,hgamma,
    hseed,_hsize,_haux,_hfirst⟩ := hresult
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
  apply packing_seed_zero p K N stride word sY n eta zeta gamma w t r hp hp0 hp1 hp2 hp3
    hb hsY hw heta hzeta hr4 hphase hr
  · rw [←hr]
    exact hpow
  · exact htransport
  · simpa only [←hr] using hseed

#print axioms TenPositiveHaltReverseGraph.halt_zero_of_model_ports
end TenPositiveHaltReverseGraph
