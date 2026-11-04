import DiophantineConsistency.Compact44.CompactHaltFirstGamma
import DiophantineConsistency.Compact44.CompactPositiveValuation
import DiophantineConsistency.Compact44.CompactAuxOrdinateOrder
import DiophantineConsistency.Compact44.FreeJModelRankBinding
import DiophantineConsistency.Compact44.FreeJModelZeroJoin

/-! Construct a positive actual free-J zero from a model halt, under explicit port casts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeJHaltModelZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing Ordinary12FreeJ
open ArithmeticPow ArithmeticPacking ArithmeticRepunit ArithmeticPellRecurrence ArithmeticOuterSeed
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactWordLowFields CompactCanonicalPerturbation CompactHaltPackedWord
open CompactConstructedRank CompactRankResidueJoin CompactHaltFirstSeed CompactHaltFirstPositive
open CompactHaltFirstGamma CompactPositiveValuation CompactAuxOrdinateOrder
open FreeJAdaptiveLift FreeJModelRankBinding FreeJModelZeroJoin
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A model halt gives a positive zero of the exact graph when all four
fixed graph ports have the stated model values. These are port hypotheses,
not yet a syntactic iPRA proof or fixed-coefficient calibration. -/
theorem halt_positive_zero_of_ports (T : V) (p : Fin 4 → ℤ)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0)
    (hbeta : ι (rep 590069 (haltLength T))*((p 0 : ℤ) : DiffRing V) =
      ι (Exp.exp ((590069:V)*haltLength T)-1))
    (hK : ((p 1 : ℤ) : DiffRing V)=ι (paramKernel rho : V))
    (hMC : ((p 2 : ℤ) : DiffRing V)=ι (low:V))
    (hMF : ((p 3 : ℤ) : DiffRing V)=ι (high+(Exp.exp (590069:V)-1))) :
    ∃ v : Fin 12 → V, (∀ j,0<v j) ∧ InternalZero (literal p) v := by
  obtain ⟨δ,hd,hbool,hs,hpack,hx,hresult⟩ := halt_first_gamma T hT
  let X := perturb (baseCell (haltRow T)) δ
  letI : 𝚺₁-Function₁ X := hx
  let N := haltLength T
  let stride := haltStride T
  let K : V := paramKernel rho
  let u : V := 590069*N
  let R := rank K N stride X
  let q := Exp.exp u
  let w := Exp.exp (R-u)
  obtain ⟨hcal,z,hz,hqw,htransport,sY,n,eta,zeta,gammaOld,hsY,hn,he,hzz,hg,
    hseed,hsize,haux,hfirst,hgamma⟩ := hresult
  obtain ⟨f,i,auxT,auxw,y,hf,hi,hTaux,haw,hy,hfx,hyic,hstrong,
    hydef,hux,hudef,huf,huc,hlit,habs,hauxnorm,hfminus,hfplus,hdi,hdiaux,hnorm⟩ := haux
  obtain ⟨hBt,r,hr,hfirsteq⟩ := hfirst
  obtain ⟨t,gamma,hgamma,hk,hgammarel⟩ := hgamma
  let Y := sY*q^3
  let a := Exp.exp R*Y+Y
  let c := ycoord R a
  let Δ := delta a
  let v := valuation K N stride X sY f auxT r eta zeta i auxw y gamma
  have hp : PackingInput 590069 K low high N stride X := by
    simpa only [X,N,stride,K,low,high,highNat] using hpack
  have hpos : ∀ j,0<v j := by
    apply CompactPositiveValuation.positive hp sY f auxT r eta zeta i auxw y gamma
      hsY hTaux hr he hzz hi hgamma
    exact hfx
  have hRpos : 0<R := lt_of_le_of_lt (by simp) (properties hp).2.2
  have hcpos : 0<c := lt_of_lt_of_le hRpos (time_le_y R a)
  have hΔpos : 0<Δ := by dsimp [Δ,delta]; exact mul_pos (by simp) (by simp)
  have hIpos : 0<Δ*i*c*c := mul_pos (mul_pos (mul_pos hΔpos hi) hcpos) hcpos
  have hwy : auxw≤y := ordinate_ge (Δ*i*c*c) auxw y hIpos hy hauxnorm
  have hv0 : v 0=rep 590069 N := rfl
  have hv1 : v 1=Fw 590069 K N stride X := rfl
  have hv2 : v 2=alpha 590069 K N stride X := rfl
  have hv3 : v 3=f-1 := rfl
  have hv4 : v 4=auxT := rfl
  have hv5 : v 5=Exp.exp R := rfl
  have hv6 : v 6=Y := rfl
  have hv7 : v 7=r := rfl
  have hv8 : v 8=eta := rfl
  have hv9 : v 9=zeta := rfl
  have hv10 : v 10=Δ*i+(y-auxw) := rfl
  have hv11 : v 11=gamma := rfl
  have hb : ι (v 0)*((p 0 : ℤ) : DiffRing V)=ι (q-1) := by simpa only [hv0,N,q,u] using hbeta
  have hRank := graph_rank_of_packing p v hp hv0 hv1 hv2 hb hMC hMF
  have hceq : c=(eta+zeta)*Y+eta := by
    have h := hseed.2.2.1
    exact h.symm
  refine ⟨v,hpos,?_⟩
  apply zero_of_model_data p v u R sY n eta zeta gammaOld q K
    (Cw 590069 N X) (Fw 590069 K N stride X) (alpha 590069 K N stride X)
    (Exp.exp R) Y r z gamma w t a c Δ f i auxT auxw y
    hseed (one_le_exp _) (packing_alpha hp).2 rfl rfl hv1 hv2 hv5 hv6 hv7 hv8 hv9 hv11
    hb hK hRank hBt hfirsteq hqw.symm hk hgammarel (pos_iff_one_le.mp hf) hwy rfl hceq rfl
    hv3 hv4 hv10 hstrong hlit hauxnorm

#print axioms FreeJHaltModelZero.halt_positive_zero_of_ports
end FreeJHaltModelZero
