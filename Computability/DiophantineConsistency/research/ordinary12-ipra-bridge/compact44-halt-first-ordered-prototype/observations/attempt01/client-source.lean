import CompactHaltFirstGamma
import CompactSeedOrdinateOrder

/-! Positive adaptive correction for the very same chosen seed and transport. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactHaltFirstOrdered
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPow ArithmeticPacking ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticOuterSeed
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactWordLowFields CompactCanonicalPerturbation CompactHaltPackedWord
open CompactConstructedRank CompactRankResidueJoin CompactHaltFirstSeed CompactHaltFirstPositive
open CompactHaltFirstGamma CompactSeedOrdinateOrder
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def OrderedAuxData (u R sY : V) : Prop :=
  let Y := sY*Exp.exp u^3
  let a := Exp.exp R*Y+Y
  let c := ycoord R a
  ∃ f i T w y : V, 0 < f ∧ 0 < i ∧ 0 < T ∧ 0 < w ∧ 0 < y ∧
    f=xcoord (R*c) a ∧ ycoord (R*c) a=i*c*c ∧
    f*f=1+delta a*(i*c*c)*(i*c*c) ∧
    let I := delta a*i*c*c
    y=ycoord R (I-2) ∧ xcoord R (I-2)=I*w ∧
    w=oddQuotient ((R-1)/2) (I-2) ∧
    (w+c)%(f*f)=0 ∧ (w+R)%c=0 ∧
    f*f*c*T=w+c+f*f*R ∧ w=absdiff (f*f*c*T) (f*f*R+c) ∧
    I*I*w*w+y*y=1+I*I*y*y ∧
    0<f-1 ∧ (f-1)+1=f ∧ 0<delta a*i ∧ 0<delta a*i+w ∧
    delta a*(f*f-1)=(c*c*c*c)*(delta a*i)*(delta a*i) ∧ w≤y

theorem aux_ordered (u R sY : V) (hR : 0<R) (h : PositiveAuxData u R sY) :
    OrderedAuxData u R sY := by
  obtain ⟨f,i,T,w,y,hf,hi,hT,hw,hy,hfx,hyic,hfn,hydef,hux,hudef,
    huf,huc,hlit,habs,hnorm,ht,he,hiOrd,hnOrd,hstrong⟩ := h
  have hwy := seed_ordinate_ge _ R i w y hR hi hy hnorm
  exact ⟨f,i,T,w,y,hf,hi,hT,hw,hy,hfx,hyic,hfn,hydef,hux,hudef,
    huf,huc,hlit,habs,hnorm,ht,he,hiOrd,hnOrd,hstrong,hwy⟩

theorem halt_first_ordered (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j≤1) ∧
      (∀ j, δ j≠0 → 0<j ∧ j+1<haltLength T ∧ j+haltStride T<haltLength T) ∧
      let X := perturb (baseCell (haltRow T)) δ
      PackingInput 590069 (paramKernel rho : V) CompactConcreteIncrement.mask (highNat : V)
        (haltLength T) (haltStride T) X ∧
      (𝚺₁-Function₁ X) ∧
      (∀ [𝚺₁-Function₁ X],
        let N := haltLength T
        let s := haltStride T
        let K : V := paramKernel rho
        let u := (590069:V)*N
        let R := rank K N s X
        let q := Exp.exp u
        let w := Exp.exp (R-u)
        R%u=(590069*s)%u ∧
        ∃ z : V, 0<z ∧ q*w=Exp.exp R ∧
          (K+w)*Cw 590069 N X=Fw 590069 K N s X+z*(q-1) ∧
        ∃ sY n eta zeta gamma : V,
          0<sY ∧ 0<n ∧ 0<eta ∧ 0<zeta ∧ 0<gamma ∧
          SeedRelations u R sY n eta zeta gamma ∧
          sY*q^3 ≤ power (Exp.exp R+1) R ∧
          OrderedAuxData u R sY ∧ FirstData K N s X sY n eta zeta z ∧
          GammaData K N s X sY eta zeta gamma w) := by
  obtain ⟨δ,hd,hbool,hs,hpack,hx,hresult⟩ := halt_first_gamma T hT
  refine ⟨δ,hd,hbool,hs,hpack,hx,?_⟩
  intro hX
  letI : 𝚺₁-Function₁ (perturb (baseCell (haltRow T)) δ) := hX
  obtain ⟨hcal,z,hz,hqw,htransport,sY,n,eta,zeta,gamma,hsY,hn,he,hzz,hg,hseed,hsize,hauxp,hfirst,hgamma⟩ := hresult
  have hp : PackingInput 590069 (paramKernel rho : V) low high (haltLength T) (haltStride T)
      (perturb (baseCell (haltRow T)) δ) := by
    simpa only [low,high,highNat] using hpack
  have hR : 0 < rank (paramKernel rho : V) (haltLength T) (haltStride T)
      (perturb (baseCell (haltRow T)) δ) := lt_of_le_of_lt (by simp) (properties hp).2.2
  have hauxo := aux_ordered (590069*haltLength T)
    (rank (paramKernel rho : V) (haltLength T) (haltStride T)
      (perturb (baseCell (haltRow T)) δ)) sY hR hauxp
  exact ⟨hcal,z,hz,hqw,htransport,sY,n,eta,zeta,gamma,hsY,hn,he,hzz,hg,hseed,hsize,hauxo,hfirst,hgamma⟩

#print axioms CompactHaltFirstOrdered.aux_ordered
#print axioms CompactHaltFirstOrdered.halt_first_ordered
end CompactHaltFirstOrdered
