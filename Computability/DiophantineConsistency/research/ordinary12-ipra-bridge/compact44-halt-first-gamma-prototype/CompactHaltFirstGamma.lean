import CompactHaltFirstPositive
import CompactPositiveGammaSeed

/-! Positive adaptive correction for the very same chosen seed and transport. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactHaltFirstGamma
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPow ArithmeticPacking ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticOuterSeed
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactWordLowFields CompactCanonicalPerturbation CompactHaltPackedWord
open CompactConstructedRank CompactHaltFirstSeed CompactHaltFirstPositive
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def GammaData (K N s : V) (X : V → V) [𝚺₁-Function₁ X]
    (sY eta zeta gammaOld w : V) : Prop :=
  let q := Exp.exp ((590069:V)*N)
  let R := rank K N s X
  ∃ t gamma : V, 0<gamma ∧
    eta+zeta=R+1+((sY*q^3)*q^2)*t ∧ gamma+w=gammaOld+t

theorem halt_first_gamma (T : V)
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
          PositiveAuxData u R sY ∧ FirstData K N s X sY n eta zeta z ∧
          GammaData K N s X sY eta zeta gamma w) := by
  obtain ⟨δ,hd,hbool,hs,hpack,hx,hresult⟩ := halt_first_positive T hT
  refine ⟨δ,hd,hbool,hs,hpack,hx,?_⟩
  intro hX
  letI : 𝚺₁-Function₁ (perturb (baseCell (haltRow T)) δ) := hX
  obtain ⟨hcal,z,hz,hqw,htransport,sY,n,eta,zeta,gamma,hsY,hn,he,hzz,hg,hseed,hsize,hauxp,hfirst⟩ := hresult
  have hp : PackingInput 590069 (paramKernel rho : V) low high (haltLength T) (haltStride T)
      (perturb (baseCell (haltRow T)) δ) := by
    simpa only [low,high,highNat] using hpack
  have hgamma := CompactPositiveGammaSeed.positive_gamma hp sY n eta zeta gamma _ hsY hg hseed hqw.symm
  exact ⟨hcal,z,hz,hqw,htransport,sY,n,eta,zeta,gamma,hsY,hn,he,hzz,hg,hseed,hsize,hauxp,hfirst,hgamma⟩

#print axioms CompactHaltFirstGamma.halt_first_gamma
end CompactHaltFirstGamma
