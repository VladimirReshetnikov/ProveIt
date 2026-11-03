import CompactHaltPellTransport
import CompactFirstTransportSeed

/-! The outer and auxiliary seed witnesses and the first-carrier witness
    are constructed from the same calibrated model-halt packing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactHaltFirstSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPow ArithmeticPacking ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticOuterSeed
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactWordLowFields CompactCanonicalPerturbation CompactHaltPackedWord
open CompactConstructedRank CompactHaltPellSeed CompactHaltPellTransport CompactFirstTransportSeed
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def AuxData (u R sY : V) : Prop :=
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
    I*I*w*w+y*y=1+I*I*y*y

def FirstData (K N s : V) (X : V → V) [𝚺₁-Function₁ X]
    (sY n eta zeta z : V) : Prop :=
  let q := Exp.exp ((590069:V)*N)
  let R := rank K N s X
  let Y := sY*q^3
  let E := Exp.exp R*Y
  let k := eta+zeta
  let ell := E*Y*k
  let tau := E*n+k-R
  let C := Cw 590069 N X
  let F := Fw 590069 K N s X
  (q*K+Exp.exp R)*C = q*F+(q-1)*(q*z) ∧
  ∃ r : V, 0<r ∧
    (q^3*(q-1))*(ell+k+r)+Y*(q-1) =
    (q^3*(q-1))*tau+(1+(q-1)*k)*q^3*((q-1)*(q*z))

theorem halt_first_seed (T : V)
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
          AuxData u R sY ∧ FirstData K N s X sY n eta zeta z) := by
  obtain ⟨δ,hd,hbool,hs,hpack,hx,hresult⟩ := halt_pell_positive_transport T hT
  refine ⟨δ,hd,hbool,hs,hpack,hx,?_⟩
  intro hX
  letI : 𝚺₁-Function₁ (perturb (baseCell (haltRow T)) δ) := hX
  obtain ⟨hcal,hbundle,z,hz,hqw,htransport⟩ := hresult
  obtain ⟨sY,n,eta,zeta,gamma,hsY,hn,he,hzz,hg,hseed,hsize,haux⟩ := hbundle
  have hp : PackingInput 590069 (paramKernel rho : V) low high (haltLength T) (haltStride T)
      (perturb (baseCell (haltRow T)) δ) := by
    simpa only [low,high,highNat] using hpack
  have hf := first_from_transport hp sY n eta zeta gamma _ z hsY hz hseed hqw htransport
  exact ⟨hcal,z,hz,hqw,htransport,sY,n,eta,zeta,gamma,hsY,hn,he,hzz,hg,hseed,hsize,haux,hf⟩

#print axioms CompactHaltFirstSeed.halt_first_seed
end CompactHaltFirstSeed
