import DiophantineConsistency.Compact44.CompactHaltRankNoHigh
import DiophantineConsistency.Compact44.CompactOuterPellSeed

/-! The chosen, calibrated model-halt packing and both Pell seeds use one word. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactHaltPellSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticPow ArithmeticPacking ArithmeticRepunit
open ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticOuterSeed
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactWordLowFields CompactCanonicalPerturbation CompactRankVariation
open CompactHaltPackedWord CompactHaltRankNoHigh CompactWordChosenRank
open CompactConstructedRank CompactRankResidueJoin CompactOuterPellSeed
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The precise simultaneous seed conclusion, with the rank tied to `X`. -/
def SeedBundle (K N s : V) (X : V → V) [𝚺₁-Function₁ X] : Prop :=
  let u := (590069:V)*N
  let R := rank K N s X
  ∃ sY n eta zeta gamma : V,
    0<sY ∧ 0<n ∧ 0<eta ∧ 0<zeta ∧ 0<gamma ∧
    SeedRelations u R sY n eta zeta gamma ∧
    sY*Exp.exp u^3 ≤ power (Exp.exp R+1) R ∧
    (let Y := sY*Exp.exp u^3
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
      I*I*w*w+y*y=1+I*I*y*y)

/-- A model halt constructs one definable pulsed packing whose exact rank is
calibrated and which supplies both seed families. -/
theorem halt_calibrated_seeds (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j≤1) ∧
      (∀ j, δ j≠0 → 0<j ∧ j+1<haltLength T ∧ j+haltStride T<haltLength T) ∧
      let X := perturb (baseCell (haltRow T)) δ
      PackingInput 590069 (paramKernel rho : V) CompactConcreteIncrement.mask (highNat : V)
        (haltLength T) (haltStride T) X ∧
      (𝚺₁-Function₁ X) ∧
      (∀ [𝚺₁-Function₁ X],
        rank (paramKernel rho : V) (haltLength T) (haltStride T) X % (590069*haltLength T) =
          (590069*haltStride T) % (590069*haltLength T) ∧
        SeedBundle (paramKernel rho : V) (haltLength T) (haltStride T) X) := by
  letI : 𝚺₁-Function₁ (fun _ : V => (0:V)) := by definability
  let N := haltLength T
  let s := haltStride T
  let c : V := (low+Exp.exp (590069*N)*(high+(Exp.exp (590069:V)-1)))*rep 590069 N
  obtain ⟨δ,hd,hb,hs,hpack,hcal⟩ := halt_chosen_rank_no_high T c hT
  have hword := halt_packed_word T (fun _ => 0) hT
  letI : 𝚺₁-Function₁ (haltRow T) := hword.1
  letI : 𝚺₁-Function₁ (baseCell (haltRow T)) := baseCell_definable (haltRow T)
  letI : 𝚺₁-Function₁ δ := hd
  have hx : 𝚺₁-Function₁ (perturb (baseCell (haltRow T)) δ) := inferInstance
  refine ⟨δ,hd,hb,hs,hpack,hx,?_⟩
  intro hX
  letI : 𝚺₁-Function₁ (perturb (baseCell (haltRow T)) δ) := hX
  have hp : PackingInput 590069 (paramKernel rho : V) low high N s
      (perturb (baseCell (haltRow T)) δ) := by
    simpa only [N,s,low,high,highNat] using hpack
  have hr := rank_eq_window (paramKernel rho : V) N s (perturb (baseCell (haltRow T)) δ)
  constructor
  · simpa only [N,s,c] using hr ▸ hcal
  · exact seeds hp

#print axioms CompactHaltPellSeed.halt_calibrated_seeds
end CompactHaltPellSeed
