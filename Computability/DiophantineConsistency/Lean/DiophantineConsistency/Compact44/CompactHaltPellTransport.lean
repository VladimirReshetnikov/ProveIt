import DiophantineConsistency.Compact44.CompactHaltPellSeed
import DiophantineConsistency.Compact44.CompactCalibratedTransport
import DiophantineConsistency.Compact44.CompactPackingGeometry

/-! Model halt supplies calibrated packing, Pell seeds and positive transport
on exactly the same constructed word. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactHaltPellTransport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPow ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactWordLowFields CompactCanonicalPerturbation CompactHaltPackedWord
open CompactConstructedRank CompactHaltPellSeed CompactCalibratedTransport
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem halt_pell_positive_transport (T : V)
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
        SeedBundle (paramKernel rho : V) (haltLength T) (haltStride T) X ∧
        let R := rank (paramKernel rho : V) (haltLength T) (haltStride T) X
        let q := Exp.exp (590069*haltLength T)
        let w := Exp.exp (R-590069*haltLength T)
        let C := Cw 590069 (haltLength T) X
        let F := Fw 590069 (paramKernel rho : V) (haltLength T) (haltStride T) X
        ∃ z : V, 0<z ∧ q*w=Exp.exp R ∧ ((paramKernel rho : V)+w)*C=F+z*(q-1)) := by
  obtain ⟨δ,hd,hbool,hs,hpack,hx,hresult⟩ := halt_calibrated_seeds T hT
  refine ⟨δ,hd,hbool,hs,hpack,hx,?_⟩
  intro hX
  letI : 𝚺₁-Function₁ (perturb (baseCell (haltRow T)) δ) := hX
  obtain ⟨hcal,hseed⟩ := hresult
  have hp : PackingInput 590069 (paramKernel rho : V) low high (haltLength T) (haltStride T)
      (perturb (baseCell (haltRow T)) δ) := by
    simpa only [low,high,highNat] using hpack
  have hs0 : 0<haltStride T := power_pos _ _ (by norm_num)
  have hsN : haltStride T<haltLength T := (CompactPackingGeometry.geometry T).2
  exact ⟨hcal,hseed,calibrated_transport hp hs0 hsN hcal⟩

#print axioms CompactHaltPellTransport.halt_pell_positive_transport
end CompactHaltPellTransport
