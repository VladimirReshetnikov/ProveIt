import DirectBFSModelMass
import DiophantineConsistency.CompactTwoBandCarry
import DiophantineConsistency.KCast

/-! Direct-BFS symbolic bands, rotations and the generic carry interface. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSBandCarry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency CompactSymbolicKernel KCast CompactPartialBandRotation
open ArithmeticCyclicWord ArithmeticWindowDigits CompactGenericAlignedMass CompactIndexedFlatten
open CompactTwoBandFlatten CompactHeterogeneousCarry DirectBFSModelMass
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel DirectBFSSymbolicKernel.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def selectorCoeff (i : Fin 943) : V := (selectors i:V)
def kernelBand (pos : Fin 41 → ℕ) (T : ℕ) : V :=
  (∑ i, selectorCoeff i*Exp.exp (67*selectorOffset T i)) +
  (∑ j, copyCoeff j*Exp.exp (67*copyOffset pos T j))
def rotatedBand (pos : Fin 41 → ℕ) (T : ℕ) (n C : V) : V :=
  (∑ i, selectorCoeff i*rot 67 n C (selectorOffset T i%n)) +
  (∑ j, copyCoeff j*rot 67 n C (copyOffset pos T j%n))

theorem symbolic_kernel_band_cast :
    ((DirectBFSSymbolicKernel.paramKernel rho : ℕ):V) =
      kernelBand (V:=V) position 4393+kernelBand (V:=V) position 5495+TwoBand.bareKernel := by
  have hspatial : ((rho:ℕ):V)^8807*((rho:ℕ):V)^42=Exp.exp ((67:V)*(8849:V)) := by
    rw [←pow_add]
    exact cast_rho_pow (V:=V) 8849
  rw [DirectBFSSymbolicKernel.cast_paramKernel (V:=V) rho,hspatial,bare_formula]
  simp only [cast_rho_pow,kernelBand,selectorCoeff,selectors,copyCoeff,selectorOffset,copyOffset]
  simp only [mul_add,Finset.sum_add_distrib]
  ring_nf

theorem band_rotation_congr (pos : Fin 41 → ℕ) (T : ℕ) (n C : V)
    (hn : 0<n) (hM : 0<Exp.exp (67*n)-1) :
    (kernelBand pos T*C)%(Exp.exp (67*n)-1)=rotatedBand pos T n C%(Exp.exp (67*n)-1) := by
  have hs := kernel_rotation_congr (67:V) n C selectorCoeff (selectorOffset T) hn hM
  have hc := kernel_rotation_congr (67:V) n C copyCoeff (copyOffset pos T) hn hM
  unfold kernelBand rotatedBand
  rw [add_mul,mod_add hM,hs,hc,←mod_add hM]

theorem combined_congr (pos : Fin 41 → ℕ) (K n C w F : V)
    (hn : 0<n) (hM : 0<Exp.exp (67*n)-1)
    (hK : K=kernelBand pos 4393+kernelBand pos 5495+TwoBand.bareKernel)
    (hgraph : ((K+w)*C)%(Exp.exp (67*n)-1)=F) :
    ((rotatedBand pos 4393 n C+rotatedBand pos 5495 n C+TwoBand.bareRotated n C)+w*C)%
      (Exp.exp (67*n)-1)=F := by
  let M : V := Exp.exp (67*n)-1
  have h1 := band_rotation_congr pos 4393 n C hn hM
  have h2 := band_rotation_congr pos 5495 n C hn hM
  have h3 := TwoBand.bare_congr n C hn hM
  have hp : ((kernelBand pos 4393+kernelBand pos 5495+TwoBand.bareKernel)*C)%M=
      (rotatedBand pos 4393 n C+rotatedBand pos 5495 n C+TwoBand.bareRotated n C)%M := by
    rw [add_mul,add_mul]
    exact TwoBand.add_congr_mod M _ _ _ _ hM (TwoBand.add_congr_mod M _ _ _ _ hM h1 h2) h3
  have hr : (((kernelBand pos 4393+kernelBand pos 5495+TwoBand.bareKernel)*C)+w*C)%M=
      ((rotatedBand pos 4393 n C+rotatedBand pos 5495 n C+TwoBand.bareRotated n C)+w*C)%M :=
    TwoBand.add_congr_mod M _ _ _ _ hM hp rfl
  rw [hK,add_mul] at hgraph
  exact hr.symm.trans hgraph

theorem exact_bands (pos : Fin 41 → ℕ) (n C : V) :
    (∑ x : Aligned (Fin 943) (Fin 41),
      (alignedCoeff selectors copies x:V)*rot 67 n C (bandOffsets pos x%n)) =
    rotatedBand pos 4393 n C+rotatedBand pos 5495 n C+TwoBand.bareRotated n C := by
  have h := CompactIndexedFlatten.flatten selectors copies (selectorOffset 4393)
    (selectorOffset 5495) (copyOffset pos 4393) (copyOffset pos 5495)
    TwoBand.bareOffset (fun x => rot 67 n C (x%n))
  simpa only [bandOffsets,rotatedBand,TwoBand.bareRotated,selectorCoeff,copyCoeff,selectors,copies] using h

theorem carry_input (pos : Fin 41 → ℕ) (n C T F : V)
    (hn : 0<n) (hM : 0<Exp.exp (67*n)-1)
    (hC : C<Exp.exp (67*n)) (hCcap : ∀ k<n,dig 67 C k≤3)
    (hT : T<Exp.exp (67*n)) (hTcap : ∀ k<n,dig 67 T k≤Exp.exp 67-1)
    (hF : F<Exp.exp (67*n)-1)
    (hgraph : ((rotatedBand pos 4393 n C+rotatedBand pos 5495 n C+
      TwoBand.bareRotated n C)+T)%(Exp.exp (67*n)-1)=F) :
    CarryInput 67 n F 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
      (GenericBandCarryFamily.coefficient (fun x => (alignedCoeff selectors copies x:V)))
      (GenericBandCarryFamily.word n C (bandOffsets pos) T) := by
  apply GenericBandCarryFamily.carry_input n C T F 1
    (fun x : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies x:V))
    (bandOffsets pos) hn hM hC hCcap hT hTcap hF
  · simpa only [exact_bands] using hgraph
  · exact DirectBFSModelMass.family_mass_b1

#print axioms DirectBFSBandCarry.symbolic_kernel_band_cast
#print axioms DirectBFSBandCarry.combined_congr
#print axioms DirectBFSBandCarry.exact_bands
#print axioms DirectBFSBandCarry.carry_input
end DirectBFSBandCarry
