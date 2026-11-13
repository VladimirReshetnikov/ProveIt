import DiophantineConsistency.Compact44.XQ91Model
import DiophantineConsistency.Compact44.QCube92Halt
import DiophantineConsistency.Compact44.FreeJRadixAlignment

/-! Fixed-port positive-existence and halt comparisons for the 91-gate graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJXQ91Halt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 Ordinary12FreeJ
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactSymbolicModelIff CompactBytePortsModelIff
open FreeJQCube92Halt FreeJXQ91 FreeJXQ91Model
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat Nat.ofDigits

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem transform_positive (v : Fin 12 → V) (hv : ∀ i, 0 < v i) :
    ∀ i, 0 < FreeJXQ91Model.transform naturalPorts v i := by
  intro i
  by_cases hi : i = 5
  · subst i
    have hq : 0 < 1 + v 0 * (naturalPorts 0 : V) := by simp
    simpa only [FreeJXQ91Model.transform, Function.update_self] using mul_pos hq (hv 5)
  · simpa [FreeJXQ91Model.transform, hi] using hv i

/-- Every positive 92-graph zero has an internal positive X/q witness. -/
theorem old_X_quotient (v : Fin 12 → V) (hv : ∀ i, 0 < v i)
    (hz : InternalZero (FreeJQCube92.graph p).output v) :
    ∃ w : V, 0 < w ∧ v 5 = (1 + v 0 * (naturalPorts 0 : V))*w := by
  let old : Fin 12 → V := FreeJQCube92Model.transform naturalPorts v
  have holdpos : ∀ i, 0 < old i :=
    FreeJQCube92NamespacedExistence.transform_positive naturalPorts v hv
  have holdzero : InternalZero (literal p) old := by
    have h := (FreeJQCube92Model.zero_iff_transformed naturalPorts v).mp hz
    exact (FreeJSumSquares.zero_iff_literal p old).mp h
  have old0 : old 0 = v 0 := by
    simp [old, FreeJQCube92Model.transform, show (0:Fin 12) ≠ 6 by decide]
  have old5 : old 5 = v 5 := by
    simp [old, FreeJQCube92Model.transform, show (5:Fin 12) ≠ 6 by decide]
  obtain ⟨_,w,_,_,_,_,_,hX,_⟩ :=
    FreeJGraphCongruenceExplore.symbolic_aligned
      CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat old
      (CompactFixedBeta.beta_identity (V:=V)) rfl rfl holdpos holdzero
  change old 5 = (1+old 0*(naturalPorts 0:V))*w at hX
  rw [old0,old5] at hX
  have hwpos : 0<w := by
    by_contra h
    have hw0 : w=0 := le_antisymm (le_of_not_gt h) (Arithmetic.zero_le w)
    rw [hw0,mul_zero] at hX
    exact (ne_of_gt (hv 5)) hX
  exact ⟨w,hwpos,hX⟩

theorem positive_zero_iff :
    (∃ v : Fin 12 → V, (∀ i, 0 < v i) ∧ InternalZero (FreeJXQ91.graph p).output v) ↔
    (∃ v : Fin 12 → V, (∀ i, 0 < v i) ∧ InternalZero (FreeJQCube92.graph p).output v) := by
  constructor
  · rintro ⟨v,hv,hz⟩
    exact ⟨FreeJXQ91Model.transform naturalPorts v, transform_positive v hv,
      (FreeJXQ91Model.zero_iff_transformed naturalPorts v).mp hz⟩
  · rintro ⟨v,hv,hz⟩
    obtain ⟨w,hw,hX⟩ := old_X_quotient v hv hz
    let u : Fin 12 → V := Function.update v 5 w
    have hu : ∀ i, 0 < u i := by
      intro i
      by_cases hi : i = 5
      · subst i; simpa [u] using hw
      · simpa [u,hi] using hv i
    have hu0 : u 0 = v 0 := by simp [u]
    have hu5 : u 5 = w := by simp [u]
    have htrans : FreeJXQ91Model.transform naturalPorts u = v := by
      funext i
      by_cases hi : i = 5
      · subst i
        simp only [FreeJXQ91Model.transform, Function.update_self]
        rw [hu0,hu5]
        exact hX.symm
      · simp [FreeJXQ91Model.transform,u,hi]
    refine ⟨u,hu,?_⟩
    apply (FreeJXQ91Model.zero_iff_transformed naturalPorts u).mpr
    rw [htrans]
    exact hz

theorem positive_model_iff :
    (∃ v : Fin 12 → V, (∀ j, 0 < v j) ∧ InternalZero (FreeJXQ91.graph p).output v) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :=
  (positive_zero_iff (V:=V)).trans (FreeJQCube92Halt.positive_model_iff (V:=V))

theorem shifted_model_iff :
    (∃ x : Fin 12 → V, InternalZero (positiveShift (FreeJXQ91.graph p).output) x) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) := by
  constructor
  · rintro ⟨x,hx⟩
    apply (positive_model_iff (V:=V)).mp
    refine ⟨fun j => x j+1, ?_, ?_⟩
    · intro j; simp
    · exact (internalZero_positiveShift _ x).mp hx
  · intro hh
    obtain ⟨v,hpos,hzero⟩ := (positive_model_iff (V:=V)).mpr hh
    let x : Fin 12 → V := fun j => v j-1
    have hx : (fun j => x j+1)=v := by
      funext j
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hpos j))
    refine ⟨x,?_⟩
    rw [internalZero_positiveShift, hx]
    exact hzero

theorem shifted_byte_model_iff :
    (∃ x : Fin 12 → V, InternalZero (positiveShift (FreeJXQ91.graph byteP).output) x) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) := by
  rw [byteP_eq]
  exact shifted_model_iff (V:=V)

#print axioms FreeJXQ91Halt.old_X_quotient
#print axioms FreeJXQ91Halt.positive_zero_iff
#print axioms FreeJXQ91Halt.positive_model_iff
#print axioms FreeJXQ91Halt.shifted_model_iff
#print axioms FreeJXQ91Halt.shifted_byte_model_iff
end FreeJXQ91Halt
