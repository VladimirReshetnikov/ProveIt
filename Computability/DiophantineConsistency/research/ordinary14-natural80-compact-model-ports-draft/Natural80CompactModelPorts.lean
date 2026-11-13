import CompactPortBoundsSlim
import StrictK0Symbolic
import DiophantineConsistency.Compact44.CompactConcreteMask
import DiophantineConsistency.Compact44.CompactSymbolicModelIff
import DiophantineConsistency.ArithmeticStandardCasts
import DiophantineConsistency.ModelDifferenceRing

/-! Source-only proposal for representing and bounding the compact symbolic
ports in an IΣ₁ model. All imports and proof scripts are unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Natural80CompactModelPortsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open ArithmeticWindowDigits ModelDifferenceRing
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Same four natural symbolic ports as the compact graph. -/
def naturalPorts : Fin 4 → ℕ :=
  ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat

def modelPorts (j : Fin 4) : V := (naturalPorts j : V)

/-- The signed symbolic port is represented by the corresponding model port. -/
theorem port_representation (j : Fin 4) :
    (CompactSymbolicModelIff.p j : DiffRing V) = ι (modelPorts (V:=V) j) := by
  change (((naturalPorts j : ℕ) : ℤ) : DiffRing V) = ι ((naturalPorts j : ℕ) : V)
  simp only [Int.cast_natCast, map_natCast]

/-- The nonzero low digit proves MC positive without evaluating its numeral. -/
theorem low_model_pos : 0 < (lowNat : V) := by
  have h4 : (4 : V) = Exp.exp (2 : V) := by
    have h := ArithmeticStandardCasts.cast_exp (V:=V) 2
    norm_num at h
    exact h.symm
  have hpow : (4 : V) ≤ Exp.exp (67 : V) := by
    rw [h4]
    exact exp_monotone_le.mpr (by norm_num)
  have htwo : (2 : V) < Exp.exp (67 : V) :=
    lt_of_lt_of_le (by norm_num : (2 : V) < 4) hpow
  have horigin : dig (67 : V) (lowNat : V) 0 = Exp.exp (67 : V) - 2 := by
    exact CompactConcreteMask.model_origin (V:=V)
  have hpositive : 0 < dig (67 : V) (lowNat : V) 0 := by
    rw [horigin]
    exact tsub_pos_iff_lt.mpr htwo
  have hnonzero : (lowNat : V) ≠ 0 := by
    intro hz
    have hzero : dig (67 : V) (lowNat : V) 0 = 0 := by
      rw [hz]
      simp [ArithmeticWindowDigits.dig]
    exact (ne_of_gt hpositive) hzero
  exact pos_iff_ne_zero.mpr hnonzero

/-- Proposed model bounds for beta, K0, MC and the already-shifted MF. -/
theorem port_bounds :
    0 < modelPorts (V:=V) 0 ∧ (46 : V) ≤ modelPorts (V:=V) 0 ∧
    0 < modelPorts (V:=V) 1 ∧ 0 < modelPorts (V:=V) 2 ∧
    modelPorts (V:=V) 2 < modelPorts (V:=V) 0 ∧
    0 < modelPorts (V:=V) 3 ∧
    modelPorts (V:=V) 3 < 2 * modelPorts (V:=V) 0 := by
  have h := CompactPortBoundsSlimDraft.port_bounds (V:=V)
    CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    CompactFixedBeta.beta_identity rfl rfl
  change 0 < modelPorts (V:=V) 0 ∧
    modelPorts (V:=V) 2 < modelPorts (V:=V) 0 ∧
    modelPorts (V:=V) 3 < 2 * modelPorts (V:=V) 0 ∧
    (46 : V) ≤ modelPorts (V:=V) 0 at h
  have hK : 0 < modelPorts (V:=V) 1 := by
    change 0 < (paramKernel rho : V)
    exact StrictK0SymbolicDraft.kernel_model_pos (V:=V)
  have hMC : 0 < modelPorts (V:=V) 2 := by
    change 0 < (lowNat : V)
    exact low_model_pos (V:=V)
  have hbeta : 0 < (CompactFixedBeta.betaNat : V) := by
    change 0 < modelPorts (V:=V) 0
    exact h.1
  have hMF : 0 < modelPorts (V:=V) 3 := by
    change 0 < ((CompactFixedBeta.betaNat + highNat : ℕ) : V)
    rw [Nat.cast_add]
    exact add_pos_of_pos_of_nonneg hbeta (by simp)
  exact ⟨h.1, h.2.2.2, hK, hMC, h.2.1, hMF, h.2.2.1⟩

end DiophantineConsistency.Natural80CompactModelPortsDraft

#print axioms DiophantineConsistency.Natural80CompactModelPortsDraft.port_representation
#print axioms DiophantineConsistency.Natural80CompactModelPortsDraft.low_model_pos
#print axioms DiophantineConsistency.Natural80CompactModelPortsDraft.port_bounds
