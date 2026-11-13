import DiophantineConsistency.SharingSeed38
import DiophantineConsistency.CurrentKernelData2011

/-! Fixed-current-port Jones correspondence only. The seed/current-equation
bridge and iPRA consistency endpoint are separate obligations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed38CurrentJones
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.radix CurrentMasks2011.lowPort CurrentMasks2011.highPort

theorem current_beta_positive : (0 : ℤ) < CurrentWindowCarry2011.ports 0 := by
  have hr : 1 < CurrentMasks2011.radix ^ 2011 :=
    one_lt_pow₀ (by decide : 1 < CurrentMasks2011.radix) (by decide)
  have hb : 0 < CurrentMasks2011.beta := by unfold CurrentMasks2011.beta; omega
  change (0 : ℤ) < (CurrentMasks2011.beta : ℤ)
  exact_mod_cast hb

theorem current_degree :
    (SharingSeed38.seed CurrentWindowCarry2011.ports).toPolynomial.totalDegree ≤ 4 :=
  SharingSeed38.seed_degree _

theorem current_normalized :
    (SharingSeed38.seed CurrentWindowCarry2011.ports).eval
      (fun j : Fin 39 => if j = 0 then (1 : ℤ) else 0) ≠ 0 := by
  exact SharingSeed38.seed_normalized _ current_beta_positive 1

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem current_nine_iff :
    (∃ a : Fin 9 → V,
      (ExecutableJones.expression (SharingSeed38.seed CurrentWindowCarry2011.ports) 0).evalRing
        (fun i => ι (a i)) = 0) ↔
    ∃ w : Fin 38 → V,
      (SharingSeed38.seed CurrentWindowCarry2011.ports).evalRing
        (fun j => ι ((Fin.cons (1 : V) w : Fin 39 → V) j)) = 0 :=
  NineFreshJones.nine_iff _ current_degree current_normalized

end DiophantineConsistency.SharingSeed38CurrentJones
#print axioms DiophantineConsistency.SharingSeed38CurrentJones.current_beta_positive
#print axioms DiophantineConsistency.SharingSeed38CurrentJones.current_degree
#print axioms DiophantineConsistency.SharingSeed38CurrentJones.current_normalized
#print axioms DiophantineConsistency.SharingSeed38CurrentJones.current_nine_iff
