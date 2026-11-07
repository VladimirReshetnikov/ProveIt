import DiophantineConsistency.SharingSeed33Degree
import DiophantineConsistency.SharingSeed33Normalize
import DiophantineConsistency.SharingSeed38CurrentJones

/-! Fixed-current-port Jones correspondence; no current source bridge or endpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed33CurrentJones
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing

theorem current_beta_positive : (0 : ℤ) < CurrentWindowCarry2011.ports 0 :=
  SharingSeed38CurrentJones.current_beta_positive

theorem current_degree :
    (SharingSeed33.seed CurrentWindowCarry2011.ports).toPolynomial.totalDegree ≤ 4 :=
  SharingSeed33.seed_degree _

theorem current_normalized :
    (SharingSeed33.seed CurrentWindowCarry2011.ports).eval
      (fun j : Fin 34 => if j = 0 then (1 : ℤ) else 0) ≠ 0 := by
  exact SharingSeed33.seed_normalized _ current_beta_positive 1

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem current_nine_iff :
    (∃ a : Fin 9 → V,
      (ExecutableJones.expression (SharingSeed33.seed CurrentWindowCarry2011.ports) 0).evalRing
        (fun i => ι (a i)) = 0) ↔
    ∃ w : Fin 33 → V,
      (SharingSeed33.seed CurrentWindowCarry2011.ports).evalRing
        (fun j => ι ((Fin.cons (1 : V) w : Fin 34 → V) j)) = 0 :=
  NineFreshJones.nine_iff _ current_degree current_normalized
end DiophantineConsistency.SharingSeed33CurrentJones
#print axioms DiophantineConsistency.SharingSeed33CurrentJones.current_beta_positive
#print axioms DiophantineConsistency.SharingSeed33CurrentJones.current_degree
#print axioms DiophantineConsistency.SharingSeed33CurrentJones.current_normalized
#print axioms DiophantineConsistency.SharingSeed33CurrentJones.current_nine_iff
