import DiophantineConsistency.Sign32CoordinateReconstruct

/-! UNCOMPILED bounded reverse residual transfer group. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32ReverseAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem q3_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (SharingSeed32Sextic.firstResidual p) v := by
  have hm : Sign32Substitution00.oldQ3 p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_head? (Sign32Substitution00.old_q3_head p))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution00.old_q3_eval p beta v hp0]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem X_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution01.newX p) v := by
  have hm : Sign32Substitution01.oldX p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution01.old_X_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution01.X_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem Y_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution01.newY p) v := by
  have hm : Sign32Substitution01.oldY p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution01.old_Y_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution01.Y_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem E_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution01.newE p) v := by
  have hm : Sign32Substitution01.oldE p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution01.old_E_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution01.E_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem kY_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution02.newkY p) v := by
  have hm : Sign32Substitution02.oldkY p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution02.old_kY_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution02.kY_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem ell_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution02.newell p) v := by
  have hm : Sign32Substitution02.oldell p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution02.old_ell_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution02.ell_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem Delta_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution02.newDelta p) v := by
  have hm : Sign32Substitution02.oldDelta p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution02.old_Delta_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution02.Delta_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

end DiophantineConsistency.Sign32ReverseAssembly

#print axioms DiophantineConsistency.Sign32ReverseAssembly.q3_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.X_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.Y_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.E_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.kY_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.ell_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.Delta_zero
