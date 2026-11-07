import DiophantineConsistency.Sign32ReverseAssembly00

/-! UNCOMPILED bounded reverse residual transfer group. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32ReverseAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem mainRoot_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution03.newmainRoot p) v := by
  have hm : Sign32Substitution03.oldmainRoot p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution03.old_mainRoot_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution03.mainRoot_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem c2_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution03.newc2 p) v := by
  have hm : Sign32Substitution03.oldc2 p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution03.old_c2_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution03.c2_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem Dc2_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution03.newDc2 p) v := by
  have hm : Sign32Substitution03.oldDc2 p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution03.old_Dc2_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution03.Dc2_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem N1_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution04.newN1 p) v := by
  have hm : Sign32Substitution04.oldN1 p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution04.old_N1_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution04.N1_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem gap_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution04.newgap p) v := by
  have hm : Sign32Substitution04.oldgap p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution04.old_gap_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution04.gap_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem tau_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution04.newtau p) v := by
  have hm : Sign32Substitution04.oldtau p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution04.old_tau_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution04.tau_eval p beta v hp0]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem N0_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution05.newN0 p) v := by
  have hm : Sign32Substitution05.oldN0 p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution05.old_N0_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution05.N0_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem Nt_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution05.newNt p) v := by
  have hm : Sign32Substitution05.oldNt p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution05.old_Nt_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution05.Nt_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

end DiophantineConsistency.Sign32ReverseAssembly

#print axioms DiophantineConsistency.Sign32ReverseAssembly.mainRoot_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.c2_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.Dc2_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.N1_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.gap_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.tau_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.N0_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.Nt_zero
