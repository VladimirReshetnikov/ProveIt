import DiophantineConsistency.Sign32ForwardAssembly00

/-! UNCOMPILED bounded forward residual transfer group. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32ForwardAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem mainRoot_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution03.oldmainRoot p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution03.newmainRoot p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution03.new_mainRoot_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution03.mainRoot_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem c2_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution03.oldc2 p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution03.newc2 p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution03.new_c2_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution03.c2_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem Dc2_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution03.oldDc2 p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution03.newDc2 p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution03.new_Dc2_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution03.Dc2_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem N1_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution04.oldN1 p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution04.newN1 p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution04.new_N1_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution04.N1_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem gap_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution04.oldgap p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution04.newgap p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution04.new_gap_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution04.gap_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem tau_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution04.oldtau p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution04.newtau p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution04.new_tau_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution04.tau_eval p beta v hp0]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem N0_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution05.oldN0 p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution05.newN0 p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution05.new_N0_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution05.N0_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem Nt_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution05.oldNt p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution05.newNt p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution05.new_Nt_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution05.Nt_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

end DiophantineConsistency.Sign32ForwardAssembly

#print axioms DiophantineConsistency.Sign32ForwardAssembly.mainRoot_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.c2_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.Dc2_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.N1_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.gap_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.tau_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.N0_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.Nt_zero
