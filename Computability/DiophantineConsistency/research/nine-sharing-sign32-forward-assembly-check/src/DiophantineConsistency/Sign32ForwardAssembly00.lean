import DiophantineConsistency.Sign32Substitution07

/-! UNCOMPILED bounded forward residual transfer group. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32ForwardAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem q3_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution00.oldQ3 p) (Sign32Substitution00.lift beta v) := by
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution00.old_q3_eval p beta v hp0]
  exact (internalZero_iff _ _).mp (hn _ List.mem_cons_self)

theorem X_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution01.oldX p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution01.newX p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution01.new_X_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution01.X_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem Y_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution01.oldY p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution01.newY p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution01.new_Y_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution01.Y_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem E_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution01.oldE p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution01.newE p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution01.new_E_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution01.E_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem kY_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution02.oldkY p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution02.newkY p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution02.new_kY_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution02.kY_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem ell_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution02.oldell p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution02.newell p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution02.new_ell_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution02.ell_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem Delta_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution02.oldDelta p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution02.newDelta p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution02.new_Delta_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution02.Delta_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

end DiophantineConsistency.Sign32ForwardAssembly

#print axioms DiophantineConsistency.Sign32ForwardAssembly.q3_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.X_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.Y_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.E_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.kY_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.ell_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.Delta_zero
