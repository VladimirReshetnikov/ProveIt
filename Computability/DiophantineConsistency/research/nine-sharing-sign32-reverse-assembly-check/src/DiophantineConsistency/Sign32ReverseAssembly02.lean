import DiophantineConsistency.Sign32ReverseAssembly01

/-! UNCOMPILED bounded reverse residual transfer group. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32ReverseAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem f2_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution05.newf2 p) v := by
  have hm : Sign32Substitution05.oldf2 p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution05.old_f2_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution05.f2_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem cTminusR_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution06.newcTminusR p) v := by
  have hm : Sign32Substitution06.oldcTminusR p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution06.old_cTminusR_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution06.cTminusR_eval p beta v hp0]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem V_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution06.newV p) v := by
  have hm : Sign32Substitution06.oldV p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution06.old_V_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution06.V_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem normalizedS_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution06.newnormalizedS p) v := by
  have hm : Sign32Substitution06.oldnormalizedS p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution06.old_normalizedS_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution06.normalizedS_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem normalizedS2_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution07.newnormalizedS2 p) v := by
  have hm : Sign32Substitution07.oldnormalizedS2 p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution07.old_normalizedS2_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution07.normalizedS2_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem V2minusY2_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution07.newV2minusY2 p) v := by
  have hm : Sign32Substitution07.oldV2minusY2 p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution07.old_V2minusY2_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution07.V2minusY2_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem Na_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution07.newNa p) v := by
  have hm : Sign32Substitution07.oldNa p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution07.old_Na_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution07.Na_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

theorem scaledNs_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (ho : ∀ e ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p, InternalZero e (Sign32Substitution00.lift beta v)) :
    InternalZero (Sign32Substitution07.newscaledNs p) v := by
  have hm : Sign32Substitution07.oldscaledNs p ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution07.old_scaledNs_row p)))
  apply (internalZero_iff _ _).mpr
  rw [← Sign32Substitution07.scaledNs_eval p beta v]
  exact (internalZero_iff _ _).mp (ho _ hm)

end DiophantineConsistency.Sign32ReverseAssembly

#print axioms DiophantineConsistency.Sign32ReverseAssembly.f2_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.cTminusR_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.V_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.normalizedS_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.normalizedS2_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.V2minusY2_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.Na_zero
#print axioms DiophantineConsistency.Sign32ReverseAssembly.scaledNs_zero
