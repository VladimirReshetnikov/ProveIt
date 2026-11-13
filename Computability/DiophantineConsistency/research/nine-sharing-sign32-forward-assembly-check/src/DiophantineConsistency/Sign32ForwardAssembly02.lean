import DiophantineConsistency.Sign32ForwardAssembly01

/-! UNCOMPILED bounded forward residual transfer group. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32ForwardAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem f2_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution05.oldf2 p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution05.newf2 p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution05.new_f2_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution05.f2_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem cTminusR_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution06.oldcTminusR p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution06.newcTminusR p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution06.new_cTminusR_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution06.cTminusR_eval p beta v hp0]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem V_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution06.oldV p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution06.newV p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution06.new_V_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution06.V_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem normalizedS_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution06.oldnormalizedS p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution06.newnormalizedS p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution06.new_normalizedS_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution06.normalizedS_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem normalizedS2_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution07.oldnormalizedS2 p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution07.newnormalizedS2 p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution07.new_normalizedS2_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution07.normalizedS2_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem V2minusY2_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution07.oldV2minusY2 p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution07.newV2minusY2 p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution07.new_V2minusY2_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution07.V2minusY2_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem Na_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution07.oldNa p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution07.newNa p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution07.new_Na_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution07.Na_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

theorem scaledNs_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hn : ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p, InternalZero e v) :
    InternalZero (Sign32Substitution07.oldscaledNs p) (Sign32Substitution00.lift beta v) := by
  have hm : Sign32Substitution07.newscaledNs p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign32Substitution07.new_scaledNs_row p)))
  apply (internalZero_iff _ _).mpr
  rw [Sign32Substitution07.scaledNs_eval p beta v]
  exact (internalZero_iff _ _).mp (hn _ hm)

end DiophantineConsistency.Sign32ForwardAssembly

#print axioms DiophantineConsistency.Sign32ForwardAssembly.f2_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.cTminusR_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.V_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.normalizedS_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.normalizedS2_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.V2minusY2_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.Na_zero
#print axioms DiophantineConsistency.Sign32ForwardAssembly.scaledNs_zero
