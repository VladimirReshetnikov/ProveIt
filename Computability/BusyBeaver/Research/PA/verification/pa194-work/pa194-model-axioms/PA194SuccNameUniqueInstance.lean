import PA194SuccNameUniqueSchematic
import PA194NameForms
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194SuccUniqueSchematic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping PA194Schematic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher PA194GuardedCompiler
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Instantiate the predicate letters with the internal term-value, ordinal-isomorphism,
    and domain-guarded successor formulas. The isomorphism is guarded on both arguments. -/
noncomputable def sourcePredicates (s : V) (hs : IsSemiterm PA194PAeq.language 0 s) :
    (i : Pred) → Bootstrapping.Semiformula V SourceL (arity i)
  | .value => ⟨valBody s, by simpa [arity] using valBody_valid hs⟩
  | .equiv => ⟨domainCode (^#(0 : V)) ^⋏ (domainCode (^#(1 : V)) ^⋏ orderIsoCode (^#(0 : V)) (^#(1 : V))), by
      apply IsSemiformula.and.mpr
      refine ⟨domainCode_valid (by simp [arity]),IsSemiformula.and.mpr ⟨domainCode_valid (by simp [arity]),?_⟩⟩
      unfold orderIsoCode
      apply templateTwo_valid orderIsoTemplate <;> simp [arity]⟩
  | .succ => ⟨domainCode (^#(1 : V)) ^⋏ successorCode (^#(0 : V)) (^#(1 : V)), by
      exact IsSemiformula.and.mpr ⟨domainCode_valid (by simp [arity]),successorCode_valid (by simp [arity]) (by simp [arity])⟩⟩

/-- The corresponding logical implication is provable, uniformly for every internal term. -/
theorem sourceInstance_provable (s : V) (hs : IsSemiterm PA194PAeq.language 0 s)
    (T : Theory SourceL) [T.Δ₁] :
    T.internalize V ⊢ PA194Schematic.instS (sourcePredicates s hs) namingSchema :=
  namingCertificate (sourcePredicates s hs) T

#print axioms sourceInstance_provable
end generic
end PA194SuccUniqueSchematic
