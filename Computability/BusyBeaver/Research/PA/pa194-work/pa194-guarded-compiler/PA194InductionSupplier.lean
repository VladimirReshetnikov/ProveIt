import PA194InductionWiring
import PA194PAeqClosedInduction
import PA194PAeqOpeningFormulaInverse
import PA194ClosedSentenceEnvironment
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The induction supplier in the form used by the arithmetic development

`induction_supplier`: for every internal formula `p` of arity one, the source theory proves
the translation, at `rootParameters`, of the fully closed induction axiom
`closedInduction p` of `pa194-model-logic`. This is the hypothesis `hind` of
`refutation_of_remaining` there, for an arbitrary source theory `T`, from the term facts,
the twelve source facts, ordinal induction of the source theory for every internal property,
and inhabitation of the domain.

It instantiates `induction_closed_provable` with `close` and `bindFormula 0`
(`bindFormula_scope_open`), uses that the fully closed axiom is invariant under shift
(`closedInduction_sentence`), and moves from the identity packet to `rootParameters` with
`sentence_root_packet`.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher PA194Schematic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : Theory SourceL} [T.Δ₁]

/-- The induction body of the arithmetic development is `indBody`. -/
theorem inductionBody_eq (p : V) : PA194PAeqBind.inductionBody p = indBody p := rfl

theorem closedInduction_tr_provable (F : TermFacts (V := V) T) (S : SourceFacts (V := V) T)
    (hInd : ∀ q : V, IsSemiformula SourceL 1 q → Provable T (indCode q))
    (hdom : Provable T (^∃ (domainCode (^#(0 : V))))) {p : V}
    (hp : IsSemiformula PA194PAeq.language 1 p) :
    Provable T (tr (PA194PAeqBind.closedInduction p)) := by
  have hs : shift PA194PAeq.language
      (PA194PAeqBind.close (PA194PAeqBind.formulaFreeBound (indBody p)) (indBody p)) =
      PA194PAeqBind.close (PA194PAeqBind.formulaFreeBound (indBody p)) (indBody p) :=
    (PA194PAeqBind.closedInduction_sentence hp).2
  have hB : ∀ φ : V, IsSemiformula PA194PAeq.language 0 φ →
      IsSemiformula PA194PAeq.language 1 (PA194PAeqBind.bindFormula 0 φ) ∧
        free PA194PAeq.language (PA194PAeqBind.bindFormula 0 φ) = φ :=
    fun φ hφ => PA194PAeq.OpeningQVec.bindFormula_scope_open φ hφ
  have hsucc : ∀ n φ : V, PA194PAeqBind.close (n+1) φ =
      ^∀ (PA194PAeqBind.bindFormula 0 (PA194PAeqBind.close n φ)) := fun n φ => by
    rw [PA194PAeqBind.close_succ]
    rfl
  exact induction_closed_provable (cl := PA194PAeqBind.close) (B := PA194PAeqBind.bindFormula 0)
    PA194PAeqBind.close_defined.to_definable PA194PAeqBind.close_zero hsucc hB F S hInd hdom hp
    (PA194PAeqBind.formulaFreeBound (indBody p)) hs

/-- The induction supplier at `rootParameters`. -/
theorem induction_supplier (F : TermFacts (V := V) T) (S : SourceFacts (V := V) T)
    (hInd : ∀ q : V, IsSemiformula SourceL 1 q → Provable T (indCode q))
    (hdom : Provable T (^∃ (domainCode (^#(0 : V))))) (p : V)
    (hp : IsSemiformula PA194PAeq.language 1 p) :
    Provable T (translateFormula (rootParameters (PA194PAeqBind.closedInduction p))
      (PA194PAeqBind.closedInduction p)) := by
  have hc := PA194PAeqBind.closedInduction_sentence hp
  rw [PA194ClosedEnvironment.sentence_root_packet hc.1.isUFormula hc.2
    (param := idParam (PA194PAeqBind.closedInduction p + 1)) (idParam_identity _).1]
  exact closedInduction_tr_provable F S hInd hdom hp

#print axioms inductionBody_eq
#print axioms closedInduction_tr_provable
#print axioms induction_supplier
end generic
end PA194GuardedCompiler
