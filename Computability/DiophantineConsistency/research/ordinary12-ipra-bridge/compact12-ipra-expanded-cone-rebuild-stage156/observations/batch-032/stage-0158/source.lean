import DiophantineConsistency.FoundationHACurrentNoZero2011
import DiophantineConsistency.ArithmeticSignedPairs

/-! The semantics of the literal current no-zero sentence in every model of IΣ1.
`classicalSentence` holds in `V` iff the split natural polynomial has no zero
in `V`, equivalently iff the original current polynomial has no zero with all
fourteen coordinates positive (the maintained single positive shift). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticCurrentSentence2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.PA FoundationHANoZero ObjectCurrentEquation2011 ArithmeticSignedPairs
attribute [local irreducible] expression naturalExpression
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem val_reflectTerm {n : ℕ} (v : ℕ → Semiterm ℒₒᵣ Empty n) (b : Fin n → V) (t : Term) :
    (reflectTerm v t).val b Empty.elim =
      Term.eval (ArithmeticExpression.semiringStructure V)
        (fun i => (v i).val b Empty.elim) t := by
  induction t with
  | var i => rfl
  | zero => rfl
  | succ t ih => exact congrArg (· + 1) ih
  | add s t ihs iht => exact congrArg₂ (· + ·) ihs iht
  | mul s t ihs iht => exact congrArg₂ (· * ·) ihs iht

theorem val_sourceTerm {n : ℕ} (e : NatExpr (Fin n)) (b : Fin n → V) :
    (sourceTerm n (ArithmeticExpression.term Fin.val e)).val b Empty.elim =
      e.evalSemiring b := by
  unfold sourceTerm
  rw [val_reflectTerm, ArithmeticExpression.eval_term]
  congr 1
  funext i
  simp [slot, i.isLt]

/-- **The literal sentence is the absence of a natural zero.** -/
theorem classicalSentence_iff_natural :
    FoundationHACurrentNoZero2011.classicalSentence.Evalb (M := V) ![] ↔
      ¬∃ v : Fin 14 → V, naturalExpression.splitNatural.1.evalSemiring v =
        naturalExpression.splitNatural.2.evalSemiring v := by
  unfold FoundationHACurrentNoZero2011.classicalSentence classicalNoZero
  simp only [Semiformula.eval_allClosure, Semiformula.eval_nrel, not_exists]
  refine forall_congr' fun e => ?_
  change ¬ ((sourceTerm 14 _).val e Empty.elim = (sourceTerm 14 _).val e Empty.elim) ↔ _
  rw [val_sourceTerm, val_sourceTerm]

/-! ### The positive shift -/

/-- A natural zero at `v` is exactly a zero of the original polynomial at `v+1`. -/
theorem natural_zero_iff (v : Fin 14 → V) :
    naturalExpression.splitNatural.1.evalSemiring v =
        naturalExpression.splitNatural.2.evalSemiring v ↔
      expression.splitNatural.1.evalSemiring (fun j => v j + 1) =
        expression.splitNatural.2.evalSemiring (fun j => v j + 1) := by
  unfold naturalExpression
  exact internalZero_positiveShift expression v

/-- A positive zero of the original polynomial. -/
def PositiveZero (u : Fin 14 → V) : Prop :=
  (∀ j, 0 < u j) ∧
    expression.splitNatural.1.evalSemiring u = expression.splitNatural.2.evalSemiring u

/-- **The literal sentence is the absence of a positive zero.** -/
theorem classicalSentence_iff :
    FoundationHACurrentNoZero2011.classicalSentence.Evalb (M := V) ![] ↔
      ¬∃ u : Fin 14 → V, PositiveZero u := by
  rw [classicalSentence_iff_natural]
  refine not_congr ⟨fun ⟨v, hv⟩ => ⟨fun j => v j + 1,
    fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _), (natural_zero_iff v).mp hv⟩,
    fun ⟨u, hu, hz⟩ => ⟨fun j => u j - 1, (natural_zero_iff _).mpr ?_⟩⟩
  have hu' : (fun j => u j - 1 + 1) = u :=
    funext fun j => tsub_add_cancel_of_le (pos_iff_one_le.mp (hu j))
  rw [hu']
  exact hz

end DiophantineConsistency.ArithmeticCurrentSentence2011
