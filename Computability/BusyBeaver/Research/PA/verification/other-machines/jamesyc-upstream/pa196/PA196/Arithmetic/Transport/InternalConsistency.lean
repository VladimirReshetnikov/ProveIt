module
public import PA196.Arithmetic.Transport.FoundationNativeRefutationTransport
public import PA196.Arithmetic.NoRefutation
public import M6PA.Calibration.Foundation
@[expose] public section
open M6.PA
namespace PA196.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- A PA theorem about its own proof predicate. No standardness premise is
used in the all-model argument establishing this syntactic PA proof. -/
theorem pa_proves_no_refutation_consistency :
    theory ⊢ noRefutationSentence 🡒 M6.PA.consistencySentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [models_iff,LogicalConnective.HomClass.map_imply]
  intro hn
  have hno := noRefutation_correct (V:=V) |>.mp hn
  have hc : theory.Consistent V := by
    intro hp
    have hp' : Provable theory (qqFalsum:V) := by
      simpa only [Sentence.quote_falsum] using hp
    obtain ⟨code,hcode⟩ :=
      Transport.FoundationNativeRefutationTransport.original_provable_refutation_transport hp'
    exact hno code hcode
  simpa [M6.PA.consistencySentence,ProvabilityAbstraction.Provability.con,
    ProvabilityAbstraction.Provability.pr,Theory.Consistent] using hc

#print axioms pa_proves_no_refutation_consistency
end PA196.Arithmetic
