module
public import M6PA.Theory
public import M6PA.Calibration.FoundationNativeRefutationTransport
@[expose] public section
namespace M6.PA.FoundationNativeRefutationTransport
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint
attribute [local irreducible] verifyGraph
noncomputable def originalRefutationSentence:ArithmeticSentence:=
  “∀ d bot, !qqFalsumDef bot → !((proof theory).sigma) d bot → ∃code, !verifyGraph 2 code”
theorem pa_proves_original_refutation_transport:theory ⊢ originalRefutationSentence:=by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [originalRefutationSentence,models_iff,verify_graph,Matrix.comp_vecCons'']
  intro d hd
  simpa only [eq_comm] using original_refutation_transport d hd
#print axioms pa_proves_original_refutation_transport
end M6.PA.FoundationNativeRefutationTransport

