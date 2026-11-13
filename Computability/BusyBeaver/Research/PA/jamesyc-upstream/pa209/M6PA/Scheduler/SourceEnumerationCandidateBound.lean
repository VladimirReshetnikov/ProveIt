module
public import M6PA.Scheduler.SourceEnumerationSuffix
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open M6.PA.SourceCommandEncodingInternal
open M6.PA.ActualCandidateBlueprint M6.PA.ActualWordEncodingBlueprint
open M6.PA.SourceCantorInternal M6.PA.ActualCommandStepGraph

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
/-- The reset atom has tag2, so the universal refuting candidate is not one of
those skipped by the actual N=2 startup. This is true in every PA model. -/
theorem candidate_ge_two (code : V) : (2 : V)≤candidateValue code := by
  have hr : decodeLeft (resetAtom : V)=2 := by
    have ha : (resetAtom : V)=axCode 0 0 0 := by
      simpa only [resetAtom,Nat.cast_zero] using
        M6.PA.ActualCommandLiteralInternal.ax_atom_numeral (V := V) 0 0 0
    rw [ha]
    simp only [axCode,M6.PA.ActualCommandStepGraph.source_left_pair,zero_add]
  have h := (decodeValue_bounds (spliceValue (resetAtom : V)
    (encodeValue (concat (M6.PA.ActualCompilerBlueprint.compiledValue code) (shiftAtom : V))))).1
  rw [splice_tag,hr] at h
  simpa only [candidateValue,encode_adjoin,add_tsub_cancel_right] using h

end M6.Arithmetic.PA.InternalTrace.CodedSource
