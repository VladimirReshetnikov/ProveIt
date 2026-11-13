module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.SourceEnumerationSuffix
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Scheduler.SourceCommandEncodingInternal
open PA196.Arithmetic.Scheduler.ActualCandidateBlueprint PA196.Arithmetic.Scheduler.ActualWordEncodingBlueprint
open M6.PA.SourceCantorInternal PA196.Arithmetic.CommandStep

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
/-- The reset atom has tag2, so the universal refuting candidate is not one of
those skipped by the actual N=2 startup. This is true in every PA model. -/
theorem candidate_ge_two (code : V) : (2 : V)≤candidateValue code := by
  have hr : decodeLeft (resetAtom : V)=2 := by
    have ha : (resetAtom : V)=axCode 0 0 0 := by
      simpa only [resetAtom,Nat.cast_zero] using
        PA196.Arithmetic.LiteralWords.ax_atom_numeral (V := V) 0 0 0
    rw [ha]
    simp only [axCode,PA196.Arithmetic.CommandStep.source_left_pair,zero_add]
  have h := (decodeValue_bounds (spliceValue (resetAtom : V)
    (encodeValue (concat (PA196.Arithmetic.Compiler.compiledValue code) (shiftAtom : V))))).1
  rw [splice_tag,hr] at h
  simpa only [candidateValue,encode_adjoin,add_tsub_cancel_right] using h

end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
