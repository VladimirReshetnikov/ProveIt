module
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.SourceCommandWordTraversal
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Scheduler.SourceCommandEncodingInternal
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open SourceCantorInternal ActualWordEncodingBlueprint CommandWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem residual_le (raw : V) : residual raw≤raw := by
  unfold residual
  split_ifs
  · exact (decodeValue_bounds raw).2
  · exact le_trans (decodeValue_bounds (decodeRight raw)).2 (decodeValue_bounds raw).2
  · exact le_trans (decodeValue_bounds (decodeRight (decodeRight raw))).2
      (le_trans (decodeValue_bounds (decodeRight raw)).2 (decodeValue_bounds raw).2)

theorem splice_tail_le (atom tail : V) : tail≤spliceValue atom tail := by
  rw [splice_value]
  split_ifs
  · exact (pairValue_bounds _ _).2
  · exact le_trans (pairValue_bounds _ _).2 (pairValue_bounds _ _).2
  · exact le_trans (pairValue_bounds _ _).2
      (le_trans (pairValue_bounds _ _).2 (pairValue_bounds _ _).2)

local instance encode_sigma_bounds : 𝚺ᴬ₁-Function₁ (encodeValue : V→V) := encode_defined.to_definable

theorem encoded_length_le (xs : V) : len xs≤encodeValue xs := by
  induction xs using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin atom xs ih =>
    rw [len_adjoin,encode_adjoin]
    exact add_le_add (le_trans ih (splice_tail_le _ _)) (le_refl 1)

theorem candidate_restore (code : V) :
    ActualCandidateBlueprint.candidateValue code+1=
      encodeValue (CompilerHaltingWord.haltWord code) := by
  unfold ActualCandidateBlueprint.candidateValue CompilerHaltingWord.haltWord
  simp only [encode_adjoin,add_sub_self,ActualCandidateBlueprint.resetAtom,
    ActualCandidateBlueprint.shiftAtom,CompilerHaltingWord.resetAtom,CompilerHaltingWord.shiftAtom,
    Commands.atom]

#print axioms residual_le
#print axioms encoded_length_le
#print axioms candidate_restore
end PA196.Arithmetic.Scheduler.SourceCommandEncodingInternal

