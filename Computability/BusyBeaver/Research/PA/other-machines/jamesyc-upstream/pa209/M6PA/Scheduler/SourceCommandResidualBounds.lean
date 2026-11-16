module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.SourceCommandWordTraversal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.SourceCommandEncodingInternal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open SourceCantorInternal ActualWordEncodingBlueprint ActualCommandWordGraph
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
      encodeValue (ActualCompilerHaltingWord.haltWord code) := by
  unfold ActualCandidateBlueprint.candidateValue ActualCompilerHaltingWord.haltWord
  rw [encode_adjoin]
  simp only [add_sub_self]

#print axioms residual_le
#print axioms encoded_length_le
#print axioms candidate_restore
end M6.PA.SourceCommandEncodingInternal

