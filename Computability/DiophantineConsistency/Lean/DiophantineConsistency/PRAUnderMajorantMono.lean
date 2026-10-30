import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRASeqDefWitnessBound
set_option autoImplicit false
namespace DiophantineConsistency.PRAUnderMajorantMono
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem expMajorant_mono (a b : V) (h : a ≤ b) :
 PRAExponentialWitnessBound.exponentialMajorant a ≤ PRAExponentialWitnessBound.exponentialMajorant b := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have h2 : a^2 ≤ b^2 := pow_le_pow_left₀ zero_le h 2
  have h4 : a^4 ≤ b^4 := pow_le_pow_left₀ zero_le h 4
  have hmul2 : 2*a^2 ≤ 2*b^2 := mul_le_mul_of_nonneg_left h2 zero_le
  have hmul : 2*a ≤ 2*b := mul_le_mul_of_nonneg_left h zero_le
  unfold PRAExponentialWitnessBound.exponentialMajorant
  exact add_le_add (add_le_add (add_le_add (add_le_add h4 le_rfl) (add_le_add h2 le_rfl)) (add_le_add hmul2 le_rfl))
    (add_le_add (add_le_add (add_le_add h4 h4) hmul) le_rfl)
theorem seq_bound_of_common_under (s w : V)
 (hsize : 2*s+1 ≤ w)
 (hunderSize : PRAExponentialWitnessBound.exponentialMajorant (2*s+1) ≤ w)
 (hmap : isMappingDef.val.Evalb ![s] → (bnd isMappingDef.val).Evalb ![s,w])
 (hdom : ∀ d l, d ≤ 2*s → l ≤ 2*s → PRASeqDefWitnessBound.domainInside.Evalb ![d,l,s] →
   (bnd PRASeqDefWitnessBound.domainInside).Evalb ![d,l,s,w]) :
 seqDef.val.Evalb ![s] → (bnd seqDef.val).Evalb ![s,w] := by
  apply PRASeqDefWitnessBound.seq_bound_of_components s w hsize ?_ hmap hdom
  intro d hd
  have hadd : d+1 ≤ 2*s+1 := by simpa [add_comm] using add_le_add_right hd 1
  exact le_trans (expMajorant_mono (d+1) (2*s+1) hadd) hunderSize
noncomputable def seqCommonBody : ArithmeticSemisentence 2 :=
  “s w. 2*s+1 ≤ w ∧
    (((2*s+1)⁴+1)+((2*s+1)²+1)+(2*(2*s+1)²+1)+((2*s+1)⁴+(2*s+1)⁴+2*(2*s+1)+1)) ≤ w ∧
    (!isMappingDef s → !PRASeqDefWitnessBound.boundedMapping s w) ∧
    (∀ d <⁺ 2*s, ∀ l <⁺ 2*s, !PRASeqDefWitnessBound.domainInside d l s → !PRASeqDefWitnessBound.boundedDomain d l s w) ∧
    !seqDef s → !PRASeqDefWitnessBound.boundedSeq s w”
theorem seqCommonBody_model (e : Fin 2 → V) : seqCommonBody.Eval e Empty.elim := by
  simp [seqCommonBody,PRASeqDefWitnessBound.boundedMapping,PRASeqDefWitnessBound.boundedDomain,
    PRASeqDefWitnessBound.boundedSeq,Semiformula.eval_substs]
  intro hs hu hm hd hseq
  apply seq_bound_of_common_under (e 0) (e 1) hs hu hm ?_ hseq
  intro d l hd' hl' h
  exact hd d hd' l hl' h
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def seqCommonSentence : Sentence language := ∀⁰* Semiformula.lMap embedding seqCommonBody
theorem candidate_proves_seq_common_bound : PRA ⊢ seqCommonSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact seqCommonBody_model e
end DiophantineConsistency.PRAUnderMajorantMono
