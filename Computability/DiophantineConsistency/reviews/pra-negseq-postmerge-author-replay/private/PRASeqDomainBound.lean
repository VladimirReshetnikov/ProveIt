import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRAUnderMajorantMono
import DiophantineConsistency.PRADomainWitnessBound
/-! Actual sequence graph with a common explicit domain polynomial; mapping remains explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRASeqDomainBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] domainDef isMappingDef

theorem bitMajorant_mono (a b : V) (h : a ≤ b) :
 PRABitFullWitnessBound.bitMajorant a ≤ PRABitFullWitnessBound.bitMajorant b := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  unfold PRABitFullWitnessBound.bitMajorant
  exact add_le_add (add_le_add (PRAUnderMajorantMono.expMajorant_mono a b h) h) le_rfl

theorem negBitMajorant_mono (a b : V) (h : a ≤ b) :
 PRANegBitFullWitnessBound.negBitMajorant a ≤ PRANegBitFullWitnessBound.negBitMajorant b := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have h2 : a^2 ≤ b^2 := pow_le_pow_left₀ zero_le h 2
  have hm : 2*a ≤ 2*b := mul_le_mul_of_nonneg_left h zero_le
  have hm2 : 2*a^2 ≤ 2*b^2 := mul_le_mul_of_nonneg_left h2 zero_le
  unfold PRANegBitFullWitnessBound.negBitMajorant PRANegExponentialWitnessBound.negExponentialMajorant
  exact add_le_add (add_le_add (add_le_add (add_le_add hm le_rfl) (add_le_add hm2 le_rfl)) h) le_rfl

theorem domainMajorant_mono_left (a b s : V) (h : a ≤ b) :
 PRADomainWitnessBound.domainMajorant a s ≤ PRADomainWitnessBound.domainMajorant b s := by
  unfold PRADomainWitnessBound.domainMajorant
  exact add_le_add (add_le_add (add_le_add (add_le_add le_rfl (bitMajorant_mono a b h)) (negBitMajorant_mono a b h)) le_rfl) le_rfl

theorem seq_bound_of_domain (s w : V)
 (hsize : 2*s+1 ≤ w)
 (hunder : PRAExponentialWitnessBound.exponentialMajorant (2*s+1) ≤ w)
 (hdom : PRADomainWitnessBound.domainMajorant (2*s) s ≤ w)
 (hmap : isMappingDef.val.Evalb ![s] → (bnd isMappingDef.val).Evalb ![s,w]) :
 seqDef.val.Evalb ![s] → (bnd seqDef.val).Evalb ![s,w] := by
  apply PRAUnderMajorantMono.seq_bound_of_common_under s w hsize hunder hmap
  intro d l hd hl h
  have hdomEval : domainDef.val.Evalb ![d,s] := by simpa [PRASeqDefWitnessBound.domainInside] using h
  have hb := PRADomainWitnessBound.domain_bound_explicit d s hdomEval
  have hbound : PRADomainWitnessBound.domainMajorant d s ≤ w := le_trans (domainMajorant_mono_left d (2*s) s hd) hdom
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hs : Fin.snoc ![d,s] (PRADomainWitnessBound.domainMajorant d s) = ![d,s,PRADomainWitnessBound.domainMajorant d s] := by
    funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hm := eval_bnd_mono domainDef.val ![d,s] (Empty.elim : Empty → V) hbound (by rw [hs]; exact hb)
  let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#2]
  have hn := PRABndRewriting.natural domainDef.val ω ![d,l,s] w
  have hv : (fun j => (ω #j).val ![d,l,s] Empty.elim) = ![d,s] := by
    funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs' : Fin.snoc ![d,l,s] w = ![d,l,s,w] := by
    funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k; exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs'' : Fin.snoc ![d,s] w = ![d,s,w] := by
    funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  rw [hv,hs',hs''] at hn
  rw [hs''] at hm
  have heq : PRASeqDefWitnessBound.domainInside = ω ▹ domainDef.val := by simp [PRASeqDefWitnessBound.domainInside, ω]
  rw [heq]
  exact hn.mpr hm
noncomputable def seqDomainBody : ArithmeticSemisentence 2 :=
  “s w. 2*s+1 ≤ w ∧
    (((2*s+1)⁴+1)+((2*s+1)²+1)+(2*(2*s+1)²+1)+((2*s+1)⁴+(2*s+1)⁴+2*(2*s+1)+1)) ≤ w ∧
    (s + ((((2*s)⁴+1)+((2*s)²+1)+(2*(2*s)²+1)+((2*s)⁴+(2*s)⁴+2*(2*s)+1))+(2*s)+1) +
      (((2*(2*s)+1)+(2*(2*s)²+1))+(2*s)+1) +
      (((s⁴+1)+(s²+1)+(2*s²+1)+(s⁴+s⁴+2*s+1))+s+1) + (((2*s+1)+(2*s²+1))+s+1)) ≤ w ∧
    (!isMappingDef s → !PRASeqDefWitnessBound.boundedMapping s w) ∧
    !seqDef s → !PRASeqDefWitnessBound.boundedSeq s w”
theorem seqDomainBody_model (e : Fin 2 → V) : seqDomainBody.Eval e Empty.elim := by
  simp [seqDomainBody,PRASeqDefWitnessBound.boundedMapping,PRASeqDefWitnessBound.boundedSeq,Semiformula.eval_substs]
  exact seq_bound_of_domain (e 0) (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def seqDomainSentence : Sentence language := ∀⁰* Semiformula.lMap embedding seqDomainBody
theorem candidate_proves_seq_domain_bound : PRA ⊢ seqDomainSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact seqDomainBody_model e
end DiophantineConsistency.PRASeqDomainBound
