import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRANegMappingWitnessBound
import DiophantineConsistency.PRANegUnderWitnessBound
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegSeqDefWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] underDef domainDef isMappingDef
theorem negExpMajorant_mono (a b : V) (h : a ≤ b) :
 PRANegExponentialWitnessBound.negExponentialMajorant a ≤ PRANegExponentialWitnessBound.negExponentialMajorant b := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have h2 : a^2 ≤ b^2 := pow_le_pow_left₀ zero_le h 2
  have hm : 2*a ≤ 2*b := mul_le_mul_of_nonneg_left h zero_le
  have hm2 : 2*a^2 ≤ 2*b^2 := mul_le_mul_of_nonneg_left h2 zero_le
  unfold PRANegExponentialWitnessBound.negExponentialMajorant
  exact add_le_add (add_le_add hm le_rfl) (add_le_add hm2 le_rfl)

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem bnd_neg_rew3 (φ : ArithmeticSemisentence 2) (ω : Rew ℒₒᵣ Empty 2 Empty 3)
 (d l s w a b : V)
 (hv : (fun j => (ω #j).val ![d,l,s] Empty.elim) = ![a,b])
 (h : (bnd (∼φ)).Evalb ![a,b,w]) : (bnd (∼(ω ▹ φ))).Evalb ![d,l,s,w] := by
  have hn := PRABndRewriting.natural (∼φ) ω ![d,l,s] w
  have hs : Fin.snoc ![d,l,s] w = ![d,l,s,w] := by simp
  have hs' : Fin.snoc ![a,b] w = ![a,b,w] := by simp
  rw [hv,hs,hs'] at hn
  have hh := hn.mpr h
  have heq : (ω ▹ (∼φ)) = ∼(ω ▹ φ) := by
    exact LogicalConnective.HomClass.map_neg (Semiformula.rew ω) φ
  rw [heq] at hh
  exact hh
 theorem neg_seq_bound (s w : V)
 (hmap : PRANegMappingWitnessBound.negMappingMajorant s ≤ w)
 (hdom : PRANegDomainWitnessBound.negDomainMajorant (2*s) s ≤ w)
 (hunder : PRANegExponentialWitnessBound.negExponentialMajorant (2*s+1) ≤ w) :
 (∼seqDef.val).Evalb ![s] → (bnd (∼seqDef.val)).Evalb ![s,w] := by
  intro h
  simp [seqDef,Semiformula.bexsLTSucc,Semiformula.bexsLT,FirstOrder.bexs,bnd,bnd_open] at h ⊢
  rcases h with hm | hm
  · left
    letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
    have hmap' : (∼isMappingDef.val).Evalb ![s] := by simpa using hm
    have hb := PRANegMappingWitnessBound.neg_mapping_bound_explicit s hmap'
    have hs : Fin.snoc ![s] (PRANegMappingWitnessBound.negMappingMajorant s) = ![s,PRANegMappingWitnessBound.negMappingMajorant s] := by simp
    have hh := eval_bnd_mono (∼isMappingDef.val) ![s] (Empty.elim : Empty → V) hmap (by rw [hs]; exact hb)
    have hs' : Fin.snoc ![s] w = ![s,w] := by simp
    rw [hs'] at hh
    exact hh
  · right
    intro l
    by_cases hl : 2*s+1 ≤ l
    · exact Or.inl hl
    · right
      intro d
      by_cases hd : 2*s+1 ≤ d
      · exact Or.inl hd
      · right
        have hd' : d ≤ 2*s := lt_succ_iff_le.mp (lt_of_not_ge hd)
        rcases hm l with hl' | hl'
        · exact (hl hl').elim
        · rcases hl' d with hd'' | hd'' | hd''
          · exact (hd hd'').elim
          · left
            letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
            have hd0 : (∼domainDef.val).Evalb ![d,s] := by simpa using hd''
            have hb := PRANegDomainWitnessBound.neg_domain_bound_explicit d s hd0
            have hsize := le_trans (PRANegMappingWitnessBound.negDomainMajorant_mono_left d (2*s) s hd') hdom
            have hs : Fin.snoc ![d,s] (PRANegDomainWitnessBound.negDomainMajorant d s) = ![d,s,PRANegDomainWitnessBound.negDomainMajorant d s] := by simp
            have hbounded := eval_bnd_mono (∼domainDef.val) ![d,s] (Empty.elim : Empty → V) hsize (by rw [hs]; exact hb)
            have hs' : Fin.snoc ![d,s] w = ![d,s,w] := by simp
            rw [hs'] at hbounded
            let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#2]
            have hv : (fun j => (ω #j).val ![d,l,s] Empty.elim) = ![d,s] := by
              funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
            exact bnd_neg_rew3 domainDef.val ω d l s w d s hv hbounded
          · right
            letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
            have hu0 : (∼underDef.val).Evalb ![d,l] := by simpa using hd''
            have hb := PRANegUnderWitnessBound.neg_under_bound d l hu0
            have hadd : d+1 ≤ 2*s+1 := by simpa [add_comm] using add_le_add_right hd' 1
            have hsize := le_trans (negExpMajorant_mono (d+1) (2*s+1) hadd) hunder
            have hs : Fin.snoc ![d,l] (PRANegExponentialWitnessBound.negExponentialMajorant (d+1)) = ![d,l,PRANegExponentialWitnessBound.negExponentialMajorant (d+1)] := by simp
            have hbounded := eval_bnd_mono (∼underDef.val) ![d,l] (Empty.elim : Empty → V) hsize (by rw [hs]; exact hb)
            have hs' : Fin.snoc ![d,l] w = ![d,l,w] := by simp
            rw [hs'] at hbounded
            let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#1]
            have hv : (fun j => (ω #j).val ![d,l,s] Empty.elim) = ![d,l] := by
              funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
            exact bnd_neg_rew3 underDef.val ω d l s w d l hv hbounded
def negSeqMajorant (s : V) : V := PRANegMappingWitnessBound.negMappingMajorant s +
 PRANegDomainWitnessBound.negDomainMajorant (2*s) s + PRANegExponentialWitnessBound.negExponentialMajorant (2*s+1)

theorem neg_seq_bound_explicit (s : V) : (∼seqDef.val).Evalb ![s] →
 (bnd (∼seqDef.val)).Evalb ![s,negSeqMajorant s] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  let A := PRANegMappingWitnessBound.negMappingMajorant s
  let B := PRANegDomainWitnessBound.negDomainMajorant (2*s) s
  let C := PRANegExponentialWitnessBound.negExponentialMajorant (2*s+1)
  have hA : A ≤ negSeqMajorant s := by simp [negSeqMajorant,A,add_assoc]
  have hB : B ≤ negSeqMajorant s := by simp [negSeqMajorant,B,add_comm,add_left_comm]
  have hC : C ≤ negSeqMajorant s := by
    simpa [negSeqMajorant,A,B,C,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := C) (b := A+B) (zero_le : 0 ≤ A+B))
  exact neg_seq_bound s (negSeqMajorant s) hA hB hC
noncomputable def negSeq : ArithmeticSemisentence 1 := ∼seqDef.val
noncomputable def boundedNegSeq : ArithmeticSemisentence 2 := bnd negSeq
noncomputable def negSeqBoundBody : ArithmeticSemisentence 1 :=
  “s. !negSeq s → !boundedNegSeq s (((2*(s)+1)+((2*(s))+(s)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1)))+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((2*(s)+(s)+1)²+1+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)))+((2*(s))+(s)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1)))+((2*(2*(s)+1)+1)+(2*(2*(s)+1)²+1)))”
theorem negSeqBoundBody_model (e : Fin 1 → V) : negSeqBoundBody.Eval e Empty.elim := by
  simp [negSeqBoundBody,boundedNegSeq,negSeq,Semiformula.eval_substs]
  have he : ![e 0] = e := by
    funext j; exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [←he]
  intro h
  have h' : (∼seqDef.val).Evalb ![e 0] := by simpa using h
  exact neg_seq_bound_explicit (e 0) h'
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def negSeqBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negSeqBoundBody
theorem candidate_proves_neg_seq_bound : PRA ⊢ negSeqBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact negSeqBoundBody_model e
end DiophantineConsistency.PRANegSeqDefWitnessBound
