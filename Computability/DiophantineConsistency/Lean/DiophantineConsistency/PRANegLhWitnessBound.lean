import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRALhWitnessBound
import DiophantineConsistency.PRAUnaryRewritingBound
import DiophantineConsistency.PRARewritingWitnessBound
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegLhWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] underDef domainDef seqDef
 theorem neg_lh_bound (l s w : V)
 (hseq : PRASeqFullWitnessBound.seqMajorant s ≤ w)
 (hnegseq : PRANegSeqDefWitnessBound.negSeqMajorant s ≤ w)
 (hdom : PRANegDomainWitnessBound.negDomainMajorant (2*s) s ≤ w)
 (hunder : PRANegExponentialWitnessBound.negExponentialMajorant (2*s+1) ≤ w) :
 (∼lhDef.val).Evalb ![l,s] → (bnd (∼lhDef.val)).Evalb ![l,s,w] := by
  intro h
  simp [lhDef,DeMorgan.imply,bnd,bnd_open] at h ⊢
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  rcases h with ⟨hp,hrest⟩ | ⟨hn,hne⟩
  · left; constructor
    · let ω : Rew ℒₒᵣ Empty 1 Empty 2 := Rew.subst ![#1]
      have hh := PRAUnaryRewritingBound.rew_bound_with seqDef.val
        PRASeqFullWitnessBound.seqMajorant PRASeqFullWitnessBound.seq_bound_explicit
        ω ![l,s] w (by simpa [ω] using hseq)
        (by simpa [ω, Semiformula.eval_substs] using hp)
      simpa using hh
    · simp [Semiformula.bexsLTSucc,Semiformula.bexsLT,FirstOrder.bexs,bnd,bnd_open]
      intro d
      by_cases hd : 2*s+1 ≤ d
      · exact Or.inl hd
      · right
        have hd' : d ≤ 2*s := lt_succ_iff_le.mp (lt_of_not_ge hd)
        by_cases hde : domainDef.val.Evalb ![d,s]
        · right
          have hno := hrest d hd' hde
          have hn : (∼underDef.val).Evalb ![d,l] := by simpa using hno
          have hadd : d+1 ≤ 2*s+1 := by simpa [add_comm] using add_le_add_right hd' 1
          have hsize := le_trans (PRANegSeqDefWitnessBound.negExpMajorant_mono (d+1) (2*s+1) hadd) hunder
          let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#1]
          simpa [LogicalConnective.HomClass.map_neg] using
            (PRARewritingWitnessBound.binary_rew_bound_with (∼underDef.val)
            (fun d _ => PRANegExponentialWitnessBound.negExponentialMajorant (d+1))
            PRANegUnderWitnessBound.neg_under_bound ω ![d,l,s] w (by simpa [ω] using hsize)
            (by simpa [ω, Semiformula.eval_substs] using hn))
        · left
          have hn : (∼domainDef.val).Evalb ![d,s] := by simpa using hde
          have hsize := le_trans (PRANegMappingWitnessBound.negDomainMajorant_mono_left d (2*s) s hd') hdom
          let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#2]
          simpa [LogicalConnective.HomClass.map_neg] using
            (PRARewritingWitnessBound.binary_rew_bound_with (∼domainDef.val)
            PRANegDomainWitnessBound.negDomainMajorant PRANegDomainWitnessBound.neg_domain_bound_explicit
            ω ![d,l,s] w (by simpa [ω] using hsize)
            (by simpa [ω, Semiformula.eval_substs] using hn))
  · right; constructor
    · have hn' : (∼seqDef.val).Evalb ![s] := by simpa using hn
      let ω : Rew ℒₒᵣ Empty 1 Empty 2 := Rew.subst ![#1]
      simpa [LogicalConnective.HomClass.map_neg] using
        (PRAUnaryRewritingBound.rew_bound_with (∼seqDef.val)
        PRANegSeqDefWitnessBound.negSeqMajorant PRANegSeqDefWitnessBound.neg_seq_bound_explicit
        ω ![l,s] w (by simpa [ω] using hnegseq)
        (by simpa [ω, Semiformula.eval_substs] using hn'))
    · exact hne
def negLhMajorant (s : V) : V := PRASeqFullWitnessBound.seqMajorant s +
 PRANegSeqDefWitnessBound.negSeqMajorant s + PRANegDomainWitnessBound.negDomainMajorant (2*s) s +
 PRANegExponentialWitnessBound.negExponentialMajorant (2*s+1)
theorem neg_lh_bound_explicit (l s : V) : (∼lhDef.val).Evalb ![l,s] →
 (bnd (∼lhDef.val)).Evalb ![l,s,negLhMajorant s] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  let A := PRASeqFullWitnessBound.seqMajorant s
  let B := PRANegSeqDefWitnessBound.negSeqMajorant s
  let C := PRANegDomainWitnessBound.negDomainMajorant (2*s) s
  let D := PRANegExponentialWitnessBound.negExponentialMajorant (2*s+1)
  have hA : A ≤ negLhMajorant s := by simp [negLhMajorant,A,add_assoc]
  have hB : B ≤ negLhMajorant s := by
    simpa [negLhMajorant,A,B,C,D,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := B) (b := A+C+D) (zero_le : 0 ≤ A+C+D))
  have hC : C ≤ negLhMajorant s := by simp [negLhMajorant,C,add_comm,add_left_comm]
  have hD : D ≤ negLhMajorant s := by
    simpa [negLhMajorant,A,B,C,D,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := D) (b := A+B+C) (zero_le : 0 ≤ A+B+C))
  exact neg_lh_bound l s (negLhMajorant s) hA hB hC hD
noncomputable def negLh : ArithmeticSemisentence 2 := ∼lhDef.val
noncomputable def boundedNegLh : ArithmeticSemisentence 3 := bnd negLh
noncomputable def negLhBoundBody : ArithmeticSemisentence 2 :=
  “l s. !negLh l s → !boundedNegLh l s (((2*(s)+1)+(((2*(s)+1)⁴+1)+((2*(s)+1)²+1)+(2*(2*(s)+1)²+1)+((2*(s)+1)⁴+(2*(s)+1)⁴+2*(2*(s)+1)+1))+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1))+((2*(s)+1)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1))+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((2*(s)+(s)+1)²+1+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1))))+(((2*(s)+1)+((2*(s))+(s)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1)))+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((2*(s)+(s)+1)²+1+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)))+((2*(s))+(s)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1)))+((2*(2*(s)+1)+1)+(2*(2*(s)+1)²+1)))+((2*(s))+(s)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1)))+((2*(2*(s)+1)+1)+(2*(2*(s)+1)²+1)))”
theorem negLhBoundBody_model (e : Fin 2 → V) : negLhBoundBody.Eval e Empty.elim := by
  simp [negLhBoundBody,boundedNegLh,negLh,Semiformula.eval_substs]
  intro h
  have h' : (∼lhDef.val).Evalb ![e 0,e 1] := by simpa using h
  exact neg_lh_bound_explicit (e 0) (e 1) h'
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def negLhBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negLhBoundBody
theorem candidate_proves_neg_lh_bound : PRA ⊢ negLhBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact negLhBoundBody_model e
end DiophantineConsistency.PRANegLhWitnessBound
