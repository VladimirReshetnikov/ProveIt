import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRALhWitnessBound
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
  have lift1 (φ : ArithmeticSemisentence 1) (a q : V) (hq : q ≤ w)
      (hb : (bnd φ).Evalb ![a,q]) : (bnd φ).Evalb ![a,w] := by
    have hs : Fin.snoc ![a] q = ![a,q] := by
      funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hh := eval_bnd_mono φ ![a] (Empty.elim : Empty → V) hq (by rw [hs]; exact hb)
    have hs' : Fin.snoc ![a] w = ![a,w] := by
      funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
    rw [hs'] at hh
    exact hh
  have lift2 (φ : ArithmeticSemisentence 2) (a b q : V) (hq : q ≤ w)
      (hb : (bnd φ).Evalb ![a,b,q]) : (bnd φ).Evalb ![a,b,w] := by
    have hs : Fin.snoc ![a,b] q = ![a,b,q] := by
      funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hh := eval_bnd_mono φ ![a,b] (Empty.elim : Empty → V) hq (by rw [hs]; exact hb)
    have hs' : Fin.snoc ![a,b] w = ![a,b,w] := by
      funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    rw [hs'] at hh
    exact hh
  rcases h with ⟨hp,hrest⟩ | ⟨hn,hne⟩
  · left; constructor
    · have hb := PRASeqFullWitnessBound.seq_bound_explicit s hp
      have hw := lift1 seqDef.val s (PRASeqFullWitnessBound.seqMajorant s) hseq hb
      let ω : Rew ℒₒᵣ Empty 1 Empty 2 := Rew.subst ![#1]
      have hv : (fun j => (ω #j).val ![l,s] Empty.elim) = ![s] := by
        funext j; exact Fin.cases rfl (fun k => Fin.elim0 k) j
      exact PRALhWitnessBound.bnd_rew1 seqDef.val ω l s w s hv hw
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
          have hb := PRANegUnderWitnessBound.neg_under_bound d l hn
          have hadd : d+1 ≤ 2*s+1 := by simpa [add_comm] using add_le_add_right hd' 1
          have hsize := le_trans (PRANegSeqDefWitnessBound.negExpMajorant_mono (d+1) (2*s+1) hadd) hunder
          have hw := lift2 (∼underDef.val) d l (PRANegExponentialWitnessBound.negExponentialMajorant (d+1)) hsize hb
          let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#1]
          have hv : (fun j => (ω #j).val ![d,l,s] Empty.elim) = ![d,l] := by
            funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
          have hh := PRALhWitnessBound.bnd_rew2 (∼underDef.val) ω d l s w d l hv hw
          have heq : (ω ▹ (∼underDef.val)) = ∼(ω ▹ underDef.val) := by
            exact LogicalConnective.HomClass.map_neg (Semiformula.rew ω) underDef.val
          rw [heq] at hh
          exact hh
        · left
          have hn : (∼domainDef.val).Evalb ![d,s] := by simpa using hde
          have hb := PRANegDomainWitnessBound.neg_domain_bound_explicit d s hn
          have hsize := le_trans (PRANegMappingWitnessBound.negDomainMajorant_mono_left d (2*s) s hd') hdom
          have hw := lift2 (∼domainDef.val) d s (PRANegDomainWitnessBound.negDomainMajorant d s) hsize hb
          let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#2]
          have hv : (fun j => (ω #j).val ![d,l,s] Empty.elim) = ![d,s] := by
            funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
          have hh := PRALhWitnessBound.bnd_rew2 (∼domainDef.val) ω d l s w d s hv hw
          have heq : (ω ▹ (∼domainDef.val)) = ∼(ω ▹ domainDef.val) := by
            exact LogicalConnective.HomClass.map_neg (Semiformula.rew ω) domainDef.val
          rw [heq] at hh
          exact hh
  · right; constructor
    · have hn' : (∼seqDef.val).Evalb ![s] := by simpa using hn
      have hb := PRANegSeqDefWitnessBound.neg_seq_bound_explicit s hn'
      have hw := lift1 (∼seqDef.val) s (PRANegSeqDefWitnessBound.negSeqMajorant s) hnegseq hb
      let ω : Rew ℒₒᵣ Empty 1 Empty 2 := Rew.subst ![#1]
      have hv : (fun j => (ω #j).val ![l,s] Empty.elim) = ![s] := by
        funext j; exact Fin.cases rfl (fun k => Fin.elim0 k) j
      have hh := PRALhWitnessBound.bnd_rew1 (∼seqDef.val) ω l s w s hv hw
      have heq : (ω ▹ (∼seqDef.val)) = ∼(ω ▹ seqDef.val) := by
        exact LogicalConnective.HomClass.map_neg (Semiformula.rew ω) seqDef.val
      rw [heq] at hh
      exact hh
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
