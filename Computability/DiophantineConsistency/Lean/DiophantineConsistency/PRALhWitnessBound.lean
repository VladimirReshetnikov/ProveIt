import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRASeqFullWitnessBound
import DiophantineConsistency.PRANegSeqDefWitnessBound
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRALhWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] underDef domainDef seqDef
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem bnd_rew1 (φ : ArithmeticSemisentence 1) (ω : Rew ℒₒᵣ Empty 1 Empty 2)
 (l s w a : V) (hv : (fun j => (ω #j).val ![l,s] Empty.elim) = ![a])
 (h : (bnd φ).Evalb ![a,w]) : (bnd (ω ▹ φ)).Evalb ![l,s,w] := by
  have hn := PRABndRewriting.natural φ ω ![l,s] w
  have hs : Fin.snoc ![l,s] w = ![l,s,w] := by
    funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs' : Fin.snoc ![a] w = ![a,w] := by
    funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
  rw [hv,hs,hs'] at hn
  exact hn.mpr h
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem bnd_rew2 (φ : ArithmeticSemisentence 2) (ω : Rew ℒₒᵣ Empty 2 Empty 3)
 (d l s w a b : V) (hv : (fun j => (ω #j).val ![d,l,s] Empty.elim) = ![a,b])
 (h : (bnd φ).Evalb ![a,b,w]) : (bnd (ω ▹ φ)).Evalb ![d,l,s,w] := by
  have hn := PRABndRewriting.natural φ ω ![d,l,s] w
  have hs : Fin.snoc ![d,l,s] w = ![d,l,s,w] := by
    funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k; exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs' : Fin.snoc ![a,b] w = ![a,b,w] := by
    funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  rw [hv,hs,hs'] at hn
  exact hn.mpr h
 theorem lh_bound (l s w : V) (hsize : 2*s+1 ≤ w)
 (hseq : PRASeqFullWitnessBound.seqMajorant s ≤ w)
 (hnegseq : PRANegSeqDefWitnessBound.negSeqMajorant s ≤ w)
 (hdom : PRADomainWitnessBound.domainMajorant (2*s) s ≤ w)
 (hunder : PRAExponentialWitnessBound.exponentialMajorant (2*s+1) ≤ w) :
 lhDef.val.Evalb ![l,s] → (bnd lhDef.val).Evalb ![l,s,w] := by
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
  constructor
  · rcases h.1 with hn | ⟨d,hd,hde,hue⟩
    · left
      have hn' : (∼seqDef.val).Evalb ![s] := by simpa using hn
      have hb := PRANegSeqDefWitnessBound.neg_seq_bound_explicit s hn'
      have hw := lift1 (∼seqDef.val) s (PRANegSeqDefWitnessBound.negSeqMajorant s) hnegseq hb
      let ω : Rew ℒₒᵣ Empty 1 Empty 2 := Rew.subst ![#1]
      have hv : (fun j => (ω #j).val ![l,s] Empty.elim) = ![s] := by
        funext j; exact Fin.cases rfl (fun k => Fin.elim0 k) j
      have hh := bnd_rew1 (∼seqDef.val) ω l s w s hv hw
      have heq : (ω ▹ (∼seqDef.val)) = ∼(ω ▹ seqDef.val) := by
        exact LogicalConnective.HomClass.map_neg (Semiformula.rew ω) seqDef.val
      rw [heq] at hh
      exact hh
    · right
      simp [Semiformula.bexsLTSucc,Semiformula.bexsLT,FirstOrder.bexs,bnd,bnd_open]
      have hd' : d < 2*s+1 := lt_succ_iff_le.mpr hd
      refine ⟨d,lt_of_lt_of_le hd' hsize,hd',?_,?_⟩
      · have hb := PRADomainWitnessBound.domain_bound_explicit d s hde
        have hdsize := le_trans (PRASeqDomainBound.domainMajorant_mono_left d (2*s) s hd) hdom
        have hw := lift2 domainDef.val d s (PRADomainWitnessBound.domainMajorant d s) hdsize hb
        let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#2]
        have hv : (fun j => (ω #j).val ![d,l,s] Empty.elim) = ![d,s] := by
          funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
        exact bnd_rew2 domainDef.val ω d l s w d s hv hw
      · have hb := PRAUnderWitnessBound.under_bound d l hue
        have hadd : d+1 ≤ 2*s+1 := by simpa [add_comm] using add_le_add_right hd 1
        have husize := le_trans (PRAUnderMajorantMono.expMajorant_mono (d+1) (2*s+1) hadd) hunder
        have hw := lift2 underDef.val d l (PRAExponentialWitnessBound.exponentialMajorant (d+1)) husize hb
        let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#1]
        have hv : (fun j => (ω #j).val ![d,l,s] Empty.elim) = ![d,l] := by
          funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
        exact bnd_rew2 underDef.val ω d l s w d l hv hw
  · rcases h.2 with hp | hp
    · left
      have hb := PRASeqFullWitnessBound.seq_bound_explicit s hp
      have hw := lift1 seqDef.val s (PRASeqFullWitnessBound.seqMajorant s) hseq hb
      let ω : Rew ℒₒᵣ Empty 1 Empty 2 := Rew.subst ![#1]
      have hv : (fun j => (ω #j).val ![l,s] Empty.elim) = ![s] := by
        funext j; exact Fin.cases rfl (fun k => Fin.elim0 k) j
      exact bnd_rew1 seqDef.val ω l s w s hv hw
    · exact Or.inr hp
def lhMajorant (s : V) : V := (2*s+1) + PRASeqFullWitnessBound.seqMajorant s +
 PRANegSeqDefWitnessBound.negSeqMajorant s + PRADomainWitnessBound.domainMajorant (2*s) s +
 PRAExponentialWitnessBound.exponentialMajorant (2*s+1)
theorem lh_bound_explicit (l s : V) : lhDef.val.Evalb ![l,s] →
 (bnd lhDef.val).Evalb ![l,s,lhMajorant s] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  let A := 2*s+1
  let B := PRASeqFullWitnessBound.seqMajorant s
  let C := PRANegSeqDefWitnessBound.negSeqMajorant s
  let D := PRADomainWitnessBound.domainMajorant (2*s) s
  let E := PRAExponentialWitnessBound.exponentialMajorant (2*s+1)
  have hA : A ≤ lhMajorant s := by simp [lhMajorant,A,add_assoc]
  have hB : B ≤ lhMajorant s := by
    simpa [lhMajorant,A,B,C,D,E,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := B) (b := A+C+D+E) (zero_le : 0 ≤ A+C+D+E))
  have hC : C ≤ lhMajorant s := by
    simpa [lhMajorant,A,B,C,D,E,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := C) (b := A+B+D+E) (zero_le : 0 ≤ A+B+D+E))
  have hD : D ≤ lhMajorant s := by
    simpa [lhMajorant,A,B,C,D,E,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := D) (b := A+B+C+E) (zero_le : 0 ≤ A+B+C+E))
  have hE : E ≤ lhMajorant s := by
    simpa [lhMajorant,A,B,C,D,E,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := E) (b := A+B+C+D) (zero_le : 0 ≤ A+B+C+D))
  exact lh_bound l s (lhMajorant s) hA hB hC hD hE
noncomputable def boundedLh : ArithmeticSemisentence 3 := bnd lhDef.val
noncomputable def lhBoundBody : ArithmeticSemisentence 2 :=
  “l s. !lhDef l s → !boundedLh l s ((2*(s)+1)+((2*(s)+1)+(((2*(s)+1)⁴+1)+((2*(s)+1)²+1)+(2*(2*(s)+1)²+1)+((2*(s)+1)⁴+(2*(s)+1)⁴+2*(2*(s)+1)+1))+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1))+((2*(s)+1)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1))+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((2*(s)+(s)+1)²+1+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1))))+(((2*(s)+1)+((2*(s))+(s)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1)))+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((2*(s)+(s)+1)²+1+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)))+((2*(s))+(s)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1)))+((2*(2*(s)+1)+1)+(2*(2*(s)+1)²+1)))+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1))+(((2*(s)+1)⁴+1)+((2*(s)+1)²+1)+(2*(2*(s)+1)²+1)+((2*(s)+1)⁴+(2*(s)+1)⁴+2*(2*(s)+1)+1)))”
theorem lhBoundBody_model (e : Fin 2 → V) : lhBoundBody.Eval e Empty.elim := by
  simp [lhBoundBody,boundedLh,Semiformula.eval_substs]
  exact lh_bound_explicit (e 0) (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def lhBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding lhBoundBody
theorem candidate_proves_lh_bound : PRA ⊢ lhBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact lhBoundBody_model e
end DiophantineConsistency.PRALhWitnessBound
