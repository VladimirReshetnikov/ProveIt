import DiophantineConsistency.PRALhWitnessBound
import DiophantineConsistency.PRANegLhWitnessBound
import Foundation.FirstOrder.Arithmetic.HFS.PRF
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRACseqWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] seqDef lhDef memRel
 theorem cseq_bound (p : PR.Blueprint 0) (s w : V)
 (hsize : 2*s+1 ≤ w)
 (hseq : PRASeqFullWitnessBound.seqMajorant s ≤ w)
 (hlh : PRANegLhWitnessBound.negLhMajorant s ≤ w)
 (hrel : ∀ x y, x ≤ 2*s+1 → y ≤ s → PRAMemRelWitnessBound.memRelMajorant s x y ≤ w)
 (hrelneg : PRANegBitFullWitnessBound.negBitMajorant s ≤ w)
 (hzero : ∀ z, z < s → p.zero.val.Evalb ![z] → (bnd p.zero.val).Evalb ![z,w])
 (hsucc : ∀ u z i, u < s → z < s → i < 2*s → p.succ.val.Evalb ![u,z,i] → (bnd p.succ.val).Evalb ![u,z,i,w]) :
 p.cseqDef.val.Evalb ![s] → (bnd p.cseqDef.val).Evalb ![s,w] := by
  intro h
  simp [PR.Blueprint.cseqDef,Semiformula.bexsLT,FirstOrder.bexs,Semiformula.ballLT,FirstOrder.ball,DeMorgan.imply,bnd,bnd_open] at h ⊢
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hsw : s ≤ w := le_trans (by simp [two_mul,add_assoc] : s ≤ 2*s+1) hsize
  have hseqb := PRASeqFullWitnessBound.seq_bound_explicit s h.1
  have hs : Fin.snoc ![s] (PRASeqFullWitnessBound.seqMajorant s) = ![s,PRASeqFullWitnessBound.seqMajorant s] := by simp
  have hsq := eval_bnd_mono seqDef.val ![s] (Empty.elim : Empty → V) hseq (by rw [hs]; exact hseqb)
  have hs' : Fin.snoc ![s] w = ![s,w] := by simp
  rw [hs'] at hsq
  constructor
  · exact hsq
  constructor
  · obtain ⟨z,hz,hze,hzr⟩ := h.2.1
    refine ⟨z,lt_of_lt_of_le hz hsw,hz,?_,?_⟩
    · let ω : Rew ℒₒᵣ Empty 1 Empty 2 := Rew.subst ![#0]
      have hv : (fun j => (ω #j).val ![z,s] Empty.elim) = ![z] := by
        funext j; exact Fin.cases rfl (fun k => Fin.elim0 k) j
      exact PRALhWitnessBound.bnd_rew1 p.zero.val ω z s w z hv (hzero z hz hze)
    · have hr : memRel.val.Evalb ![s,0,z] := by simpa [Semiformula.Operator.val,memRelOpr] using hzr
      have hb := PRAMemRelWitnessBound.memRel_bound_explicit s 0 z hr
      have hrelw := hrel 0 z zero_le (le_of_lt hz)
      have hv0 : Fin.snoc ![s,0,z] (PRAMemRelWitnessBound.memRelMajorant s 0 z) = ![s,0,z,PRAMemRelWitnessBound.memRelMajorant s 0 z] := by simp
      have hm := eval_bnd_mono memRel.val ![s,0,z] (Empty.elim : Empty → V) hrelw (by rw [hv0]; exact hb)
      let ω : Rew ℒₒᵣ Empty 3 Empty 2 := Rew.subst ![#1,Semiterm.numeral 0,#0]
      have hn := PRABndRewriting.natural memRel.val ω ![z,s] w
      have hv : (fun j => (ω #j).val ![z,s] Empty.elim) = ![s,0,z] := by
        funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
        exact Fin.cases rfl (fun k => Fin.elim0 k) k
      have hv1 : Fin.snoc ![z,s] w = ![z,s,w] := by simp
      have hv2 : Fin.snoc ![s,0,z] w = ![s,0,z,w] := by simp
      rw [hv,hv1,hv2] at hn
      rw [hv2] at hm
      simpa [Semiformula.Operator.operator,memRelOpr,Rewriting.emb] using hn.mpr hm
  · intro i
    by_cases hi : 2*s ≤ i
    · exact Or.inl hi
    · have hi' : i < 2*s := lt_of_not_ge hi
      rcases h.2.2 i with hi0 | hi0 | hi0
      · exact (hi hi0).elim
      · right; left
        simp [Semiformula.bexsLTSucc,Semiformula.bexsLT,FirstOrder.bexs,bnd,bnd_open]
        intro l
        by_cases hls : 2*s+1 ≤ l
        · exact Or.inl hls
        · right
          have hl : l ≤ 2*s := lt_succ_iff_le.mp (lt_of_not_ge hls)
          by_cases hp : lhDef.val.Evalb ![l,s]
          · exact Or.inr (hi0 l hl hp)
          · left
            have hn : (∼lhDef.val).Evalb ![l,s] := by simpa using hp
            have hb := PRANegLhWitnessBound.neg_lh_bound_explicit l s hn
            have hs : Fin.snoc ![l,s] (PRANegLhWitnessBound.negLhMajorant s) = ![l,s,PRANegLhWitnessBound.negLhMajorant s] := by simp
            have hm := eval_bnd_mono (∼lhDef.val) ![l,s] (Empty.elim : Empty → V) hlh (by rw [hs]; exact hb)
            have hs' : Fin.snoc ![l,s] w = ![l,s,w] := by simp
            rw [hs'] at hm
            let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#2]
            have hv : (fun j => (ω #j).val ![l,i,s] Empty.elim) = ![l,s] := by
              funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
            have hh := PRALhWitnessBound.bnd_rew2 (∼lhDef.val) ω l i s w l s hv hm
            have heq : (ω ▹ (∼lhDef.val)) = ∼(ω ▹ lhDef.val) := by
              exact LogicalConnective.HomClass.map_neg (Semiformula.rew ω) lhDef.val
            rw [heq] at hh
            exact hh
      · right; right
        intro z
        by_cases hzbound : s ≤ z
        · exact Or.inl hzbound
        · have hz' : z < s := lt_of_not_ge hzbound
          rcases hi0 z with hz | hz | hz
          · exact (hzbound hz).elim
          · right; left
            have hr : (∼memRel.val).Evalb ![s,i,z] := by simpa [Semiformula.Operator.val,memRelOpr] using hz
            have hb := PRANegMemRelWitnessBound.neg_memRel_bound s i z w hrelneg hr
            let ω : Rew ℒₒᵣ Empty 3 Empty 3 := Rew.subst ![#2,#1,#0]
            have hn := PRABndRewriting.natural (∼memRel.val) ω ![z,i,s] w
            have hv : (fun j => (ω #j).val ![z,i,s] Empty.elim) = ![s,i,z] := by
              funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
              exact Fin.cases rfl (fun k => Fin.elim0 k) k
            have hv1 : Fin.snoc ![z,i,s] w = ![z,i,s,w] := by simp
            have hv2 : Fin.snoc ![s,i,z] w = ![s,i,z,w] := by simp
            rw [hv,hv1,hv2] at hn
            have hh := hn.mpr hb
            have heq : (ω ▹ (∼memRel.val)) = ∼(ω ▹ memRel.val) := by
              exact LogicalConnective.HomClass.map_neg (Semiformula.rew ω) memRel.val
            rw [heq] at hh
            simpa [Semiformula.Operator.operator,memRelOpr,Rewriting.emb] using hh
          · right; right
            obtain ⟨u,hu,hus,hur⟩ := hz
            refine ⟨u,lt_of_lt_of_le hu hsw,hu,?_,?_⟩
            · let ω : Rew ℒₒᵣ Empty 3 Empty 4 := Rew.subst ![#0,#1,#2]
              have hn := PRABndRewriting.natural p.succ.val ω ![u,z,i,s] w
              have hv : (fun j => (ω #j).val ![u,z,i,s] Empty.elim) = ![u,z,i] := by
                funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
                exact Fin.cases rfl (fun k => Fin.elim0 k) k
              have hv1 : Fin.snoc ![u,z,i,s] w = ![u,z,i,s,w] := by simp
              have hv2 : Fin.snoc ![u,z,i] w = ![u,z,i,w] := by simp
              rw [hv,hv1,hv2] at hn
              exact hn.mpr (hsucc u z i hu hz' hi' hus)
            · have hr : memRel.val.Evalb ![s,i+1,u] := by simpa [Semiformula.Operator.val,memRelOpr] using hur
              have hb := PRAMemRelWitnessBound.memRel_bound_explicit s (i+1) u hr
              have hi2 : i+1 ≤ 2*s+1 := by simpa [add_comm] using add_le_add_right (le_of_lt hi') 1
              have hrelw := hrel (i+1) u hi2 (le_of_lt hu)
              have hv0 : Fin.snoc ![s,i+1,u] (PRAMemRelWitnessBound.memRelMajorant s (i+1) u) = ![s,i+1,u,PRAMemRelWitnessBound.memRelMajorant s (i+1) u] := by simp
              have hm := eval_bnd_mono memRel.val ![s,i+1,u] (Empty.elim : Empty → V) hrelw (by rw [hv0]; exact hb)
              let ω : Rew ℒₒᵣ Empty 3 Empty 4 := Rew.subst ![#3,‘#2+1’,#0]
              have hn := PRABndRewriting.natural memRel.val ω ![u,z,i,s] w
              have hv : (fun j => (ω #j).val ![u,z,i,s] Empty.elim) = ![s,i+1,u] := by
                funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
                exact Fin.cases rfl (fun k => Fin.elim0 k) k
              have hv1 : Fin.snoc ![u,z,i,s] w = ![u,z,i,s,w] := by simp
              have hv2 : Fin.snoc ![s,i+1,u] w = ![s,i+1,u,w] := by simp
              rw [hv,hv1,hv2] at hn
              rw [hv2] at hm
              simpa [Semiformula.Operator.operator,memRelOpr,Rewriting.emb] using hn.mpr hm
def relationHistoryMajorant (s : V) : V := (2*s+1+s+1)^2+1 + PRABitFullWitnessBound.bitMajorant s
def cseqMajorant (s : V) : V := (2*s+1) + PRASeqFullWitnessBound.seqMajorant s +
 PRANegLhWitnessBound.negLhMajorant s + relationHistoryMajorant s + PRANegBitFullWitnessBound.negBitMajorant s

theorem relation_history_bound (s x y : V) (hx : x ≤ 2*s+1) (hy : y ≤ s) :
 PRAMemRelWitnessBound.memRelMajorant s x y ≤ relationHistoryMajorant s := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hadd : x+y+1 ≤ 2*s+1+s+1 := by
    have h := add_le_add hx hy
    simpa [add_comm] using add_le_add_right h 1
  have hp := pow_le_pow_left₀ (zero_le : 0 ≤ x+y+1) hadd 2
  unfold PRAMemRelWitnessBound.memRelMajorant relationHistoryMajorant
  exact add_le_add (add_le_add hp le_rfl) le_rfl

theorem cseq_bound_explicit (p : PR.Blueprint 0) (s : V)
 (hzero : ∀ z, z < s → p.zero.val.Evalb ![z] → (bnd p.zero.val).Evalb ![z,cseqMajorant s])
 (hsucc : ∀ u z i, u < s → z < s → i < 2*s → p.succ.val.Evalb ![u,z,i] → (bnd p.succ.val).Evalb ![u,z,i,cseqMajorant s]) :
 p.cseqDef.val.Evalb ![s] → (bnd p.cseqDef.val).Evalb ![s,cseqMajorant s] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  let A := 2*s+1
  let B := PRASeqFullWitnessBound.seqMajorant s
  let C := PRANegLhWitnessBound.negLhMajorant s
  let D := relationHistoryMajorant s
  let E := PRANegBitFullWitnessBound.negBitMajorant s
  have hA : A ≤ cseqMajorant s := by simp [cseqMajorant,A,add_assoc]
  have hB : B ≤ cseqMajorant s := by
    simpa [cseqMajorant,A,B,C,D,E,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := B) (b := A+C+D+E) (zero_le : 0 ≤ A+C+D+E))
  have hC : C ≤ cseqMajorant s := by
    simpa [cseqMajorant,A,B,C,D,E,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := C) (b := A+B+D+E) (zero_le : 0 ≤ A+B+D+E))
  have hD : D ≤ cseqMajorant s := by
    simpa [cseqMajorant,A,B,C,D,E,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := D) (b := A+B+C+E) (zero_le : 0 ≤ A+B+C+E))
  have hE : E ≤ cseqMajorant s := by
    simpa [cseqMajorant,A,B,C,D,E,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := E) (b := A+B+C+D) (zero_le : 0 ≤ A+B+C+D))
  apply cseq_bound p s (cseqMajorant s) hA hB hC ?_ hE hzero hsucc
  intro x y hx hy
  exact le_trans (relation_history_bound s x y hx hy) hD
noncomputable def zeroCore (p : PR.Blueprint 0) : ArithmeticSemisentence 1 := p.zero.val
noncomputable def succCore (p : PR.Blueprint 0) : ArithmeticSemisentence 3 := p.succ.val
noncomputable def boundedZero (p : PR.Blueprint 0) : ArithmeticSemisentence 2 := bnd (zeroCore p)
noncomputable def boundedSucc (p : PR.Blueprint 0) : ArithmeticSemisentence 4 := bnd (succCore p)
noncomputable def cseqCore (p : PR.Blueprint 0) : ArithmeticSemisentence 1 := p.cseqDef.val
noncomputable def boundedCseq (p : PR.Blueprint 0) : ArithmeticSemisentence 2 := bnd (cseqCore p)
noncomputable def cseqBoundBody (p : PR.Blueprint 0) : ArithmeticSemisentence 2 :=
  “s w. 2*s+1 ≤ w ∧ ((2*(s)+1)+(((2*(s)+1)⁴+1)+((2*(s)+1)²+1)+(2*(2*(s)+1)²+1)+((2*(s)+1)⁴+(2*(s)+1)⁴+2*(2*(s)+1)+1))+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1))+((2*(s)+1)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1))+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((2*(s)+(s)+1)²+1+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)))) ≤ w ∧ (((2*(s)+1)+(((2*(s)+1)⁴+1)+((2*(s)+1)²+1)+(2*(2*(s)+1)²+1)+((2*(s)+1)⁴+(2*(s)+1)⁴+2*(2*(s)+1)+1))+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1))+((2*(s)+1)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1))+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((2*(s)+(s)+1)²+1+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1))))+(((2*(s)+1)+((2*(s))+(s)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1)))+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((2*(s)+(s)+1)²+1+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)))+((2*(s))+(s)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1)))+((2*(2*(s)+1)+1)+(2*(2*(s)+1)²+1)))+((2*(s))+(s)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1)))+((2*(2*(s)+1)+1)+(2*(2*(s)+1)²+1))) ≤ w ∧
    (∀ x <⁺ 2*s+1, ∀ y <⁺ s, ((x+y+1)²+1+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)) ≤ w) ∧ (((2*(s)+1)+(2*(s)²+1))+(s)+1) ≤ w ∧
    (∀ z < s, !((zeroCore p)) z → !((boundedZero p)) z w) ∧
    (∀ u < s, ∀ z < s, ∀ i < 2*s, !((succCore p)) u z i → !((boundedSucc p)) u z i w) ∧
    !((cseqCore p)) s → !((boundedCseq p)) s w”
theorem cseqBoundBody_model (p : PR.Blueprint 0) (e : Fin 2 → V) : (cseqBoundBody p).Eval e Empty.elim := by
  simp [cseqBoundBody,boundedZero,boundedSucc,boundedCseq,zeroCore,succCore,cseqCore,Semiformula.eval_substs]
  intro hsize hseq hlh hrel hrelneg hzero hsucc hcseq
  apply cseq_bound p (e 0) (e 1) hsize hseq hlh ?_ hrelneg hzero ?_ hcseq
  · intro x y hx hy
    exact hrel x hx y hy
  · intro u z i hu hz hi hh
    exact hsucc u hu z hz i hi hh
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def cseqBoundSentence (p : PR.Blueprint 0) : Sentence language := ∀⁰* Semiformula.lMap embedding (cseqBoundBody p)
theorem candidate_proves_cseq_bound (p : PR.Blueprint 0) : PRA ⊢ cseqBoundSentence p := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, cseqBoundSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact cseqBoundBody_model p e
end DiophantineConsistency.PRACseqWitnessBound
