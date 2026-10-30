import ZFCinPA.ModelCodedClosedSchemaAxioms

/-!
All-internal repeated universal specialization by a total proof-code iterator
independent of proof validity. Correctness uses Π1 induction with explicit
input/output proof codes, rather than an implication between existential
provability statements. This is a same-language proof operation, not a
C254/ZFC interpretation or consistency comparison.
-/
namespace LeanProofs.ZFCinPA.ModelCodedSpecialization
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedBindFree
open LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace QVectorIteration
noncomputable def blueprint (L : Language) [L.Encodable] [L.LORDefinable] : PR.Blueprint 1 where
  zero := .mkSigma “out vector. out = vector”
  succ := .mkSigma “out previous time vector. !(qVecGraph L) out previous”
noncomputable def construction (L : Language) [L.Encodable] [L.LORDefinable] :
    PR.Construction V (blueprint L) where
  zero v := v 0
  succ _ _ previous := qVec L previous
  zero_defined := .mk fun e => by simp [blueprint]
  succ_defined := .mk fun e => by simp [blueprint]
end QVectorIteration

noncomputable def qVecIter (L : Language) [L.Encodable] [L.LORDefinable]
    (time vector : V) : V := (QVectorIteration.construction L).result ![vector] time
noncomputable def qVecIterDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 3 := (QVectorIteration.blueprint L).resultDef
instance qVecIter_defined : 𝚺₁-Function₂[V] (qVecIter L) via qVecIterDef L :=
  .mk fun e => by simpa [qVecIterDef,qVecIter,Matrix.constant_eq_singleton]
    using (QVectorIteration.construction L).result_defined.defined e
private instance qVecIter_delta : 𝚫₁-Function₂[V] (qVecIter L) :=
  qVecIter_defined.graph_delta.to_definable
@[simp] lemma qVecIter_zero (vector : V) : qVecIter L 0 vector = vector := by
  simp [qVecIter,QVectorIteration.construction]
@[simp] lemma qVecIter_succ (time vector : V) :
    qVecIter L (time+1) vector = qVec L (qVecIter L time vector) := by
  simp [qVecIter,QVectorIteration.construction]

lemma qVecIter_succ_left (time vector : V) :
    qVecIter L (time+1) vector = qVecIter L time (qVec L vector) := by
  suffices ∀ vector : V, qVecIter L (time+1) vector = qVecIter L time (qVec L vector)
    from this vector
  induction time using ISigma1.pi1_succ_induction
  · definability
  case zero =>
    intro vector
    simpa only [zero_add,qVecIter_zero] using qVecIter_succ (L := L) 0 vector
  case succ time ih =>
    intro vector
    calc
      qVecIter L ((time+1)+1) vector = qVec L (qVecIter L (time+1) vector) := qVecIter_succ _ _
      _ = qVec L (qVecIter L time (qVec L vector)) := congrArg (qVec L) (ih vector)
      _ = qVecIter L (time+1) (qVec L vector) := (qVecIter_succ _ _).symm

lemma qVecIter_isSemitermVec {n m vector : V} (hw : IsSemitermVec L n m vector)
    (time : V) : IsSemitermVec L (n+time) (m+time) (qVecIter L time vector) := by
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using hw
  case succ time ih => simpa [add_assoc] using ih.qVec

/-- Substitution through an internal number of binders. All lengths are internal. -/
lemma subst_qqAlls (time : V) : ∀ n m p vector : V,
    IsSemiformula L (n+time) p → IsSemitermVec L n m vector →
    subst L vector (qqAlls p time) =
      qqAlls (subst L (qVecIter L time vector) p) time := by
  induction time using ISigma1.pi1_succ_induction
  · definability
  case zero => intros; simp
  case succ time ih =>
    intro n m p vector hp hv
    have hbody : IsSemiformula L ((n+1)+time) p := by
      simpa [add_assoc,add_comm,add_left_comm] using hp
    rw [qqAlls_succ,substs_all ((isUFormula_qqAlls).mpr hp.isUFormula),
      ih (n+1) (m+1) p (qVec L vector) hbody hv.qVec,
      ← qVecIter_succ_left]
    simp

/-- Iterated lifting inserts the identity bound-variable prefix, independent
of the initial typed vector. -/
lemma qVecIter_prefix {n m vector : V} (hw : IsSemitermVec L n m vector)
    (time : V) : ∀ i<time, (qVecIter L time vector).[i] = ^#i := by
  induction time using ISigma1.pi1_succ_induction
  · definability
  case zero => intro i hi; simp at hi
  case succ time ih =>
    intro i hi
    rcases zero_or_succ i with rfl | ⟨i,rfl⟩
    · simp [qVecIter_succ,Bootstrapping.qVec]
    · have hi' : i<time := by simpa using hi
      have hv := qVecIter_isSemitermVec hw time
      rw [qVecIter_succ]
      simp only [Bootstrapping.qVec,nth_adjoin_succ,hv.lh]
      rw [nth_termBShiftVec hv.isUTerm (lt_of_lt_of_le hi' (by simp)),ih i hi']
      simp

/-- qVec iteration retains each lower bound slot and shifts the final free term. -/
lemma qVecIter_free_spec (time : V) : ∀ x : V,
    (∀ i < time, (qVecIter L time (^&x ∷ 0)).[i] = ^#i) ∧
      (qVecIter L time (^&x ∷ 0)).[time] = ^&x := by
  induction time using ISigma1.pi1_succ_induction
  · definability
  case zero => intro x; simp
  case succ time ih =>
    intro x
    have hvec : IsSemitermVec L (time+1) time (qVecIter L time (^&x ∷ 0)) := by
      simpa [add_comm] using qVecIter_isSemitermVec (L := L)
        (show IsSemitermVec (V := V) L 1 0 (^&x ∷ 0) by simp) time
    refine ⟨?_,?_⟩
    · exact qVecIter_prefix (show IsSemitermVec (V := V) L 1 0 (^&x ∷ 0) by simp) _
    · rw [qVecIter_succ]
      simp only [Bootstrapping.qVec,nth_adjoin_succ,hvec.lh]
      rw [nth_termBShiftVec hvec.isUTerm (by simp),(ih x).2]
      simp

/-- The transformed-body induction ends in the intended simultaneous opening. -/
lemma fvarVec_subst_qVecIter (time : V) :
    termSubstVec L (time+1) (fvarVec time) (qVecIter L time (^&time ∷ 0)) =
      fvarVec (time+1) := by
  have hvec : IsSemitermVec L (time+1) time (qVecIter L time (^&time ∷ 0)) := by
    simpa [add_comm] using qVecIter_isSemitermVec (L := L)
      (show IsSemitermVec (V := V) L 1 0 (^&time ∷ 0) by simp) time
  apply nth_ext' (time+1)
  · simp [hvec.isUTerm]
  · simp
  · intro i hi
    rw [nth_termSubstVec hvec.isUTerm hi,nth_fvarVec _ _ hi]
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with hit | heq
    · rw [(qVecIter_free_spec time time).1 i hit,termSubst_bvar,nth_fvarVec _ _ hit]
    · rw [heq,(qVecIter_free_spec time time).2,termSubst_fvar]

/-- Literal single universal elimination using weakening, excluded middle, ∃ and cut. -/
noncomputable def specializeCode (L : Language) [L.Encodable] [L.LORDefinable]
    (proof body term : V) : V :=
  let result := substs1 L term body
  let s := insert result (0 : V)
  let allBody := ^∀ body
  let leftS := insert allBody s
  let rightS := insert (neg L allBody) s
  let emS := insert (substs1 L term (neg L body)) rightS
  cutRule s allBody (wkRule leftS proof)
    (exsIntro rightS (neg L body) term (axL emS result))

noncomputable def specializeCodeDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 4 := .mkSigma “out proof body term.
      ∃ result, !(substs1Graph L) result term body ∧
      ∃ s, !insertDef s result 0 ∧ ∃ allBody, !qqAllDef allBody body ∧
      ∃ leftS, !insertDef leftS allBody s ∧
      ∃ negAll, !(negGraph L) negAll allBody ∧
      ∃ rightS, !insertDef rightS negAll s ∧
      ∃ negBody, !(negGraph L) negBody body ∧
      ∃ negInstance, !(substs1Graph L) negInstance term negBody ∧
      ∃ emS, !insertDef emS negInstance rightS ∧
      ∃ emD, !axLGraph emD emS result ∧
      ∃ exD, !exsIntroGraph exD rightS negBody term emD ∧
      ∃ wkD, !wkRuleGraph wkD leftS proof ∧
      !cutRuleGraph out s allBody wkD exD”
instance specializeCode_defined : 𝚺₁-Function₃[V] (specializeCode L)
    via specializeCodeDef L := .mk fun e => by simp [specializeCodeDef,specializeCode]

variable (T : Theory L) [T.Δ₁]

lemma specializeCode_isProof {proof body term : V}
    (hb : IsSemiformula L 1 body) (ht : IsTerm L term)
    (hd : Proof T proof (^∀ body)) :
    Proof T (specializeCode L proof body term) (substs1 L term body) := by
  have hi : IsFormula L (substs1 L term body) := hb.substs1 ht
  have hn : substs1 L term (neg L body) = neg L (substs1 L term body) := by
    simpa [substs1] using substs_neg hb (show IsSemitermVec (V := V) L 1 0 (term ∷ 0) by simp [ht])
  have hz : IsFormulaSet L (0 : V) := by
    change IsFormulaSet L ∅
    simp
  unfold specializeCode
  refine ⟨by simp [singleton_eq_insert,emptyset_def], Derivation.cutRule ?_ ?_⟩
  · refine ⟨by simp, Derivation.wkRule ?_ ?_ hd⟩
    · simp [hi,hb,hz]
    · intro x hx; simp at hx; simp [hx]
  · refine ⟨by simp, Derivation.exsIntro ?_ ht ?_⟩
    · simp [neg_all hb.isUFormula]
    · refine ⟨by simp, Derivation.axL ?_ ?_ ?_⟩
      · simp [hi,hb,hn,hz]
      · simp
      · simp [hn]

variable {T}

/-- A raw state is ⟪remaining-binders,current-formula,current-proof⟫. Invalid
states also have a total next value; no validity oracle occurs in the iterator. -/
noncomputable def advance (L : Language) [L.Encodable] [L.LORDefinable] (state : V) : V := by
  classical
  let remaining := π₁ state
  let formula := π₁ (π₂ state)
  let proof := π₂ (π₂ state)
  exact if remaining = 0 then state else
    ⟪remaining-1, substs1 L (^&(remaining-1)) (sndIdx formula),
      specializeCode L proof (sndIdx formula) (^&(remaining-1))⟫

noncomputable def advanceDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 2 := .mkSigma “out state.
      ∃ remaining, !pi₁Def remaining state ∧
      ((remaining = 0 ∧ out = state) ∨ (remaining ≠ 0 ∧
        ∃ rest, !pi₂Def rest state ∧ ∃ formula, !pi₁Def formula rest ∧
        ∃ proof, !pi₂Def proof rest ∧ ∃ nextRemaining, !subDef nextRemaining remaining 1 ∧
        ∃ body, !sndIdxDef body formula ∧ ∃ term, !qqFvarDef term nextRemaining ∧
        ∃ nextFormula, !(substs1Graph L) nextFormula term body ∧
        ∃ nextProof, !(specializeCodeDef L) nextProof proof body term ∧
        ∃ tail, !pairDef tail nextFormula nextProof ∧ !pairDef out nextRemaining tail))”
instance advance_defined : 𝚺₁-Function₁[V] (advance L) via advanceDef L :=
  .mk fun e => by
    classical
    by_cases h : π₁ (e 1) = 0
    · simp [advanceDef,advance,h]
    · simp [advanceDef,advance,h]
private instance advance_delta : 𝚫₁-Function₁[V] (advance L) :=
  advance_defined.graph_delta.to_definable

namespace ProofIteration
noncomputable def blueprint (L : Language) [L.Encodable] [L.LORDefinable] : PR.Blueprint 1 where
  zero := .mkSigma “out initial. out = initial”
  succ := .mkSigma “out previous time initial. !(advanceDef L) out previous”
noncomputable def construction (L : Language) [L.Encodable] [L.LORDefinable] :
    PR.Construction V (blueprint L) where
  zero v := v 0
  succ _ _ previous := advance L previous
  zero_defined := .mk fun e => by simp [blueprint]
  succ_defined := .mk fun e => by simp [blueprint]
end ProofIteration
noncomputable def runState (L : Language) [L.Encodable] [L.LORDefinable]
    (time initial : V) : V := (ProofIteration.construction L).result ![initial] time
noncomputable def runStateDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 3 := (ProofIteration.blueprint L).resultDef
instance runState_defined : 𝚺₁-Function₂[V] (runState L) via runStateDef L :=
  .mk fun e => by simpa [runStateDef,runState,Matrix.constant_eq_singleton]
    using (ProofIteration.construction L).result_defined.defined e
private instance runState_delta : 𝚫₁-Function₂[V] (runState L) :=
  runState_defined.graph_delta.to_definable
@[simp] lemma runState_zero (state : V) : runState L 0 state = state := by
  simp [runState,ProofIteration.construction]
@[simp] lemma runState_succ (time state : V) :
    runState L (time+1) state = advance L (runState L time state) := by
  simp [runState,ProofIteration.construction]
lemma runState_succ_left (time state : V) :
    runState L (time+1) state = runState L time (advance L state) := by
  suffices ∀ state : V, runState L (time+1) state = runState L time (advance L state)
    from this state
  induction time using ISigma1.pi1_succ_induction
  · definability
  case zero =>
    intro state
    simpa only [zero_add,runState_zero] using runState_succ (L := L) 0 state
  case succ time ih =>
    intro state
    calc
      runState L ((time+1)+1) state = advance L (runState L (time+1) state) := runState_succ _ _
      _ = advance L (runState L time (advance L state)) := congrArg (advance L) (ih state)
      _ = runState L (time+1) (advance L state) := (runState_succ _ _).symm

noncomputable def specializedProofCode (L : Language) [L.Encodable] [L.LORDefinable]
    (binders body proof : V) : V :=
  π₂ (π₂ (runState L binders ⟪binders,qqAlls body binders,proof⟫))
noncomputable def specializedProofCodeDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 4 := .mkSigma “out binders body proof.
      ∃ formula, !qqAllsDef formula body binders ∧ ∃ tail, !pairDef tail formula proof ∧
      ∃ initial, !pairDef initial binders tail ∧ ∃ state, !(runStateDef L) state binders initial ∧
      ∃ rest, !pi₂Def rest state ∧ !pi₂Def out rest”
instance specializedProofCode_defined : 𝚺₁-Function₃[V] (specializedProofCode L)
    via specializedProofCodeDef L := .mk fun e => by simp [specializedProofCodeDef,specializedProofCode]
private instance specializedProofCode_delta : 𝚫₁-Function₃[V] (specializedProofCode L) :=
  specializedProofCode_defined.graph_delta.to_definable

/-- Explicit proof-code correctness, permitting Π1 induction despite changing
body/proof inputs. There is no existential proof-selection premise in the IH. -/
theorem specializedProofCode_isProof (T : Theory L) [T.Δ₁] (binders : V) :
    ∀ body proof : V, IsSemiformula L binders body →
      Proof T proof (qqAlls body binders) →
      Proof T (specializedProofCode L binders body proof) (subst L (fvarVec binders) body) := by
  induction binders using ISigma1.pi1_succ_induction
  · definability
  case zero =>
    intro body proof hb hd
    have he : subst L (fvarVec (0 : V)) body = body := by
      apply Bootstrapping.subst_eq_self hb
      · simp
      · simp
    rw [he]
    simpa [specializedProofCode] using hd
  case succ binders ih =>
    intro body proof hb hd
    let vector := qVecIter L binders (^&binders ∷ 0)
    let nextBody := subst L vector body
    let nextProof := specializeCode L proof (qqAlls body binders) (^&binders)
    have hvec : IsSemitermVec L (binders+1) binders vector := by
      simpa [vector,add_comm] using qVecIter_isSemitermVec (L := L)
        (show IsSemitermVec (V := V) L 1 0 (^&binders ∷ 0) by simp) binders
    have hnbody : IsSemiformula L binders nextBody := hb.subst hvec
    have hall : IsSemiformula L 1 (qqAlls body binders) := by
      apply IsSemiformula.qqAlls
      simpa [add_comm] using hb
    have hnext : substs1 L (^&binders) (qqAlls body binders) = qqAlls nextBody binders := by
      exact subst_qqAlls binders 1 0 body (^&binders ∷ 0)
        (by simpa [add_comm] using hb) (by simp)
    have hproof : Proof T nextProof (qqAlls nextBody binders) := by
      rw [←hnext]
      exact specializeCode_isProof T hall (by simp) (by simpa using hd)
    have hfinal : subst L (fvarVec binders) nextBody = subst L (fvarVec (binders+1)) body := by
      rw [show nextBody = subst L vector body from rfl,
        substs_substs hb (fvarVec_isTermVec binders) hvec]
      rw [show vector = qVecIter L binders (^&binders ∷ 0) from rfl,
        fvarVec_subst_qVecIter]
    have hstate : advance L ⟪binders+1,qqAlls body (binders+1),proof⟫ =
        ⟪binders,qqAlls nextBody binders,nextProof⟫ := by
      simp [advance,qqAlls_succ,qqAll,sndIdx,hnext,nextProof]
    have hcode : specializedProofCode L (binders+1) body proof =
        specializedProofCode L binders nextBody nextProof := by
      unfold specializedProofCode
      rw [runState_succ_left,hstate]
    rw [hcode,←hfinal]
    exact ih nextBody nextProof hnbody hproof

/-- The closing traversal followed by internal specialization recovers the
original formula, for any literal input proof of its closed code. -/
theorem openClosedCode_isProof (T : Theory L) [T.Δ₁] {p proof : V}
    (hp : IsFormula L p) (hd : Proof T proof (closeFormulaCode L p)) :
    Proof T (specializedProofCode L (bv L (bindFreeAt L 0 p)) (bindFreeAt L 0 p) proof) p := by
  have hc := bindFreeAt_closing hp
  have h := specializedProofCode_isProof T (bv L (bindFreeAt L 0 p))
    (bindFreeAt L 0 p) proof hc.1.isSemiformula hd
  simpa only [hc.2.2] using h

end LeanProofs.ZFCinPA.ModelCodedSpecialization
