import ZFCinPA.ModelCodedDecoderConstructors254

/-!
Explicit internal proof codes for decoded truth and modus ponens. These are
total fixed Sigma1 operations on raw codes; their proof-validity theorems use
actual internal Proof predicates. No proof is chosen from an existential.
GEN and the axiom-row interpretations remain separate.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderPropositional254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

noncomputable def impIdentityCode (L : Language) [L.Encodable] [L.LORDefinable]
    (p : V) : V :=
  let np := neg L p
  let s := insert (imp L p p) (0 : V)
  orIntro s np p (axL (insert np (insert p s)) p)

noncomputable def impIdentityCodeDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 2 := .mkSigma “out p.
      ∃ np, !(negGraph L) np p ∧ ∃ ip, !(impGraph L) ip p p ∧
      ∃ s, !insertDef s ip 0 ∧ ∃ ps, !insertDef ps p s ∧
      ∃ nps, !insertDef nps np ps ∧ ∃ em, !axLGraph em nps p ∧
      !orIntroGraph out s np p em”
instance impIdentityCode_defined : 𝚺₁-Function₁[V] (impIdentityCode L)
    via impIdentityCodeDef L := .mk fun e => by simp [impIdentityCodeDef,impIdentityCode]

theorem impIdentityCode_isProof (T : Theory L) [T.Δ₁] {p : V}
    (hp : IsFormula L p) : Proof T (impIdentityCode L p) (imp L p p) := by
  have hz : IsFormulaSet L (0 : V) := by change IsFormulaSet L ∅; simp
  unfold impIdentityCode
  refine ⟨by simp [singleton_eq_insert,emptyset_def], Derivation.orIntro ?_ ?_⟩
  · simp [imp]
  · refine ⟨by simp, Derivation.axL ?_ ?_ ?_⟩
    · simp [hp,hz]
    · simp
    · simp

/-- A literal cut of the implication against its negation, built from the two
input proofs, weakening, conjunction introduction and excluded middle. -/
noncomputable def mpCode (L : Language) [L.Encodable] [L.LORDefinable]
    (p q implicationProof antecedentProof : V) : V :=
  let ip := imp L p q
  let s := insert q (0 : V)
  let rightS := insert (neg L ip) s
  cutRule s ip (wkRule (insert ip s) implicationProof)
    (andIntro rightS p (neg L q)
      (wkRule (insert p rightS) antecedentProof)
      (axL (insert (neg L q) rightS) q))

noncomputable def mpCodeDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 5 := .mkSigma “out p q implicationProof antecedentProof.
      ∃ ip, !(impGraph L) ip p q ∧ ∃ nip, !(negGraph L) nip ip ∧
      ∃ nq, !(negGraph L) nq q ∧ ∃ s, !insertDef s q 0 ∧
      ∃ leftS, !insertDef leftS ip s ∧ ∃ rightS, !insertDef rightS nip s ∧
      ∃ pS, !insertDef pS p rightS ∧ ∃ nqS, !insertDef nqS nq rightS ∧
      ∃ leftD, !wkRuleGraph leftD leftS implicationProof ∧
      ∃ pD, !wkRuleGraph pD pS antecedentProof ∧ ∃ em, !axLGraph em nqS q ∧
      ∃ rightD, !andIntroGraph rightD rightS p nq pD em ∧
      !cutRuleGraph out s ip leftD rightD”
instance mpCode_defined : 𝚺₁-Function₄[V] (mpCode L)
    via mpCodeDef L := .mk fun e => by simp [mpCodeDef,mpCode]

theorem mpCode_isProof (T : Theory L) [T.Δ₁] {p q di da : V}
    (hp : IsFormula L p) (hq : IsFormula L q)
    (hi : Proof T di (imp L p q)) (ha : Proof T da p) :
    Proof T (mpCode L p q di da) q := by
  have hz : IsFormulaSet L (0 : V) := by change IsFormulaSet L ∅; simp
  have hn : neg L (imp L p q) = p ^⋏ neg L q := by
    simp only [imp,neg_or hp.isUFormula.neg hq.isUFormula,hp.isUFormula.neg_neg]
  unfold mpCode
  refine ⟨by simp [singleton_eq_insert,emptyset_def], Derivation.cutRule ?_ ?_⟩
  · refine ⟨by simp, Derivation.wkRule ?_ ?_ hi⟩
    · simp [hp,hq,hz]
    · intro x hx; simp at hx; simp [hx]
  · refine ⟨by simp, Derivation.andIntro ?_ ?_ ?_⟩
    · simp [hn]
    · refine ⟨by simp, Derivation.wkRule ?_ ?_ ha⟩
      · simp [hp,hq,hz]
      · intro x hx; simp at hx; simp [hx]
    · refine ⟨by simp, Derivation.axL ?_ ?_ ?_⟩
      · simp [hp,hq,hz]
      · simp
      · simp

/-- At the zero implication alias, return the antecedent proof unchanged.
For every other raw pair, use the literal target modus-ponens code. -/
noncomputable def decodedMPCode (a b implicationProof antecedentProof : V) : V := by
  classical
  exact if a = 0 ∧ b = 0 then antecedentProof else
    mpCode ℒₛₑₜ (decode a) (decode b) implicationProof antecedentProof

noncomputable def decodedMPCodeDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out a b implicationProof antecedentProof.
    (a = 0 ∧ b = 0 ∧ out = antecedentProof) ∨
    ((a ≠ 0 ∨ b ≠ 0) ∧ ∃ p, !decodeDef p a ∧ ∃ q, !decodeDef q b ∧
      !(mpCodeDef ℒₛₑₜ) out p q implicationProof antecedentProof)”
instance decodedMPCode_defined : 𝚺₁-Function₄[V] decodedMPCode via decodedMPCodeDef :=
  .mk fun e => by
    classical
    by_cases h : e 1 = 0 ∧ e 2 = 0
    · simp [decodedMPCodeDef,decodedMPCode,h]
    · have hn : e 1 ≠ 0 ∨ e 2 ≠ 0 := not_and_or.mp h
      simp [decodedMPCodeDef,decodedMPCode,h,hn]
      intro ha hb
      exact (h ⟨ha,hb⟩).elim

theorem decodedMPCode_isProof (T : Theory ℒₛₑₜ) [T.Δ₁] {a b di da : V}
    (hi : Proof T di (decode (4*cantor a b))) (ha : Proof T da (decode a)) :
    Proof T (decodedMPCode a b di da) (decode b) := by
  classical
  by_cases h : a = 0 ∧ b = 0
  · rcases h with ⟨rfl,rfl⟩
    simpa [decodedMPCode] using ha
  · simp only [decodedMPCode,if_neg h]
    apply mpCode_isProof T (decode_isFormula a) (decode_isFormula b) _ ha
    simpa only [decode_imp a b h] using hi

theorem decodedZero_isProof (T : Theory ℒₛₑₜ) [T.Δ₁] :
    Proof T (impIdentityCode ℒₛₑₜ (atomCode 1 (0 : V) 0)) (decode (0 : V)) := by
  rw [decode_zero]
  exact impIdentityCode_isProof T (memCode_isFormula 0 0)

theorem decodedProvable_mp (T : Theory ℒₛₑₜ) [T.Δ₁] {a b : V}
    (hi : Provable T (decode (4*cantor a b))) (ha : Provable T (decode a)) :
    Provable T (decode b) := by
  rcases hi with ⟨di,hi⟩
  rcases ha with ⟨da,ha⟩
  exact ⟨decodedMPCode a b di da,decodedMPCode_isProof T hi ha⟩

theorem decodedProvable_zero (T : Theory ℒₛₑₜ) [T.Δ₁] : Provable T (decode (0 : V)) :=
  ⟨impIdentityCode ℒₛₑₜ (atomCode 1 0 0),decodedZero_isProof T⟩

end LeanProofs.ZFCinPA.ModelCodedDecoderPropositional254
