import ZFCinPA.ModelCodedDecoderPropositional254

/-!
The actual decoded falsity code is membership(0,0), not primitive Bottom.
A fixed ordinary ZF theorem, quoted into every IΣ1 model and specialized,
provides its negation. Explicit internal cut constructors close the endpoint.
No accepted-history translation or PA sentence equivalence is assumed here.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderFalsity254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedSpecialization
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- One fixed ordinary sentence, with no internal-code parameter. -/
def irreflexivitySentence : SetTheorySentence := “∀ x, x ∉ x”

lemma zf_irreflexivity_outer : (𝗭𝗙 : SetTheory) ⊢ irreflexivitySentence := by
  apply SetTheory.provable_of_models.{0}
  intro M _ _ _
  have hp : ∀ x y : M, ∃ z : M, ∀ w : M, w ∈ z ↔ w = x ∨ w = y := by
    simpa [models_iff,Axiom.pairing] using
      (Theory.models M 𝗭𝗙 ZermeloFraenkel.axiom_of_pairing)
  have hf : ∀ x : M, (∃ z : M, z ∈ x) → ∃ y : M, y ∈ x ∧ ∀ z : M, z ∈ x → z ∉ y := by
    simpa [models_iff,Axiom.foundation,isNonempty,Rew.q,Rew.subst] using
      (Theory.models M 𝗭𝗙 ZermeloFraenkel.axiom_of_foundation)
  suffices ∀ x : M, x ∉ x by simpa [irreflexivitySentence,models_iff]
  intro x hxx
  obtain ⟨s,hs⟩ := hp x x
  have hxs : x ∈ s := (hs x).mpr (Or.inl rfl)
  obtain ⟨y,hys,hy⟩ := hf s ⟨x,hxs⟩
  have hyx : y = x := by simpa using (hs y).mp hys
  subst y
  exact hy x hxs hxx

lemma quote_irreflexivity : (⌜irreflexivitySentence⌝ : V) =
    ^∀ (^nrel 2 1 ?[^#0,^#0]) := by
  simp [irreflexivitySentence,FirstOrder.Sentence.quote_def,
    FirstOrder.Semiformula.quote_def,
    FirstOrder.Semiformula.Operator.mem_def,SemitermVec.val]
  constructor
  · change ((1 : Nat) : V) = 1
    simp
  · constructor <;> change (^#((0 : Nat) : V) : V) = ^#0 <;> simp

/-- The fixed finite ZF theorem is internalized before specializing its bound
variable. Completeness is used only for that ordinary fixed theorem. -/
lemma zf_irreflexivity_internal :
    Provable (𝗭𝗙 : SetTheory) (neg ℒₛₑₜ (atomCode 1 (0 : V) 0)) := by
  have hc : Provable (𝗭𝗙 : SetTheory) (⌜irreflexivitySentence⌝ : V) :=
    internalize_provability zf_irreflexivity_outer
  rw [quote_irreflexivity] at hc
  obtain ⟨d,hd⟩ := hc
  have hr : (ℒₛₑₜ).IsRel (2 : V) 1 := by
    simpa using (isRel_quote_quote (V := V) (L := ℒₛₑₜ) (k := 2) (x := 1)).mpr
      ⟨Language.Set.Rel.mem,rfl⟩
  have hb : IsSemiformula ℒₛₑₜ (1 : V) (^nrel 2 1 ?[^#0,^#0]) := by simp [hr]
  refine ⟨specializeCode ℒₛₑₜ d (^nrel 2 1 ?[^#0,^#0]) (^&0),?_⟩
  have h := specializeCode_isProof (𝗭𝗙 : SetTheory) hb
    (show IsTerm ℒₛₑₜ (^& (0 : V)) by simp) hd
  simpa [substs1,atomCode,hr] using h

noncomputable def contradictionCode (L : Language) [L.Encodable] [L.LORDefinable]
    (p positiveProof negativeProof : V) : V :=
  let s := insert (^⊥ : V) 0
  cutRule s p (wkRule (insert p s) positiveProof)
    (wkRule (insert (neg L p) s) negativeProof)

noncomputable def contradictionCodeDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 4 := .mkSigma “out p positiveProof negativeProof.
      ∃ bot, !qqFalsumDef bot ∧ ∃ np, !(negGraph L) np p ∧
      ∃ s, !insertDef s bot 0 ∧ ∃ leftS, !insertDef leftS p s ∧
      ∃ rightS, !insertDef rightS np s ∧
      ∃ dl, !wkRuleGraph dl leftS positiveProof ∧
      ∃ dr, !wkRuleGraph dr rightS negativeProof ∧ !cutRuleGraph out s p dl dr”
instance contradictionCode_defined : 𝚺₁-Function₃[V] (contradictionCode L)
    via contradictionCodeDef L := .mk fun e => by
  simp [contradictionCodeDef,contradictionCode]

lemma contradictionCode_isProof (T : Theory L) [T.Δ₁] {p dp dn : V}
    (hp : IsFormula L p) (hdp : Proof T dp p) (hdn : Proof T dn (neg L p)) :
    Proof T (contradictionCode L p dp dn) (^⊥ : V) := by
  have hz : IsFormulaSet L (0 : V) := by change IsFormulaSet L ∅; simp
  unfold contradictionCode
  refine ⟨by simp [singleton_eq_insert,emptyset_def], Derivation.cutRule ?_ ?_⟩
  · refine ⟨by simp, Derivation.wkRule ?_ ?_ hdp⟩
    · simp [hp,hz]
    · intro x hx; simp at hx; simp [hx]
  · refine ⟨by simp, Derivation.wkRule ?_ ?_ hdn⟩
    · simp [hp,hz]
    · intro x hx; simp at hx; simp [hx]

noncomputable def explosionCode (p bottomProof : V) : V :=
  let s := insert p 0
  cutRule s (^⊥ : V) (wkRule (insert (^⊥ : V) s) bottomProof)
    (verumIntro (insert (^⊤ : V) s))

def explosionCodeDef : 𝚺₁.Semisentence 3 := .mkSigma “out p bottomProof.
  ∃ bot, !qqFalsumDef bot ∧ ∃ top, !qqVerumDef top ∧
  ∃ s, !insertDef s p 0 ∧ ∃ leftS, !insertDef leftS bot s ∧
  ∃ rightS, !insertDef rightS top s ∧ ∃ dl, !wkRuleGraph dl leftS bottomProof ∧
  ∃ dr, !verumIntroGraph dr rightS ∧ !cutRuleGraph out s bot dl dr”
instance explosionCode_defined : 𝚺₁-Function₂[V] explosionCode via explosionCodeDef :=
  .mk fun e => by simp [explosionCodeDef,explosionCode]

lemma explosionCode_isProof (T : Theory L) [T.Δ₁] {p db : V}
    (hp : IsFormula L p) (hd : Proof T db (^⊥ : V)) :
    Proof T (explosionCode p db) p := by
  have hz : IsFormulaSet L (0 : V) := by change IsFormulaSet L ∅; simp
  unfold explosionCode
  refine ⟨by simp [singleton_eq_insert,emptyset_def], Derivation.cutRule ?_ ?_⟩
  · refine ⟨by simp, Derivation.wkRule ?_ ?_ hd⟩
    · simp [hp,hz]
    · intro x hx; simp at hx; simp [hx]
  · refine ⟨by simp, Derivation.verumIntro ?_ ?_⟩
    · simp [hp,hz]
    · simp

lemma decoded_one_provable_iff_bottom :
    Provable (𝗭𝗙 : SetTheory) (decode (1 : V)) ↔
      Provable (𝗭𝗙 : SetTheory) (^⊥ : V) := by
  rw [decode_one]
  constructor
  · rintro ⟨dp,hp⟩
    obtain ⟨dn,hn⟩ := zf_irreflexivity_internal (V := V)
    exact ⟨contradictionCode ℒₛₑₜ (atomCode 1 0 0) dp dn,
      contradictionCode_isProof _ (memCode_isFormula 0 0) hp hn⟩
  · rintro ⟨db,hb⟩
    exact ⟨explosionCode (atomCode 1 0 0) db,
      explosionCode_isProof _ (memCode_isFormula 0 0) hb⟩

end LeanProofs.ZFCinPA.ModelCodedDecoderFalsity254
