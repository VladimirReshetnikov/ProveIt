import IPRABridge.OpenSequents
import IPRABridge.ReferenceNormalization

/-! Reflect Foundation sequents whose finite free-variable scope is given
explicitly. A scoped formula is represented as a semisentence and opened at
the distinct labels supplied by an injection. -/

set_option autoImplicit false

namespace IPRABridge

open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open LeanProofs.ConciseIPRA (Fm PTm Prf PRAAx)
open DiophantineConsistency
open IPRAOrderErasure (embed erase)
open IPRAOrderErasureRew (eraseRew erase_rew)
open IPRAReferenceRew (embedRew embed_rew)
open IPRAStandardTheory (standardTheory)
open IPRATheoryHilbertBridge (extended)

local notation "L" => PRALanguage.language
local notation "R" => IPRAEqualityOnlyReference.language

local instance scopedNativeDecidableEq : PRALanguage.language.DecidableEq where
  func k := by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel k := by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

local instance scopedReferenceDecidableEq : IPRAEqualityOnlyReference.language.DecidableEq where
  func k := by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel k := by
    change DecidableEq (IPRAEqualityOnlyReference.EqualityRel k)
    infer_instance

private def labelRew {A : Language} {n : ℕ} (label : Fin n ↪ ℕ) : Rew A Empty n ℕ 0 :=
  Rew.embSubsts (fun i => .fvar (label i))

/-- Open a semisentence by interpreting the given scope as distinct free
variable labels. The quantifiers in the formula keep their original binders. -/
def atLabels {A : Language} {n : ℕ} (label : Fin n ↪ ℕ) (φ : Semisentenceᵢ A n) :
    Propositionᵢ A :=
  labelRew label ▹ φ

/-- Read a standard iPRA formula of finite scope as a Concise formula,
keeping its scoped variables in order. -/
def toConciseSemisentence {n : ℕ} (φ : Semisentenceᵢ L n) : Fm PTm n :=
  toConciseFormula PTm.var Empty.elim (erase φ)

private theorem erase_atLabels {n : ℕ} (label : Fin n ↪ ℕ) (φ : Semisentenceᵢ L n) :
    erase (atLabels label φ) = atLabels label (erase φ) := by
  have e : eraseRew (labelRew (A := L) label) = labelRew (A := R) label := by
    ext i
    · simp [eraseRew, labelRew]
    · exact Empty.elim i
  simp only [atLabels, erase_rew, e]

private theorem normalize_atLabels {n : ℕ} (label : Fin n ↪ ℕ) (φ : Semisentenceᵢ R n) :
    normalizeFormula (atLabels label φ) = atLabels label (normalizeFormula φ) := by
  have e : normalizeRew (labelRew (A := R) label) = labelRew (A := R) label := by
    ext i
    · simp [normalizeRew, normalizeTerm, labelRew]
    · exact Empty.elim i
  simp only [atLabels, normalizeFormula_rew, e]

private theorem embed_atLabels {n : ℕ} (label : Fin n ↪ ℕ) (φ : Semisentenceᵢ R n) :
    embed (atLabels label φ) = atLabels label (embed φ) := by
  have e : embedRew (labelRew (A := R) label) = labelRew (A := L) label := by
    ext i
    · simp [embedRew, labelRew]
    · exact Empty.elim i
  simp only [atLabels, embed_rew, e]

/-- Reading back a formula opened at distinct labels recovers its scoped image. -/
theorem toConciseProposition_atLabels {n : ℕ} (label : Fin n ↪ ℕ) (φ : Semisentenceᵢ L n) :
    toConciseProposition (conciseLabelAssignment label) (atLabels label φ) =
      toConciseSemisentence φ := by
  rw [toConciseProposition, erase_atLabels, atLabels, toConciseFormula_rew, toConciseSemisentence]
  congr 1
  · funext i
    simp only [labelRew, Rew.embSubsts_bvar, toConciseTerm, conciseLabelAssignment_apply,
      PTm.var_eq]
  · exact funext isEmptyElim

private theorem scopeImage {n : ℕ} (label : Fin n ↪ ℕ) (φ : Semisentenceᵢ L n) :
    toStandardInEnv (fun i => .fvar (label i)) (toConciseSemisentence φ) =
      embed (normalizeFormula (erase (atLabels label φ))) := by
  rw [erase_atLabels, normalize_atLabels, embed_atLabels]
  unfold toStandardInEnv toConciseSemisentence atLabels labelRew
  rw [referenceFormula_roundtrip]

private noncomputable def scopeEquivalence {n : ℕ} (label : Fin n ↪ ℕ) (φ : Semisentenceᵢ L n) :
    extended standardTheory ⊢! atLabels label φ 🡘
      toStandardInEnv (fun i => .fvar (label i)) (toConciseSemisentence φ) := by
  rw [scopeImage]
  have order := standardOrderRoundtripOpen (atLabels label φ)
  have h := referenceToStandardOpen
    (referenceNormalizationOpen (erase (atLabels label φ)))
  change extended standardTheory ⊢! _ 🡘 _ at h
  exact Entailment.E_intro
    (Entailment.C_trans (Entailment.K_left order) (Entailment.K_left h))
    (Entailment.C_trans (Entailment.K_right h) (Entailment.K_right order))

/-- An original Foundation sequent opened at distinct labels is provable
exactly when its scoped Concise translation is provable. -/
theorem scopedStandardSequent_iff {n : ℕ} (label : Fin n ↪ ℕ)
    (Γ : List (Semisentenceᵢ L n)) (p : Semisentenceᵢ L n) :
    (Γ.map (atLabels label) ⊢[extended standardTheory] atLabels label p) ↔
      Prf PRAAx (Γ.map toConciseSemisentence) (toConciseSemisentence p) := by
  constructor
  · intro h
    simpa only [List.map_map, Function.comp_def, toConciseProposition_atLabels] using
      standardToConciseSequent h (conciseLabelAssignment label)
  · intro h
    let f (q : Semisentenceᵢ L n) :=
      toStandardInEnv (fun i => .fvar (label i)) (toConciseSemisentence q)
    have d : (Γ.map f) ⊢[extended standardTheory] f p := by
      simpa only [List.map_map, Function.comp_def, f] using
        conciseToStandardSequent h (fun i => .fvar (label i))
    have each : ∀ q ∈ Γ.map f, Γ.map (atLabels label) ⊢[extended standardTheory] q := by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      exact ⟨FiniteContext.of (Entailment.K_left (scopeEquivalence label r)) ⨀
        FiniteContext.byAxm (List.mem_map_of_mem hr)⟩
    let premises : Γ.map (atLabels label) ⊢[extended standardTheory]! ⋀(Γ.map f) :=
      Entailment.Conj₂_intro (Γ.map f) (fun q hq => (each q hq).some)
    have conclusion := FiniteContext.of (FiniteContext.toDef d.some) ⨀ premises
    exact ⟨FiniteContext.of (Entailment.K_right (scopeEquivalence label p)) ⨀ conclusion⟩

end IPRABridge
