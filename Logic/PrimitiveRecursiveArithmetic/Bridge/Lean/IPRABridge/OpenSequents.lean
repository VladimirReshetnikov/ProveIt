import IPRABridge.Standard

/-!
# Open-sequent transport for standard iPRA

Foundation sequents have finite lists of assumptions and natural-number free
variable labels. Forward transport assigns a Concise term to each label.
Reverse transport assigns a Foundation term to each variable in the Concise
scope. An injective assignment of labels gives a reflection theorem for
embedded Concise sequents.
-/

set_option autoImplicit false

namespace IPRABridge

open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open LeanProofs.ConciseIPRA (Fm PTm Prf PRAAx Syn)
open DiophantineConsistency
open IPRAEqualityOnlyReference (referenceTheory)
open IPRAOrderErasure (embed erase termsToReference toNative)
open IPRAStandardTheory (standardTheory)
open IPRATheoryHilbertBridge

local notation "L" => PRALanguage.language
local notation "R" => IPRAEqualityOnlyReference.language

local instance nativeDecidableEq : PRALanguage.language.DecidableEq where
  func k := by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel k := by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

local instance referenceDecidableEq : IPRAEqualityOnlyReference.language.DecidableEq where
  func k := by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel k := by
    change DecidableEq (IPRAEqualityOnlyReference.EqualityRel k)
    infer_instance

private noncomputable def mapExtended {A B : Language} [A.DecidableEq] [B.DecidableEq]
    {T : Theoryᵢ A 𝗜𝗻𝘁¹} {U : Theoryᵢ B 𝗜𝗻𝘁¹}
    (f : Propositionᵢ A → Propositionᵢ B)
    (mapImp : ∀ p q, f (p 🡒 q) = (f p 🡒 f q))
    (mapConj : ∀ Γ : List (Propositionᵢ A), f (⋀Γ) = ⋀(Γ.map f))
    (mapLogic : ∀ {p}, (𝗜𝗻𝘁¹ : Hilbertᵢ A) ⊢! p → (𝗜𝗻𝘁¹ : Hilbertᵢ B) ⊢! f p)
    (mapAxiom : ∀ σ ∈ T.theory, extended U ⊢! f (Rewriting.emb σ))
    {p : Propositionᵢ A} (h : extended T ⊢! p) : extended U ⊢! f p := by
  obtain ⟨Γ, hΓ, d⟩ := extendedToContext T h
  have pImp := HilbertProofᵢ.ofLE (le_extended U) (mapLogic (FiniteContext.toDef d))
  rw [mapImp, mapConj] at pImp
  refine pImp ⨀ Entailment.Conj₂_intro (Γ.map f) ?_
  intro q hq
  have witness := List.mem_map.mp hq
  let r := Classical.choose witness
  have hr := Classical.choose_spec witness
  rw [← hr.2]
  have axiomWitness := hΓ r hr.1
  let σ := Classical.choose axiomWitness
  have hσ := Classical.choose_spec axiomWitness
  change extended U ⊢! f r
  rw [← hσ.2]
  exact mapAxiom σ hσ.1

private noncomputable def standardToReferenceOpen {p : Propositionᵢ L}
    (h : extended standardTheory ⊢! p) : extended referenceTheory ⊢! erase p :=
  mapExtended erase (fun _ _ => rfl) IPRAOrderErasureTheoryTransfer.erase_conj
    (fun d => IPRAOrderErasureHilbert.eraseHilbert d)
    (fun σ hσ => by
      rw [IPRAOrderErasureRew.erase_emb]
      exact theoryToExtended referenceTheory (standardToReference ⟨Axiomatized.prfAxm hσ⟩).some)
    h

/-- Embed an open theorem of the reference calculus into standard iPRA. -/
noncomputable def referenceToStandardOpen {p : Propositionᵢ R}
    (h : extended referenceTheory ⊢! p) : extended standardTheory ⊢! embed p :=
  mapExtended embed (fun _ _ => rfl) IPRAReferenceTheoryTransfer.embed_conj
    (fun d => IPRAReferenceHilbert.embedHilbert d)
    (fun σ hσ => by
      rw [IPRAReferenceRew.embed_emb]
      exact theoryToExtended standardTheory (referenceAxiomInStandard σ hσ).some)
    h

/-- Erasing order and re-embedding an open standard iPRA proposition
preserves it up to a provable biconditional. -/
noncomputable def standardOrderRoundtripOpen (p : Propositionᵢ L) :
    extended standardTheory ⊢! p 🡘 embed (erase p) :=
  mapExtended id (fun _ _ => rfl) (fun Γ => by simp) (fun d => d)
    (fun σ hσ => theoryToExtended standardTheory (IPRAStandardTheory.native_axiom σ hσ).some)
    (nativeOrderRoundtripOpen p)

/-- Erase order from a standard iPRA finite-context proof. The map acts on
both the assumptions and the conclusion. -/
theorem standardToReferenceSequent {Γ : List (Propositionᵢ L)} {p : Propositionᵢ L}
    (h : Γ ⊢[extended standardTheory] p) :
    Γ.map erase ⊢[extended referenceTheory] erase p := by
  have d := standardToReferenceOpen (FiniteContext.toDef h.some)
  change extended referenceTheory ⊢! erase (⋀Γ) 🡒 erase p at d
  rw [IPRAOrderErasureTheoryTransfer.erase_conj] at d
  exact ⟨FiniteContext.ofDef d⟩

/-- Embed a finite-context proof of the equality-only reference theory into
standard iPRA. -/
theorem referenceToStandardSequent {Γ : List (Propositionᵢ R)} {p : Propositionᵢ R}
    (h : Γ ⊢[extended referenceTheory] p) :
    Γ.map embed ⊢[extended standardTheory] embed p := by
  have d := referenceToStandardOpen (FiniteContext.toDef h.some)
  change extended standardTheory ⊢! embed (⋀Γ) 🡒 embed p at d
  rw [IPRAReferenceTheoryTransfer.embed_conj] at d
  exact ⟨FiniteContext.ofDef d⟩

/-- Read an open standard iPRA proposition under a Concise term assignment. -/
def toConciseProposition {n : ℕ} (free : ℕ → PTm n) (p : Propositionᵢ L) : Fm PTm n :=
  toConciseFormula Fin.elim0 free (erase p)

private theorem imageConj {n : ℕ} (free : ℕ → PTm n) {Δ : List (Fm PTm n)} :
    ∀ (Γ : List (Propositionᵢ R)),
      (∀ p ∈ Γ, Prf PRAAx Δ (toConciseFormula Fin.elim0 free p)) →
      Prf PRAAx Δ (toConciseFormula Fin.elim0 free (⋀Γ))
  | [], _ => Prf.impI Prf.hyp0
  | [p], h => h p (by simp)
  | p :: q :: Γ, h =>
    .andI (h p (by simp)) (imageConj free (q :: Γ) (fun r hr => h r (.tail p hr)))

/-- Transport a standard iPRA sequent under any assignment of its free
variables to Concise terms. -/
theorem standardToConciseSequent {n : ℕ} {Γ : List (Propositionᵢ L)} {p : Propositionᵢ L}
    (h : Γ ⊢[extended standardTheory] p) (free : ℕ → PTm n) :
    Prf PRAAx (Γ.map (toConciseProposition free)) (toConciseProposition free p) := by
  have d := extendedToConcise referenceTheory referenceAxiomImage
    (FiniteContext.toDef (standardToReferenceSequent h).some) free
  let f := toConciseFormula Fin.elim0 free
  change Prf PRAAx [] (.imp (f (⋀(Γ.map erase))) (f (erase p))) at d
  have hΓ : Prf PRAAx ((Γ.map erase).map f) (f (⋀(Γ.map erase))) :=
    imageConj free _ (fun _ hp => .hyp (List.mem_map_of_mem hp))
  change Prf PRAAx (Γ.map (f ∘ erase)) (f (erase p))
  rw [← List.map_map]
  exact .impE (d.weaken (by simp)) hΓ

/-- Read a Concise formula under an assignment of standard iPRA terms. -/
def toStandardInEnv {n : ℕ} (v : Fin n → Term L ℕ) (p : Fm PTm n) : Propositionᵢ L :=
  Rew.embSubsts v ▹ embed (toFoundation p)

private theorem embed_inEnv {n : ℕ} (v : Fin n → Term L ℕ) (p : Fm PTm n) :
    embed (toFoundationInEnv (fun i => Semiterm.lMap termsToReference (v i)) p) =
      toStandardInEnv v p := by
  unfold toFoundationInEnv ConciseToFoundationLogic.atEnv toStandardInEnv
  rw [IPRAReferenceRew.embed_rew]
  have rewImage : IPRAReferenceRew.embedRew
      (Rew.embSubsts (fun i => Semiterm.lMap termsToReference (v i))) = Rew.embSubsts v := by
    ext i
    · simp [IPRAReferenceRew.embedRew, nativeTermRoundtrip]
    · exact Empty.elim i
  rw [rewImage]

/-- Transport a Concise sequent into standard iPRA under arbitrary target
term assignments. -/
theorem conciseToStandardSequent {n : ℕ} {Γ : List (Fm PTm n)} {p : Fm PTm n}
    (h : Prf PRAAx Γ p) (v : Fin n → Term L ℕ) :
    Γ.map (toStandardInEnv v) ⊢[extended standardTheory] toStandardInEnv v p := by
  have d := toFoundation_provable_of_axioms (fun hAx => concise_axiom_image hAx) h
    (fun i => Semiterm.lMap termsToReference (v i))
  simpa only [List.map_map, Function.comp_def, embed_inEnv] using referenceToStandardSequent d

/-- Translating the standard image of a Concise formula back to Concise
amounts to substituting the translated environment for its variables. -/
theorem toConciseProposition_inEnv {m n : ℕ} (free : ℕ → PTm n)
    (v : Fin m → Term L ℕ) (p : Fm PTm m) :
    toConciseProposition free (toStandardInEnv v p) =
      p.subst (fun i => toConciseTerm Fin.elim0 free (Semiterm.lMap termsToReference (v i))) := by
  rw [← embed_inEnv, toConciseProposition, IPRAOrderErasure.erase_embed]
  unfold toFoundationInEnv ConciseToFoundationLogic.atEnv
  have back := toConciseFormula_subst PTm.var Empty.elim
    (fun i => toConciseTerm Fin.elim0 free (Semiterm.lMap termsToReference (v i))) (toFoundation p)
  rw [formula_roundtrip p] at back
  rw [toConciseFormula_rew, back]
  congr 1
  exact funext isEmptyElim

/-- Read each supplied label back as its corresponding Concise variable.
Unused labels may be assigned zero. -/
noncomputable def conciseLabelAssignment {n : ℕ} (label : Fin n ↪ ℕ) : ℕ → PTm n := by
  classical
  exact fun x =>
    if hx : ∃ i, label i = x then Syn.var (Classical.choose hx) else PTm.zero

@[simp] theorem conciseLabelAssignment_apply {n : ℕ} (label : Fin n ↪ ℕ) (i : Fin n) :
    conciseLabelAssignment label (label i) = Syn.var i := by
  have hi : ∃ j, label j = label i := ⟨i, rfl⟩
  simp only [conciseLabelAssignment, dif_pos hi, label.injective (Classical.choose_spec hi)]

/-- Reflection for the standard image of a Concise sequent. Distinct labels
preserve the identity of each variable when transporting the sequent back. -/
theorem conciseSequent_iff {n : ℕ} (label : Fin n ↪ ℕ)
    (Γ : List (Fm PTm n)) (p : Fm PTm n) :
    Prf PRAAx Γ p ↔
      Γ.map (toStandardInEnv (fun i => .fvar (label i))) ⊢[extended standardTheory]
        toStandardInEnv (fun i => .fvar (label i)) p := by
  refine ⟨fun h => conciseToStandardSequent h _, ?_⟩
  intro h
  let free := conciseLabelAssignment label
  have image (q : Fm PTm n) :
      toConciseProposition free (toStandardInEnv (fun i => .fvar (label i)) q) = q := by
    rw [toConciseProposition_inEnv]
    change q.subst (fun i => free (label i)) = q
    simp only [free, conciseLabelAssignment_apply, Fm.subst_id]
  simpa only [List.map_map, Function.comp_def, image, List.map_id_fun', id_eq] using
    standardToConciseSequent h free

end IPRABridge
