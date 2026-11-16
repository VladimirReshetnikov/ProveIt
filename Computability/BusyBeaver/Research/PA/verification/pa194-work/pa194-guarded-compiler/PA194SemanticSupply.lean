import PA194NameFactsProof
import PA194TypedTheory
import PA194AdjunctiveFullSep
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Fixed facts about the source theory from truth in its models

The fixed hypotheses of the guarded compiler (`SourceFacts`, `sA3`, `sM3`, `sAP`, …) are
typed quotes of standard formulas, `tHyp φ = ⌜sinst tau0 φ⌝`. By the completeness theorem and
the first derivability condition, such a hypothesis is internally provable in every model of
arithmetic as soon as the standard formula holds in every structure that satisfies the source
theory. No derivation has to be written.

* `letterStructure τ s f`: a structure for the source language `L` becomes a structure for the
  language of the letters, each letter being read as the standard formula `τ` assigns to it.
* `eval_sinst`: truth of the standard instance `sinst τ φ` is truth of `φ` in that structure.
  So the statements `ev_sE1`, …, `ev_sAP`, … of `PA194NameSemantics` and its successors
  describe the instance directly.
* `sinst_closed`: the standard instance of closed formulas has no free variable.
* `source_supply`: let `φ` be a sentence over the letters. Assume that `φ` is true in the
  letter structure of every nonempty structure `N` of the relational source language in
  which equality is equality, weak adjunction holds, and every separation instance holds at
  every assignment of its parameters. Then
  `adjunctiveFullSepTheory.internalize V ⊢ tHyp φ` for every model `V` of `𝗜𝚺₁`.

The module proves no fact about the source theory; it changes what has to be proved.
-/
namespace PA194Schematic
open LO LO.FirstOrder
open scoped LO.FirstOrder

section instances
variable {L : Language} {ι : Type} {ar : ι → ℕ}

/-- The relations of the letter structure. -/
def letterRel (τ : (i : ι) → Semiproposition L (ar i)) {N : Type} (s : Structure L N)
    (f : ℕ → N) : {k : ℕ} → BoxRel ar k → (Fin k → N) → Prop
  | _, .box i => fun v => FirstOrder.Semiformula.Eval (s := s) v f (τ i)

/-- A structure for `L` as a structure for the letters: the letter `i` is the relation
defined by `τ i`. -/
@[reducible] def letterStructure (τ : (i : ι) → Semiproposition L (ar i)) {N : Type} (s : Structure L N)
    (f : ℕ → N) : Structure (boxL ar) N where
  func := fun _ g _ => nomatch g
  rel := fun _ r v => letterRel τ s f r v

theorem val_tstd {N : Type} (s : Structure L N) (s' : Structure (boxL ar) N) (f : ℕ → N)
    {n : ℕ} (b : Fin n → N) (t : FirstOrder.Semiterm (boxL ar) Empty n) :
    FirstOrder.Semiterm.val (s := s) b f (tstd (L := L) t) = FirstOrder.Semiterm.val (s := s') b Empty.elim t := by
  cases t with
  | bvar i => simp [tstd]
  | fvar x => exact nomatch x
  | func g _ => exact nomatch g

/-- Truth of a standard instance. -/
theorem eval_sinst (τ : (i : ι) → Semiproposition L (ar i)) {N : Type} (s : Structure L N)
    (f : ℕ → N) {n : ℕ} (b : Fin n → N) (φ : FirstOrder.Semiformula (boxL ar) Empty n) :
    FirstOrder.Semiformula.Eval (s := s) b f (sinst τ φ) ↔
      FirstOrder.Semiformula.Eval (s := letterStructure τ s f) b Empty.elim φ := by
  induction φ using FirstOrder.Semiformula.rec'
  case hrel k r v =>
    cases r with
    | box i =>
      show FirstOrder.Semiformula.Eval (s := s) b f ((τ i) ⇜ fun j => tstd (v j)) ↔
        letterRel τ s f (.box i)
          (fun j => FirstOrder.Semiterm.val (s := letterStructure τ s f) b Empty.elim (v j))
      rw [FirstOrder.Semiformula.eval_substs]
      have e : (FirstOrder.Semiterm.val (s := s) b f ∘ fun j => tstd (L := L) (v j)) =
          fun j => FirstOrder.Semiterm.val (s := letterStructure τ s f) b Empty.elim (v j) :=
        funext fun j => val_tstd s _ f b (v j)
      rw [e]
      rfl
  case hnrel k r v =>
    cases r with
    | box i =>
      show FirstOrder.Semiformula.Eval (s := s) b f (∼((τ i) ⇜ fun j => tstd (L := L) (v j))) ↔
        ¬letterRel τ s f (.box i)
          (fun j => FirstOrder.Semiterm.val (s := letterStructure τ s f) b Empty.elim (v j))
      have h0 : FirstOrder.Semiformula.Eval (s := s) b f
            (∼((τ i) ⇜ fun j => tstd (L := L) (v j))) ↔
          ¬FirstOrder.Semiformula.Eval (s := s) b f ((τ i) ⇜ fun j => tstd (L := L) (v j)) := by
        simp
      rw [h0, FirstOrder.Semiformula.eval_substs]
      have e : (FirstOrder.Semiterm.val (s := s) b f ∘ fun j => tstd (L := L) (v j)) =
          fun j => FirstOrder.Semiterm.val (s := letterStructure τ s f) b Empty.elim (v j) :=
        funext fun j => val_tstd s _ f b (v j)
      rw [e]
      rfl
  case hverum => simp [sinst]
  case hfalsum => simp [sinst]
  case hand φ ψ ihφ ihψ => simp [sinst, ihφ, ihψ]
  case hor φ ψ ihφ ihψ => simp [sinst, ihφ, ihψ]
  case hall φ ih => simp [sinst, ih]
  case hexs φ ih => simp [sinst, ih]

theorem tstd_closed {n : ℕ} (t : FirstOrder.Semiterm (boxL ar) Empty n) (x : ℕ) :
    ¬(tstd (L := L) t).FVar? x := by
  cases t with
  | bvar i => simp [tstd]
  | fvar x => exact nomatch x
  | func g _ => exact nomatch g

/-- The standard instance of closed formulas is closed. -/
theorem sinst_closed (τ : (i : ι) → Semiproposition L (ar i))
    (hτ : ∀ i, (τ i).freeVariables = ∅) {n : ℕ}
    (φ : FirstOrder.Semiformula (boxL ar) Empty n) : (sinst τ φ).freeVariables = ∅ := by
  induction φ using FirstOrder.Semiformula.rec'
  case hrel k r v =>
    cases r with
    | box i =>
      show ((τ i) ⇜ fun j => tstd (v j)).freeVariables = ∅
      ext x
      suffices x ∉ ((τ i) ⇜ fun j => tstd (L := L) (v j)).freeVariables by simpa using this
      intro hx
      rcases FirstOrder.Semiformula.fvar?_rew hx with (⟨j, hj⟩ | ⟨z, hz, _⟩)
      · exact tstd_closed (L := L) (v j) x (by simpa using hj)
      · have hz' : z ∈ (τ i).freeVariables := hz
        rw [hτ i] at hz'
        simp at hz'
  case hnrel k r v =>
    cases r with
    | box i =>
      show (∼((τ i) ⇜ fun j => tstd (v j))).freeVariables = ∅
      rw [FirstOrder.Semiformula.freeVariables_not]
      ext x
      suffices x ∉ ((τ i) ⇜ fun j => tstd (L := L) (v j)).freeVariables by simpa using this
      intro hx
      rcases FirstOrder.Semiformula.fvar?_rew hx with (⟨j, hj⟩ | ⟨z, hz, _⟩)
      · exact tstd_closed (L := L) (v j) x (by simpa using hj)
      · have hz' : z ∈ (τ i).freeVariables := hz
        rw [hτ i] at hz'
        simp at hz'
  case hverum => simp [sinst]
  case hfalsum => simp [sinst]
  case hand φ ψ ihφ ihψ => simp [sinst, ihφ, ihψ]
  case hor φ ψ ihφ ihψ => simp [sinst, ihφ, ihψ]
  case hall φ ih => simp [sinst, ih]
  case hexs φ ih => simp [sinst, ih]

#print axioms eval_sinst
#print axioms sinst_closed
end instances
end PA194Schematic

namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher PA194Schematic
open M6.PA.RelationalSource

attribute [local instance] PA194ModelLogic.sourceLanguageAdjTheory

/-- The standard formulas of the letters are closed. -/
theorem tau0_closed : ∀ l : Letter, (tau0 l).freeVariables = ∅ := by
  intro l
  cases l with
  | val i => rfl
  | _ => decide

/-- The structure of the letters on a structure of the relational source language. -/
abbrev sourceLetters {N : Type} (s : Structure SourceL N) (f : ℕ → N) : Structure NL N :=
  letterStructure tau0 s f

theorem eqAxiom_subset : (𝗘𝗤 SourceL : Theory SourceL) ⊆ adjunctiveFullSepTheory := by
  intro σ hσ
  refine Or.inl ?_
  rw [adjunctiveTheory_eq]
  exact Or.inl hσ

theorem weakAdjunction_mem : sourceWeakAdjunction ∈ adjunctiveFullSepTheory := by
  refine Or.inl ?_
  rw [adjunctiveTheory_eq]
  exact Or.inr rfl

theorem separation_mem (p : Semiproposition SourceL 1) :
    (separationFormula p).univCl ∈ adjunctiveFullSepTheory :=
  Or.inr ((PA194TypedSchema.fullSepTheory_mem_iff_typed _).mpr ⟨p, rfl⟩)

section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local instance] adjunctiveFullSepTheoryDelta

/-- A fixed hypothesis of the guarded compiler is internally provable in the source theory
if it is true in the letter structure of every structure with equality that satisfies weak
adjunction and all separation instances. -/
theorem source_supply (φ : SF 0)
    (H : ∀ (N : Type) [Nonempty N] [s : Structure SourceL N] [Structure.Eq SourceL N],
      N↓[SourceL] ⊧ sourceWeakAdjunction →
      (∀ (p : Semiproposition SourceL 1) (f : ℕ → N),
        FirstOrder.Semiformula.Evalf (s := s) f (separationFormula p)) →
      ∀ f : ℕ → N,
        FirstOrder.Semiformula.Eval (s := sourceLetters s f) (![] : Fin 0 → N) Empty.elim φ) :
    adjunctiveFullSepTheory.internalize V ⊢ (tHyp φ : Bootstrapping.Semiformula V SourceL 0) := by
  have hfv : (sinst tau0 φ).freeVariables = ∅ := sinst_closed tau0 tau0_closed φ
  haveI : (𝗘𝗤 SourceL : Theory SourceL) ⪯ adjunctiveFullSepTheory :=
    Entailment.WeakerThan.ofSubset eqAxiom_subset
  have hT : adjunctiveFullSepTheory ⊢ (sinst tau0 φ).univCl := by
    apply Theory.Proof.complete_on_eq_models
    intro N _ s _ hN
    apply models_iff_proposition.mpr
    intro f
    have hwa : N↓[SourceL] ⊧ sourceWeakAdjunction :=
      models_theory_iff.mp hN _ weakAdjunction_mem
    have hsep : ∀ (p : Semiproposition SourceL 1) (g : ℕ → N),
        FirstOrder.Semiformula.Evalf (s := s) g (separationFormula p) := fun p =>
      models_iff_proposition.mp (models_theory_iff.mp hN _ (separation_mem p))
    have e : (![] : Fin 0 → N) = Matrix.vecEmpty := rfl
    exact (eval_sinst tau0 s f (![] : Fin 0 → N) φ).mpr (H N hwa hsep f)
  have h1 : Provable adjunctiveFullSepTheory (⌜(sinst tau0 φ).univCl⌝ : V) :=
    internalize_provability hT
  have e0 : (Rewriting.emb (sinst tau0 φ).univCl : Proposition SourceL) = sinst tau0 φ := by
    rw [FirstOrder.Semiformula.coe_univCl_eq_univCl']
    exact FirstOrder.Semiformula.univCl'_eq_self_of _ hfv
  rw [Sentence.quote_def, e0] at h1
  rw [tHyp_eq_quote]
  exact tprovable_tquote_iff_provable_quote.mpr h1

#print axioms tau0_closed
#print axioms source_supply
end generic
end PA194GuardedCompiler
