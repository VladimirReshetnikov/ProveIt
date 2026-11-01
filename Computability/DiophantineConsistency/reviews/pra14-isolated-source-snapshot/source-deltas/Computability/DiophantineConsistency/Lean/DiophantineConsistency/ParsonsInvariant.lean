import DiophantineConsistency.ParsonsBlock
import DiophantineConsistency.ParsonsFold
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsInvariant
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsStructure ParsonsBlock ParsonsOpened

/-- A sequent occurrence retains its role even if another occurrence has the
same formula. An induction block carries its exact partially opened state. -/
inductive Entry where
  | side (P : Proposition ℒₒᵣ) (hP : Hierarchy 𝚷 2 P)
  | base (σ : ArithmeticSentence) (h : σ ∈ 𝗣𝗔⁻)
  | block (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 1 φ)
      (n : ℕ) (A : ArithmeticSemiformula ℕ n) (h : State φ A)

def Entry.formula : Entry → Proposition ℒₒᵣ
  | .side P _ => P
  | .base σ _ => ∼(Rewriting.emb σ)
  | .block _ _ _ A _ => ∃⁰* A

def Entry.output : Entry → Proposition ℒₒᵣ
  | .side P _ => P
  | .base _ _ => ⊥
  | .block _ _ _ _ _ => ⊥

theorem output_pi_two (es : List Entry) : Hierarchy 𝚷 2 (disjoin (es.map Entry.output)) := by
  induction es with
  | nil => simp [disjoin]
  | cons e es ih =>
    cases e with
    | side P hP => simpa [disjoin, Entry.output] using And.intro hP ih
    | base σ h => simpa [disjoin, Entry.output] using ih
    | block φ hφ n A hs => simpa [disjoin, Entry.output] using ih

def Entry.isBlock : Entry → Prop
  | .block _ _ _ _ _ => True
  | _ => False

def ordinary : List Entry → List (Proposition ℒₒᵣ)
  | [] => []
  | .side P _ :: es => P :: ordinary es
  | _ :: es => ordinary es

def bases : List Entry → List ArithmeticSentence
  | [] => []
  | .base σ _ :: es => σ :: bases es
  | _ :: es => bases es

theorem bases_mem (es : List Entry) (σ : ArithmeticSentence) : σ ∈ bases es → σ ∈ 𝗣𝗔⁻ := by
  induction es with
  | nil => simp [bases]
  | cons e es ih =>
    cases e with
    | side P hP => simpa [bases] using ih
    | base τ h =>
      simp only [bases, List.mem_cons]
      rintro (rfl | hmem)
      · exact h
      · exact ih hmem
    | block φ hφ n A hs => simpa [bases] using ih

theorem ordinary_subset_output (es : List Entry) : ordinary es ⊆ es.map Entry.output := by
  induction es with
  | nil => simp [ordinary]
  | cons e es ih =>
    cases e with
    | side P hP =>
      intro Q hQ
      simp only [ordinary, List.mem_cons] at hQ
      rcases hQ with rfl | hQ
      · simp [Entry.output]
      · simp only [List.map_cons, List.mem_cons]
        exact Or.inr (ih hQ)
    | base σ h =>
      intro Q hQ
      simp only [ordinary] at hQ
      simp only [List.map_cons, List.mem_cons]
      exact Or.inr (ih hQ)
    | block φ hφ n A hs =>
      intro Q hQ
      simp only [ordinary] at hQ
      simp only [List.map_cons, List.mem_cons]
      exact Or.inr (ih hQ)

theorem plain_subset_base (es : List Entry)
    (hn : ∀ e ∈ es, ¬e.isBlock) :
    es.map Entry.formula ⊆ ordinary es ++ (bases es).map (fun σ => ∼(Rewriting.emb σ)) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have htail : ∀ e ∈ es, ¬e.isBlock := by intro x hx; exact hn x (by simp [hx])
    have ht := ih htail
    intro P hp
    simp only [List.map_cons, List.mem_cons] at hp
    rcases hp with hp | hp
    · subst P
      cases e with
      | side Q hQ => simp [ordinary, Entry.formula]
      | base σ h => simp [ordinary, bases, Entry.formula]
      | block φ hφ n A hs =>
        have hb := hn (Entry.block φ hφ n A hs) (by simp)
        simp [Entry.isBlock] at hb
    · have hm := ht hp
      cases e with
      | side Q hQ =>
        simp only [ordinary, bases, List.cons_append, List.mem_cons]
        exact Or.inr hm
      | base σ h =>
        simp only [ordinary, bases, List.map_cons, List.mem_append, List.mem_cons] at hm ⊢
        tauto
      | block φ hφ n A hs =>
        have hb := hn (Entry.block φ hφ n A hs) (by simp)
        simp [Entry.isBlock] at hb

/-- The complete base-only branch for a marked, arbitrarily interleaved
context; side contributions are retained and no block is silently removed. -/
noncomputable def base_branch (es : List Entry)
    (hn : ∀ e ∈ es, ¬e.isBlock) (d : Derivation (es.map Entry.formula)) :
    Proof 𝗣𝗔⁻ (disjoin (es.map Entry.output)) := by
  have hs := plain_subset_base es hn
  have hd : Derivation (ordinary es ++ (bases es).map (fun σ => ∼(Rewriting.emb σ))) :=
    d.contra hs
  have hp := ParsonsFold.base_leaf (ordinary es) (bases es) (bases_mem es) hd
  exact weakening (ordinary es) (es.map Entry.output) (ordinary_subset_output es) hp

/-- Select a marked occurrence for each formula in a premise sub-sequent.
Different occurrences of the same formula may have different roles. -/
noncomputable def selectEntries (Δ : Sequent ℒₒᵣ) (es : List Entry)
    (hsub : Δ ⊆ es.map Entry.formula) : List Entry :=
  Δ.attach.map (fun x => Classical.choose (List.mem_map.mp (hsub x.property)))

theorem selected_subset (Δ : Sequent ℒₒᵣ) (es : List Entry)
    (hsub : Δ ⊆ es.map Entry.formula) : selectEntries Δ es hsub ⊆ es := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  exact (Classical.choose_spec (List.mem_map.mp (hsub x.property))).1

theorem selected_formulas (Δ : Sequent ℒₒᵣ) (es : List Entry)
    (hsub : Δ ⊆ es.map Entry.formula) :
    (selectEntries Δ es hsub).map Entry.formula = Δ := by
  simp only [selectEntries, List.map_map, Function.comp_def]
  rw [show (fun x : {P // P ∈ Δ} => Entry.formula
      (Classical.choose (List.mem_map.mp (hsub x.property)))) = Subtype.val by
    funext x
    exact (Classical.choose_spec (List.mem_map.mp (hsub x.property))).2]
  exact List.attach_map_subtype_val Δ

theorem selected_outputs_subset (Δ : Sequent ℒₒᵣ) (es : List Entry)
    (hsub : Δ ⊆ es.map Entry.formula) :
    (selectEntries Δ es hsub).map Entry.output ⊆ es.map Entry.output := by
  intro P hp
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
  exact List.mem_map.mpr ⟨e, selected_subset Δ es hsub he, rfl⟩

/-- Contraction for marked contexts, preserving the chosen role of each
premise occurrence and invoking a strictly smaller cut-free derivation. -/
theorem marked_contraction (Δ : Sequent ℒₒᵣ) (es : List Entry)
    (hsub : Δ ⊆ es.map Entry.formula) (d : Derivation Δ) (hc : Derivation.IsCutFree d)
    (ih : ∀ (e : Derivation Δ), Derivation.IsCutFree e →
      e.height < (d.contraction hsub).height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((selectEntries Δ es hsub).map Entry.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin (es.map Entry.output))) := by
  have hh : d.height < (d.contraction hsub).height := by simp
  exact ⟨weakening _ _ (selected_outputs_subset Δ es hsub) (ih d hc hh).some⟩

def initialBlock (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 1 φ) : Entry :=
  Entry.block φ hφ _ (normalizedBody φ) (ParsonsBlock.start φ)

/-- Tag the actual normalized IΣ₁ output: each induction formula starts with
its certified parameter block, the conclusion is the sole side entry, and
all retained base entries carry PA-minus membership. -/
def initial {σ : ArithmeticSentence}
    (p : ParsonsTheoryNormalize.NormalizedProof 𝗣𝗔⁻ (Hierarchy 𝚺 1) σ)
    (hσ : Hierarchy 𝚷 2 (Rewriting.emb σ : Proposition ℒₒᵣ)) : List Entry :=
  p.formulas.attach.map (fun x => initialBlock x.val (p.formulas_mem x.val x.property)) ++
  Entry.side (Rewriting.emb σ) hσ ::
  p.baseAxioms.attach.map (fun x => Entry.base x.val (p.base_mem x.val x.property))

theorem initial_formulas {σ : ArithmeticSentence}
    (p : ParsonsTheoryNormalize.NormalizedProof 𝗣𝗔⁻ (Hierarchy 𝚺 1) σ)
    (hσ : Hierarchy 𝚷 2 (Rewriting.emb σ : Proposition ℒₒᵣ)) :
    (initial p hσ).map Entry.formula = p.formulas.map ParsonsClosure.normalizedCounterexample ++
      Rewriting.emb σ :: p.baseAxioms.map (fun τ => ∼(Rewriting.emb τ)) := by
  simp [initial, initialBlock, Entry.formula, ParsonsOpened.normalized_shape, List.map_map, Function.comp_def]

/-- The marked global invariant starts from the actual normalized cut-free
proof; no relationship to the height before cut elimination is asserted. -/
def initial_derivation {σ : ArithmeticSentence}
    (p : ParsonsTheoryNormalize.NormalizedProof 𝗣𝗔⁻ (Hierarchy 𝚺 1) σ)
    (hσ : Hierarchy 𝚷 2 (Rewriting.emb σ : Proposition ℒₒᵣ)) :
    {d : Derivation ((initial p hσ).map Entry.formula) // Derivation.IsCutFree d} := by
  rw [initial_formulas]
  exact p.derivation

/-- The marked initial output contains the desired sentence as its only
non-false contribution. -/
noncomputable def initial_result {σ : ArithmeticSentence}
    (p : ParsonsTheoryNormalize.NormalizedProof 𝗣𝗔⁻ (Hierarchy 𝚺 1) σ)
    (hσ : Hierarchy 𝚷 2 (Rewriting.emb σ : Proposition ℒₒᵣ))
    (h : Proof 𝗣𝗔⁻ (disjoin ((initial p hσ).map Entry.output))) :
    Proof 𝗣𝗔⁻ (Rewriting.emb σ) := by
  have hi : Proof 𝗣𝗔⁻ (disjoin ((initial p hσ).map Entry.output) 🡒 Rewriting.emb σ) :=
    ParsonsGuardedCollection.of_semantics _ _ (by
      intro M _ _ f hp
      rw [ParsonsStructure.eval_disjoin] at hp
      simp [initial, initialBlock, Entry.output, List.mem_append] at hp
      obtain ⟨P, hP, hv⟩ := hp
      rcases hP with ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩
      · simp at hv
      · exact hv
      · simp at hv)
  exact .mp hi h

end DiophantineConsistency.ParsonsInvariant
