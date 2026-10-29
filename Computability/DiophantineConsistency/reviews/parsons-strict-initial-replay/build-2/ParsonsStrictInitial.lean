import DiophantineConsistency.ParsonsGlobalStrict
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsStrictInitial
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsUnified ParsonsGuardTree ParsonsStrictInvariant ParsonsBaseInvariant ParsonsGlobalStrict ParsonsRule

theorem initial_good {σ : ArithmeticSentence}
    (p : ParsonsTheoryNormalize.NormalizedProof 𝗣𝗔⁻ (Hierarchy 𝚺 1) σ)
    (hσ : Hierarchy 𝚷 2 (Rewriting.emb σ : Proposition ℒₒᵣ))
    (ht : Tree (Rewriting.emb σ : Proposition ℒₒᵣ)) : Good (initial p hσ) := by
  intro e he
  obtain ⟨e',he',rfl⟩ := List.mem_map.mp he
  simp only [ParsonsInvariant.initial, List.mem_append, List.mem_cons, List.mem_map] at he'
  rcases he' with ⟨x,hx,rfl⟩ | rfl | ⟨x,hx,rfl⟩
  · trivial
  · exact ht
  · trivial

theorem initial_strict {σ : ArithmeticSentence}
    (p : ParsonsTheoryNormalize.NormalizedProof 𝗣𝗔⁻ (Hierarchy 𝚺 1) σ)
    (hσ : Hierarchy 𝚷 2 (Rewriting.emb σ : Proposition ℒₒᵣ))
    (hstrict : ∀ φ ∈ p.formulas, Strict φ) : StrictBlocks (initial p hσ) := by
  intro e he
  obtain ⟨e',he',rfl⟩ := List.mem_map.mp he
  simp only [ParsonsInvariant.initial, List.mem_append, List.mem_cons, List.mem_map] at he'
  rcases he' with ⟨x,hx,rfl⟩ | rfl | ⟨x,hx,rfl⟩
  · exact hstrict x.val x.property
  · trivial
  · trivial

/-- A normalized proof whose induction predicates are all syntactically
strict translates to an actual rule proof of any Tree-described conclusion. -/
theorem normalized {σ : ArithmeticSentence}
    (p : ParsonsTheoryNormalize.NormalizedProof 𝗣𝗔⁻ (Hierarchy 𝚺 1) σ)
    (ht : Tree (Rewriting.emb σ : Proposition ℒₒᵣ))
    (hstrict : ∀ φ ∈ p.formulas, Strict φ) :
    Nonempty (Proof 𝗣𝗔⁻ (Rewriting.emb σ)) := by
  let hσ := ht.pi
  let es := initial p hσ
  have hs : Stable es := ⟨initial_good p hσ ht, initial_strict p hσ hstrict, initial_base p hσ⟩
  let d := initial_derivation p hσ
  have hp := translate es d.val hs d.property
  exact ⟨initial_result p hσ hp.some⟩

/-- Embed the strict fragment into the existing Σ₁-normalization record. -/
def widen {σ : ArithmeticSentence}
    (p : ParsonsTheoryNormalize.NormalizedProof 𝗣𝗔⁻ Strict σ) :
    ParsonsTheoryNormalize.NormalizedProof 𝗣𝗔⁻ (Hierarchy 𝚺 1) σ where
  baseAxioms := p.baseAxioms
  formulas := p.formulas
  base_mem := p.base_mem
  formulas_mem := fun φ h => sigma (p.formulas_mem φ h)
  derivation := p.derivation

/-- An actual proof from PA-minus and strict Σ₁ induction translates to the
explicit rule calculus, for a Tree-described sentence. -/
theorem strict_fragment {σ : ArithmeticSentence}
    (p : Theory.Proof (𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ Strict) σ)
    (ht : Tree (Rewriting.emb σ : Proposition ℒₒᵣ)) :
    Nonempty (Proof 𝗣𝗔⁻ (Rewriting.emb σ)) := by
  let np := ParsonsTheoryNormalize.normalizeTheory p
  exact normalized (widen np) ht np.formulas_mem
end DiophantineConsistency.ParsonsStrictInitial
