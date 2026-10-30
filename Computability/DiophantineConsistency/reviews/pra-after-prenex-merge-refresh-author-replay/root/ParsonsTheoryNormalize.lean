import DiophantineConsistency.ParsonsClosure
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsTheoryNormalize
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsClosure
variable {L : Language} [L.ORing]

theorem partition (T : Theory L) (C : Semiproposition L 1 → Prop)
    (A : List (Sentence L))
    (h : ∀ σ ∈ A, σ ∈ T ∪ InductionScheme L C) :
    ∃ (B : List (Sentence L)) (Φ : List (Semiproposition L 1)),
      (∀ σ ∈ B, σ ∈ T) ∧ (∀ φ ∈ Φ, C φ) ∧
      A ⊆ B ++ Φ.map (fun φ ↦ (succInd φ).univCl) := by
  induction A with
  | nil => exact ⟨[], [], by simp⟩
  | cons a A ih =>
    obtain ⟨B, Φ, hb, hf, hs⟩ := ih (fun σ hm => h σ (by simp [hm]))
    have ha := h a (by simp)
    rcases ha with ha | ha
    · refine ⟨a :: B, Φ, ?_, hf, ?_⟩
      · intro σ hm; simp only [List.mem_cons] at hm; rcases hm with rfl | hm
        · exact ha
        · exact hb σ hm
      · intro σ hm; simp only [List.mem_cons] at hm; rcases hm with rfl | hm
        · simp
        · have := hs hm; simp only [List.mem_append, List.mem_cons] at *; tauto
    · obtain ⟨φ, hc, he⟩ := ha
      refine ⟨B, φ :: Φ, hb, ?_, ?_⟩
      · intro ψ hm; simp only [List.mem_cons] at hm; rcases hm with rfl | hm
        · exact hc
        · exact hf ψ hm
      · intro σ hm; simp only [List.mem_cons] at hm; rcases hm with rfl | hm
        · simp [he]
        · have := hs hm; simp only [List.map_cons, List.mem_append, List.mem_cons] at *; tauto

structure NormalizedProof (T : Theory L) (C : Semiproposition L 1 → Prop)
    (σ : Sentence L) where
  baseAxioms : List (Sentence L)
  formulas : List (Semiproposition L 1)
  base_mem : ∀ ψ ∈ baseAxioms, ψ ∈ T
  formulas_mem : ∀ φ ∈ formulas, C φ
  derivation : {d : Derivation (formulas.map normalizedCounterexample ++
    Rewriting.emb σ :: baseAxioms.map (fun ψ => ∼(Rewriting.emb ψ))) // Derivation.IsCutFree d}

noncomputable def normalizeTheory [L.DecidableEq] {T : Theory L} {C : Semiproposition L 1 → Prop}
    {σ : Sentence L} (p : Theory.Proof (T ∪ InductionScheme L C) σ) : NormalizedProof T C σ := by
  let hex := partition T C p.axioms p.axioms_mem
  let B := Classical.choose hex
  let Φ := Classical.choose (Classical.choose_spec hex)
  have h := Classical.choose_spec (Classical.choose_spec hex)
  have d : Derivation (Φ.map (fun φ ↦ ∼((succInd φ).univCl : Proposition L)) ++
      Rewriting.emb σ :: B.map (fun ψ => ∼(Rewriting.emb ψ))) := by
    refine Derivation.contraction p.derivation ?_
    intro χ hc
    simp only [List.tilde_def, List.map_map, Function.comp_def, List.map_cons, List.mem_cons,
      List.mem_map, List.mem_append] at hc ⊢
    rcases hc with hc | ⟨ψ, hψ, rfl⟩
    · exact Or.inr (Or.inl hc)
    · have hp := h.2.2 hψ
      simp only [List.mem_append, List.mem_map] at hp
      rcases hp with hp | ⟨φ, hp, rfl⟩
      · exact Or.inr (Or.inr ⟨ψ, hp, by simp⟩)
      · exact Or.inl ⟨φ, hp, by simp⟩
  exact ⟨B, Φ, h.1, h.2.1, normalized_cut_free Φ _ d⟩
/-- Every actual IΣ₁ proof has a normalized cut-free sequent with only
PA-minus axioms left in the base context. -/
noncomputable def normalizeISigma {σ : ArithmeticSentence} (p : Theory.Proof 𝗜𝚺₁ σ) :
    NormalizedProof 𝗣𝗔⁻ (Hierarchy 𝚺 1) σ := normalizeTheory p

theorem isigma_has_normalized {σ : ArithmeticSentence} (h : 𝗜𝚺₁ ⊢ σ) :
    Nonempty (NormalizedProof 𝗣𝗔⁻ (Hierarchy 𝚺 1) σ) := by
  obtain ⟨p⟩ := h
  exact ⟨normalizeISigma p⟩

end DiophantineConsistency.ParsonsTheoryNormalize
