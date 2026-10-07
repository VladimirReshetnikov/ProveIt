import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {D G : Type*} {B : D → Type*}

noncomputable def samplerSeparatedVariable (inactive : D → Prop) (h : D → ℕ) :
    SamplerTupleIndex G B h →
      SamplerLongVariables inactive G B h ⊕ (PrincipalTupleIndex B h × Option Empty) := by
  classical
  exact fun
    | .inl g => .inl (.inl g)
    | .inr ⟨d, b, v⟩ =>
        if hd : inactive d then .inr (⟨d, b, v⟩, none)
        else .inl (.inr ⟨⟨d, hd⟩, b, v⟩)

@[simp] theorem samplerSeparatedVariable_common (inactive : D → Prop)
    (h : D → ℕ) (g : G) :
    samplerSeparatedVariable (B := B) inactive h (.inl g) = .inl (.inl g) := rfl

@[simp] theorem samplerSeparatedVariable_inactive (inactive : D → Prop)
    (h : D → ℕ) (d : D) (b : B d) (v : Fin (h d)) (hd : inactive d) :
    samplerSeparatedVariable (G := G) inactive h (.inr ⟨d, b, v⟩) =
      .inr (⟨d, b, v⟩, none) := by
  simp only [samplerSeparatedVariable, hd, dite_true]

@[simp] theorem samplerSeparatedVariable_active (inactive : D → Prop)
    (h : D → ℕ) (d : D) (b : B d) (v : Fin (h d)) (hd : ¬ inactive d) :
    samplerSeparatedVariable (G := G) inactive h (.inr ⟨d, b, v⟩) =
      .inl (.inr ⟨⟨d, hd⟩, b, v⟩) := by
  simp only [samplerSeparatedVariable, hd, dite_false]

def samplerFrozenRaw {R : Type*} [Zero R] (h : D → ℕ)
    (raw : PrincipalTupleIndex B h × Option Empty → R) :
    SamplerTupleIndex G B h → R :=
  fun
    | .inl _ => 0
    | .inr k => raw (k, none)

theorem samplerSeparatedValues_eq_extend {R : Type*} [Zero R]
    (inactive : D → Prop) (h : D → ℕ)
    (long : SamplerLongVariables inactive G B h → R)
    (raw : PrincipalTupleIndex B h × Option Empty → R) :
    Sum.elim long raw ∘ samplerSeparatedVariable inactive h =
      Function.extend (samplerLongEmbedding inactive h) long (samplerFrozenRaw h raw) := by
  funext k
  rcases k with g | ⟨d, b, v⟩
  · exact ((samplerLongEmbedding (B := B) inactive h).injective.extend_apply
      long (samplerFrozenRaw h raw) (.inl g)).symm
  · by_cases hd : inactive d
    · have hn : ¬ ∃ k, samplerLongEmbedding (G := G) inactive h k = .inr ⟨d, b, v⟩ := by
        intro hk
        exact ((samplerLongEmbedding_dedicated_mem_range inactive h d b v).mp hk) hd
      rw [Function.extend_apply' long (samplerFrozenRaw h raw) _ hn]
      simp only [Function.comp_apply, samplerSeparatedVariable_inactive inactive h d b v hd,
        Sum.elim_inr, samplerFrozenRaw]
    · simp only [Function.comp_apply, samplerSeparatedVariable_active inactive h d b v hd,
        Sum.elim_inl]
      exact ((samplerLongEmbedding (G := G) inactive h).injective.extend_apply
        long (samplerFrozenRaw h raw) (.inr ⟨⟨d, hd⟩, b, v⟩)).symm

theorem eval_rename_samplerSeparatedVariable {R : Type*} [CommRing R]
    (inactive : D → Prop) (h : D → ℕ)
    (P : MvPolynomial (SamplerTupleIndex G B h) R)
    (long : SamplerLongVariables inactive G B h → R)
    (raw : PrincipalTupleIndex B h × Option Empty → R) :
    eval (Sum.elim long raw) (rename (samplerSeparatedVariable inactive h) P) =
      eval long (conditionPolynomial (samplerLongEmbedding inactive h)
        (samplerLongEmbedding inactive h).injective (samplerFrozenRaw h raw) P) := by
  rw [eval_rename, samplerSeparatedValues_eq_extend, eval_conditionPolynomial]

end Erdos3

end

end OAI
