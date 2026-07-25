import ZFCinPA.ReplacementDelta1

/-!
# `𝗭𝗙` and `𝗭𝗙𝗖` are `Δ₁` theories

`𝗭𝗙` decomposes as the union of the equality axioms `𝗘𝗤 ℒₛₑₜ` (finite, since
`ℒₛₑₜ` is a finite language), seven fixed axioms, and the separation and
replacement schemata.  The first two parts are `Δ₁` by Foundation's finite
combinators; the schemata are `Δ₁` by `ZFCinPA.SeparationDelta1` and
`ZFCinPA.ReplacementDelta1`.  `𝗔𝗖` is a singleton, and `𝗭𝗙𝗖 = 𝗭𝗙 ∪ 𝗔𝗖`
follows from the union combinator.

With `Theory.Δ₁` in place, Foundation's generic arithmetized provability
predicate `Bootstrapping.Provable` and the Hilbert–Bernays condition **D1**
(`internalize_provability`) become available for `𝗭𝗙𝗖`.
-/

namespace LeanProofs.ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory

/-! ## The decomposition of `𝗭𝗙` -/

/-- The seven fixed (non-schematic, non-equality) axioms of `𝗭𝗙`. -/
def zfFixed : SetTheory :=
  {Axiom.empty, Axiom.extentionality, Axiom.pairing, Axiom.union,
    Axiom.power, Axiom.infinity, Axiom.foundation}

/-- `𝗭𝗙`, decomposed into equality axioms, fixed axioms, and the two schemata. -/
lemma zf_eq :
    (𝗭𝗙 : SetTheory) = 𝗘𝗤 ℒₛₑₜ ∪ zfFixed ∪ separationTheory ∪ replacementTheory := by
  ext φ
  constructor
  · rintro ⟨h⟩
    · exact Or.inl (Or.inl (Or.inl (by assumption)))
    · exact Or.inl (Or.inl (Or.inr (by simp [zfFixed])))
    · exact Or.inl (Or.inl (Or.inr (by simp [zfFixed])))
    · exact Or.inl (Or.inl (Or.inr (by simp [zfFixed])))
    · exact Or.inl (Or.inl (Or.inr (by simp [zfFixed])))
    · exact Or.inl (Or.inl (Or.inr (by simp [zfFixed])))
    · exact Or.inl (Or.inl (Or.inr (by simp [zfFixed])))
    · exact Or.inl (Or.inl (Or.inr (by simp [zfFixed])))
    · exact Or.inl (Or.inr ⟨_, rfl⟩)
    · exact Or.inr ⟨_, rfl⟩
  · rintro (((h | h) | ⟨ψ, rfl⟩) | ⟨ψ, rfl⟩)
    · exact ZermeloFraenkel.axiom_of_equality φ h
    · simp only [zfFixed, Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ZermeloFraenkel.axiom_of_empty_set
      · exact ZermeloFraenkel.axiom_of_extentionality
      · exact ZermeloFraenkel.axiom_of_pairing
      · exact ZermeloFraenkel.axiom_of_union
      · exact ZermeloFraenkel.axiom_of_power_set
      · exact ZermeloFraenkel.axiom_of_infinity
      · exact ZermeloFraenkel.axiom_of_foundation
    · exact ZermeloFraenkel.axiom_of_separation ψ
    · exact ZermeloFraenkel.axiom_of_replacement ψ

/-! ## `Δ₁` of the pieces -/

/-- The equality axioms of `ℒₛₑₜ` form a finite, hence `Δ₁`, theory. -/
noncomputable instance eqAxiom_delta1 : (𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁ :=
  Theory.Δ₁.ofFinite _ Theory.EqAxiom.finite

/-- The seven fixed axioms of `𝗭𝗙` form a `Δ₁` theory. -/
noncomputable instance zfFixed_delta1 : zfFixed.Δ₁ :=
  (Theory.Δ₁.ofList
    [Axiom.empty, Axiom.extentionality, Axiom.pairing, Axiom.union,
      Axiom.power, Axiom.infinity, Axiom.foundation]).ofEq (by ext φ; simp [zfFixed])

/-! ## The headline instances -/

/-- `𝗭𝗙` is a `Δ₁` theory. -/
noncomputable instance ZF_delta1 : (𝗭𝗙 : SetTheory).Δ₁ :=
  Theory.Δ₁.ofEq inferInstance zf_eq.symm

/-- `𝗔𝗖` is a singleton, hence a `Δ₁` theory. -/
noncomputable instance AC_delta1 : (𝗔𝗖 : SetTheory).Δ₁ :=
  (Theory.Δ₁.singleton Axiom.choice).ofEq rfl

/-- `𝗭𝗙𝗖` is a `Δ₁` theory. -/
noncomputable instance ZFC_delta1 : (𝗭𝗙𝗖 : SetTheory).Δ₁ :=
  inferInstance

/-! ## Smoke tests

The generic arithmetized provability layer now fires for `𝗭𝗙𝗖`: the internal
provability predicate elaborates over `ℕ`, and the derivability condition D1
internalizes actual `𝗭𝗙𝗖`-derivations. -/

#check (Bootstrapping.Provable (V := ℕ) (T := (𝗭𝗙𝗖 : SetTheory)))

#check fun (σ : SetTheorySentence) (h : 𝗭𝗙𝗖 ⊢ σ) =>
  Bootstrapping.internalize_provability (V := ℕ) h

#check fun (σ : SetTheorySentence) (h : 𝗭𝗙𝗖 ⊢ σ) =>
  Bootstrapping.internal_provable_of_outer_provable (V := ℕ) h

end LeanProofs.ZFCinPA
