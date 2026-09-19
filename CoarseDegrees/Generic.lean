import CoarseDegrees.Sets
import Mathlib.Computability.PartrecCode

/-!
# Existence of 1-generic sets

The classical finite-extension construction (Jockusch 1980; Downey--Hirschfeldt 2010, §2.24):
list all codes of partial computable functions; at stage `s` extend the current string into the
`s`-th c.e. set of strings if that is possible, and leave it alone otherwise.  The construction
is carried out classically, so no oracle bound is obtained (the textbook proof gives
`X ≤ᵀ ∅'`).  Everything in this file is proved.
-/

noncomputable section

open scoped Classical
open Nat.Partrec (Code)

namespace CoarseDegrees

/-- The c.e. set of strings with index `c`: the strings on which the code `c` halts. -/
def accepts (c : Code) (σ : List Bool) : Prop :=
  (c.eval (Encodable.encode σ)).Dom

/-- Every c.e. set of strings has an index. -/
theorem exists_code_of_rePred {W : List Bool → Prop} (hW : REPred W) :
    ∃ c : Code, ∀ σ, accepts c σ ↔ W σ := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hW
  refine ⟨c, fun σ => ?_⟩
  unfold accepts
  rw [hc]
  simp only [Encodable.encodek, Part.coe_some, Part.bind_some, Part.map_Dom]
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    exact ⟨h, trivial⟩

/-- One stage: extend `σ` into the set with index `c` if possible, then append a bit so that
the strings grow. -/
def step (c : Option Code) (σ : List Bool) : List Bool :=
  match c with
  | none => σ ++ [false]
  | some c =>
    if h : ∃ τ, σ <+: τ ∧ accepts c τ then h.choose ++ [false] else σ ++ [false]

theorem prefix_step (c : Option Code) (σ : List Bool) : σ <+: step c σ := by
  unfold step
  cases c with
  | none => exact List.prefix_append _ _
  | some c =>
    by_cases h : ∃ τ, σ <+: τ ∧ accepts c τ
    · simp only [h, dif_pos]
      exact h.choose_spec.1.trans (List.prefix_append _ _)
    · simp only [h, dif_neg, not_false_eq_true]
      exact List.prefix_append _ _

theorem length_step (c : Option Code) (σ : List Bool) : σ.length < (step c σ).length := by
  unfold step
  cases c with
  | none => simp
  | some c =>
    by_cases h : ∃ τ, σ <+: τ ∧ accepts c τ
    · simp only [h, dif_pos, List.length_append, List.length_singleton]
      exact Nat.lt_succ_of_le h.choose_spec.1.length_le
    · simp [h]

/-- The strings built by the construction. -/
def stage : ℕ → List Bool
  | 0 => []
  | s + 1 => step (Encodable.decode s) (stage s)

theorem stage_prefix_succ (s : ℕ) : stage s <+: stage (s + 1) :=
  prefix_step _ _

theorem stage_mono {s t : ℕ} (h : s ≤ t) : stage s <+: stage t := by
  induction t, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t _ ih => exact ih.trans (stage_prefix_succ t)

/-- The set built by the construction. -/
def genericSet : Set ℕ := {i | ∃ s, (stage s)[i]? = some true}

theorem isPrefixOf_stage (s : ℕ) : IsPrefixOf (stage s) genericSet := by
  intro i hi
  constructor
  · intro h
    exact ⟨s, by rw [List.getElem?_eq_getElem hi, h]⟩
  · rintro ⟨t, ht⟩
    have hit : i < (stage t).length := by
      by_contra hcon
      rw [List.getElem?_eq_none (not_lt.mp hcon)] at ht
      exact absurd ht (by simp)
    rw [List.getElem?_eq_getElem hit] at ht
    have htrue : (stage t)[i] = true := Option.some.inj ht
    rcases le_total s t with hst | hts
    · exact ((stage_mono hst).getElem hi).trans htrue
    · exact ((stage_mono hts).getElem hit).symm.trans htrue

theorem IsPrefixOf.of_prefix {σ τ : List Bool} {X : Set ℕ} (h : σ <+: τ)
    (hτ : IsPrefixOf τ X) : IsPrefixOf σ X := by
  intro i hi
  rw [h.getElem hi]
  exact hτ i (lt_of_lt_of_le hi h.length_le)

/-- The set built by the construction is 1-generic. -/
theorem oneGeneric_genericSet : OneGeneric genericSet := by
  intro W hW
  obtain ⟨c, hc⟩ := exists_code_of_rePred hW
  have hdec : Encodable.decode (α := Code) (Encodable.encode c) = some c := Encodable.encodek c
  by_cases h : ∃ τ, stage (Encodable.encode c) <+: τ ∧ accepts c τ
  · refine ⟨h.choose, ?_, Or.inl ((hc _).mp h.choose_spec.2)⟩
    refine IsPrefixOf.of_prefix ?_ (isPrefixOf_stage (Encodable.encode c + 1))
    show h.choose <+: step (Encodable.decode (Encodable.encode c)) (stage (Encodable.encode c))
    rw [hdec]
    simp only [step, h, dif_pos]
    exact List.prefix_append _ _
  · refine ⟨stage (Encodable.encode c), isPrefixOf_stage _, Or.inr fun τ hτ hWτ => ?_⟩
    exact h ⟨τ, hτ, (hc τ).mpr hWτ⟩

/-- 1-generic sets exist. -/
theorem exists_oneGeneric : ∃ X : Set ℕ, OneGeneric X :=
  ⟨genericSet, oneGeneric_genericSet⟩

end CoarseDegrees
