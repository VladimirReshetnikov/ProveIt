/-
  Exacting, relatively exacting, cover-exacting and ultraexacting cardinals
  (synthesis Definitions 2.1 and 2.2), together with strongly compact and
  extendible cardinals.

  Structures with a unary predicate, `(V_ α, ∈, Y)`, are handled with Mathlib's
  first-order model theory (language `Lex` with a binary and a unary relation).

  There are no admitted statements in this file.
-/
import Cardinals.Foundations.Basic
import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.Order.Filter.Ultrafilter.Defs
import Cardinals.Combinatorics.Completeness

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal FirstOrder

/-! ### The language `{∈, Y}` -/

/-- Relation symbols: membership and one unary predicate. -/
inductive ExRel : ℕ → Type
  | mem : ExRel 2
  | pred : ExRel 1

/-- The language of set theory with one additional unary predicate. -/
def Lex : Language.{0, 0} := ⟨fun _ => PEmpty, ExRel⟩

/-- The carrier of the structure `(A, ∈, Y ∩ A)`; the predicate is recorded in the
type so that the structure instance can find it. -/
def Str (A _Y : ZFSet.{u}) : Type (u + 1) := {x : ZFSet.{u} // x ∈ A}

instance (A Y : ZFSet.{u}) : Lex.Structure (Str A Y) where
  funMap := fun f => nomatch f
  RelMap := fun {n} r xs =>
    match n, r with
    | _, ExRel.mem => (xs 0).1 ∈ (xs 1).1
    | _, ExRel.pred => (xs 0).1 ∈ Y

/-- A relative `lam`-exacting witness for `(V_ α, ∈, Y)`:
an elementary substructure `X` containing `V_ lam ∪ {lam}` and an elementary
`j : (X, ∈, Y ∩ X) → (V_ α, ∈, Y)` with `j lam = lam` and `j ↾ lam ≠ id`. -/
structure RelWitness (lam α : Ordinal.{u}) (Y : ZFSet.{u}) where
  X : ZFSet.{u}
  X_sub : X ⊆ V_ α
  /-- the inclusion of `X` is elementary -/
  incl : Str X Y ↪ₑ[Lex] Str (V_ α) Y
  incl_val : ∀ x, (incl x).1 = x.1
  j : Str X Y ↪ₑ[Lex] Str (V_ α) Y
  base : V_ lam ⊆ X
  lam_mem : ordZ lam ∈ X
  j_lam : (j ⟨ordZ lam, lam_mem⟩).1 = ordZ lam
  moves : ∃ ξ < lam, ∃ h : ordZ ξ ∈ X, (j ⟨ordZ ξ, h⟩).1 ≠ ordZ ξ

/-- `lam` is exacting relative to the set `Y`: witnesses exist at every
sufficiently large height.  (By synthesis Lemma 3.3(b) this agrees with the
all-admissible-heights convention.) -/
def REx (lam : Ordinal.{u}) (Y : ZFSet.{u}) : Prop :=
  ∃ α₀, ∀ α ≥ α₀, lam < α → Y ⊆ V_ α → Nonempty (RelWitness lam α Y)

/-- `lam` is `γ`-cover exacting. The bound `γ` is fixed before `α` and `y`. -/
def CEx (γ : Cardinal.{u}) (lam : Ordinal.{u}) : Prop :=
  ∀ α > lam, ∀ y ∈ V_ α, ∃ Y : ZFSet.{u},
    Y ⊆ V_ α ∧ y ∈ Y ∧ ZFSet.card Y ≤ γ ∧ Nonempty (RelWitness lam α Y)

/-- `lam` is exacting (witnesses with the empty predicate at every height). -/
def Ex (lam : Ordinal.{u}) : Prop :=
  ∀ α > lam, Nonempty (RelWitness lam α ∅)

/-- A cover-exacting cardinal is exacting: forget the predicate.  -/
theorem CEx.nonempty_witness {γ : Cardinal.{u}} {lam : Ordinal.{u}} (h : CEx γ lam)
    {α : Ordinal.{u}} (hα : lam < α) :
    ∃ Y : ZFSet.{u}, Y ⊆ V_ α ∧ Nonempty (RelWitness lam α Y) := by
  have h0 : (∅ : ZFSet.{u}) ∈ V_ α := by
    rw [mem_vonNeumann, rank_empty]
    exact lt_of_le_of_lt bot_le hα
  obtain ⟨Y, hY, -, -, hw⟩ := h α hα ∅ h0
  exact ⟨Y, hY, hw⟩

/-! ### Strongly compact and extendible cardinals -/

/-- `δ` is strongly compact: uncountable, and every `δ`-complete filter on every
set extends to a `δ`-complete ultrafilter. -/
def SC (δ : Cardinal.{u}) : Prop :=
  ℵ₀ < δ ∧ ∀ (α : Type u) (F : Filter α), F.NeBot → Completeness.IsComplete δ F →
    ∃ U : Ultrafilter α, (U : Filter α) ≤ F ∧ Completeness.IsComplete δ (U : Filter α)

/-- `i` is an elementary embedding `(V_ η, ∈) → (V_ θ, ∈)`. -/
def IsElemEmb (η θ : Ordinal.{u}) (i : Carrier (V_ η) → Carrier (V_ θ)) : Prop :=
  ∀ (φ : SetTheory.Form) (e : ℕ → Carrier (V_ η)),
    SetTheory.Sat (memOn (V_ η)) e φ ↔ SetTheory.Sat (memOn (V_ θ)) (fun n => i (e n)) φ

/-- `δ` is extendible: for every `η > δ` there is an elementary `i : V_ η → V_ θ`
with critical point `δ` and `i δ > η`. -/
def Extendible (δ : Ordinal.{u}) : Prop :=
  ∀ η > δ, ∃ (θ : Ordinal.{u}) (i : Carrier (V_ η) → Carrier (V_ θ)), IsElemEmb η θ i ∧
    (∀ ξ < δ, ∀ h : ordZ ξ ∈ V_ η, (i ⟨ordZ ξ, h⟩).1 = ordZ ξ) ∧
    ∃ (h : ordZ δ ∈ V_ η) (ζ : Ordinal.{u}), (i ⟨ordZ δ, h⟩).1 = ordZ ζ ∧ η < ζ

end Cardinals
