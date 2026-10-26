import DiophantineConsistency.NativeEnumeratorBounds

/-! # Isolating the single trace used by the native enumerator

These named rows expose the metadata of the existing iterator. Equality of
metadata with `DirectGraphEnumerator.iterate` is checked by reduction of its
constructor fields; no theorem field is used to extract syntax.
-/

namespace DiophantineConsistency.IterationSize

open Rep (Thin)
open NativeEnumerationSize (allowance)
open DirectGraphEnumerator (R)

attribute [local irreducible] Nat.unpair

abbrev V := Option (Fin 1) ⊕ Fin 2

def a : GraphRep (fun v : V → ℕ => v (.inr 0)) := GraphRep.coordinate (σ := V) (Sum.inr 0)
def b : GraphRep (fun v : V → ℕ => v (.inr 1)) := GraphRep.coordinate (σ := V) (Sum.inr 1)
def k : GraphRep (fun v : V → ℕ => v (.inl (some 0))) := GraphRep.coordinate (σ := V) (Sum.inl (some 0))
def out : GraphRep (fun v : V → ℕ => v (.inl none)) := GraphRep.coordinate (σ := V) (Sum.inl none)
def index : GraphRep (fun v : Option V → ℕ => v none) := GraphRep.coordinate (σ := Option V) none

def equalityGraphs {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) : Rep σ (fun v => f v = g v) := by
  let arguments : ∀ i : Fin 2, GraphRep (![f, g] i) :=
    Fin.cases r (Fin.cases s (fun i => Fin.elim0 i))
  exact (Rep.compose
    (PellRepresentation.NaturalRelation.equality
      (.var (0 : Fin 2)) (.var 1)) arguments).ofIff (fun _ => Iff.rfl)

/-- The equality-coordinate constructor itself has two graph witnesses. -/
theorem equalityGraphs_witnessCount {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) :
    (equalityGraphs r s).witnessCount = 4 + r.witnessCount + s.witnessCount := by
  change 2 + (2 + (r.witnessCount + (s.witnessCount + 0))) = _
  omega

theorem equalityGraphs_thin {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) (hr : Thin allowance r) (hs : Thin allowance s) :
    Thin allowance (equalityGraphs r s) := by
  unfold equalityGraphs
  rw [Rep.thin_ofIff]
  have hfixed : Thin allowance (PellRepresentation.NaturalRelation.equality
      (.var (0 : Fin 2)) (.var 1)) := by unfold Thin; decide
  apply Rep.thin_compose _ (by decide) (by decide) _ _ hfixed
  intro i
  fin_cases i <;> assumption

def first (initial : ℕ) := equalityGraphs
  (ScalarPRRepresentation.entryGraph a b (GraphRep.constant 0)) (GraphRep.constant initial)
def last := equalityGraphs (ScalarPRRepresentation.entryGraph a b k) out

def transition {f : ℕ → ℕ} (p : R f) :=
  let aa := a.reindex some
  let bb := b.reindex some
  let before := ScalarPRRepresentation.entryGraph aa bb index
  let after := ScalarPRRepresentation.entryGraph aa bb (index.add (GraphRep.constant 1))
  let next := GraphRep.compose p (fun _ : Fin 1 => before)
  equalityGraphs after next

def rows {f : ℕ → ℕ} (p : R f) (initial : ℕ) :=
  ((first initial).conjunction (last.conjunction
    ((transition p).boundedForall (.inl (some 0))))).existsBlock

theorem iterate_witnessCount {f : ℕ → ℕ} (p : R f) (initial : ℕ) :
    (DirectGraphEnumerator.iterate p initial).witnessCount = (rows p initial).witnessCount := rfl

theorem iterate_depth {f : ℕ → ℕ} (p : R f) (initial : ℕ) :
    (DirectGraphEnumerator.iterate p initial).depth = (rows p initial).depth := rfl

theorem entryGraph_witnessCount {σ : Type*} {f g h : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) (t : GraphRep h) :
    (ScalarPRRepresentation.entryGraph r s t).witnessCount =
      11 + r.witnessCount + s.witnessCount + t.witnessCount := by
  simp only [ScalarPRRepresentation.entryGraph, BoundedForallSize.mod_count,
    BoundedForallSize.add_count, BoundedForallSize.mul_count,
    BoundedForallSize.constant_count, BoundedForallSize.modCost,
    BoundedForallSize.addCost, BoundedForallSize.mulCost]
  have hm : GraphRep.modCoordinates.witnessCount = 2 := rfl
  rw [hm]
  omega

theorem entryGraph_thin {σ : Type*} {f g h : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) (t : GraphRep h)
    (hr : Thin allowance r) (hs : Thin allowance s) (ht : Thin allowance t) :
    Thin allowance (ScalarPRRepresentation.entryGraph r s t) := by
  let rhs := ((t.add (GraphRep.constant 1)).mul s).add (GraphRep.constant 1)
  have hc : Thin allowance (GraphRep.constant (σ := σ) 1) :=
    GraphRep.thin_constant _ (by decide) _
  have hrhs : Thin allowance rhs := GraphRep.thin_add _ _ _
    (GraphRep.thin_mul _ _ _ (GraphRep.thin_add _ _ _ ht hc) hs) hc
  unfold ScalarPRRepresentation.entryGraph GraphRep.mod
  have hfixed : Thin allowance GraphRep.modCoordinates := by unfold Thin; decide
  apply GraphRep.thin_compose _ (by decide) (by decide) _ _ hfixed
  intro i
  fin_cases i
  · exact hr
  · exact hrhs

theorem transition_witnessCount {f : ℕ → ℕ} (p : R f) :
    (transition p).witnessCount = p.witnessCount + 30 := by
  simp only [transition, equalityGraphs_witnessCount, entryGraph_witnessCount,
    GraphRep.witnessCount_add, GraphRep.witnessCount_constant,
    GraphRep.witnessCount_reindex, GraphRep.compose_witnessCount,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  change 4 + (11 + 0 + 0 + (2 + 0 + 0)) + (2 + (p.witnessCount + (11 + 0 + 0 + 0 + 0))) = _
  omega

theorem first_witnessCount (initial : ℕ) : (first initial).witnessCount = 15 := rfl
theorem last_witnessCount : last.witnessCount = 15 := rfl

theorem transition_thin {f : ℕ → ℕ} (p : R f) (hp : Thin allowance p) :
    Thin allowance (transition p) := by
  let aa := a.reindex some
  let bb := b.reindex some
  have hc {σ : Type} (i : σ) : Thin allowance (GraphRep.coordinate i) :=
    GraphRep.thin_coordinate _ (by decide) _
  have ha : Thin allowance aa := (GraphRep.thin_reindex _ a some).2 (hc (σ := V) (Sum.inr 0))
  have hb : Thin allowance bb := (GraphRep.thin_reindex _ b some).2 (hc (σ := V) (Sum.inr 1))
  have hi : Thin allowance index := hc (σ := Option V) none
  have hbefore := entryGraph_thin aa bb index ha hb hi
  have hafter := entryGraph_thin aa bb (index.add (GraphRep.constant 1)) ha hb
    (GraphRep.thin_add _ _ _ hi (GraphRep.thin_constant _ (by decide) 1))
  exact equalityGraphs_thin _ _ hafter
    (GraphRep.thin_compose _ (by decide) (by decide) _ _ hp (fun _ => hbefore))

theorem first_thin (initial : ℕ) : Thin allowance (first initial) := by
  apply equalityGraphs_thin
  · apply entryGraph_thin
    · exact GraphRep.thin_coordinate _ (by decide) _
    · exact GraphRep.thin_coordinate _ (by decide) _
    · exact GraphRep.thin_constant _ (by decide) _
  · exact GraphRep.thin_constant _ (by decide) _

theorem last_thin : Thin allowance last := by
  apply equalityGraphs_thin
  · apply entryGraph_thin
    · exact GraphRep.thin_coordinate _ (by decide) _
    · exact GraphRep.thin_coordinate _ (by decide) _
    · exact GraphRep.thin_coordinate _ (by decide) _
  · exact GraphRep.thin_coordinate _ (by decide) _

set_option maxRecDepth 10000 in
theorem native_step_witnessCount : NativeGraphEnumerator.optionStepProgram.witnessCount = 1752 := rfl

theorem native_transition_witnessCount :
    (transition NativeGraphEnumerator.optionStepProgram).witnessCount = 1782 := by
  rw [transition_witnessCount, native_step_witnessCount]

theorem native_transition_depth :
    (transition NativeGraphEnumerator.optionStepProgram).depth ≤ 11204 := by
  have h := transition_thin NativeGraphEnumerator.optionStepProgram
    NativeEnumeratorBounds.optionStepProgram_thin
  unfold Thin at h
  rw [native_transition_witnessCount] at h
  exact h

end DiophantineConsistency.IterationSize
