import Mathlib.Data.Set.Basic
import Mathlib.Logic.Small.Defs
import Mathlib.Order.Defs.PartialOrder

/-!
# Size obstructions and small cut interfaces

This file formalizes the elementary size arguments in
`docs/foundations-and-computation/foundations/article.tex`, especially
`found:prop:allcuts` and `found:prop:universecut`.

The index universe `u` is independent of the carrier universe `v`. The intended
surreal application has `v = u + 1`. Cut input data do not assert that a cut is
realized: the consequences of cut filling below take that property as an
explicit hypothesis. No surreal construction or cut-filling axiom is assumed.
-/

universe u v

namespace Surreal.Foundations

/-- The predicate-based form of `found:prop:allcuts`: an irreflexive relation
cannot have a strict-bound operation defined on every predicate on its carrier.
This is the guard in the shipped `foundationssketch.lean`. -/
theorem noUniversalStrictBound
    {X : Type v} (lt : X → X → Prop)
    (irrefl : ∀ x, ¬ lt x x)
    (bound : (X → Prop) → X)
    (above : ∀ A x, A x → lt x (bound A)) : False := by
  let all : X → Prop := fun _ => True
  exact irrefl (bound all) (above all (bound all) True.intro)

/-- The existential, relation-based form of `found:prop:allcuts`. It requires
neither choice of a bound function nor transitivity of the relation. -/
theorem noUnrestrictedStrictBounds
    {X : Type v} (lt : X → X → Prop) (irrefl : ∀ x, ¬ lt x x) :
    ¬ (∀ s : Set X, ∃ b : X, ∀ x ∈ s, lt x b) := by
  intro h
  obtain ⟨b, hb⟩ := h Set.univ
  exact irrefl b (hb b (Set.mem_univ b))

/-- The ordered-carrier form of `found:prop:allcuts`, corresponding to
`noUnrestrictedUpperBounds` in the shipped `logicalguards.lean`. -/
theorem noUnrestrictedUpperBounds (X : Type v) [Preorder X] :
    ¬ (∀ s : Set X, ∃ b : X, ∀ x ∈ s, x < b) :=
  noUnrestrictedStrictBounds (· < ·) lt_irrefl

/-- The two-sided form of `found:prop:allcuts`: the separated pair consisting
of the entire carrier and the empty set cannot have a strict separator. -/
theorem noUnrestrictedCuts
    {X : Type v} (lt : X → X → Prop) (irrefl : ∀ x, ¬ lt x x) :
    ¬ (∀ L R : Set X, (∀ l ∈ L, ∀ r ∈ R, lt l r) →
      ∃ x : X, (∀ l ∈ L, lt l x) ∧ (∀ r ∈ R, lt x r)) := by
  intro h
  obtain ⟨x, hx, _⟩ := h Set.univ ∅ (fun _ _ _ hr => False.elim hr)
  exact irrefl x (hx x (Set.mem_univ x))

/-- Cut input data from `found:sub:cutdata`. The option indices lie in `Type u`
and the values lie in `Type v`. The structure contains a separation proof but
does not contain or assert the existence of a separator. -/
structure SmallCutData (X : Type v) (lt : X → X → Prop) where
  Left : Type u
  Right : Type u
  left : Left → X
  right : Right → X
  separated : ∀ l r, lt (left l) (right r)

/-- A value strictly separates the two option families of a small cut. -/
def SmallCutData.IsRealizedBy {X : Type v} {lt : X → X → Prop}
    (c : SmallCutData.{u, v} X lt) (x : X) : Prop :=
  (∀ l, lt (c.left l) x) ∧ (∀ r, lt x (c.right r))

/-- Every cut with indices in `Type u` has a separator in the carrier `X`.
This is a property to be proved for a construction, not an axiom or instance. -/
def HasSmallCutFillers (X : Type v) (lt : X → X → Prop) : Prop :=
  ∀ c : SmallCutData.{u, v} X lt, ∃ x : X, c.IsRealizedBy x

/-- Every family indexed by a type in `Type u` has a strict upper bound in `X`.
In particular, this does not quantify over every unrestricted subset of `X`. -/
def HasSmallStrictUpperBounds (X : Type v) (lt : X → X → Prop) : Prop :=
  ∀ (I : Type u) (f : I → X), ∃ b : X, ∀ i, lt (f i) b

/-- The upper-bound step of `found:lem:bounds`: fill the cut with the given
small family on the left and no options on the right. -/
theorem HasSmallCutFillers.hasSmallStrictUpperBounds
    {X : Type v} {lt : X → X → Prop} (h : HasSmallCutFillers.{u, v} X lt) :
    HasSmallStrictUpperBounds.{u, v} X lt := by
  intro I f
  let c : SmallCutData.{u, v} X lt :=
    { Left := I
      Right := PEmpty
      left := f
      right := PEmpty.elim
      separated := fun _ r => PEmpty.elim r }
  obtain ⟨b, hb, _⟩ := h c
  exact ⟨b, hb⟩

/-- The lower-bound step of `found:lem:bounds`: fill the cut with no left
options and the given small family on the right. -/
theorem HasSmallCutFillers.exists_strict_lower_bound
    {X : Type v} {lt : X → X → Prop} (h : HasSmallCutFillers.{u, v} X lt)
    (I : Type u) (f : I → X) : ∃ b : X, ∀ i, lt b (f i) := by
  let c : SmallCutData.{u, v} X lt :=
    { Left := PEmpty
      Right := I
      left := PEmpty.elim
      right := f
      separated := fun l _ => PEmpty.elim l }
  obtain ⟨b, _, hb⟩ := h c
  exact ⟨b, hb⟩

/-- The positive-lower-bound argument of `found:lem:bounds`, stated for an
arbitrary lower endpoint. Taking `a = 0` gives a positive strict lower bound
for any small family of positive elements, including an empty family. -/
theorem HasSmallCutFillers.exists_strict_lower_bound_above
    {X : Type v} {lt : X → X → Prop} (h : HasSmallCutFillers.{u, v} X lt)
    (a : X) (I : Type u) (f : I → X) (ha : ∀ i, lt a (f i)) :
    ∃ b : X, lt a b ∧ ∀ i, lt b (f i) := by
  let c : SmallCutData.{u, v} X lt :=
    { Left := PUnit
      Right := I
      left := fun _ => a
      right := f
      separated := fun _ i => ha i }
  obtain ⟨b, hb, hf⟩ := h c
  exact ⟨b, hb PUnit.unit, hf⟩

/-- Small-family strict bounds imply the carrier is not itself small at the
index universe. This is the size argument of `found:prop:universecut`, with
the weaker hypothesis of upper-bound existence in place of cut filling. -/
theorem not_small_of_small_strict_upper_bounds
    {X : Type v} {lt : X → X → Prop} (irrefl : ∀ x, ¬ lt x x)
    (h : HasSmallStrictUpperBounds.{u, v} X lt) : ¬ Small.{u} X := by
  intro hsmall
  obtain ⟨I, ⟨e⟩⟩ := hsmall.equiv_small
  obtain ⟨b, hb⟩ := h I e.invFun
  exact irrefl b ((congrArg (fun x => lt x b) (e.left_inv b)).mp (hb (e.toFun b)))

/-- The missing self-cut, `found:prop:universecut`: if all separated
`u`-small option families can be filled, an irreflexive carrier cannot be
`u`-small. The proof does not assume a particular surreal representation. -/
theorem not_small_of_small_cut_fillers
    {X : Type v} {lt : X → X → Prop} (irrefl : ∀ x, ¬ lt x x)
    (h : HasSmallCutFillers.{u, v} X lt) : ¬ Small.{u} X :=
  not_small_of_small_strict_upper_bounds irrefl h.hasSmallStrictUpperBounds

/-- A subset qualifies for the small-family bound only when its element type
is small. This is the predicate-based version of the size discipline in
`found:sub:cutdata` and the upper-bound conclusion of `found:lem:bounds`. -/
theorem HasSmallStrictUpperBounds.exists_bound_of_small_set
    {X : Type v} {lt : X → X → Prop} (h : HasSmallStrictUpperBounds.{u, v} X lt)
    (s : Set X) [hs : Small.{u} s] : ∃ b : X, ∀ x ∈ s, lt x b := by
  obtain ⟨I, ⟨e⟩⟩ := hs.equiv_small
  obtain ⟨b, hb⟩ := h I (fun i => (e.invFun i).val)
  refine ⟨b, fun x hx => ?_⟩
  exact (congrArg (fun y : s => lt y.val b) (e.left_inv ⟨x, hx⟩)).mp
    (hb (e.toFun ⟨x, hx⟩))

end Surreal.Foundations
