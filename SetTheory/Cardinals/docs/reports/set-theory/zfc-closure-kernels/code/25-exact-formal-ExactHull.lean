/-
Exact hulls in a raw membership structure.

This file uses only Lean's core logic.  In particular, it assumes no
Extensionality, Foundation, Choice, replacement principle, or axiom equating
objects with the same incoming members.

The inputs `hL` and `hJ` explicitly supply the two representable predicates
used in the argument.  They are resources, not consequences of bare
monotonicity.  The result is leastness relative to the container C.  Global
leastness would additionally require representatives of intersections with
arbitrary preclosed objects, or another argument supplying that resource.

This is the familiar intersection-of-prefixed-points argument of
Knaster--Tarski, specialized to two separation representatives in a raw
membership structure.  It is not a formalization of a formula-indexed
set-theory interpretation or of a Turing machine.
-/

universe u

namespace ProveIt.ExactHull

variable {U : Type u}

/-- Inclusion compares incoming membership predicates; it does not assert
    or require equality of representing objects. -/
def Included (mem : U → U → Prop) (A B : U) : Prop :=
  ∀ y, mem y A → mem y B

/-- A prefixed point of F, represented by an object of the raw structure. -/
def Preclosed (mem F : U → U → Prop) (A : U) : Prop :=
  ∀ y, F A y → mem y A

/-- F respects inclusion of incoming membership predicates. -/
def Monotone (mem F : U → U → Prop) : Prop :=
  ∀ {A B : U}, Included mem A B → ∀ y, F A y → F B y

/-- L represents the intersection, inside C, of all represented preclosed
    subobjects of C. -/
def HullRepresentative (mem F : U → U → Prop) (C L : U) : Prop :=
  ∀ y, mem y L ↔
    mem y C ∧
      ∀ B, (Included mem B C ∧ Preclosed mem F B) → mem y B

/-- J represents the particular separated predicate C ∩ F(L). -/
def ImageRepresentative (mem F : U → U → Prop) (C L J : U) : Prop :=
  ∀ y, mem y J ↔ mem y C ∧ F L y

/-- Every conclusion is about incoming members, not equality of objects. -/
structure ExactHullResult (mem F : U → U → Prop) (C L : U) : Prop where
  included : Included mem L C
  preclosed : Preclosed mem F L
  fixed_point : ∀ y, mem y L ↔ F L y
  least : ∀ B, Included mem B C → Preclosed mem F B → Included mem L B

/-- Two particular separation representatives suffice for a least exact
    fixed point within the given preclosed container.  No classical logic
    is needed.  An inhabitedness instance for U is also unnecessary:
    the supplied objects C, L and J already witness inhabitedness. -/
theorem exact_hull
    (mem F : U → U → Prop)
    (hmono : Monotone mem F)
    (C L J : U)
    (hC : Preclosed mem F C)
    (hL : HullRepresentative mem F C L)
    (hJ : ImageRepresentative mem F C L J) :
    ExactHullResult mem F C L := by
  have hLC : Included mem L C := by
    intro y hy
    exact ((hL y).mp hy).1

  have hleast :
      ∀ B, Included mem B C → Preclosed mem F B → Included mem L B := by
    intro B hBC hB y hy
    exact ((hL y).mp hy).2 B ⟨hBC, hB⟩

  have hpreL : Preclosed mem F L := by
    intro y hFy
    apply (hL y).mpr
    constructor
    · exact hC y (hmono hLC y hFy)
    · intro B hB
      exact hB.2 y (hmono (hleast B hB.1 hB.2) y hFy)

  have hJC : Included mem J C := by
    intro y hy
    exact ((hJ y).mp hy).1

  have hJL : Included mem J L := by
    intro y hy
    exact hpreL y ((hJ y).mp hy).2

  have hpreJ : Preclosed mem F J := by
    intro y hFy
    have hFLy : F L y := hmono hJL y hFy
    exact (hJ y).mpr ⟨hLC y (hpreL y hFLy), hFLy⟩

  have hLJ : Included mem L J := hleast J hJC hpreJ

  exact {
    included := hLC
    preclosed := hpreL
    fixed_point := fun y =>
      ⟨fun hy => ((hJ y).mp (hLJ y hy)).2, hpreL y⟩
    least := hleast
  }

/-- K represents the intersection of two incoming membership predicates. -/
def IntersectionRepresentative (mem : U → U → Prop) (A B K : U) : Prop :=
  ∀ y, mem y K ↔ mem y A ∧ mem y B

/-- Relative leastness becomes global leastness when intersections with C
    are representable for every preclosed object.  This is an additional
    separation resource, explicitly absent from `exact_hull`. -/
theorem exact_hull_global_least
    (mem F : U → U → Prop)
    (hmono : Monotone mem F)
    (C L : U)
    (hC : Preclosed mem F C)
    (hL : ExactHullResult mem F C L)
    (hintersections : ∀ B, Preclosed mem F B →
      ∃ K, IntersectionRepresentative mem B C K) :
    ∀ B, Preclosed mem F B → Included mem L B := by
  intro B hB
  cases hintersections B hB with
  | intro K hK =>
    have hKB : Included mem K B := by
      intro y hy
      exact ((hK y).mp hy).1
    have hKC : Included mem K C := by
      intro y hy
      exact ((hK y).mp hy).2
    have hpreK : Preclosed mem F K := by
      intro y hFy
      exact (hK y).mpr
        ⟨hB y (hmono hKB y hFy), hC y (hmono hKC y hFy)⟩
    intro y hy
    exact hKB y (hL.least K hKC hpreK y hy)

/-- Raw emptiness.  Distinct empty objects are allowed. -/
def Empty (mem : U → U → Prop) (x : U) : Prop :=
  ∀ z, ¬ mem z x

/-- R-images of the empty objects and the members of b. -/
def SeedImage (mem R : U → U → Prop) (b y : U) : Prop :=
  ∃ x, (Empty mem x ∨ mem x b) ∧ R x y

/-- The seed-image operator is monotone without any conditions on R. -/
theorem seedImage_monotone (mem R : U → U → Prop) :
    Monotone mem (SeedImage mem R) := by
  intro A B hAB y hy
  cases hy with
  | intro x hx =>
    exact ⟨x,
      Or.elim hx.1
        (fun hEmpty => Or.inl hEmpty)
        (fun hxA => Or.inr (hAB x hxA)),
      hx.2⟩

/-- The exact-hull theorem specialized to the seeded relational image.
    Its separation resources are supplied explicitly, as in `exact_hull`.
    It does not assume that R is functional or extensional. -/
theorem seed_exact_hull
    (mem R : U → U → Prop)
    (C L J : U)
    (hC : Preclosed mem (SeedImage mem R) C)
    (hL : HullRepresentative mem (SeedImage mem R) C L)
    (hJ : ImageRepresentative mem (SeedImage mem R) C L J) :
    ExactHullResult mem (SeedImage mem R) C L :=
  exact_hull mem (SeedImage mem R) (seedImage_monotone mem R)
    C L J hC hL hJ

/-
The following three-object example checks the scope of the theorem.
It is a counterexample to GLOBAL leastness with only the original two
representative resources; it is not a model of any proposed set theory.

Incoming member sets are c = {c,b}, b = {b,t}, t = {c,b,t}.
The operator has F(c) = F(t) = {c,b}, F(b) = empty.
Choose C = L = J = c.  Both required representatives exist and c is a
relative least exact fixed point.  But b is preclosed and c is not
included in b.  The missing intersection would have incoming members
{b}, and no object represents that predicate.
-/
namespace ScopeCounterexample

inductive Raw where
  | c
  | b
  | t

def rawMem (y B : Raw) : Prop :=
  match B with
  | .c => y ≠ .t
  | .b => y ≠ .c
  | .t => True

def rawF (A y : Raw) : Prop :=
  match A with
  | .b => False
  | .c => rawMem y .c
  | .t => rawMem y .c

theorem raw_monotone : Monotone rawMem rawF := by
  intro A B hAB y hFy
  cases A with
  | b => exact False.elim hFy
  | c =>
    cases B with
    | c => exact hFy
    | t => exact hFy
    | b =>
      have hcc : rawMem Raw.c Raw.c := by intro h; cases h
      have hcb := hAB Raw.c hcc
      exact False.elim (hcb rfl)
  | t =>
    cases B with
    | c => exact hFy
    | t => exact hFy
    | b =>
      have hcb := hAB Raw.c True.intro
      exact False.elim (hcb rfl)

theorem container_preclosed : Preclosed rawMem rawF Raw.c := by
  intro y hy
  exact hy

theorem hull_representative :
    HullRepresentative rawMem rawF Raw.c Raw.c := by
  intro y
  constructor
  · intro hy
    refine ⟨hy, ?_⟩
    intro B hB
    cases B with
    | c => exact hy
    | b =>
      have htb : rawMem Raw.t Raw.b := by intro h; cases h
      have htc := hB.1 Raw.t htb
      exact False.elim (htc rfl)
    | t => trivial
  · intro hy
    exact hy.1

theorem image_representative :
    ImageRepresentative rawMem rawF Raw.c Raw.c Raw.c := by
  intro y
  exact ⟨fun hy => ⟨hy, hy⟩, fun hy => hy.1⟩

theorem relative_fixed_point :
    ExactHullResult rawMem rawF Raw.c Raw.c :=
  exact_hull rawMem rawF raw_monotone Raw.c Raw.c Raw.c
    container_preclosed hull_representative image_representative

theorem competitor_preclosed : Preclosed rawMem rawF Raw.b := by
  intro y hy
  exact False.elim hy

theorem not_global :
    ¬ (∀ B, Preclosed rawMem rawF B → Included rawMem Raw.c B) := by
  intro h
  have hcc : rawMem Raw.c Raw.c := by intro h; cases h
  have hcb := h Raw.b competitor_preclosed Raw.c hcc
  exact hcb rfl

end ScopeCounterexample

end ProveIt.ExactHull

#print axioms ProveIt.ExactHull.exact_hull
#print axioms ProveIt.ExactHull.exact_hull_global_least
#print axioms ProveIt.ExactHull.seedImage_monotone
#print axioms ProveIt.ExactHull.seed_exact_hull
#print axioms ProveIt.ExactHull.ScopeCounterexample.relative_fixed_point
#print axioms ProveIt.ExactHull.ScopeCounterexample.not_global
