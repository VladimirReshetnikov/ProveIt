import BusyBeaver.ZFC.PositiveClosure

/-!
The remaining forward set-existence steps for subset-only positive closure.

Every closure hypothesis names its particular relation: a two-cycle, a
Russell-rooted partial image, or the successor relation. Separation and Union
resources used later are explicit assumptions. These are shallow semantic
lemmas over an arbitrary membership relation, not a first-order theory
equivalence, proof translator, internal consistency theorem, or TM endpoint.
All equality is Lean equality. No Foundation or set-theoretic Choice is assumed.
-/

namespace SetTheory.BusyBeaver.ZFC.Bootstrap

open PositiveClosure

universe u
variable {V : Type u}

def Pair (mem : V → V → Prop) (a b p : V) : Prop :=
  ∀ z, mem z p ↔ z = a ∨ z = b

def PairingSets (mem : V → V → Prop) : Prop :=
  ∀ a b, ∃ p, Pair mem a b p

def UnionSets (mem : V → V → Prop) : Prop :=
  ∀ a, ∃ s, Exact mem (fun z => ∃ x, mem x a ∧ mem z x) s

def Extensional (mem : V → V → Prop) : Prop :=
  ∀ a b, (∀ z, mem z a ↔ mem z b) → a = b

def TwoCycle (a b x y : V) : Prop :=
  (x = a ∧ y = b) ∨ (x = b ∧ y = a)

theorem twoCycle_subset_bounded (mem : V → V → Prop) (a b : V) :
    SubsetBounded mem (TwoCycle a b) := by
  classical
  intro x
  by_cases hxa : x = a
  · refine ⟨b, ?_⟩
    intro y hy
    have hyb : y = b := by
      rcases hy with hy | hy
      · exact hy.2
      · exact hy.2.trans (hxa.symm.trans hy.1)
    subst y
    exact sub_refl mem b
  · refine ⟨a, ?_⟩
    intro y hy
    rcases hy with hy | hy
    · exact False.elim (hxa hy.1)
    · rw [hy.2]
      exact sub_refl mem a

/-- A two-cycle puts both endpoints in the positive output hull, including a=b. -/
theorem pairing_of_instance (mem : V → V → Prop) (seed : V → V → Prop)
    (hSeed : ∀ a, seed a a) (a b : V)
    (hInstance : ClosureInstance mem seed (TwoCycle a b)) :
    ∃ p, Pair mem a b p := by
  obtain ⟨p, hClosed, hSupport⟩ := hInstance (twoCycle_subset_bounded mem a b) a
  have hb : mem b p := hClosed a b (Or.inl (hSeed a)) (Or.inl ⟨rfl, rfl⟩)
  have ha : mem a p := hClosed b a (Or.inr hb) (Or.inr ⟨rfl, rfl⟩)
  refine ⟨p, ?_⟩
  intro y
  constructor
  · intro hy
    obtain ⟨x, hxy⟩ := hSupport y hy
    rcases hxy with hxy | hxy
    · exact Or.inr hxy.2
    · exact Or.inl hxy.2
  · intro hy
    rcases hy with hy | hy
    · rw [hy]
      exact ha
    · rw [hy]
      exact hb

def PartialFunctionalOn (mem : V → V → Prop) (a : V) (r : V → V → Prop) : Prop :=
  ∀ x, mem x a → ∀ y z, r x y → r x z → y = z

/-- The exact separated Russell subset lies outside its source set. -/
theorem russell_not_mem (mem : V → V → Prop) (a root : V)
    (hRussell : Exact mem (fun t => mem t a ∧ ¬ mem t t) root) :
    ¬ mem root a := by
  intro hRoot
  have hNot : ¬ mem root root := fun h => ((hRussell root).mp h).2 h
  exact hNot ((hRussell root).mpr ⟨hRoot, hNot⟩)

def RootedImage (mem : V → V → Prop) (a root : V) (r : V → V → Prop)
    (x y : V) : Prop :=
  (x = root ∧ mem y a) ∨ (mem x a ∧ r x y)

/-- The root fiber is bounded by Union(A); every other nonempty fiber is a singleton. -/
theorem rootedImage_subset_bounded (mem : V → V → Prop) (a root union : V)
    (r : V → V → Prop) (hRoot : ¬ mem root a)
    (hUnion : Exact mem (fun z => ∃ x, mem x a ∧ mem z x) union)
    (hFunctional : PartialFunctionalOn mem a r) :
    SubsetBounded mem (RootedImage mem a root r) := by
  classical
  intro x
  by_cases hx : x = root
  · refine ⟨union, ?_⟩
    intro y hy
    rcases hy with hy | hy
    · intro z hz
      exact (hUnion z).mpr ⟨y, hy.2, hz⟩
    · exact False.elim (hRoot (hx ▸ hy.1))
  · by_cases hOutput : ∃ y, mem x a ∧ r x y
    · obtain ⟨b, hxa, hxb⟩ := hOutput
      refine ⟨b, ?_⟩
      intro y hy
      rcases hy with hy | hy
      · exact False.elim (hx hy.1)
      · have hyb : y = b := hFunctional x hxa y b hy.2 hxb
        rw [hyb]
        exact sub_refl mem b
    · refine ⟨x, ?_⟩
      intro y hy
      rcases hy with hy | hy
      · exact False.elim (hx hy.1)
      · exact False.elim (hOutput ⟨y, hy⟩)

/-- The exact image-separation predicate is the only Separation resource here.
The Russell subset and Union(A) are supplied as explicit witnesses from earlier steps. -/
theorem partial_replacement_of_instance (mem : V → V → Prop) (seed : V → V → Prop)
    (hSeed : ∀ a, seed a a) (a root union : V) (r : V → V → Prop)
    (hRussell : Exact mem (fun t => mem t a ∧ ¬ mem t t) root)
    (hUnion : Exact mem (fun z => ∃ x, mem x a ∧ mem z x) union)
    (hFunctional : PartialFunctionalOn mem a r)
    (hInstance : ClosureInstance mem seed (RootedImage mem a root r))
    (hImageSeparation : ∀ c, ∃ b,
      Exact mem (fun y => mem y c ∧ ∃ x, mem x a ∧ r x y) b) :
    ∃ b, Exact mem (fun y => ∃ x, mem x a ∧ r x y) b := by
  have hRoot := russell_not_mem mem a root hRussell
  obtain ⟨c, hClosed, _hSupport⟩ := hInstance
    (rootedImage_subset_bounded mem a root union r hRoot hUnion hFunctional) root
  have hCover : ∀ y, (∃ x, mem x a ∧ r x y) → mem y c := by
    intro y hy
    obtain ⟨x, hxa, hxy⟩ := hy
    have hxC : mem x c :=
      hClosed root x (Or.inl (hSeed root)) (Or.inl ⟨rfl, hxa⟩)
    exact hClosed x y (Or.inr hxC) (Or.inr ⟨hxa, hxy⟩)
  obtain ⟨b, hb⟩ := hImageSeparation c
  refine ⟨b, ?_⟩
  intro y
  constructor
  · intro hy
    exact ((hb y).mp hy).2
  · intro hy
    exact (hb y).mpr ⟨hCover y hy, hy⟩

def Adjoin (mem : V → V → Prop) (a t b : V) : Prop :=
  ∀ z, mem z b ↔ mem z a ∨ z = t

/-- A union of the pair A,{t} adjoins t; no Foundation or Choice is used. -/
theorem adjoin_of_pair_union (mem : V → V → Prop)
    (hSingletons : SingletonsExact mem) (hPairs : PairingSets mem)
    (hUnions : UnionSets mem) (a t : V) :
    ∃ b, Adjoin mem a t b := by
  obtain ⟨s, hs⟩ := hSingletons t
  obtain ⟨p, hp⟩ := hPairs a s
  obtain ⟨b, hb⟩ := hUnions p
  refine ⟨b, ?_⟩
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, hzx⟩ := (hb z).mp hz
    rcases (hp x).mp hx with hxa | hxs
    · exact Or.inl (hxa ▸ hzx)
    · exact Or.inr ((hs z).mp (hxs ▸ hzx))
  · intro hz
    apply (hb z).mpr
    rcases hz with hza | hzt
    · exact ⟨a, (hp a).mpr (Or.inl rfl), hza⟩
    · exact ⟨s, (hp s).mpr (Or.inr rfl), (hs z).mpr hzt⟩

def Successor (mem : V → V → Prop) (x y : V) : Prop :=
  Adjoin mem x x y

theorem successors_of_pair_union (mem : V → V → Prop)
    (hSingletons : SingletonsExact mem) (hPairs : PairingSets mem)
    (hUnions : UnionSets mem) : ∀ x, ∃ y, Successor mem x y := by
  intro x
  exact adjoin_of_pair_union mem hSingletons hPairs hUnions x x

theorem successor_unique (mem : V → V → Prop) (hExt : Extensional mem)
    (x y z : V) (hy : Successor mem x y) (hz : Successor mem x z) : y = z := by
  apply hExt y z
  intro t
  exact (hy t).trans (hz t).symm

theorem successor_subset_bounded (mem : V → V → Prop)
    (hSuccessors : ∀ x, ∃ y, Successor mem x y) :
    SubsetBounded mem (Successor mem) := by
  intro x
  obtain ⟨b, hb⟩ := hSuccessors x
  refine ⟨b, ?_⟩
  intro y hy z hz
  exact (hb z).mpr ((hy z).mp hz)

def Inductive (mem : V → V → Prop) (e i : V) : Prop :=
  mem e i ∧ ∀ x, mem x i → ∃ y, Successor mem x y ∧ mem y i

/-- Adjoining the initial root repairs the positive hull's possible omission of it. -/
theorem inductive_of_successor_instance (mem : V → V → Prop) (seed : V → V → Prop)
    (hSeed : ∀ a, seed a a) (e : V)
    (hSuccessors : ∀ x, ∃ y, Successor mem x y)
    (hInstance : ClosureInstance mem seed (Successor mem))
    (hAdjoin : ∀ c, ∃ i, Adjoin mem c e i) :
    ∃ i, Inductive mem e i := by
  obtain ⟨c, hClosed, _hSupport⟩ := hInstance
    (successor_subset_bounded mem hSuccessors) e
  obtain ⟨i, hi⟩ := hAdjoin c
  refine ⟨i, (hi e).mpr (Or.inr rfl), ?_⟩
  intro x hx
  obtain ⟨y, hxy⟩ := hSuccessors x
  refine ⟨y, hxy, (hi y).mpr (Or.inl ?_)⟩
  rcases (hi x).mp hx with hxC | hxe
  · exact hClosed x y (Or.inr hxC) hxy
  · exact hClosed x y (Or.inl (hxe ▸ hSeed e)) hxy

/-- Infinity from the successor instance and previously supplied set constructions. -/
theorem infinity_of_instance (mem : V → V → Prop) (seed : V → V → Prop)
    (hSeed : ∀ a, seed a a)
    (e : V) (hEmpty : Exact mem (fun _ => False) e)
    (hSingletons : SingletonsExact mem) (hPairs : PairingSets mem)
    (hUnions : UnionSets mem)
    (hInstance : ClosureInstance mem seed (Successor mem)) :
    ∃ empty i, Exact mem (fun _ => False) empty ∧ Inductive mem empty i := by
  obtain ⟨i, hi⟩ := inductive_of_successor_instance mem seed hSeed e
    (successors_of_pair_union mem hSingletons hPairs hUnions) hInstance
    (fun c => adjoin_of_pair_union mem hSingletons hPairs hUnions c e)
  exact ⟨e, i, hEmpty, hi⟩

#print axioms pairing_of_instance
#print axioms partial_replacement_of_instance
#print axioms infinity_of_instance

end SetTheory.BusyBeaver.ZFC.Bootstrap
