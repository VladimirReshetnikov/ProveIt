/-
Subset-only positive seeded closure: the new bootstrap's core lemmas.

Self-contained, mathlib-free, Lean core only. All equality below is Lean's
actual equality on V. This is a shallow semantic interface over an abstract
membership relation. `ClosureInstance` assumes ONE explicitly supplied relation
instance; it is not a first-order syntax, axiom recognizer, proof transformer,
internal ZFC theorem, or machine correctness theorem. In particular, no theorem
here states the full ZFC equiconsistency result from the research note.

Credits: the three external reports reconciled in
SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md.
They supply constant-fiber exactness and the gated singleton decoder. The new
step proved here is that the positive decoder hull covers every member of its
root even when the root itself is not an output. This recovers Separation and
Union under subset-only bounds without assuming either construction first.
-/
namespace SetTheory.BusyBeaver.ZFC.PositiveClosure

universe u
variable {V : Type u}

/-- Membership-defined subset, with no set-existence assumption. -/
def Sub (mem : V → V → Prop) (a b : V) : Prop :=
  ∀ z, mem z a → mem z b

/-- Every member of C is a subset of C. -/
def Transitive (mem : V → V → Prop) (c : V) : Prop :=
  ∀ x, mem x c → Sub mem x c

def Sing (mem : V → V → Prop) (s t : V) : Prop :=
  ∀ z, mem z s ↔ z = t

def SingletonsExact (mem : V → V → Prop) : Prop :=
  ∀ t, ∃ s, Sing mem s t

def Exact (mem : V → V → Prop) (theta : V → Prop) (e : V) : Prop :=
  ∀ y, mem y e ↔ theta y

def SubsetBounded (mem : V → V → Prop) (r : V → V → Prop) : Prop :=
  ∀ x, ∃ b, ∀ y, r x y → Sub mem y b

/-- Positive output hull: the initial inputs themselves need not belong to C. -/
def PositiveHull (mem : V → V → Prop) (seed r : V → V → Prop)
    (a c : V) : Prop :=
  (∀ x y, (seed x a ∨ mem x c) → r x y → mem y c) ∧
  (∀ y, mem y c → ∃ x, r x y)

/-- One semantic closure instance, with the matrix relation supplied explicitly. -/
def ClosureInstance (mem : V → V → Prop) (seed r : V → V → Prop) : Prop :=
  SubsetBounded mem r → ∀ a, ∃ c, PositiveHull mem seed r a c

def Switch (mem : V → V → Prop) (x y : V) : Prop :=
  Sing mem x y ∨ ((¬ ∃ t, Sing mem x t) ∧ Sub mem y x)

theorem sub_refl (mem : V → V → Prop) (x : V) : Sub mem x x :=
  fun _ hz => hz

theorem point_seed_reflexive : ∀ a : V, a = a := fun _ => rfl

theorem subset_seed_reflexive (mem : V → V → Prop) : ∀ a, Sub mem a a :=
  sub_refl mem

/-- An exact extension follows from only its constant-relation instance.
The explicit witness is the nonempty first-order domain convention. -/
theorem constant_exact_of_instance (mem : V → V → Prop) (seed : V → V → Prop)
    (witness : V) (hSeed : ∀ a, seed a a) (theta : V → Prop)
    (hBound : ∃ b, ∀ y, theta y → Sub mem y b)
    (hInstance : ClosureInstance mem seed (fun _ y => theta y)) :
    ∃ e, Exact mem theta e := by
  obtain ⟨b, hb⟩ := hBound
  have hLocal : SubsetBounded mem (fun _ y => theta y) := by
    intro _
    exact ⟨b, hb⟩
  obtain ⟨e, hClosed, hSupport⟩ := hInstance hLocal witness
  refine ⟨e, ?_⟩
  intro y
  constructor
  · intro hy
    obtain ⟨_, hTheta⟩ := hSupport y hy
    exact hTheta
  · intro hTheta
    exact hClosed witness y (Or.inl (hSeed witness)) hTheta

/-- Singleton formation uses only its own exact constant-relation instances. -/
theorem singletons_of_instances (mem : V → V → Prop) (seed : V → V → Prop)
    (witness : V) (hSeed : ∀ a, seed a a)
    (hInstance : ∀ t : V, ClosureInstance mem seed (fun _ y => y = t)) :
    SingletonsExact mem := by
  intro t
  have hBound : ∃ b, ∀ y : V, y = t → Sub mem y b := by
    refine ⟨t, ?_⟩
    intro y hy
    subst y
    exact sub_refl mem t
  exact constant_exact_of_instance mem seed witness hSeed
    (fun y => y = t) hBound (hInstance t)

/-- Power Set comes directly from a subset fiber, independently of Switch. -/
theorem power_of_instance (mem : V → V → Prop) (seed : V → V → Prop)
    (witness : V) (hSeed : ∀ a, seed a a) (a : V)
    (hInstance : ClosureInstance mem seed (fun _ y => Sub mem y a)) :
    ∃ p, ∀ y, mem y p ↔ Sub mem y a := by
  apply constant_exact_of_instance mem seed witness hSeed (fun y => Sub mem y a)
  · exact ⟨a, fun _ h => h⟩
  · exact hInstance

/-- The gate ensures each local fiber has one bound, without assuming Union. -/
theorem switch_subset_bounded (mem : V → V → Prop) :
    SubsetBounded mem (Switch mem) := by
  classical
  intro x
  by_cases hSingle : ∃ t, Sing mem x t
  · obtain ⟨t, ht⟩ := hSingle
    refine ⟨t, ?_⟩
    intro y hy
    rcases hy with hy | hy
    · have hyt : y = t := (ht y).mp ((hy y).mpr rfl)
      subst y
      exact sub_refl mem t
    · exact False.elim (hy.1 ⟨t, ht⟩)
  · refine ⟨x, ?_⟩
    intro y hy
    rcases hy with hy | hy
    · exact False.elim (hSingle ⟨y, hy⟩)
    · exact hy.2

/-- Any Switch-closed set is transitive, using exact singleton existence only. -/
theorem switch_closed_transitive (mem : V → V → Prop)
    (hSingletons : SingletonsExact mem) (c : V)
    (hClosed : ∀ x y, mem x c → Switch mem x y → mem y c) :
    Transitive mem c := by
  classical
  intro x hx y hy
  by_cases hSingle : ∃ t, Sing mem x t
  · obtain ⟨t, ht⟩ := hSingle
    have hyt : y = t := (ht y).mp hy
    subst y
    exact hClosed x t hx (Or.inl ht)
  · obtain ⟨s, hs⟩ := hSingletons y
    have hsub : Sub mem s x := by
      intro z hz
      have hzy : z = y := (hs z).mp hz
      subst z
      exact hy
    have hsC : mem s c := hClosed x s hx (Or.inr ⟨hSingle, hsub⟩)
    exact hClosed s y hsC (Or.inl hs)

/-- Initial Switch outputs suffice to cover members of A; A need not be in C. -/
theorem switch_root_covers (mem : V → V → Prop)
    (hSingletons : SingletonsExact mem) (a c : V)
    (hInitial : ∀ y, Switch mem a y → mem y c)
    (hClosed : ∀ x y, mem x c → Switch mem x y → mem y c) :
    Sub mem a c := by
  classical
  intro y hy
  by_cases hSingle : ∃ t, Sing mem a t
  · obtain ⟨t, ht⟩ := hSingle
    have hyt : y = t := (ht y).mp hy
    subst y
    exact hInitial t (Or.inl ht)
  · obtain ⟨s, hs⟩ := hSingletons y
    have hsub : Sub mem s a := by
      intro z hz
      have hzy : z = y := (hs z).mp hz
      subst z
      exact hy
    have hsC : mem s c := hInitial s (Or.inr ⟨hSingle, hsub⟩)
    exact hClosed s y hsC (Or.inl hs)

/-- The new bootstrap: a positive decoder hull is a transitive cover of A. -/
theorem positive_decoder_cover (mem : V → V → Prop) (seed : V → V → Prop)
    (hSeed : ∀ a, seed a a) (hSingletons : SingletonsExact mem)
    (hInstance : ClosureInstance mem seed (Switch mem)) (a : V) :
    ∃ c, Transitive mem c ∧ Sub mem a c := by
  obtain ⟨c, hClosed, _hSupport⟩ := hInstance (switch_subset_bounded mem) a
  have hStep : ∀ x y, mem x c → Switch mem x y → mem y c := by
    intro x y hx hr
    exact hClosed x y (Or.inr hx) hr
  refine ⟨c, switch_closed_transitive mem hSingletons c hStep, ?_⟩
  apply switch_root_covers mem hSingletons a c
  · intro y hr
    exact hClosed a y (Or.inl (hSeed a)) hr
  · exact hStep

/-- Separation needs the decoder instance and this precise constant instance.
P is a semantic predicate parameter; no claim of a global first-order proof
transformer follows from this shallow statement. -/
theorem separation_of_instances (mem : V → V → Prop) (seed : V → V → Prop)
    (witness : V) (hSeed : ∀ a, seed a a) (hSingletons : SingletonsExact mem)
    (hSwitch : ClosureInstance mem seed (Switch mem)) (a : V) (p : V → Prop)
    (hConstant : ClosureInstance mem seed (fun _ y => mem y a ∧ p y)) :
    ∃ s, ∀ y, mem y s ↔ mem y a ∧ p y := by
  obtain ⟨c, hTrans, hCover⟩ := positive_decoder_cover mem seed hSeed hSingletons hSwitch a
  apply constant_exact_of_instance mem seed witness hSeed (fun y => mem y a ∧ p y)
  · refine ⟨c, ?_⟩
    intro y hy
    exact hTrans y (hCover y hy.1)
  · exact hConstant

/-- Union likewise needs no prior Union, Separation, Foundation, or Collection. -/
theorem union_of_instances (mem : V → V → Prop) (seed : V → V → Prop)
    (witness : V) (hSeed : ∀ a, seed a a) (hSingletons : SingletonsExact mem)
    (hSwitch : ClosureInstance mem seed (Switch mem)) (a : V)
    (hConstant : ClosureInstance mem seed (fun _ y => ∃ x, mem x a ∧ mem y x)) :
    ∃ s, ∀ y, mem y s ↔ ∃ x, mem x a ∧ mem y x := by
  obtain ⟨c, hTrans, hCover⟩ := positive_decoder_cover mem seed hSeed hSingletons hSwitch a
  apply constant_exact_of_instance mem seed witness hSeed (fun y => ∃ x, mem x a ∧ mem y x)
  · refine ⟨c, ?_⟩
    intro y hy
    obtain ⟨x, hxA, hyx⟩ := hy
    have hyC : mem y c := hTrans x (hCover x hxA) y hyx
    exact hTrans y hyC
  · exact hConstant

end SetTheory.BusyBeaver.ZFC.PositiveClosure

-- Audit the proved dependency boundary; these are not new axioms.
#print axioms SetTheory.BusyBeaver.ZFC.PositiveClosure.constant_exact_of_instance
#print axioms SetTheory.BusyBeaver.ZFC.PositiveClosure.switch_subset_bounded
#print axioms SetTheory.BusyBeaver.ZFC.PositiveClosure.positive_decoder_cover
#print axioms SetTheory.BusyBeaver.ZFC.PositiveClosure.separation_of_instances
#print axioms SetTheory.BusyBeaver.ZFC.PositiveClosure.union_of_instances
