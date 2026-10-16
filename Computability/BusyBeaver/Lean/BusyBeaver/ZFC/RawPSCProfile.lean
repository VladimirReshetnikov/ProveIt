import BusyBeaver.ZFC.PSCSaturation

/-!
Equality-free raw PSC bootstrap by full-profile twin singletons.

The full profile includes both incoming and outgoing membership agreement.
Its outgoing half makes twin-singleton decoding work without raw profile
congruence or logical equality in a schema matrix. The constructions follow
batch144 source08 of the closure-kernel collection. Every PSC resource names
its particular relation instance; actual first-order adapters are separate.
There is no assumption of closure for arbitrary semantic relations, and no
whole-theory consistency or machine theorem is asserted here.
-/

namespace SetTheory.BusyBeaver.ZFC.RawPSCProfile

open PositiveClosure Profile

universe u
variable {V : Type u}

def Full (mem : V → V → Prop) (x y : V) : Prop :=
  Same mem x y ∧ ∀ z, mem x z ↔ mem y z

def TwinSing (mem : V → V → Prop) (s t : V) : Prop :=
  ∀ z, mem z s ↔ Full mem z t

def TwinSingletons (mem : V → V → Prop) : Prop :=
  ∀ t, ∃ s, TwinSing mem s t

def TwinSwitch (mem : V → V → Prop) (x y : V) : Prop :=
  TwinSing mem x y ∨ ((¬ ∃ t, TwinSing mem x t) ∧ Sub mem y x)

theorem full_refl (mem : V → V → Prop) (x : V) : Full mem x x :=
  ⟨same_refl mem x, fun _ => Iff.rfl⟩

theorem full_symm (mem : V → V → Prop) {x y : V} (h : Full mem x y) : Full mem y x :=
  ⟨same_symm mem h.1, fun z => (h.2 z).symm⟩

theorem full_trans (mem : V → V → Prop) {x y z : V}
    (hxy : Full mem x y) (hyz : Full mem y z) : Full mem x z :=
  ⟨same_trans mem hxy.1 hyz.1, fun t => (hxy.2 t).trans (hyz.2 t)⟩

theorem full_mem_congr (mem : V → V → Prop) {x x' y y' : V}
    (hxx' : Full mem x x') (hyy' : Full mem y y') : mem x y ↔ mem x' y' :=
  (hxx'.2 y).trans (hyy'.1 x')

theorem full_right_iff (mem : V → V → Prop) {x y z : V}
    (hyz : Full mem y z) : Full mem x y ↔ Full mem x z :=
  ⟨fun h => full_trans mem h hyz, fun h => full_trans mem h (full_symm mem hyz)⟩

theorem full_subset (mem : V → V → Prop) {x y : V} (hxy : Full mem x y) : Sub mem x y :=
  fun z hz => (hxy.1 z).mp hz

theorem twin_of_instance (mem : V → V → Prop) (seed : V → V → Prop)
    (witness : V) (hSeed : ∀ a, seed a a) (t : V)
    (hInstance : ClosureInstance mem seed (fun _ y => Full mem y t)) :
    ∃ s, TwinSing mem s t := by
  exact constant_exact_of_instance mem seed witness hSeed (fun y => Full mem y t)
    ⟨t, fun _ hy => full_subset mem hy⟩ hInstance

theorem twins_of_instances (mem : V → V → Prop) (seed : V → V → Prop)
    (witness : V) (hSeed : ∀ a, seed a a)
    (hInstances : ∀ t, ClosureInstance mem seed (fun _ y => Full mem y t)) :
    TwinSingletons mem := by
  intro t
  exact twin_of_instance mem seed witness hSeed t (hInstances t)

theorem empty_of_instance (mem : V → V → Prop) (seed : V → V → Prop)
    (witness : V) (hSeed : ∀ a, seed a a)
    (hInstance : ClosureInstance mem seed (fun _ _ => False)) :
    ∃ e, ∀ y, ¬ mem y e := by
  obtain ⟨e, he⟩ := constant_exact_of_instance mem seed witness hSeed (fun _ => False)
    ⟨witness, fun _ h => h.elim⟩ hInstance
  exact ⟨e, fun y hy => (he y).mp hy⟩

/-- A twin singleton can have many raw members, all with one full profile. -/
theorem switch_subset_bounded (mem : V → V → Prop) :
    SubsetBounded mem (TwinSwitch mem) := by
  classical
  intro x
  by_cases hTwin : ∃ t, TwinSing mem x t
  · obtain ⟨t, ht⟩ := hTwin
    refine ⟨t, ?_⟩
    intro y hy
    rcases hy with hy | hy
    · exact full_subset mem ((ht y).mp ((hy y).mpr (full_refl mem y)))
    · exact (hy.1 ⟨t, ht⟩).elim
  · refine ⟨x, ?_⟩
    intro y hy
    rcases hy with hy | hy
    · exact (hTwin ⟨y, hy⟩).elim
    · exact hy.2

/-- Each membership edge is decoded in at most two switch steps. -/
theorem switch_edge_decode (mem : V → V → Prop) (hTwins : TwinSingletons mem)
    {x y : V} (hyx : mem y x) :
    TwinSwitch mem x y ∨ ∃ s, TwinSwitch mem x s ∧ TwinSwitch mem s y := by
  classical
  by_cases hTwin : ∃ t, TwinSing mem x t
  · obtain ⟨t, ht⟩ := hTwin
    have hyt : Full mem y t := (ht y).mp hyx
    exact Or.inl (Or.inl (fun z => (ht z).trans (full_right_iff mem hyt).symm))
  · obtain ⟨s, hs⟩ := hTwins y
    have hsx : Sub mem s x := by
      intro z hzs
      exact (((hs z).mp hzs).2 x).mpr hyx
    exact Or.inr ⟨s, Or.inr ⟨hTwin, hsx⟩, Or.inl hs⟩

theorem switch_closed_transitive (mem : V → V → Prop) (hTwins : TwinSingletons mem)
    (c : V) (hClosed : ∀ x y, mem x c → TwinSwitch mem x y → mem y c) :
    Transitive mem c := by
  intro x hxc y hyx
  rcases switch_edge_decode mem hTwins hyx with hxy | ⟨s, hxs, hsy⟩
  · exact hClosed x y hxc hxy
  · exact hClosed s y (hClosed x s hxc hxs) hsy

theorem switch_root_covers (mem : V → V → Prop) (hTwins : TwinSingletons mem)
    (a c : V) (hRoot : ∀ y, TwinSwitch mem a y → mem y c)
    (hClosed : ∀ x y, mem x c → TwinSwitch mem x y → mem y c) : Sub mem a c := by
  intro y hya
  rcases switch_edge_decode mem hTwins hya with hay | ⟨s, has, hsy⟩
  · exact hRoot y hay
  · exact hClosed s y (hRoot s has) hsy

theorem transitive_cover_of_instances (mem : V → V → Prop) (seed : V → V → Prop)
    (hSeed : ∀ a, seed a a) (hTwins : TwinSingletons mem)
    (hSwitch : ClosureInstance mem seed (TwinSwitch mem)) (a : V) :
    ∃ c, Transitive mem c ∧ Sub mem a c := by
  obtain ⟨c, hClosed, _⟩ := hSwitch (switch_subset_bounded mem) a
  have hStep : ∀ x y, mem x c → TwinSwitch mem x y → mem y c :=
    fun x y hx hxy => hClosed x y (Or.inr hx) hxy
  exact ⟨c, switch_closed_transitive mem hTwins c hStep,
    switch_root_covers mem hTwins a c
      (fun y hay => hClosed a y (Or.inl (hSeed a)) hay) hStep⟩

theorem separation_of_cover_instance (mem : V → V → Prop) (seed : V → V → Prop)
    (witness : V) (hSeed : ∀ a, seed a a) (a : V) (p : V → Prop)
    (hCover : ∃ c, Transitive mem c ∧ Sub mem a c)
    (hInstance : ClosureInstance mem seed (fun _ y => mem y a ∧ p y)) :
    ∃ b, Exact mem (fun y => mem y a ∧ p y) b := by
  obtain ⟨c, hc, hac⟩ := hCover
  exact constant_exact_of_instance mem seed witness hSeed (fun y => mem y a ∧ p y)
    ⟨c, fun y hy => hc y (hac y hy.1)⟩ hInstance

theorem union_of_cover_instance (mem : V → V → Prop) (seed : V → V → Prop)
    (witness : V) (hSeed : ∀ a, seed a a) (a : V)
    (hCover : ∃ c, Transitive mem c ∧ Sub mem a c)
    (hInstance : ClosureInstance mem seed (fun _ y => ∃ x, mem x a ∧ mem y x)) :
    ∃ b, Exact mem (fun y => ∃ x, mem x a ∧ mem y x) b := by
  obtain ⟨c, hc, hac⟩ := hCover
  apply constant_exact_of_instance mem seed witness hSeed _ ⟨c, ?_⟩ hInstance
  rintro y ⟨x, hxa, hyx⟩
  exact hc y (hc x (hac x hxa) y hyx)

theorem separation_of_instances (mem : V → V → Prop) (seed : V → V → Prop)
    (witness : V) (hSeed : ∀ a, seed a a) (hTwins : TwinSingletons mem)
    (hSwitch : ClosureInstance mem seed (TwinSwitch mem)) (a : V) (p : V → Prop)
    (hInstance : ClosureInstance mem seed (fun _ y => mem y a ∧ p y)) :
    ∃ b, Exact mem (fun y => mem y a ∧ p y) b := by
  exact separation_of_cover_instance mem seed witness hSeed a p
    (transitive_cover_of_instances mem seed hSeed hTwins hSwitch a) hInstance

theorem union_of_instances (mem : V → V → Prop) (seed : V → V → Prop)
    (witness : V) (hSeed : ∀ a, seed a a) (hTwins : TwinSingletons mem)
    (hSwitch : ClosureInstance mem seed (TwinSwitch mem)) (a : V)
    (hInstance : ClosureInstance mem seed (fun _ y => ∃ x, mem x a ∧ mem y x)) :
    ∃ b, Exact mem (fun y => ∃ x, mem x a ∧ mem y x) b := by
  exact union_of_cover_instance mem seed witness hSeed a
    (transitive_cover_of_instances mem seed hSeed hTwins hSwitch a) hInstance

#print axioms full_mem_congr
#print axioms twins_of_instances
#print axioms switch_subset_bounded
#print axioms switch_edge_decode
#print axioms transitive_cover_of_instances
#print axioms separation_of_instances
#print axioms union_of_instances

end SetTheory.BusyBeaver.ZFC.RawPSCProfile
