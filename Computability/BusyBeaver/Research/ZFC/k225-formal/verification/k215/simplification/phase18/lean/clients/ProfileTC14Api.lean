import BusyBeaver.ZFC.ProfileComposition
import BusyBeaver.ZFC.KLowerEqv

/-! Explicit six-contract client, checked with both the weak and old strong premises.
This is a prospective external audit; it adds no production declaration or assumption. -/
namespace SetTheory.BusyBeaver.ZFC.ProfileTC14Api

open Profile ProfilePairs ProfileCollection ProfileComposition

universe u
variable {V : Type u}

structure SixEdgeContracts (mem : V → V → Prop) : Prop where
  union_edges (family : V)
    (hCollect : CollectionInstance mem (UnionChoice mem family)) :
    ∃ s, ∀ a b, App mem s a b ↔ ∃ r, mem r family ∧ App mem r a b
  composition (r1 r2 : V)
    (hCodes : ∀ a b, ∃ c, OrderedPair mem a b c)
    (hFibers : ∀ d, CollectionInstance mem (FiberChoice mem r2 d))
    (hComposition : CollectionInstance mem (CompositionChoice mem r1 r2))
    (hUnions : ∀ family, CollectionInstance mem (UnionChoice mem family)) :
    ∃ s, ∀ a b, App mem s a b ↔ ∃ t, App mem r1 a t ∧ App mem r2 t b
  transitivity
    (hCodes : ∀ a b, ∃ c, OrderedPair mem a b c)
    (hFibers : ∀ r2 d, CollectionInstance mem (FiberChoice mem r2 d))
    (hCompositions : ∀ r1 r2, CollectionInstance mem (CompositionChoice mem r1 r2))
    (hUnions : ∀ family, CollectionInstance mem (UnionChoice mem family))
    {x y z : V} (hxy : Eqv mem x y) (hyz : Eqv mem y z) : Eqv mem x z
  join (r1 r2 : V)
    (hPairs : ∀ a b, ∃ p, Pair mem p a b)
    (hUnions : ∀ family, CollectionInstance mem (UnionChoice mem family)) :
    ∃ s, ∀ a b, App mem s a b ↔ App mem r1 a b ∨ App mem r2 a b
  matching (x y : V)
    (hPairs : ∀ a b, ∃ p, Pair mem p a b)
    (hUnions : ∀ family, CollectionInstance mem (UnionChoice mem family))
    (hForwardCollection : CollectionInstance mem (MatchChoice mem x y))
    (hBackCollection : CollectionInstance mem (BackMatchChoice mem x y))
    (hForward : ∀ a, mem a x → ∃ b, mem b y ∧ Eqv mem a b)
    (hBack : ∀ b, mem b y → ∃ a, mem a x ∧ Eqv mem a b) : Eqv mem x y
  extensionality
    (hPairs : ∀ a b, ∃ p, Pair mem p a b)
    (hUnions : ∀ family, CollectionInstance mem (UnionChoice mem family))
    (hForwardCollection : ∀ x y, CollectionInstance mem (MatchChoice mem x y))
    (hBackCollection : ∀ x y, CollectionInstance mem (BackMatchChoice mem x y))
    (hRefl : ∀ x, Eqv mem x x)
    (hSymm : ∀ x y, Eqv mem x y → Eqv mem y x)
    (x y : V) (hMembers : ∀ z, Member mem z x ↔ Member mem z y) : Eqv mem x y

theorem from_transitive (mem : V → V → Prop) (hTC : TransContainers mem) :
    SixEdgeContracts mem where
  union_edges family hCollect := union_edges_of_instance mem family hTC hCollect
  composition r1 r2 hCodes hFibers hComposition hUnions :=
    composition_of_instances mem r1 r2 hTC hCodes hFibers hComposition hUnions
  transitivity hCodes hFibers hCompositions hUnions _ _ _ hxy hyz :=
    eqv_trans_of_instances mem hTC hCodes hFibers hCompositions hUnions hxy hyz
  join r1 r2 hPairs hUnions := join_edges_of_instances mem r1 r2 hTC hPairs hUnions
  matching x y hPairs hUnions hForwardCollection hBackCollection hForward hBack :=
    eqv_matching_of_instances mem x y hTC hPairs hUnions hForwardCollection
      hBackCollection hForward hBack
  extensionality hPairs hUnions hForwardCollection hBackCollection hRefl hSymm x y hMembers :=
    eqv_extensionality_of_instances mem hTC hPairs hUnions hForwardCollection
      hBackCollection hRefl hSymm x y hMembers

theorem strong_to_transitive {mem : V → V → Prop} (h : Containers mem) :
    TransContainers mem := transContainers_of_containers h

theorem from_containers (mem : V → V → Prop) (h : Containers mem) :
    SixEdgeContracts mem := from_transitive mem (strong_to_transitive h)

theorem tag_trans {mem : V → V → Prop}
    (hs : KLower.FormSeed mem) (hirr : ∀ x, ¬ mem x x)
    {t : V} (ht : ∀ z, ¬ mem z t)
    {x y z : KLower.Tag mem t}
    (h1 : Eqv (KLower.tmem mem t) x y) (h2 : Eqv (KLower.tmem mem t) y z) :
    Eqv (KLower.tmem mem t) x z := KLower.tag_trans hs hirr ht h1 h2

theorem tag_ext {mem : V → V → Prop}
    (hs : KLower.FormSeed mem) (hirr : ∀ x, ¬ mem x x)
    {t : V} (ht : ∀ z, ¬ mem z t)
    (x y : KLower.Tag mem t)
    (h : ∀ z, Member (KLower.tmem mem t) z x ↔ Member (KLower.tmem mem t) z y) :
    Eqv (KLower.tmem mem t) x y := KLower.tag_ext hs hirr ht x y h

#print axioms strong_to_transitive
#print axioms from_transitive
#print axioms from_containers
#print axioms tag_trans
#print axioms tag_ext

end SetTheory.BusyBeaver.ZFC.ProfileTC14Api
