import BusyBeaver.ZFC.ProfileCollection

/-!
Composition of equality-free profile-coded bisimulations.

Two named GIC templates collect one composition fiber per source code;
a third forms a union up to raw profiles. This proves exact composition
at the represented App relation, without raw Separation, profile congruence,
literal representative selection or closure for arbitrary semantic relations.
These are semantic per-instance lemmas; first-order syntax adapters and
whole-theory/machine calibration are separate obligations.
-/

namespace SetTheory.BusyBeaver.ZFC.ProfileComposition

open Profile ProfilePairs ProfileCollection

universe u
variable {V : Type u}

/-- Every set lies in a transitive set: the half of `Containers` that the edge lemmas read.
(The tagged domain of the lower chain has these but no literal power containers.) -/
def TransContainers (mem : V → V → Prop) : Prop :=
  ∀ a, ∃ v, mem a v ∧ PositiveClosure.Transitive mem v

theorem transContainers_of_containers {mem : V → V → Prop} (h : Containers mem) :
    TransContainers mem :=
  fun a => let ⟨v, hav, ht, _⟩ := h a; ⟨v, hav, ht⟩

theorem orderedPair_code_congr (mem : V → V → Prop) {a b c d : V}
    (hcd : Same mem c d) (hc : OrderedPair mem a b c) : OrderedPair mem a b d :=
  let ⟨s, p, hs, hp, hOuter⟩ := hc; ⟨s, p, hs, hp, pair_object_congr mem hcd hOuter⟩

theorem app_object_congr (mem : V → V → Prop) {r s : V}
    (hrs : Same mem r s) (a b : V) : App mem r a b ↔ App mem s a b :=
  ⟨fun ⟨c, hc, hab⟩ => ⟨c, (hrs c).mp hc, hab⟩, fun ⟨c, hc, hab⟩ => ⟨c, (hrs c).mpr hc, hab⟩⟩

def UnionChoice (mem : V → V → Prop) (family x y : V) : Prop :=
  (∃ r, mem r family ∧ mem x r) ∧ Same mem y x

/-- Approximate raw Union is exact at the represented edge relation. -/
theorem union_edges_of_instance (mem : V → V → Prop) (family : V)
    (hContainers : TransContainers mem)
    (hCollect : CollectionInstance mem (UnionChoice mem family)) :
    ∃ s, ∀ a b, App mem s a b ↔ ∃ r, mem r family ∧ App mem r a b := by
  obtain ⟨domain, hFamily, hTrans⟩ := hContainers family
  obtain ⟨s, hSupport, hCover⟩ := hCollect domain
  refine ⟨s, fun a b => ?_⟩
  constructor
  · rintro ⟨c, hcs, hcode⟩
    obtain ⟨d, ⟨r, hrFamily, hdr⟩, hcd⟩ := hSupport c hcs
    exact ⟨r, hrFamily, d, hdr, orderedPair_code_congr mem hcd hcode⟩
  · rintro ⟨r, hrFamily, d, hdr, hcode⟩
    obtain ⟨c, hcs, _, hcd⟩ := hCover d (hTrans r (hTrans family hFamily r hrFamily) d hdr)
      ⟨d, ⟨r, hrFamily, hdr⟩, same_refl mem d⟩
    exact ⟨c, hcs, orderedPair_code_congr mem (same_symm mem hcd) hcode⟩

def FiberChoice (mem : V → V → Prop) (r2 d c e : V) : Prop :=
  mem c r2 ∧ ∃ s t u, OrderedPair mem s t d ∧
    OrderedPair mem t u c ∧ OrderedPair mem s u e

def FiberProfile (mem : V → V → Prop) (r2 d s : V) : Prop :=
  ∀ a b, App mem s a b ↔ ∃ t, OrderedPair mem a t d ∧ App mem r2 t b

/-- GIC over the second relation collects all edges composable with this code. -/
theorem fiber_of_instance (mem : V → V → Prop) (r2 d : V)
    (hCodes : ∀ a b, ∃ c, OrderedPair mem a b c)
    (hCollect : CollectionInstance mem (FiberChoice mem r2 d)) :
    ∃ s, FiberProfile mem r2 d s := by
  obtain ⟨s, hSupport, hCover⟩ := hCollect r2
  refine ⟨s, fun a b => ?_⟩
  constructor
  · rintro ⟨e, hes, hab⟩
    obtain ⟨c, hcr2, p, q, u, hpq, hqu, hpu⟩ := hSupport e hes
    obtain ⟨hap, hbu⟩ := orderedPair_injective mem hab hpu
    refine ⟨q, orderedPair_endpoint_congr mem (same_symm mem hap) (same_refl mem q) hpq, ?_⟩
    exact app_congr mem (same_refl mem q) (same_symm mem hbu) ⟨c, hcr2, hqu⟩
  · rintro ⟨t, hat, c, hcr2, htb⟩
    obtain ⟨e, hae⟩ := hCodes a b
    obtain ⟨f, hfs, _, p, q, u, hpq, hqu, hpu⟩ :=
      hCover c hcr2 ⟨e, hcr2, a, t, b, hat, htb, hae⟩
    exact ⟨f, hfs, orderedPair_endpoint_congr mem
      (same_symm mem (orderedPair_injective mem hat hpq).1)
      (same_symm mem (orderedPair_injective mem htb hqu).2) hpu⟩

def CompositionChoice (mem : V → V → Prop) (r1 r2 d s : V) : Prop :=
  mem d r1 ∧ FiberProfile mem r2 d s

/-- Two GIC layers plus the named approximate-union instance compose App exactly. -/
theorem composition_of_instances (mem : V → V → Prop) (r1 r2 : V)
    (hContainers : TransContainers mem)
    (hCodes : ∀ a b, ∃ c, OrderedPair mem a b c)
    (hFibers : ∀ d, CollectionInstance mem (FiberChoice mem r2 d))
    (hComposition : CollectionInstance mem (CompositionChoice mem r1 r2))
    (hUnions : ∀ family, CollectionInstance mem (UnionChoice mem family)) :
    ∃ s, ∀ a b, App mem s a b ↔ ∃ t, App mem r1 a t ∧ App mem r2 t b := by
  obtain ⟨family, hSupport, hCover⟩ := hComposition r1
  obtain ⟨s, hs⟩ := union_edges_of_instance mem family hContainers (hUnions family)
  refine ⟨s, fun a b => ?_⟩
  constructor
  · intro hab
    obtain ⟨fiber, hfFamily, habFiber⟩ := (hs a b).mp hab
    obtain ⟨d, hdr1, hFiber⟩ := hSupport fiber hfFamily
    obtain ⟨t, hat, htb⟩ := (hFiber a b).mp habFiber
    exact ⟨t, ⟨d, hdr1, hat⟩, htb⟩
  · rintro ⟨t, ⟨d, hdr1, hat⟩, htb⟩
    obtain ⟨fiber, hFiber⟩ := fiber_of_instance mem r2 d hCodes (hFibers d)
    obtain ⟨selected, hSelected, _, hSelectedFiber⟩ :=
      hCover d hdr1 ⟨fiber, hdr1, hFiber⟩
    exact (hs a b).mpr ⟨selected, hSelected, (hSelectedFiber a b).mpr ⟨t, hat, htb⟩⟩

theorem bisim_composition (mem : V → V → Prop) {r1 r2 s : V}
    (h1 : Bisim mem r1) (h2 : Bisim mem r2)
    (hComp : ∀ a b, App mem s a b ↔ ∃ t, App mem r1 a t ∧ App mem r2 t b) :
    Bisim mem s := by
  intro a b hab
  obtain ⟨t, hat, htb⟩ := (hComp a b).mp hab
  obtain ⟨hF1, hB1⟩ := h1 a t hat
  obtain ⟨hF2, hB2⟩ := h2 t b htb
  refine ⟨fun x hx => ?_, fun z hz => ?_⟩
  · obtain ⟨y, hy, hxy⟩ := hF1 x hx
    obtain ⟨z, hz, hyz⟩ := hF2 y hy
    exact ⟨z, hz, (hComp x z).mpr ⟨y, hxy, hyz⟩⟩
  · obtain ⟨y, hy, hyz⟩ := hB2 z hz
    obtain ⟨x, hx, hxy⟩ := hB1 y hy
    exact ⟨x, hx, (hComp x z).mpr ⟨y, hxy, hyz⟩⟩

/-- Bisimulation transitivity from the three fixed collection-template families. -/
theorem eqv_trans_of_instances (mem : V → V → Prop)
    (hContainers : TransContainers mem)
    (hCodes : ∀ a b, ∃ c, OrderedPair mem a b c)
    (hFibers : ∀ r2 d, CollectionInstance mem (FiberChoice mem r2 d))
    (hCompositions : ∀ r1 r2, CollectionInstance mem (CompositionChoice mem r1 r2))
    (hUnions : ∀ family, CollectionInstance mem (UnionChoice mem family))
    {x y z : V} (hxy : Eqv mem x y) (hyz : Eqv mem y z) : Eqv mem x z := by
  obtain ⟨r1, h1, hxy⟩ := hxy
  obtain ⟨r2, h2, hyz⟩ := hyz
  obtain ⟨s, hs⟩ := composition_of_instances mem r1 r2 hContainers hCodes
    (hFibers r2) (hCompositions r1 r2) hUnions
  exact ⟨s, bisim_composition mem h1 h2 hs, (hs x z).mpr ⟨y, hxy, hyz⟩⟩

theorem join_edges_of_instances (mem : V → V → Prop) (r1 r2 : V)
    (hContainers : TransContainers mem)
    (hPairs : ∀ a b, ∃ p, Pair mem p a b)
    (hUnions : ∀ family, CollectionInstance mem (UnionChoice mem family)) :
    ∃ s, ∀ a b, App mem s a b ↔ App mem r1 a b ∨ App mem r2 a b := by
  obtain ⟨p, hp⟩ := hPairs r1 r2
  obtain ⟨s, hs⟩ := union_edges_of_instance mem p hContainers (hUnions p)
  refine ⟨s, fun a b => ?_⟩
  constructor
  · intro hab
    obtain ⟨r, hrp, hrab⟩ := (hs a b).mp hab
    rcases (hp r).mp ⟨r, hrp, same_refl mem r⟩ with hr1 | hr2
    · exact Or.inl ((app_object_congr mem hr1 a b).mp hrab)
    · exact Or.inr ((app_object_congr mem hr2 a b).mp hrab)
  · rintro (h1 | h2)
    · obtain ⟨r, hrp, hr1⟩ := (hp r1).mpr (Or.inl (same_refl mem r1))
      exact (hs a b).mpr ⟨r, hrp, (app_object_congr mem hr1 a b).mp h1⟩
    · obtain ⟨r, hrp, hr2⟩ := (hp r2).mpr (Or.inr (same_refl mem r2))
      exact (hs a b).mpr ⟨r, hrp, (app_object_congr mem hr2 a b).mp h2⟩

theorem singleton_edges (mem : V → V → Prop) (k p : V) (hp : Pair mem p k k) :
    ∀ a b, App mem p a b ↔ OrderedPair mem a b k := by
  intro a b
  constructor
  · rintro ⟨c, hcp, hab⟩
    exact orderedPair_code_congr mem (((hp c).mp ⟨c, hcp, same_refl mem c⟩).elim id id) hab
  · intro hab
    obtain ⟨c, hcp, hkc⟩ := (hp k).mpr (Or.inl (same_refl mem k))
    exact ⟨c, hcp, orderedPair_code_congr mem hkc hab⟩

theorem bisim_union_edges (mem : V → V → Prop) (family s : V)
    (hFamily : ∀ r, mem r family → Bisim mem r)
    (hUnion : ∀ a b, App mem s a b ↔ ∃ r, mem r family ∧ App mem r a b) :
    Bisim mem s := by
  intro a b hab
  obtain ⟨r, hr, hrab⟩ := (hUnion a b).mp hab
  obtain ⟨hForth, hBack⟩ := hFamily r hr a b hrab
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · obtain ⟨y, hy, hxy⟩ := hForth x hx
    exact ⟨y, hy, (hUnion x y).mpr ⟨r, hr, hxy⟩⟩
  · obtain ⟨x, hx, hxy⟩ := hBack y hy
    exact ⟨x, hx, (hUnion x y).mpr ⟨r, hr, hxy⟩⟩

theorem bisim_join_edges (mem : V → V → Prop) {r1 r2 s : V}
    (h1 : Bisim mem r1) (h2 : Bisim mem r2)
    (hJoin : ∀ a b, App mem s a b ↔ App mem r1 a b ∨ App mem r2 a b) :
    Bisim mem s := by
  intro a b hab
  rcases (hJoin a b).mp hab with hab1 | hab2
  · obtain ⟨hForth, hBack⟩ := h1 a b hab1
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · obtain ⟨y, hy, hxy⟩ := hForth x hx
      exact ⟨y, hy, (hJoin x y).mpr (Or.inl hxy)⟩
    · obtain ⟨x, hx, hxy⟩ := hBack y hy
      exact ⟨x, hx, (hJoin x y).mpr (Or.inl hxy)⟩
  · obtain ⟨hForth, hBack⟩ := h2 a b hab2
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · obtain ⟨y, hy, hxy⟩ := hForth x hx
      exact ⟨y, hy, (hJoin x y).mpr (Or.inr hxy)⟩
    · obtain ⟨x, hx, hxy⟩ := hBack y hy
      exact ⟨x, hx, (hJoin x y).mpr (Or.inr hxy)⟩

def MatchChoice (mem : V → V → Prop) (x y a r : V) : Prop :=
  mem a x ∧ ∃ b, mem b y ∧ Bisim mem r ∧ App mem r a b

def BackMatchChoice (mem : V → V → Prop) (x y b r : V) : Prop :=
  mem b y ∧ ∃ a, mem a x ∧ Bisim mem r ∧ App mem r a b

/-- Collect entire forward and backward matching bisimulations, then adjoin the root edge. -/
theorem eqv_matching_of_instances (mem : V → V → Prop) (x y : V)
    (hContainers : TransContainers mem)
    (hPairs : ∀ a b, ∃ p, Pair mem p a b)
    (hUnions : ∀ family, CollectionInstance mem (UnionChoice mem family))
    (hForwardCollection : CollectionInstance mem (MatchChoice mem x y))
    (hBackCollection : CollectionInstance mem (BackMatchChoice mem x y))
    (hForward : ∀ a, mem a x → ∃ b, mem b y ∧ Eqv mem a b)
    (hBack : ∀ b, mem b y → ∃ a, mem a x ∧ Eqv mem a b) : Eqv mem x y := by
  obtain ⟨ff, hSupportF, hCoverF⟩ := hForwardCollection x
  obtain ⟨bf, hSupportB, hCoverB⟩ := hBackCollection y
  obtain ⟨fr, hUnionF⟩ := union_edges_of_instance mem ff hContainers (hUnions ff)
  obtain ⟨br, hUnionB⟩ := union_edges_of_instance mem bf hContainers (hUnions bf)
  have hBisF : Bisim mem fr := bisim_union_edges mem ff fr (fun r hr => by
    obtain ⟨a, _, b, _, hBis, _⟩ := hSupportF r hr; exact hBis) hUnionF
  have hBisB : Bisim mem br := bisim_union_edges mem bf br (fun r hr => by
    obtain ⟨b, _, a, _, hBis, _⟩ := hSupportB r hr; exact hBis) hUnionB
  obtain ⟨joined, hJoin⟩ := join_edges_of_instances mem fr br hContainers hPairs hUnions
  have hRootF : ∀ a, mem a x → ∃ b, mem b y ∧ App mem joined a b := by
    intro a ha
    obtain ⟨b, hb, r, hr, hab⟩ := hForward a ha
    obtain ⟨selected, hSelected, _, b', hb', _, hab'⟩ :=
      hCoverF a ha ⟨r, ha, b, hb, hr, hab⟩
    exact ⟨b', hb', (hJoin a b').mpr (Or.inl
      ((hUnionF a b').mpr ⟨selected, hSelected, hab'⟩))⟩
  have hRootB : ∀ b, mem b y → ∃ a, mem a x ∧ App mem joined a b := by
    intro b hb
    obtain ⟨a, ha, r, hr, hab⟩ := hBack b hb
    obtain ⟨selected, hSelected, _, a', ha', _, hab'⟩ :=
      hCoverB b hb ⟨r, hb, a, ha, hr, hab⟩
    exact ⟨a', ha', (hJoin a' b).mpr (Or.inr
      ((hUnionB a' b).mpr ⟨selected, hSelected, hab'⟩))⟩
  obtain ⟨k, hk⟩ := orderedPairs_of_pairs mem hPairs x y
  obtain ⟨single, hSingle⟩ := hPairs k k
  have hSingleEdges := singleton_edges mem k single hSingle
  obtain ⟨r, hRootJoin⟩ :=
    join_edges_of_instances mem joined single hContainers hPairs hUnions
  refine ⟨r, fun a b hab => ?_, (hRootJoin x y).mpr (Or.inr ((hSingleEdges x y).mpr hk))⟩
  rcases (hRootJoin a b).mp hab with hOld | hRoot
  · obtain ⟨hForth, hBack⟩ := bisim_join_edges mem hBisF hBisB hJoin a b hOld
    refine ⟨fun u hu => ?_, fun v hv => ?_⟩
    · obtain ⟨v, hv, huv⟩ := hForth u hu
      exact ⟨v, hv, (hRootJoin u v).mpr (Or.inl huv)⟩
    · obtain ⟨u, hu, huv⟩ := hBack v hv
      exact ⟨u, hu, (hRootJoin u v).mpr (Or.inl huv)⟩
  · obtain ⟨hax, hby⟩ := orderedPair_injective mem ((hSingleEdges a b).mp hRoot) hk
    refine ⟨fun u hu => ?_, fun v hv => ?_⟩
    · obtain ⟨v, hv, huv⟩ := hRootF u ((hax u).mp hu)
      exact ⟨v, (hby v).mpr hv, (hRootJoin u v).mpr (Or.inl huv)⟩
    · obtain ⟨u, hu, huv⟩ := hRootB v ((hby v).mp hv)
      exact ⟨u, (hax u).mpr hu, (hRootJoin u v).mpr (Or.inl huv)⟩

def Member (mem : V → V → Prop) (x y : V) : Prop :=
  ∃ u, mem u y ∧ Eqv mem x u

/-- Quotient Extensionality uses only the two explicit matching templates and App union. -/
theorem eqv_extensionality_of_instances (mem : V → V → Prop)
    (hContainers : TransContainers mem)
    (hPairs : ∀ a b, ∃ p, Pair mem p a b)
    (hUnions : ∀ family, CollectionInstance mem (UnionChoice mem family))
    (hForwardCollection : ∀ x y, CollectionInstance mem (MatchChoice mem x y))
    (hBackCollection : ∀ x y, CollectionInstance mem (BackMatchChoice mem x y))
    (hRefl : ∀ x, Eqv mem x x)
    (hSymm : ∀ x y, Eqv mem x y → Eqv mem y x)
    (x y : V) (hMembers : ∀ z, Member mem z x ↔ Member mem z y) : Eqv mem x y := by
  apply eqv_matching_of_instances mem x y hContainers hPairs hUnions
    (hForwardCollection x y) (hBackCollection x y)
  · exact fun a ha => (hMembers a).mp ⟨a, ha, hRefl a⟩
  · intro b hb
    obtain ⟨a, ha, hba⟩ := (hMembers b).mpr ⟨b, hb, hRefl b⟩
    exact ⟨a, ha, hSymm b a hba⟩

#print axioms union_edges_of_instance
#print axioms composition_of_instances
#print axioms eqv_trans_of_instances
#print axioms eqv_extensionality_of_instances

end SetTheory.BusyBeaver.ZFC.ProfileComposition
