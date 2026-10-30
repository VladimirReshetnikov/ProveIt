import BusyBeaver.ZFC.ProfilePairs
import BusyBeaver.ZFC.PositiveClosure

/-!
Equality-free profile-pair existence and diagonal bisimulations.

Each collection assumption names one explicit semantic relation instance.
The profile predicates use no actual equality or profile-congruence axiom.
This file does not yet represent those instances in first-order syntax or
prove a whole-theory interpretation. In particular, bisimulation
transitivity and quotient Extensionality remain separate obligations.
-/

namespace SetTheory.BusyBeaver.ZFC.ProfileCollection

open Profile ProfilePairs

universe u
variable {V : Type u}

/-- The global-image collection witness; it may choose one output per input. -/
def ImageCollection (mem : V → V → Prop) (r : V → V → Prop) (a b : V) : Prop :=
  (∀ y, mem y b → ∃ x, r x y) ∧
  (∀ x, mem x a → (∃ y, r x y) → ∃ y, mem y b ∧ r x y)

def CollectionInstance (mem : V → V → Prop) (r : V → V → Prop) : Prop :=
  ∀ a, ∃ b, ImageCollection mem r a b

def Containers (mem : V → V → Prop) : Prop :=
  ∀ a, ∃ v, mem a v ∧ PositiveClosure.Transitive mem v ∧
    ∀ x, mem x v → ∃ p, mem p v ∧ ∀ z, PositiveClosure.Sub mem z x → mem z p

theorem empty_of_collection (mem : V → V → Prop) (witness : V)
    (hCollect : CollectionInstance mem (fun _ _ => False)) :
    ∃ e, ∀ z, ¬ mem z e := by
  obtain ⟨e, hs, _⟩ := hCollect witness
  exact ⟨e, fun z hz => (hs z hz).elim fun _ h => h⟩

/-- An empty object and its power bound give distinct input profiles in one host. -/
theorem two_indices_of_container (mem : V → V → Prop) (e : V)
    (hEmpty : ∀ z, ¬ mem z e) (hContainers : Containers mem) :
    ∃ domain j, mem e domain ∧ mem j domain ∧ ¬ Same mem e j := by
  obtain ⟨domain, he, _, hp⟩ := hContainers e
  obtain ⟨j, hj, hBound⟩ := hp e he
  have hej : mem e j := hBound e (PositiveClosure.sub_refl mem e)
  exact ⟨domain, j, he, hj, fun hSame => hEmpty e ((hSame e).mpr hej)⟩

def PairChoice (mem : V → V → Prop) (i j a b x y : V) : Prop :=
  (Same mem x i ∧ Same mem y a) ∨ (Same mem x j ∧ Same mem y b)

/-- Two distinct input profiles suffice to collect a pair of output profiles. -/
theorem pair_of_collection (mem : V → V → Prop) (i j domain a b : V)
    (hi : mem i domain) (hj : mem j domain) (hDifferent : ¬ Same mem i j)
    (hCollect : CollectionInstance mem (PairChoice mem i j a b)) :
    ∃ p, Pair mem p a b := by
  obtain ⟨p, hSupport, hCover⟩ := hCollect domain
  obtain ⟨ua, hua, hia⟩ := hCover i hi
    ⟨a, Or.inl ⟨same_refl mem i, same_refl mem a⟩⟩
  obtain ⟨ub, hub, hjb⟩ := hCover j hj
    ⟨b, Or.inr ⟨same_refl mem j, same_refl mem b⟩⟩
  have huaClass : Same mem ua a := Or.elim hia And.right fun h => absurd h.1 hDifferent
  have hubClass : Same mem ub b :=
    Or.elim hjb (fun h => absurd (same_symm mem h.1) hDifferent) And.right
  refine ⟨p, fun z => ⟨?_, fun hz => hz.elim
    (fun hza => ⟨ua, hua, same_trans mem hza (same_symm mem huaClass)⟩)
    (fun hzb => ⟨ub, hub, same_trans mem hzb (same_symm mem hubClass)⟩)⟩⟩
  rintro ⟨y, hy, hzy⟩
  obtain ⟨x, hxy⟩ := hSupport y hy
  exact Or.elim hxy (fun h => Or.inl (same_trans mem hzy h.2))
    (fun h => Or.inr (same_trans mem hzy h.2))

theorem singleton_of_pair (mem : V → V → Prop) {a s : V} (h : Pair mem s a a) :
    Singleton mem s a :=
  fun z => (h z).trans ⟨fun h => h.elim id id, Or.inl⟩

theorem orderedPairs_of_pairs (mem : V → V → Prop)
    (hPairs : ∀ a b, ∃ p, Pair mem p a b) (a b : V) :
    ∃ c, OrderedPair mem a b c := by
  obtain ⟨s, hs⟩ := hPairs a a
  obtain ⟨p, hp⟩ := hPairs a b
  obtain ⟨c, hc⟩ := hPairs s p
  exact ⟨c, s, p, singleton_of_pair mem hs, hp, hc⟩

/-- Only the false and fixed four-parameter pair-choice templates are used. -/
theorem pairs_of_instances (mem : V → V → Prop) (witness : V)
    (hContainers : Containers mem)
    (hFalse : CollectionInstance mem (fun _ _ => False))
    (hChoices : ∀ i j a b, CollectionInstance mem (PairChoice mem i j a b)) :
    ∀ a b, ∃ p, Pair mem p a b := by
  obtain ⟨e, he⟩ := empty_of_collection mem witness hFalse
  obtain ⟨domain, j, hei, hj, hDifferent⟩ := two_indices_of_container mem e he hContainers
  exact fun a b => pair_of_collection mem e j domain a b hei hj hDifferent (hChoices e j a b)

def App (mem : V → V → Prop) (r x y : V) : Prop :=
  ∃ c, mem c r ∧ OrderedPair mem x y c

theorem app_congr (mem : V → V → Prop) {r x y x' y' : V}
    (hx : Same mem x x') (hy : Same mem y y') (h : App mem r x y) :
    App mem r x' y' := by
  obtain ⟨c, hc, hxy⟩ := h
  exact ⟨c, hc, orderedPair_endpoint_congr mem hx hy hxy⟩

def Bisim (mem : V → V → Prop) (r : V) : Prop :=
  ∀ x y, App mem r x y →
    (∀ a, mem a x → ∃ b, mem b y ∧ App mem r a b) ∧
    (∀ b, mem b y → ∃ a, mem a x ∧ App mem r a b)

def Eqv (mem : V → V → Prop) (x y : V) : Prop :=
  ∃ r, Bisim mem r ∧ App mem r x y

def DiagonalChoice (mem : V → V → Prop) (domain x c : V) : Prop :=
  mem x domain ∧ OrderedPair mem x x c

/-- Collecting diagonal codes over one transitive container gives reflexivity.
No endpoint itself is inferred to lie in the container from profile equality;
only its literal members are transported to the represented input. -/
theorem bisim_refl_of_collection (mem : V → V → Prop) (a domain : V)
    (ha : mem a domain) (hTrans : PositiveClosure.Transitive mem domain)
    (hPairs : ∀ x y, ∃ c, OrderedPair mem x y c)
    (hCollect : CollectionInstance mem (DiagonalChoice mem domain)) : Eqv mem a a := by
  obtain ⟨r, hSupport, hCover⟩ := hCollect domain
  have hDiagonal (x : V) (hx : mem x domain) : App mem r x x := by
    obtain ⟨c, hc⟩ := hPairs x x
    exact (hCover x hx ⟨c, hx, hc⟩).imp fun _ h => ⟨h.1, h.2.2⟩
  have hShape (x y : V) (hxy : App mem r x y) :
      ∃ t, mem t domain ∧ Same mem x t ∧ Same mem y t := by
    obtain ⟨c, hcr, hxy⟩ := hxy
    obtain ⟨t, ht, htt⟩ := hSupport c hcr
    exact ⟨t, ht, orderedPair_injective mem hxy htt⟩
  refine ⟨r, fun x y hxy => ?_, hDiagonal a ha⟩
  obtain ⟨t, ht, hxt, hyt⟩ := hShape x y hxy
  have hsame : Same mem x y := same_trans mem hxt (same_symm mem hyt)
  exact ⟨fun u hu => ⟨u, (hsame u).mp hu, hDiagonal u (hTrans t ht u ((hxt u).mp hu))⟩,
    fun u hu => ⟨u, (hsame u).mpr hu, hDiagonal u (hTrans t ht u ((hyt u).mp hu))⟩⟩

def ReverseChoice (mem : V → V → Prop) (r d c : V) : Prop :=
  mem d r ∧ ∃ x y, OrderedPair mem x y d ∧ OrderedPair mem y x c

theorem reverse_of_collection (mem : V → V → Prop) (r : V)
    (hPairs : ∀ x y, ∃ c, OrderedPair mem x y c)
    (hCollect : CollectionInstance mem (ReverseChoice mem r)) :
    ∃ s, ∀ x y, App mem s x y ↔ App mem r y x := by
  obtain ⟨s, hSupport, hCover⟩ := hCollect r
  refine ⟨s, fun x y => ⟨?_, ?_⟩⟩
  · rintro ⟨c, hc, hxy⟩
    obtain ⟨d, hdr, p, q, hpq, hqp⟩ := hSupport c hc
    obtain ⟨hxq, hyp⟩ := orderedPair_injective mem hxy hqp
    exact app_congr mem (same_symm mem hyp) (same_symm mem hxq) ⟨d, hdr, hpq⟩
  · rintro ⟨d, hdr, hyx⟩
    obtain ⟨c, hxy⟩ := hPairs x y
    obtain ⟨e, hes, _, p, q, hpq, hqp⟩ := hCover d hdr ⟨c, hdr, y, x, hyx, hxy⟩
    obtain ⟨hyp, hxq⟩ := orderedPair_injective mem hyx hpq
    exact ⟨e, hes, orderedPair_endpoint_congr mem
      (same_symm mem hxq) (same_symm mem hyp) hqp⟩

theorem bisim_reverse (mem : V → V → Prop) {r s : V}
    (hr : Bisim mem r) (hReverse : ∀ x y, App mem s x y ↔ App mem r y x) :
    Bisim mem s := by
  intro x y hxy
  obtain ⟨hForth, hBack⟩ := hr y x ((hReverse x y).mp hxy)
  exact ⟨fun a ha => (hBack a ha).imp fun b h => ⟨h.1, (hReverse a b).mpr h.2⟩,
    fun b hb => (hForth b hb).imp fun a h => ⟨h.1, (hReverse a b).mpr h.2⟩⟩

/-- Symmetry uses only the explicitly named reversal relation instances. -/
theorem eqv_symm_of_instances (mem : V → V → Prop)
    (hPairs : ∀ x y, ∃ c, OrderedPair mem x y c)
    (hReverse : ∀ r, CollectionInstance mem (ReverseChoice mem r))
    {x y : V} (h : Eqv mem x y) : Eqv mem y x := by
  obtain ⟨r, hr, hxy⟩ := h
  obtain ⟨s, hs⟩ := reverse_of_collection mem r hPairs (hReverse r)
  exact ⟨s, bisim_reverse mem hr hs, (hs y x).mpr hxy⟩

#print axioms pair_of_collection
#print axioms orderedPairs_of_pairs
#print axioms bisim_refl_of_collection
#print axioms eqv_symm_of_instances

end SetTheory.BusyBeaver.ZFC.ProfileCollection
