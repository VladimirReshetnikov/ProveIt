import BusyBeaver.ZFC.ProfileCongruence

/-!
Equality-free ordered-pair codes with endpoint uniqueness up to raw profiles.

No profile congruence, Extensionality, set existence or actual singleton axiom
is assumed. All definitions use only membership and logical connectives; Lean
equality is not part of the represented predicates. Existence of these codes
in the equality-free container/collection theory is a separate obligation.
The final bisimulation interpretation and machine calibration remain open.
-/

namespace SetTheory.BusyBeaver.ZFC.ProfilePairs

open Profile

universe u
variable {V : Type u}

/-- Membership saturated in its first argument by raw predecessor profiles. -/
def ClassMember (mem : V → V → Prop) (a b : V) : Prop :=
  ∃ z, mem z b ∧ Same mem a z

/-- A nonempty singleton of profile classes; literal representatives may vary. -/
def Singleton (mem : V → V → Prop) (s a : V) : Prop :=
  ∀ z, ClassMember mem z s ↔ Same mem z a

def Pair (mem : V → V → Prop) (p a b : V) : Prop :=
  ∀ z, ClassMember mem z p ↔ Same mem z a ∨ Same mem z b

def OrderedPair (mem : V → V → Prop) (a b c : V) : Prop :=
  ∃ s p, Singleton mem s a ∧ Pair mem p a b ∧ Pair mem c s p

theorem classMember_right_congr (mem : V → V → Prop) {a b : V}
    (h : Same mem a b) (z : V) :
    ClassMember mem z a ↔ ClassMember mem z b := by
  constructor
  · rintro ⟨t, ht, hzt⟩
    exact ⟨t, (h t).mp ht, hzt⟩
  · rintro ⟨t, ht, hzt⟩
    exact ⟨t, (h t).mpr ht, hzt⟩

theorem classMember_left_congr (mem : V → V → Prop) {a b : V}
    (h : Same mem a b) (c : V) :
    ClassMember mem a c ↔ ClassMember mem b c := by
  constructor
  · rintro ⟨t, ht, hat⟩
    exact ⟨t, ht, same_trans mem (same_symm mem h) hat⟩
  · rintro ⟨t, ht, hbt⟩
    exact ⟨t, ht, same_trans mem h hbt⟩

/-- Every inner member class of a Kuratowski code contains its first endpoint. -/
theorem orderedPair_first (mem : V → V → Prop) {a b c : V}
    (h : OrderedPair mem a b c) (z : V) (hz : ClassMember mem z c) :
    ClassMember mem a z := by
  obtain ⟨s, p, hs, hp, hc⟩ := h
  rcases (hc z).mp hz with hzs | hzp
  · exact (classMember_right_congr mem hzs a).mpr
      ((hs a).mpr (same_refl mem a))
  · exact (classMember_right_congr mem hzp a).mpr
      ((hp a).mpr (Or.inl (same_refl mem a)))

/-- The union of the inner member classes is exactly the two endpoint classes. -/
theorem orderedPair_union (mem : V → V → Prop) {a b c : V}
    (h : OrderedPair mem a b c) (z : V) :
    (∃ t, ClassMember mem t c ∧ ClassMember mem z t) ↔
      Same mem z a ∨ Same mem z b := by
  obtain ⟨s, p, hs, hp, hc⟩ := h
  constructor
  · rintro ⟨t, ht, hzt⟩
    rcases (hc t).mp ht with hts | htp
    · exact Or.inl ((hs z).mp ((classMember_right_congr mem hts z).mp hzt))
    · exact (hp z).mp ((classMember_right_congr mem htp z).mp hzt)
  · intro hz
    exact ⟨p, (hc p).mpr (Or.inr (same_refl mem p)), (hp z).mpr hz⟩

/-- Endpoint uniqueness requires only raw profiles, without profile congruence. -/
theorem orderedPair_injective (mem : V → V → Prop) {a b a' b' c : V}
    (h : OrderedPair mem a b c) (h' : OrderedPair mem a' b' c) :
    Same mem a a' ∧ Same mem b b' := by
  obtain ⟨s', p', hs', hp', hc'⟩ := h'
  have hFirst : Same mem a a' := by
    apply (hs' a).mp
    exact orderedPair_first mem h s' ((hc' s').mpr (Or.inl (same_refl mem s')))
  have hAgain : OrderedPair mem a' b' c := ⟨s', p', hs', hp', hc'⟩
  have hUnion (z : V) :
      (Same mem z a ∨ Same mem z b) ↔ (Same mem z a' ∨ Same mem z b') :=
    (orderedPair_union mem h z).symm.trans (orderedPair_union mem hAgain z)
  refine ⟨hFirst, ?_⟩
  classical
  by_cases hba : Same mem b a
  · have hb' : Same mem b' a ∨ Same mem b' b :=
      (hUnion b').mpr (Or.inr (same_refl mem b'))
    rcases hb' with hb'a | hb'b
    · exact same_trans mem hba (same_symm mem hb'a)
    · exact same_symm mem hb'b
  · rcases (hUnion b).mp (Or.inr (same_refl mem b)) with hba' | hbb'
    · exact False.elim (hba (same_trans mem hba' (same_symm mem hFirst)))
    · exact hbb'

theorem singleton_object_congr (mem : V → V → Prop) {s t a : V}
    (hst : Same mem s t) (hs : Singleton mem s a) : Singleton mem t a := by
  intro z
  exact (classMember_right_congr mem hst z).symm.trans (hs z)

theorem pair_object_congr (mem : V → V → Prop) {p q a b : V}
    (hpq : Same mem p q) (hp : Pair mem p a b) : Pair mem q a b := by
  intro z
  exact (classMember_right_congr mem hpq z).symm.trans (hp z)

theorem orderedPair_code_congr (mem : V → V → Prop) {a b c d : V}
    (hcd : Same mem c d) (h : OrderedPair mem a b c) : OrderedPair mem a b d := by
  obtain ⟨s, p, hs, hp, hc⟩ := h
  exact ⟨s, p, hs, hp, pair_object_congr mem hcd hc⟩

/-- Codes are stable under changing either endpoint within its raw profile. -/
theorem orderedPair_endpoint_congr (mem : V → V → Prop) {a b a' b' c : V}
    (ha : Same mem a a') (hb : Same mem b b') (h : OrderedPair mem a b c) :
    OrderedPair mem a' b' c := by
  obtain ⟨s, p, hs, hp, hc⟩ := h
  refine ⟨s, p, ?_, ?_, hc⟩
  · intro z
    exact (hs z).trans ⟨fun hz => same_trans mem hz ha,
      fun hz => same_trans mem hz (same_symm mem ha)⟩
  · intro z
    apply (hp z).trans
    exact or_congr
      ⟨fun hz => same_trans mem hz ha, fun hz => same_trans mem hz (same_symm mem ha)⟩
      ⟨fun hz => same_trans mem hz hb, fun hz => same_trans mem hz (same_symm mem hb)⟩

#print axioms orderedPair_injective
#print axioms orderedPair_endpoint_congr

end SetTheory.BusyBeaver.ZFC.ProfilePairs
