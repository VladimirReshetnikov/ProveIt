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
    ClassMember mem z a ↔ ClassMember mem z b :=
  ⟨fun ⟨t, ht, hzt⟩ => ⟨t, (h t).mp ht, hzt⟩, fun ⟨t, ht, hzt⟩ => ⟨t, (h t).mpr ht, hzt⟩⟩

/-- Every inner member class of a Kuratowski code contains its first endpoint. -/
theorem orderedPair_first (mem : V → V → Prop) {a b c : V}
    (h : OrderedPair mem a b c) (z : V) (hz : ClassMember mem z c) :
    ClassMember mem a z := by
  obtain ⟨s, p, hs, hp, hc⟩ := h
  exact ((hc z).mp hz).elim
    (fun hzs => (classMember_right_congr mem hzs a).mpr ((hs a).mpr (same_refl mem a)))
    (fun hzp => (classMember_right_congr mem hzp a).mpr ((hp a).mpr (Or.inl (same_refl mem a))))

/-- The union of the inner member classes is exactly the two endpoint classes. -/
theorem orderedPair_union (mem : V → V → Prop) {a b c : V}
    (h : OrderedPair mem a b c) (z : V) :
    (∃ t, ClassMember mem t c ∧ ClassMember mem z t) ↔
      Same mem z a ∨ Same mem z b := by
  obtain ⟨s, p, hs, hp, hc⟩ := h
  exact ⟨fun ⟨t, ht, hzt⟩ => ((hc t).mp ht).elim
      (fun hts => Or.inl ((hs z).mp ((classMember_right_congr mem hts z).mp hzt)))
      (fun htp => (hp z).mp ((classMember_right_congr mem htp z).mp hzt)),
    fun hz => ⟨p, (hc p).mpr (Or.inr (same_refl mem p)), (hp z).mpr hz⟩⟩

/-- Endpoint uniqueness requires only raw profiles, without profile congruence. -/
theorem orderedPair_injective (mem : V → V → Prop) {a b a' b' c : V}
    (h : OrderedPair mem a b c) (h' : OrderedPair mem a' b' c) :
    Same mem a a' ∧ Same mem b b' := by
  have hUnion (z : V) :
      (Same mem z a ∨ Same mem z b) ↔ (Same mem z a' ∨ Same mem z b') :=
    (orderedPair_union mem h z).symm.trans (orderedPair_union mem h' z)
  obtain ⟨s', _, hs', _, hc'⟩ := h'
  have hFirst : Same mem a a' :=
    (hs' a).mp (orderedPair_first mem h s' ((hc' s').mpr (Or.inl (same_refl mem s'))))
  refine ⟨hFirst, ?_⟩
  by_cases hba : Same mem b a
  · exact ((hUnion b').mpr (Or.inr (same_refl mem b'))).elim
      (fun hb'a => same_trans mem hba (same_symm mem hb'a)) (same_symm mem)
  · exact ((hUnion b).mp (Or.inr (same_refl mem b))).elim
      (fun hba' => (hba (same_trans mem hba' (same_symm mem hFirst))).elim) id

theorem pair_object_congr (mem : V → V → Prop) {p q a b : V}
    (hpq : Same mem p q) (hp : Pair mem p a b) : Pair mem q a b :=
  fun z => (classMember_right_congr mem hpq z).symm.trans (hp z)

theorem orderedPair_code_congr (mem : V → V → Prop) {a b c d : V}
    (hcd : Same mem c d) (h : OrderedPair mem a b c) : OrderedPair mem a b d := by
  obtain ⟨s, p, hs, hp, hc⟩ := h
  exact ⟨s, p, hs, hp, pair_object_congr mem hcd hc⟩

/-- Codes are stable under changing either endpoint within its raw profile. -/
theorem orderedPair_endpoint_congr (mem : V → V → Prop) {a b a' b' c : V}
    (ha : Same mem a a') (hb : Same mem b b') (h : OrderedPair mem a b c) :
    OrderedPair mem a' b' c := by
  obtain ⟨s, p, hs, hp, hc⟩ := h
  have hA (z : V) : Same mem z a ↔ Same mem z a' :=
    ⟨fun hz => same_trans mem hz ha, fun hz => same_trans mem hz (same_symm mem ha)⟩
  have hB (z : V) : Same mem z b ↔ Same mem z b' :=
    ⟨fun hz => same_trans mem hz hb, fun hz => same_trans mem hz (same_symm mem hb)⟩
  exact ⟨s, p, fun z => (hs z).trans (hA z), fun z => (hp z).trans (or_congr (hA z) (hB z)), hc⟩

#print axioms orderedPair_injective
#print axioms orderedPair_endpoint_congr

end SetTheory.BusyBeaver.ZFC.ProfilePairs
