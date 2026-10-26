import DiophantineConsistency.QuadraticNatPairing

namespace CanonicalPairing

abbrev Certificate := DiophantineConsistency.QuadraticNatPairing.Certificate

theorem certificate_zero_iff (z a b s m : Nat) :
    Certificate z a b 0 s m ↔ m = b ∧ b = a+s+1 ∧ z = b*b+a := by
  simp only [Certificate, DiophantineConsistency.QuadraticNatPairing.Certificate, Nat.cast_zero, zero_mul, sub_zero, one_mul,
    add_zero, true_and]
  constructor
  · rintro ⟨hm, hs, hz⟩
    have hmb : m = b := by omega
    subst m
    rw [← Int.natCast_mul] at hz
    exact ⟨rfl, by omega, by omega⟩
  · rintro ⟨rfl, hs, rfl⟩
    simp only [Nat.cast_add, Nat.cast_mul, sub_self]
    exact ⟨trivial, by omega, by omega⟩

theorem certificate_one_iff (z a b s m : Nat) :
    Certificate z a b 1 s m ↔ m = a ∧ a = b+s ∧ z = a*a+a+b := by
  simp only [Certificate, DiophantineConsistency.QuadraticNatPairing.Certificate, Nat.cast_one, sub_self, mul_zero, zero_mul, zero_add,
    one_mul, sub_zero, true_and]
  constructor
  · rintro ⟨hm, hs, hz⟩
    have hma : m = a := by omega
    subst m
    rw [← Int.natCast_mul] at hz
    exact ⟨rfl, by omega, by omega⟩
  · rintro ⟨rfl, hs, rfl⟩
    simp only [Nat.cast_add, Nat.cast_mul, sub_self]
    exact ⟨trivial, by omega, by omega⟩


def selector (a b : Nat) : Nat := if a < b then 0 else 1
def slack (a b : Nat) : Nat := if a < b then b-a-1 else a-b

theorem certificate_normal_form (z a b t s m : Nat) :
    Certificate z a b t s m ↔
      z = Nat.pair a b ∧ t = selector a b ∧ s = slack a b ∧ m = max a b := by
  constructor
  · intro h
    have ht : t = 0 ∨ t = 1 := by
      rcases mul_eq_zero.mp h.1 with hz | ho
      · exact Or.inl (Int.natCast_eq_zero.mp hz)
      · right; omega
    rcases ht with rfl | rfl
    · obtain ⟨hm,hs,hz⟩ := (certificate_zero_iff _ _ _ _ _).mp h
      have hab : a < b := by omega
      simp only [selector, slack, Nat.pair, if_pos hab, max_eq_right (Nat.le_of_lt hab)]
      exact ⟨hz, trivial, by omega, hm⟩
    · obtain ⟨hm,hs,hz⟩ := (certificate_one_iff _ _ _ _ _).mp h
      have hab : ¬a < b := by omega
      simp only [selector, slack, Nat.pair, if_neg hab, max_eq_left (Nat.le_of_not_gt hab)]
      exact ⟨hz, trivial, by omega, hm⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    by_cases hab : a < b
    · simp only [selector, slack, if_pos hab, max_eq_right (Nat.le_of_lt hab)]
      apply (certificate_zero_iff _ _ _ _ _).mpr
      exact ⟨rfl, by omega, by simp only [Nat.pair, if_pos hab]⟩
    · simp only [selector, slack, if_neg hab, max_eq_left (Nat.le_of_not_gt hab)]
      apply (certificate_one_iff _ _ _ _ _).mpr
      exact ⟨rfl, by omega, by simp only [Nat.pair, if_neg hab]⟩

theorem certificate_sound {z a b t s m : Nat} (h : Certificate z a b t s m) :
    z = Nat.pair a b := ((certificate_normal_form _ _ _ _ _ _).mp h).1

theorem certificate_complete {z a b : Nat} (h : z = Nat.pair a b) :
    ∃ t s m, Certificate z a b t s m :=
  ⟨selector a b, slack a b, max a b, (certificate_normal_form _ _ _ _ _ _).mpr ⟨h,rfl,rfl,rfl⟩⟩

/-- A new interface for inverse-graph clients: every certificate witness is
    forced, including the branch bit and slack at a=b. -/
theorem certificate_unique {z a b t s m t' s' m' : Nat}
    (h : Certificate z a b t s m) (h' : Certificate z a b t' s' m') :
    t=t' ∧ s=s' ∧ m=m' := by
  obtain ⟨_, ht, hs, hm⟩ := (certificate_normal_form _ _ _ _ _ _).mp h
  obtain ⟨_, ht', hs', hm'⟩ := (certificate_normal_form _ _ _ _ _ _).mp h'
  exact ⟨ht.trans ht'.symm, hs.trans hs'.symm, hm.trans hm'.symm⟩

#print axioms certificate_normal_form
#print axioms certificate_sound
#print axioms certificate_complete
#print axioms certificate_unique
end CanonicalPairing
