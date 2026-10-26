import Init

namespace ProofSimplification20261026

/-- The same nondependent overwrite operation as Function.update. -/
def overwrite {ι α : Type} [DecidableEq ι]
    (f : ι → α) (i : ι) (a : α) (j : ι) : α :=
  if j = i then a else f j

theorem overwrite_preserves {ι α : Type} [DecidableEq ι]
    (P : ι → α → Prop) (f : ι → α) (i : ι) (a : α)
    (hf : ∀ j, P j (f j)) (ha : P i a) :
    ∀ j, P j (overwrite f i a j) := by
  intro j
  by_cases h : j = i
  · subst j
    simpa [overwrite] using ha
  · simpa only [overwrite, if_neg h] using hf j

/-- Numeric controls may be completely arbitrary for support preservation. -/
def controlled (f : Nat → Nat) (dummy marker : Nat) : Nat → Nat :=
  overwrite (overwrite f 1004 marker) 977 dummy

theorem controlled_eq (f : Nat → Nat) (dummy marker e : Nat) :
    controlled f dummy marker e =
      if e = 977 then dummy else if e = 1004 then marker else f e := rfl

theorem controlled_support (S : Nat → Prop) (f : Nat → Nat)
    (hd : S 977) (hm : S 1004) (hf : ∀ e, ¬ S e → f e = 0)
    (dummy marker : Nat) :
    ∀ e, ¬ S e → controlled f dummy marker e = 0 := by
  apply overwrite_preserves (fun e x => ¬ S e → x = 0)
  · apply overwrite_preserves (fun e x => ¬ S e → x = 0)
    · exact hf
    · exact fun h => False.elim (h hm)
  · exact fun h => False.elim (h hd)

theorem controlled_boolean (f : Nat → Nat) (dummy marker : Nat)
    (hf : ∀ e, f e ≤ 1) (hd : dummy ≤ 1) (hm : marker ≤ 1) :
    ∀ e, controlled f dummy marker e ≤ 1 := by
  apply overwrite_preserves (fun _ x => x ≤ 1)
  · exact overwrite_preserves (fun _ x => x ≤ 1) f 1004 marker hf hm
  · exact hd

/-- A capacity predicate can replace the Boolean/support pair if every
client wants the combined bound. No global ring or cyclic modulus is used. -/
theorem controlled_capacity (capacity : Nat → Nat) (f : Nat → Nat)
    (dummy marker : Nat) (hf : ∀ e, f e < capacity e)
    (hd : dummy < capacity 977) (hm : marker < capacity 1004) :
    ∀ e, controlled f dummy marker e < capacity e := by
  apply overwrite_preserves (fun e x => x < capacity e)
  · exact overwrite_preserves (fun e x => x < capacity e) f 1004 marker hf hm
  · exact hd

/-- Repeated positions obey last-write priority; distinctness is not required
by the invariant theorem. This prevents an accidental hidden assumption. -/
example (f : Nat → Nat) : overwrite (overwrite f 977 3) 977 5 977 = 5 := by
  simp [overwrite]

example (f : Nat → Nat) : controlled f 5 7 977 = 5 := by
  simp [controlled, overwrite]

example (f : Nat → Nat) : controlled f 5 7 1004 = 7 := by
  simp [controlled, overwrite]

example (f : Nat → Nat) : controlled f 5 7 0 = f 0 := by
  simp [controlled, overwrite]

#print axioms overwrite_preserves
#print axioms controlled_support
#print axioms controlled_boolean
#print axioms controlled_capacity

end ProofSimplification20261026
