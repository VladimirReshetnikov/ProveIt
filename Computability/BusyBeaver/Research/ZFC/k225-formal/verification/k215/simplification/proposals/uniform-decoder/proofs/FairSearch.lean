import Init

/-!
A generic finite-progress interface for proof enumerators. `Reach` is intended
to be finite execution, `Ready` means between candidates, and `next` is the
next candidate counter. A complete instantiation must prove `advance` from
the concrete fetch/drain lemmas; this file does not assume arbitrary infinite
fairness and does not establish an endpoint for any particular machine.
-/

namespace ProofSimplification.FairSearch

universe u

section

variable {S : Type u}
  (Reach : S → S → Prop) (Halts Ready : S → Prop) (next : S → Nat)
  (refl : ∀ s, Reach s s)
  (trans : ∀ {a b c}, Reach a b → Reach b c → Reach a c)
  (halts_before : ∀ {a b}, Reach a b → Halts b → Halts a)
  (advance : ∀ s, Ready s →
    (∃ t, Reach s t ∧ Ready t ∧ next t = next s + 1) ∨ Halts s)

include refl trans halts_before advance

/-- Each specified later candidate is finitely reached, or halting has already
    occurred. This proof is independent of command encodings and formula codes. -/
theorem visit_or_halt (s : S) (hs : Ready s) : ∀ k : Nat,
    (∃ t, Reach s t ∧ Ready t ∧ next t = next s + k) ∨ Halts s := by
  intro k
  induction k with
  | zero => exact Or.inl ⟨s, refl s, hs, rfl⟩
  | succ k ih =>
    cases ih with
    | inr h => exact Or.inr h
    | inl h =>
      obtain ⟨t, hst, ht, hn⟩ := h
      cases advance t ht with
      | inr h => exact Or.inr (halts_before hst h)
      | inl h =>
        obtain ⟨v, htv, hv, hn'⟩ := h
        apply Or.inl
        refine ⟨v, trans hst htv, hv, ?_⟩
        calc
          next v = next t + 1 := hn'
          _ = (next s + k) + 1 := congrArg (fun n => n + 1) hn
          _ = next s + (k + 1) := Nat.add_assoc (next s) k 1

/-- A reset-and-refute command list with a sufficiently late code suffices.
    Soundness is separate: use the invariant to obtain the other implication. -/
theorem complete (s : S) (hs : Ready s)
    (killer : ∃ k, ∀ t, Ready t → next t = next s + k → Halts t) : Halts s := by
  obtain ⟨k, hk⟩ := killer
  cases visit_or_halt Reach Halts Ready next refl trans halts_before advance s hs k with
  | inr h => exact h
  | inl h =>
    obtain ⟨t, hst, ht, hn⟩ := h
    exact halts_before hst (hk t ht hn)

end

#print axioms visit_or_halt
#print axioms complete

end ProofSimplification.FairSearch
