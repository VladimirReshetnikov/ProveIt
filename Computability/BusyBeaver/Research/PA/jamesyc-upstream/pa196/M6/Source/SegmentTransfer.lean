module
public import M6.Source.Determinism
@[expose] public section

namespace M6.Source

/-- Transport a source invocation through a local state embedding, stopping at
its first normal exit. The destination need not be absorbing after that exit;
therefore artificial exit stutters are truncated rather than transported. -/
theorem transfer_until_exit
    (embed : Configuration → Configuration) (Inv : Configuration → Prop)
    (preserve : ∀ c, Inv c → Inv (step fromSites c))
    (commute : ∀ c, Inv c → c.control ≠ .exited →
      step toSites (embed c) = embed (step fromSites c))
    (h : Steps fromSites n a b) (ha : Inv a) (hne : a.control ≠ .exited)
    (hb : b.control = .exited) :
    ∃ m, 0 < m ∧ m ≤ n ∧ Steps toSites m (embed a) (embed b) := by
  induction h with
  | refl => exact False.elim (hne hb)
  | @cons n a b h ih =>
    by_cases hx : (step fromSites a).control = .exited
    · have hs : step fromSites (step fromSites a) = step fromSites a := by
        rcases he : step fromSites a with ⟨q,r⟩
        rw [he] at hx
        simp only at hx
        subst q
        rfl
      have heq : step fromSites a = b := (run_stable hs n).symm.trans h.eq_run
      refine ⟨1, by omega, by omega, ?_⟩
      apply Steps.cons
      rw [commute a ha hne, heq]
      exact Steps.refl _
    · rcases ih (preserve a ha) hx hb with ⟨m,hm,hmn,hmstep⟩
      refine ⟨m+1, by omega, by omega, ?_⟩
      apply Steps.cons
      rw [commute a ha hne]
      exact hmstep

#print axioms transfer_until_exit
end M6.Source

