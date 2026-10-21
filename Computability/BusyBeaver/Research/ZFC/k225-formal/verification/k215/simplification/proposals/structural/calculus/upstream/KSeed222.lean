import BusyBeaver.ZFC.KCode222

/-!
Semantics of the decoded seed bundle of the 222/221 calculus.

`SeedProp mem Q A` is Elliot Glazer's seed form of K for a binary relation `Q` (input, output)
and an input `A`: there is a container `C` that

* answers the seed request: if `A` has a `Q`-output, some output of `A` lies in `C`;
* consists of outputs (each member of `C` is an output of some input), each of whose subsets
  has its request answered in `C`.

`bundle_of_seed`: in an irreflexive structure, if `SeedProp` holds for the relation that the
decoded matrix `dec c` defines at roles `a` (input) and `b` (output), then the decoded bundle
`dec (bundle222 a b c)` holds. Both the ordinary roles (`a ≠ b`) and the degenerate ones are
covered; the label `c` is never free in its own decoded matrix (`sat_dec_agree`).
-/

namespace SetTheory.BusyBeaver.ZFC.KSeed222

open SetTheory.BusyBeaver.ZFC.Tarski
open SetTheory.BusyBeaver.ZFC.Code254
open SetTheory.BusyBeaver.ZFC.KCode222
open NF

universe u
variable {V : Type u}

/-! ## The label is not free in its own decoded matrix -/

theorem decF_occurs : ∀ (f n i : Nat), Occurs i (decF f n) → i = 0 ∨ i < n
  | 0, _, i, h => by
      simp only [decF, T0, Occurs] at h; omega
  | _ + 1, 0, i, h => by
      simp only [decF, T0, Occurs] at h; omega
  | f + 1, n + 1, i, h => by
      have hz := ofNat_le ((n + 1) / 4)
      have hd : (n + 1) / 4 < n + 1 := Nat.div_lt_self (by omega) (by omega)
      simp only [decF] at h
      split at h
      · simp only [Occurs] at h
        rcases h with h | h
        · rcases decF_occurs f _ i h with h | h <;> omega
        · rcases decF_occurs f _ i h with h | h <;> omega
      · simp only [Occurs] at h; omega
      · simp only [Occurs] at h
        rcases h with h | h
        · omega
        · rcases decF_occurs f _ i h with h | h <;> omega
      · simp only [Occurs] at h; omega

/-- Truth of `dec c` does not depend on the value of the name `c`. -/
theorem sat_dec_agree (mem : V → V → Prop) (c : Nat) (e1 e2 : Nat → V)
    (h : ∀ n, n ≠ c → e1 n = e2 n) :
    Tarski.Sat mem e1 (dec c) ↔ Tarski.Sat mem e2 (dec c) := by
  by_cases hc : c = 0
  · subst hc
    rw [dec_zero]; simp only [T0, Tarski.Sat]
    exact ⟨fun _ h => h, fun _ h => h⟩
  · apply sat_ext
    intro n hn
    apply h
    intro hnc
    subst hnc
    rcases decF_occurs (n + 1) n n (Free.occurs hn) with h0 | h0 <;> omega

/-! ## The seed property -/

/-- Glazer's seed form of K for the relation `Q` (input, output) at input `A`. -/
def SeedProp (mem : V → V → Prop) (Q : V → V → Prop) (A : V) : Prop :=
  ∃ C, (∀ y, Q A y → ∃ z, Q A z ∧ mem z C) ∧
    ∀ y, mem y C → ∃ x, Q x y ∧
      ∀ x', (∀ w, mem w x' → mem w y) → ∀ y', Q x' y' → ∃ z, Q x' z ∧ mem z C

/-- The relation that the decoded matrix `dec c` defines at input `a` and output `b`. -/
def matrixRel (mem : V → V → Prop) (e : Nat → V) (a b c : Nat) (x y : V) : Prop :=
  Tarski.Sat mem (update (update e a x) b y) (dec c)

/-! ## The decoded bundle from the seed property -/

section Bundle

variable (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
include hirr

theorem bundle_of_seed (e : Nat → V) (a b c : Nat) (hca : c ≠ a) (hcb : c ≠ b)
    (h : SeedProp mem (matrixRel mem e a b c) (e a)) :
    Tarski.Sat mem e (dec (bundle222 a b c)) := by
  obtain ⟨C, hroot, hcl⟩ := h
  simp only [bundle222]
  rw [sat_wn mem hirr, sat_wim]
  intro hall
  -- membership vacuity holds outright
  have hRV : Tarski.Sat mem e (dec (vrel a b c)) := by
    simp only [vrel]
    rw [sat_wim, sat_wel, sat_wal]
    intro hm d
    rw [sat_wel, update_other _ _ (Ne.symm hca), update_other _ _ (Ne.symm hcb)]
    exact hm
  have hN := hall hRV
  simp only [nks] at hN
  rw [sat_wal] at hN
  have hC := hN C
  rw [sat_wim, sat_wn mem hirr] at hC
  -- the request at a given input, read through the matrix relation
  have hreq : ∀ (E' : Nat → V) (x : V), (∀ n, n ≠ c → n ≠ b →
        E' n = update e a x n) → E' c = C →
      (∀ y', matrixRel mem e a b c x y' → ∃ z, matrixRel mem e a b c x z ∧ mem z C) →
      Tarski.Sat mem E' (dec (req b c c)) := by
    intro E' x hE' hEc hQ
    simp only [req]
    rw [sat_wal]
    intro y
    rw [sat_wim, sat_wn mem hirr, sat_wal]
    intro hy hnone
    have hy' : matrixRel mem e a b c x y := by
      unfold matrixRel
      refine (sat_dec_agree mem c _ _ ?_).mp hy
      intro n hn
      by_cases hnb : n = b
      · subst hnb; simp [update]
      · rw [update_other _ _ hnb, update_other _ _ hnb, hE' n hn hnb]
    obtain ⟨z, hz, hzC⟩ := hQ y hy'
    have hz' := hnone z
    rw [sat_wim, sat_wn mem hirr, sat_wel] at hz'
    apply hz'
    · refine (sat_dec_agree mem c _ _ ?_).mpr hz
      intro n hn
      by_cases hnb : n = b
      · subst hnb; simp [update]
      · rw [update_other _ _ hnb, update_other _ _ hnb, update_other _ _ hnb, hE' n hn hnb]
    · rw [update_same, update_other _ _ hcb, update_other _ _ hcb, hEc]
      exact hzC
  apply hC
  · -- the closure
    simp only [clos]
    rw [sat_wal]
    intro y
    rw [sat_wim, sat_wel, update_same, update_other _ _ hcb, update_same, sat_wn mem hirr,
      sat_wal]
    intro hyC hnone
    obtain ⟨x, hxy, hsub⟩ := hcl y hyC
    by_cases hab : a = b
    · -- degenerate roles: the matrix sees only the output
      subst hab
      apply (sat_wim mem _ _ _).mp (hnone y) ?_ |> (sat_wn mem hirr _ _).mp
      · rw [sat_wal]
        intro x'
        rw [sat_wim]
        intro _
        refine hreq _ y ?_ ?_ ?_
        · intro n hn hnb
          simp only [update, hnb, hn, if_false]
        · simp [update, hca]
        · intro y' hy'
          have hy'' : matrixRel mem e a a c y y' := by
            unfold matrixRel at hy' ⊢
            refine (sat_ext mem _ _ _ ?_).mp hy'
            intro n _; by_cases hn : n = a <;> simp [update, hn]
          obtain ⟨z, hz, hzC⟩ := hsub y (fun w hw => hw) y' hy''
          refine ⟨z, ?_, hzC⟩
          unfold matrixRel at hz ⊢
          refine (sat_ext mem _ _ _ ?_).mp hz
          intro n _; by_cases hn : n = a <;> simp [update, hn]
      · unfold matrixRel at hxy
        refine (sat_dec_agree mem c _ _ ?_).mpr hxy
        intro n hn
        by_cases hna : n = a
        · subst hna; simp [update]
        · simp [update, hna, hn]
    · -- ordinary roles
      apply (sat_wim mem _ _ _).mp (hnone x) ?_ |> (sat_wn mem hirr _ _).mp
      · rw [sat_wal]
        intro x'
        rw [sat_wim]
        intro hsubx
        have hsub' : ∀ w, mem w x' → mem w y := by
          intro w hw
          rw [sat_wal] at hsubx
          have := hsubx w
          rw [sat_wim, sat_wel, sat_wel, update_same, update_other _ _ (Ne.symm hca),
            update_other _ _ (Ne.symm hcb)] at this
          rw [update_same] at this
          rw [update_other _ _ (Ne.symm hab), update_other _ _ (Ne.symm hab), update_same] at this
          exact this hw
        refine hreq _ x' ?_ ?_ (hsub x' hsub')
        · intro n hn hnb
          by_cases hna : n = a
          · subst hna; simp [update]
          · simp [update, hna, hnb, hn]
        · simp [update, hca, hcb]
      · unfold matrixRel at hxy
        refine (sat_dec_agree mem c _ _ ?_).mpr hxy
        intro n hn
        by_cases hna : n = a
        · subst hna; simp [update, hab]
        · by_cases hnb : n = b
          · subst hnb; simp [update, hna]
          · simp [update, hna, hnb, hn]
  · -- the seed request at the input `e a`
    refine hreq (update e c C) (e a) ?_ ?_ ?_
    · intro n hn _
      rw [update_other _ _ hn]
      by_cases hna : n = a
      · subst hna; simp [update]
      · simp [update, hna]
    · rw [update_same]
    · exact hroot

end Bundle

#print axioms bundle_of_seed

end SetTheory.BusyBeaver.ZFC.KSeed222

