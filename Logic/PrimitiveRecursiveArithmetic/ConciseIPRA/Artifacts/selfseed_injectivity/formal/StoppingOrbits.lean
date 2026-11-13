/-
The abstract algebraic core of successor injectivity for the self-seeded
recursor presentation T_F^-.

This file does NOT formalize the syntax or proof system of iPRA. The fields
below are the precise lemmas established in the accompanying written proof.
The only induction hypothesis supplied is for equality of these particular
stopping orbits, not arbitrary predicates or arbitrary functions.

No Mathlib dependency, `sorry`, added axiom, or classical choice is used.
-/

universe u

namespace SelfSeed

structure StoppingOrbits (α : Type u) where
  zero : α
  succ : α → α
  orbit : α → α → α
  update : α → α → α
  succ_ne_zero : ∀ n, succ n ≠ zero
  no_fixed : ∀ n, succ n ≠ n
  no_two_cycle : ∀ n, succ (succ n) ≠ n
  coverage : ∀ n, n = zero ∨ ∃ p, n = succ p
  update_zero : ∀ a, update a zero = zero
  update_self : ∀ a, update a a = a
  update_other : ∀ a v, v ≠ zero → v ≠ a → update a v = succ v
  orbit_zero : ∀ a, orbit a zero = succ zero
  orbit_step : ∀ a n, orbit a (succ n) = update a (orbit a n)
  orbit_range : ∀ a n, orbit a n = succ n ∨ orbit a n = a
  eq_induction : ∀ a b,
    orbit a zero = orbit b zero →
    (∀ n, orbit a n = orbit b n → orbit a (succ n) = orbit b (succ n)) →
    ∀ n, orbit a n = orbit b n

variable {α : Type u}

theorem diagonal (d : StoppingOrbits α) (a : α) (ha : a ≠ d.zero) :
    d.orbit a a = a := by
  rcases d.coverage a with h | ⟨p, hp⟩
  · exact False.elim (ha h)
  · have hv : d.orbit a p = a := by
      rcases d.orbit_range a p with h | h
      · exact h.trans hp.symm
      · exact h
    calc
      d.orbit a a = d.orbit a (d.succ p) := congrArg (d.orbit a) hp
      _ = d.update a (d.orbit a p) := d.orbit_step a p
      _ = d.update a a := congrArg (d.update a) hv
      _ = a := d.update_self a

theorem cross_absorption (d : StoppingOrbits α) (a b : α)
    (ha : a ≠ d.zero) (hs : d.succ a = d.succ b) :
    d.orbit a b = a := by
  rcases d.orbit_range a b with h | h
  · have hc : d.succ b ≠ a := by
      intro e
      exact d.no_fixed a (hs.trans e)
    have hstep : d.orbit a (d.succ b) = d.succ (d.succ b) := by
      calc
        d.orbit a (d.succ b) = d.update a (d.orbit a b) := d.orbit_step a b
        _ = d.update a (d.succ b) := congrArg (d.update a) h
        _ = d.succ (d.succ b) := d.update_other a (d.succ b) (d.succ_ne_zero b) hc
    have hsame : d.orbit a (d.succ b) = a := by
      calc
        d.orbit a (d.succ b) = d.orbit a (d.succ a) := congrArg (d.orbit a) hs.symm
        _ = d.update a (d.orbit a a) := d.orbit_step a a
        _ = d.update a a := congrArg (d.update a) (diagonal d a ha)
        _ = a := d.update_self a
    exact False.elim (d.no_two_cycle a
      ((congrArg d.succ hs).trans (hstep.symm.trans hsame)))
  · exact h

theorem predecessor_one [DecidableEq α] (d : StoppingOrbits α) (b : α)
    (hs : d.succ b = d.succ d.zero) : b = d.zero := by
  by_cases hb : b = d.zero
  · exact hb
  · have hcross := cross_absorption d b d.zero hb hs
    have h1 : d.succ d.zero = b := (d.orbit_zero b).symm.trans hcross
    exact False.elim (d.no_fixed b (hs.trans h1))

theorem excludes_other (d : StoppingOrbits α) (a b : α)
    (ha : a ≠ d.zero) (hb : b ≠ d.zero) (hab : a ≠ b)
    (hs : d.succ a = d.succ b) : ∀ n, d.orbit a n ≠ b := by
  intro n hn
  rcases d.orbit_range a n with hr | hr
  · have hnb : d.succ n = b := hr.symm.trans hn
    have hstep : d.orbit a b = d.succ b := by
      calc
        d.orbit a b = d.orbit a (d.succ n) := congrArg (d.orbit a) hnb.symm
        _ = d.update a (d.orbit a n) := d.orbit_step a n
        _ = d.update a b := congrArg (d.update a) hn
        _ = d.succ b := d.update_other a b hb (Ne.symm hab)
    have hcross := cross_absorption d a b ha hs
    exact d.no_fixed a (hs.trans (hstep.symm.trans hcross))
  · exact hab (hr.symm.trans hn)

theorem successor_injective [DecidableEq α] (d : StoppingOrbits α) :
    ∀ a b, d.succ a = d.succ b → a = b := by
  intro a b hs
  by_cases hab : a = b
  · exact hab
  · have ha : a ≠ d.zero := by
      intro h
      have hb0 : b = d.zero := predecessor_one d b (hs.symm.trans (congrArg d.succ h))
      exact hab (h.trans hb0.symm)
    have hb : b ≠ d.zero := by
      intro h
      have ha0 : a = d.zero := predecessor_one d a (hs.trans (congrArg d.succ h))
      exact hab (ha0.trans h.symm)
    have hnoab := excludes_other d a b ha hb hab hs
    have hnoba := excludes_other d b a hb ha (Ne.symm hab) hs.symm
    have heq : ∀ n, d.orbit a n = d.orbit b n := by
      apply d.eq_induction a b
      · exact (d.orbit_zero a).trans (d.orbit_zero b).symm
      · intro n hn
        have hva : d.orbit b n ≠ a := hnoba n
        have hvb : d.orbit b n ≠ b := by
          intro e
          exact hnoab n (hn.trans e)
        have hu : d.update a (d.orbit b n) = d.update b (d.orbit b n) := by
          by_cases hz : d.orbit b n = d.zero
          · calc
              d.update a (d.orbit b n) = d.update a d.zero := congrArg (d.update a) hz
              _ = d.zero := d.update_zero a
              _ = d.update b d.zero := (d.update_zero b).symm
              _ = d.update b (d.orbit b n) := congrArg (d.update b) hz.symm
          · exact (d.update_other a (d.orbit b n) hz hva).trans
              (d.update_other b (d.orbit b n) hz hvb).symm
        calc
          d.orbit a (d.succ n) = d.update a (d.orbit a n) := d.orbit_step a n
          _ = d.update a (d.orbit b n) := congrArg (d.update a) hn
          _ = d.update b (d.orbit b n) := hu
          _ = d.orbit b (d.succ n) := (d.orbit_step b n).symm
    calc
      a = d.orbit a a := (diagonal d a ha).symm
      _ = d.orbit b a := heq a
      _ = b := cross_absorption d b a hb hs.symm

#print axioms successor_injective

end SelfSeed
