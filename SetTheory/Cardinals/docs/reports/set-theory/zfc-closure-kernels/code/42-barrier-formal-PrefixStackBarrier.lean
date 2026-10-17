import Std

/-!
An abstract stack barrier for a monotone enumeration of command lists.

The concrete enumerator is not imported here. Its marked-occurrence map must
be shown to supply `back`, `push`, and `injective` below. The conclusions then
exclude every read of an arbitrary initial stack tail. All assumptions are
explicit theorem arguments; no new axioms, admissions, or decision oracles
are introduced.
-/

namespace PrefixStackBarrier

/-! Elementary finite counting, using only Lean's standard library. -/

private theorem injection_length_le (xs ys : List Nat) (f : Nat → Nat)
    (nd : xs.Nodup)
    (into : ∀ x ∈ xs, f x ∈ ys)
    (inj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    have hx : f x ∈ ys := into x (by simp)
    have nds : xs.Nodup := (List.nodup_cons.mp nd).2
    have into' : ∀ a ∈ xs, f a ∈ ys.erase (f x) := by
      intro a ha
      have ne : f a ≠ f x := by
        intro he
        have ax := inj a (by simp [ha]) x (by simp) he
        exact (List.nodup_cons.mp nd).1 (ax ▸ ha)
      exact (List.mem_erase_of_ne ne).mpr (into a (by simp [ha]))
    have inj' : ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b := by
      intro a ha b hb he
      exact inj a (by simp [ha]) b (by simp [hb]) he
    have hi := ih (ys.erase (f x)) nds into' inj'
    have he := List.length_erase_of_mem hx
    simp only [List.length_cons]
    have hp : 0 < ys.length := List.length_pos_iff_exists_mem.mpr ⟨f x, hx⟩
    omega

def events (p : Nat → Bool) (n : Nat) : List Nat :=
  (List.range n).filter p

def count (p : Nat → Bool) (n : Nat) : Nat := (events p n).length

@[simp] theorem mem_events (p : Nat → Bool) (n x : Nat) :
    x ∈ events p n ↔ x < n ∧ p x = true := by
  simp [events]

theorem events_nodup (p : Nat → Bool) (n : Nat) : (events p n).Nodup :=
  (List.filter_sublist).nodup List.nodup_range

@[simp] theorem count_zero (p : Nat → Bool) : count p 0 = 0 := by
  simp [count, events]

theorem count_succ (p : Nat → Bool) (n : Nat) :
    count p (n + 1) = count p n + if p n then 1 else 0 := by
  simp [count, events, List.range_succ, List.filter_append]
  split <;> simp_all

/-- An injection from pop events to strictly earlier distinguished pushes. -/
structure EarlierInjection (isPop isPush : Nat → Bool) where
  mate : Nat → Nat
  back : ∀ n, isPop n = true → mate n < n
  push : ∀ n, isPop n = true → isPush (mate n) = true
  injective : ∀ n m, isPop n = true → isPop m = true → mate n = mate m → n = m

/-- Every completed prefix has at least as many distinguished pushes as pops. -/
theorem prefix_count_le {isPop isPush : Nat → Bool}
    (I : EarlierInjection isPop isPush) (n : Nat) :
    count isPop n ≤ count isPush n := by
  apply injection_length_le (events isPop n) (events isPush n) I.mate
    (events_nodup isPop n)
  · intro x hx
    obtain ⟨hxn, hpop⟩ := (mem_events _ _ _).mp hx
    exact (mem_events _ _ _).mpr ⟨Nat.lt_trans (I.back x hpop) hxn, I.push x hpop⟩
  · intro x hx y hy he
    exact I.injective x y ((mem_events _ _ _).mp hx).2
      ((mem_events _ _ _).mp hy).2 he

/-- Before each pop, at least one distinguished push remains unspent.

The current pop itself is included on the left. This strict version is the
point needed at a pop instruction; mere nonnegative balance at candidate
boundaries would not suffice.
-/
theorem before_pop {isPop isPush : Nat → Bool}
    (I : EarlierInjection isPop isPush) (n : Nat) (hp : isPop n = true) :
    count isPop n + 1 ≤ count isPush n := by
  have hh : count isPop (n + 1) ≤ count isPush n := by
    apply injection_length_le (events isPop (n + 1)) (events isPush n) I.mate
      (events_nodup isPop (n + 1))
    · intro x hx
      obtain ⟨hxn, hpop⟩ := (mem_events _ _ _).mp hx
      exact (mem_events _ _ _).mpr ⟨by have := I.back x hpop; omega, I.push x hpop⟩
    · intro x hx y hy he
      exact I.injective x y ((mem_events _ _ _).mp hx).2
        ((mem_events _ _ _).mp hy).2 he
  rw [count_succ, hp] at hh
  exact hh

theorem pop_has_positive_credit {isPop isPush : Nat → Bool}
    (I : EarlierInjection isPop isPush) (n : Nat) (hp : isPop n = true) :
    0 < count isPush n - count isPop n := by
  have := before_pop I n hp
  omega

/-! Stack representations do not require unique finite-list encodings. -/

universe u v

structure StackOps (A : Type u) (S : Type v) where
  push : A → S → S
  head : S → A
  tail : S → S
  head_push : ∀ a s, head (push a s) = a
  tail_push : ∀ a s, tail (push a s) = s

variable {A : Type u} {S : Type v}

def fold (K : StackOps A S) : List A → S → S
  | [], bottom => bottom
  | a :: xs, bottom => K.push a (fold K xs bottom)

/-- A witnessed nonempty prefix makes the next read independent of `bottom`. -/
theorem protected_pop (K : StackOps A S) (good : A → Prop)
    (xs : List A) (bottom : S) (positive : 0 < xs.length)
    (safe : ∀ x ∈ xs, good x) :
    ∃ x rest, good x ∧ (∀ a ∈ rest, good a) ∧
      K.head (fold K xs bottom) = x ∧
      K.tail (fold K xs bottom) = fold K rest bottom ∧
      rest.length + 1 = xs.length := by
  cases xs with
  | nil => simp at positive
  | cons x rest =>
    refine ⟨x, rest, safe x (by simp), ?_, ?_, ?_, ?_⟩
    · intro a ha; exact safe a (by simp [ha])
    · exact K.head_push x _
    · exact K.tail_push x _
    · simp

/-- Combining the counting theorem with any maintained prefix-length bound
excludes an observation of the arbitrary initial stack tail. Additional
safe pushes (AX and successful MP in the intended application) only improve
the bound and need not be paired with any pop.
-/
theorem bottom_unread {isPop isPush : Nat → Bool}
    (I : EarlierInjection isPop isPush) (n : Nat) (hp : isPop n = true)
    (K : StackOps A S) (good : A → Prop) (xs : List A) (bottom : S)
    (balance : count isPush n ≤ xs.length + count isPop n)
    (safe : ∀ x ∈ xs, good x) :
    ∃ x rest, good x ∧ (∀ a ∈ rest, good a) ∧
      K.head (fold K xs bottom) = x ∧
      K.tail (fold K xs bottom) = fold K rest bottom ∧
      rest.length + 1 = xs.length := by
  apply protected_pop K good xs bottom
  · have := before_pop I n hp; omega
  · exact safe

#print axioms prefix_count_le
#print axioms before_pop
#print axioms pop_has_positive_credit
#print axioms bottom_unread

end PrefixStackBarrier
