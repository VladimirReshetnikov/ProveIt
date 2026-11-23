import Std

/-!
Finite von Neumann ordinals with Ackermann's binary coding of hereditarily
finite sets. The natural order on codes is used for primitive recursion;
`Mem` is set membership, and `Sub` is inclusion.
-/
namespace FiniteOrdinal

def Mem (x a : Nat) : Prop := a.testBit x = true

def Sub (a b : Nat) : Prop := ∀ x, Mem x a → Mem x b

def TransSet (a : Nat) : Prop := ∀ x, Mem x a → Sub x a

def von : Nat → Nat
  | 0 => 0
  | n+1 => von n ||| 2 ^ von n

theorem von_succ_add (n : Nat) : von (n+1) = von n + 2 ^ von n :=
  Nat.or_two_pow_eq_add_of_lt Nat.lt_two_pow_self

theorem von_step (n : Nat) : von n < von (n+1) :=
  Nat.lt_of_lt_of_le Nat.lt_two_pow_self Nat.right_le_or

theorem von_mono {m n : Nat} (h : m ≤ n) : von m ≤ von n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Nat.le_of_lt (von_step _))

theorem von_lt {m n : Nat} (h : m < n) : von m < von n :=
  Nat.lt_of_lt_of_le (von_step m) (von_mono h)

theorem von_inj {m n : Nat} (h : von m = von n) : m = n := by
  rcases Nat.lt_trichotomy m n with hm | he | hn
  · exact False.elim (Nat.ne_of_lt (von_lt hm) h)
  · exact he
  · exact False.elim (Nat.ne_of_lt (von_lt hn) h.symm)

theorem mem_succ {x n : Nat} :
    Mem x (von (n+1)) ↔ Mem x (von n) ∨ x = von n := by
  simp only [Mem, von, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_eq]
  exact or_congr Iff.rfl eq_comm

/-- Every bit, including the bits at non-ordinal positions, is characterized. -/
theorem elements (x n : Nat) :
    Mem x (von n) ↔ ∃ i, i < n ∧ x = von i := by
  induction n with
  | zero => simp [Mem, von, Nat.zero_testBit]
  | succ n ih =>
    rw [mem_succ, ih]
    constructor
    · rintro (⟨i, hi, hx⟩ | hx)
      · exact ⟨i, Nat.lt_succ_of_lt hi, hx⟩
      · exact ⟨n, Nat.lt_succ_self n, hx⟩
    · rintro ⟨i, hi, hx⟩
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with he | hl
      · exact Or.inr (he ▸ hx)
      · exact Or.inl ⟨i, hl, hx⟩

theorem ordinal_mem_iff (m n : Nat) : Mem (von m) (von n) ↔ m < n := by
  rw [elements]
  constructor
  · rintro ⟨i, hi, h⟩
    exact von_inj h ▸ hi
  · intro h
    exact ⟨m, h, rfl⟩

theorem ordinal_sub_iff (m n : Nat) : Sub (von m) (von n) ↔ m ≤ n := by
  constructor
  · intro h
    rcases Nat.le_total m n with hmn | hnm
    · exact hmn
    · rcases Nat.eq_or_lt_of_le hnm with he | hn
      · exact he ▸ Nat.le_refl _
      · have := h (von n) ((ordinal_mem_iff n m).mpr hn)
        exact False.elim (Nat.lt_irrefl n ((ordinal_mem_iff n n).mp this))
  · intro h x hx
    obtain ⟨i, hi, hi'⟩ := (elements _ _).mp hx
    exact (elements _ _).mpr ⟨i, Nat.lt_of_lt_of_le hi h, hi'⟩

theorem ordinal_transitive (n : Nat) : TransSet (von n) := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := (elements _ _).mp hx
  exact (ordinal_sub_iff _ _).mpr (Nat.le_of_lt hi)

theorem index_le_code (n : Nat) : n ≤ von n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (von_step n))

/-- A bounded Boolean search for any property with a numerical witness. -/
def existsBelow (p : Nat → Bool) : Nat → Bool
  | 0 => false
  | n+1 => existsBelow p n || p n

theorem existsBelow_spec (p : Nat → Bool) (b : Nat) :
    existsBelow p b = true ↔ ∃ i, i < b ∧ p i = true := by
  induction b with
  | zero => simp [existsBelow]
  | succ b ih =>
    simp only [existsBelow, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi, hp⟩ | hp)
      · exact ⟨i, Nat.lt_succ_of_lt hi, hp⟩
      · exact ⟨b, Nat.lt_succ_self _, hp⟩
    · rintro ⟨i, hi, hp⟩
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with he | hl
      · exact Or.inr (he ▸ hp)
      · exact Or.inl ⟨i, hl, hp⟩

/-- A direct but intentionally inefficient decision procedure. -/
def isVon (x : Nat) : Bool := existsBelow (fun i => decide (von i = x)) (x+1)

theorem isVon_spec (x : Nat) : isVon x = true ↔ ∃ i, x = von i := by
  rw [isVon, existsBelow_spec]
  constructor
  · rintro ⟨i, _, h⟩
    exact ⟨i, (of_decide_eq_true h).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, Nat.lt_succ_of_le (index_le_code i), by simp⟩

theorem mem_code_lt {y x : Nat} (hy : Mem y x) : y < x := by
  rcases Nat.lt_or_ge y x with h | h
  · exact h
  · have hf := Nat.testBit_lt_two_pow (Nat.lt_of_le_of_lt h Nat.lt_two_pow_self)
    simp [Mem, hf] at hy

theorem hf_ext {a b : Nat} (h : ∀ y, Mem y a ↔ Mem y b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro y
  have hh := h y
  unfold Mem at hh
  simpa using hh

/-- One plus the largest index below b whose ordinal is a member, or zero. -/
def cut (x : Nat) : Nat → Nat
  | 0 => 0
  | b+1 => if (x.testBit (von b)) then b+1 else cut x b

theorem cut_le (x b : Nat) : cut x b ≤ b := by
  induction b with
  | zero => exact Nat.zero_le _
  | succ b ih =>
    simp only [cut]
    split
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le ih

theorem cut_spec (x : Nat) (ht : TransSet x) (b i : Nat) (hi : i < b) :
    Mem (von i) x ↔ i < cut x b := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hb : x.testBit (von b) = true
    · simp only [cut, hb, ↓reduceIte]
      refine ⟨fun _ => hi, fun _ => ?_⟩
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with he | hl
      · exact he ▸ hb
      · exact ht _ hb _ ((ordinal_mem_iff i b).mpr hl)
    · simp only [cut, hb]
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with he | hl
      · subst i
        have hle := cut_le x b
        exact ⟨fun h => False.elim (hb h), fun h => False.elim (Nat.not_lt_of_ge hle h)⟩
      · exact ih hl

theorem transitive_of_ordinals {x : Nat} (ht : TransSet x)
    (hmem : ∀ y, Mem y x → ∃ i, y = von i) : x = von (cut x x) := by
  apply hf_ext
  intro y
  rw [elements]
  constructor
  · intro hy
    obtain ⟨i, rfl⟩ := hmem y hy
    have bound := Nat.lt_of_le_of_lt (index_le_code i) (mem_code_lt hy)
    exact ⟨i, (cut_spec x ht x i bound).mp hy, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    have bound := Nat.lt_of_lt_of_le hi (cut_le x x)
    exact (cut_spec x ht x i bound).mpr hi

/-- In hereditarily finite sets, a transitive set of transitive sets is ordinal. -/
theorem von_iff_two_trans (x : Nat) :
    (∃ i, x = von i) ↔ TransSet x ∧ ∀ y, Mem y x → TransSet y := by
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨ordinal_transitive i, ?_⟩
    intro y hy
    obtain ⟨j, _, rfl⟩ := (elements y i).mp hy
    exact ordinal_transitive j
  · induction x using Nat.strongRecOn with
    | ind x ih =>
      rintro ⟨ht, elt⟩
      refine ⟨cut x x, transitive_of_ordinals ht ?_⟩
      intro y hy
      apply ih y (mem_code_lt hy)
      exact ⟨elt _ hy, fun z hz => elt _ (ht _ hy _ hz)⟩

theorem structural_recognition (x : Nat) :
    isVon x = true ↔ TransSet x ∧ ∀ y, Mem y x → TransSet y :=
  (isVon_spec x).trans (von_iff_two_trans x)

end FiniteOrdinal

namespace FiniteOrdinal

/-- Counting a decidable subset of [0,n). -/
def tally (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => tally p n + if p n then 1 else 0

theorem tally_le_bound (p : Nat → Bool) (n : Nat) : tally p n ≤ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    simp only [tally]
    split <;> omega

theorem tally_mono (p q : Nat → Bool) (n : Nat)
    (hs : ∀ i, i < n → p i = true → q i = true) : tally p n ≤ tally q n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have prev := ih (fun i hi => hs i (Nat.lt_succ_of_lt hi))
    have here := hs n (Nat.lt_succ_self n)
    simp only [tally]
    cases hp : p n <;> cases hq : q n <;> simp_all <;> omega

theorem tally_strict (p q : Nat → Bool) (n : Nat)
    (hs : ∀ i, i < n → p i = true → q i = true)
    (hw : ∃ i, i < n ∧ p i = false ∧ q i = true) : tally p n < tally q n := by
  induction n with
  | zero => obtain ⟨i, hi, _⟩ := hw; omega
  | succ n ih =>
    obtain ⟨i, hi, hp, hq⟩ := hw
    have hs' : ∀ j, j < n → p j = true → q j = true :=
      fun j hj => hs j (Nat.lt_succ_of_lt hj)
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with he | hl
    · subst i
      have prev := tally_mono p q n hs'
      simp [tally, hp, hq]
      omega
    · have prev := ih hs' ⟨i, hl, hp, hq⟩
      have here := hs n (Nat.lt_succ_self n)
      simp only [tally]
      cases pp : p n <;> cases qq : q n <;> simp_all <;> omega

/-- An injection from a finite initial interval into itself is onto.
The proof removes the last input and moves its output into the hole left
by the largest output. -/
theorem interval_surj (n : Nat) (f : Nat → Nat)
    (bounded : ∀ i, i < n → f i < n)
    (inj : ∀ i j, i < n → j < n → f i = f j → i = j)
    (y : Nat) (hy : y < n) : ∃ i, i < n ∧ f i = y := by
  induction n generalizing f y with
  | zero => omega
  | succ n ih =>
    have hlast := bounded n (Nat.lt_succ_self n)
    by_cases same : f n = y
    · exact ⟨n, Nat.lt_succ_self n, same⟩
    let g := fun i => if f i = n then f n else f i
    have away (i : Nat) (hi : i < n) : f i ≠ f n := by
      intro h
      have := inj i n (Nat.lt_succ_of_lt hi) (Nat.lt_succ_self n) h
      omega
    have bg (i : Nat) (hi : i < n) : g i < n := by
      have hb := bounded i (Nat.lt_succ_of_lt hi)
      have hn := away i hi
      simp only [g]
      split <;> omega
    have ig (i j : Nat) (hi : i < n) (hj : j < n) (hh : g i = g j) : i = j := by
      apply inj i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj)
      have h1 := away i hi
      have h2 := away j hj
      by_cases si : f i = n <;> by_cases sj : f j = n <;> simp_all [g]
    by_cases top : y = n
    · subst y
      have sub : f n < n := by omega
      obtain ⟨i, hi, he⟩ := ih g bg ig (f n) sub
      refine ⟨i, Nat.lt_succ_of_lt hi, ?_⟩
      have hn := away i hi
      by_cases h : f i = n
      · exact h
      · exact False.elim (hn (by simpa only [g, if_neg h] using he))
    · have sub : y < n := by omega
      obtain ⟨i, hi, he⟩ := ih g bg ig y sub
      refine ⟨i, Nat.lt_succ_of_lt hi, ?_⟩
      by_cases h : f i = n
      · exact False.elim (same (by simpa only [g, if_pos h] using he))
      · simpa only [g, if_neg h] using he

/-- A strict linear order on the first n naturals, given by a Boolean test. -/
structure OrderOn (n : Nat) (r : Nat → Nat → Bool) : Prop where
  irrefl : ∀ x, x < n → r x x = false
  trans : ∀ x y z, x < n → y < n → z < n →
    r x y = true → r y z = true → r x z = true
  total : ∀ x y, x < n → y < n → x ≠ y → r x y = true ∨ r y x = true

def rank (r : Nat → Nat → Bool) (n x : Nat) : Nat := tally (fun z => r z x) n

theorem rank_strict {n r} (h : OrderOn n r) {x y}
    (hx : x < n) (hy : y < n) (hxy : r x y = true) : rank r n x < rank r n y :=
  tally_strict _ _ _ (fun z hz hzx => h.trans z x y hz hx hy hzx hxy)
    ⟨x, hx, h.irrefl x hx, hxy⟩

theorem rank_bounded {n r} (h : OrderOn n r) {x} (hx : x < n) : rank r n x < n := by
  have small := tally_strict (fun z => r z x) (fun _ => true) n
    (fun _ _ _ => rfl) ⟨x, hx, h.irrefl x hx, rfl⟩
  exact Nat.lt_of_lt_of_le small (tally_le_bound _ _)

theorem rank_inj {n r} (h : OrderOn n r) {x y}
    (hx : x < n) (hy : y < n) (eq : rank r n x = rank r n y) : x = y := by
  by_cases he : x = y
  · exact he
  · rcases h.total x y hx hy he with hxy | hyx
    · exact False.elim (Nat.ne_of_lt (rank_strict h hx hy hxy) eq)
    · exact False.elim (Nat.ne_of_lt (rank_strict h hy hx hyx) eq.symm)

theorem rank_onto {n r} (h : OrderOn n r) {j} (hj : j < n) :
    ∃ x, x < n ∧ rank r n x = j :=
  interval_surj n (rank r n) (fun _ => rank_bounded h)
    (fun _ _ => rank_inj h) j hj

theorem rank_lt_iff {n r} (h : OrderOn n r) {x y} (hx : x < n) (hy : y < n) :
    rank r n x < rank r n y ↔ r x y = true := by
  refine ⟨?_, rank_strict h hx hy⟩
  intro less
  have ne : x ≠ y := by
    intro eq
    subst y
    exact Nat.lt_irrefl _ less
  rcases h.total x y hx hy ne with hxy | hyx
  · exact hxy
  · exact False.elim (Nat.lt_asymm less (rank_strict h hy hx hyx))

/-- The last matching position in a bounded scan, conventionally zero if none. -/
def lastHit (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => if p n then n else lastHit p n

theorem lastHit_spec (p : Nat → Bool) (n : Nat) (hw : ∃ i, i < n ∧ p i = true) :
    lastHit p n < n ∧ p (lastHit p n) = true := by
  induction n with
  | zero => obtain ⟨i, hi, _⟩ := hw; omega
  | succ n ih =>
    by_cases here : p n = true
    · simp only [lastHit, here, ↓reduceIte]
      exact ⟨Nat.lt_succ_self n, True.intro⟩
    · simp only [lastHit, here]
      obtain ⟨i, hi, hp⟩ := hw
      have low : i < n := by
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with he | hl
        · exact False.elim (here (he ▸ hp))
        · exact hl
      obtain ⟨hb, hm⟩ := ih ⟨i, low, hp⟩
      exact ⟨Nat.lt_succ_of_lt hb, hm⟩

def unrank (r : Nat → Nat → Bool) (n j : Nat) :=
  lastHit (fun x => decide (rank r n x = j)) n

theorem rank_unrank {n r} (h : OrderOn n r) {j} (hj : j < n) :
    unrank r n j < n ∧ rank r n (unrank r n j) = j := by
  obtain ⟨i, hi, eq⟩ := rank_onto h hj
  have ⟨bd, val⟩ := lastHit_spec (fun x => decide (rank r n x = j)) n
    ⟨i, hi, by simp [eq]⟩
  exact ⟨bd, of_decide_eq_true val⟩

theorem unrank_rank {n r} (h : OrderOn n r) {x} (hx : x < n) :
    unrank r n (rank r n x) = x := by
  obtain ⟨hu, hr⟩ := rank_unrank h (rank_bounded h hx)
  exact rank_inj h hu hx hr

end FiniteOrdinal
