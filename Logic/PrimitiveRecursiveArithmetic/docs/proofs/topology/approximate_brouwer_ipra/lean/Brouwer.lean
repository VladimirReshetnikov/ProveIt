import Std

/-! Finite core of constructive approximate Brouwer, with no dependencies
outside Lean's standard library. All rational inequalities are represented
after clearing one positive common denominator. -/

namespace ApproxBrouwer

/-- Sum the first n signed coordinates. -/
def isum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => isum f n + f n

theorem isum_sub (f g : Nat → Int) (n : Nat) :
    isum (fun i => f i - g i) n = isum f n - isum g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [isum, ih]; omega

theorem isum_le (n : Nat) (f : Nat → Int) (t : Int)
    (h : ∀ i, i < n → f i ≤ t) : isum f n ≤ (n : Int) * t := by
  induction n with
  | zero => simp [isum]
  | succ n ih =>
    have h' := ih (fun i hi => h i (by omega))
    have hlast := h n (by omega)
    simp only [isum, Int.natCast_succ, Int.add_mul, Int.one_mul]
    omega

/-- Bound all terms of the sum except one chosen term. -/
theorem isum_one_free (n : Nat) (f : Nat → Int) (t : Int)
    (h : ∀ j, j < n → f j ≤ t) (i : Nat) (hi : i < n) :
    isum f n ≤ f i + ((n : Int) - 1) * t := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hp : ∀ j, j < n → f j ≤ t := fun j hj => h j (by omega)
    have hm : ((n : Int) - 1) * t = (n : Int) * t - t := by
      rw [Int.sub_mul, Int.one_mul]
    have hs : ((↑(n + 1) : Int) - 1) = (n : Int) := by omega
    rw [hs, isum]
    by_cases hil : i < n
    · have he := ih hp hil
      have ht := h n (by omega)
      omega
    · have he := isum_le n f t hp
      have hei : i = n := by omega
      subst i
      omega

/-- Scan a finite initial segment. A found entry is retained. -/
def first? (p : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | n + 1 => match first? p n with
    | some i => some i
    | none => if p n then some n else none

theorem first?_some {p : Nat → Bool} (n i : Nat)
    (h : first? p n = some i) : i < n ∧ p i = true := by
  induction n with
  | zero => simp [first?] at h
  | succ n ih =>
    cases he : first? p n with
    | some j =>
      simp [first?, he] at h
      subst i
      obtain ⟨hj, hp⟩ := ih he
      exact ⟨by omega, hp⟩
    | none =>
      cases hp : p n <;> simp [first?, he, hp] at h
      subst i
      exact ⟨by omega, hp⟩

theorem first?_none {p : Nat → Bool} (n : Nat)
    (h : first? p n = none) : ∀ i, i < n → p i = false := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases he : first? p n with
    | some j => simp [first?, he] at h
    | none =>
      cases hp : p n with
      | true => simp [first?, he, hp] at h
      | false =>
        intro i hi
        by_cases hil : i < n
        · exact ih he i hil
        · have : i = n := by omega
          simpa [this] using hp

/-- Choose an active barycentric coordinate whose input mass is at least
its image mass. Both input and image use one common scale. -/
def label? (n : Nat) (x y : Nat → Int) : Option Nat :=
  first? (fun i => decide (0 < x i ∧ y i ≤ x i)) n

theorem label_exists (n : Nat) (x y : Nat → Int)
    (hy : ∀ i, i < n → 0 ≤ y i)
    (hmass : 0 < isum x n) (hsum : isum y n = isum x n) :
    ∃ i, label? n x y = some i ∧ i < n ∧ 0 < x i ∧ y i ≤ x i := by
  cases he : label? n x y with
  | some i =>
    obtain ⟨hi, hxy⟩ := first?_some n i he
    exact ⟨i, rfl, hi, of_decide_eq_true hxy⟩
  | none =>
    exfalso
    have hbad (i : Nat) (hi : i < n) : ¬(0 < x i ∧ y i ≤ x i) :=
      of_decide_eq_false (first?_none n he i hi)
    have hle (i : Nat) (hi : i < n) : x i - y i ≤ 0 := by
      by_cases hp : 0 < x i
      · have hn : ¬ y i ≤ x i := fun H => hbad i hi ⟨hp, H⟩
        omega
      · have := hy i hi
        omega
    cases ep : first? (fun i => decide (0 < x i)) n with
    | none =>
      have hz (i : Nat) (hi : i < n) : x i ≤ 0 := by
        have hn : ¬(0 < x i) := of_decide_eq_false (first?_none n ep i hi)
        omega
      have hzero := isum_le n x 0 hz
      simp only [Int.mul_zero] at hzero
      omega
    | some i =>
      obtain ⟨hi, hpos⟩ := first?_some n i ep
      have hpos' : 0 < x i := of_decide_eq_true hpos
      have hstrict : ¬ y i ≤ x i := fun H => hbad i hi ⟨hpos', H⟩
      have hneg := isum_one_free n (fun j => x j - y j) 0 hle i hi
      rw [isum_sub] at hneg
      simp only [Int.mul_zero, Int.add_zero] at hneg
      omega

/-- Retain the first index of greatest score among admissible indices. -/
def best? (ok : Nat → Bool) (score : Nat → Int) : Nat → Option Nat
  | 0 => none
  | n + 1 =>
    let b := best? ok score n
    if ok n then
      match b with
      | none => some n
      | some i => if score i < score n then some n else some i
    else b

def BestSpec (ok : Nat → Bool) (score : Nat → Int) (n : Nat) :
    Option Nat → Prop
  | none => ∀ j, j < n → ok j = false
  | some i => i < n ∧ ok i = true ∧
      ∀ j, j < n → ok j = true → score j ≤ score i

theorem best?_spec (ok : Nat → Bool) (score : Nat → Int) (n : Nat) :
    BestSpec ok score n (best? ok score n) := by
  induction n with
  | zero =>
    change ∀ j, j < 0 → ok j = false
    omega
  | succ n ih =>
    cases hb : best? ok score n with
    | none =>
      rw [hb] at ih
      change ∀ j, j < n → ok j = false at ih
      cases hn : ok n with
      | false =>
        simp only [best?, hb, hn, Bool.false_eq_true, ↓reduceIte, BestSpec]
        intro j hj
        by_cases h : j < n
        · exact ih j h
        · have : j = n := by omega
          simpa [this] using hn
      | true =>
        simp only [best?, hb, hn, ↓reduceIte, BestSpec]
        refine ⟨by omega, True.intro, ?_⟩
        intro j hj hjOk
        by_cases h : j < n
        · rw [ih j h] at hjOk
          contradiction
        · have : j = n := by omega
          simp [this]
    | some i =>
      rw [hb] at ih
      obtain ⟨hi, hiOk, hiMax⟩ := ih
      cases hn : ok n with
      | false =>
        simp only [best?, hb, hn, Bool.false_eq_true, ↓reduceIte, BestSpec]
        refine ⟨by omega, hiOk, ?_⟩
        intro j hj hjOk
        by_cases h : j < n
        · exact hiMax j h hjOk
        · have : j = n := by omega
          rw [this, hn] at hjOk
          contradiction
      | true =>
        by_cases hscore : score i < score n
        · simp only [best?, hb, hn, hscore, ↓reduceIte, BestSpec]
          refine ⟨by omega, True.intro, ?_⟩
          intro j hj hjOk
          by_cases h : j < n
          · exact Int.le_trans (hiMax j h hjOk) (Int.le_of_lt hscore)
          · have : j = n := by omega
            simp [this]
        · simp only [best?, hb, hn, hscore, ↓reduceIte, BestSpec]
          refine ⟨by omega, hiOk, ?_⟩
          intro j hj hjOk
          by_cases h : j < n
          · exact hiMax j h hjOk
          · have : j = n := by omega
            rw [this]
            omega

def maxLabel? (n : Nat) (x y : Nat → Int) : Option Nat :=
  best? (fun i => decide (0 < x i)) (fun i => x i - y i) n

theorem maxLabel_correct (n : Nat) (x y : Nat → Int)
    (hy : ∀ i, i < n → 0 ≤ y i)
    (hmass : 0 < isum x n) (hsum : isum y n = isum x n) :
    ∃ i, maxLabel? n x y = some i ∧ i < n ∧ 0 < x i ∧
      ∀ j, j < n → x j - y j ≤ x i - y i := by
  obtain ⟨w, _, hw, hwPos, hwGood⟩ := label_exists n x y hy hmass hsum
  have hbest := best?_spec (fun i => decide (0 < x i)) (fun i => x i - y i) n
  change BestSpec _ _ n (maxLabel? n x y) at hbest
  cases he : maxLabel? n x y with
  | none =>
    rw [he] at hbest
    have hn : ¬(0 < x w) := of_decide_eq_false (hbest w hw)
    contradiction
  | some i =>
    rw [he] at hbest
    obtain ⟨hi, hip, hmax⟩ := hbest
    refine ⟨i, rfl, hi, of_decide_eq_true hip, ?_⟩
    intro j hj
    by_cases hjp : 0 < x j
    · exact hmax j hj (decide_eq_true hjp)
    · have hw' := hmax w hw (decide_eq_true hwPos)
      have hy' := hy j hj
      dsimp at hw'
      omega

theorem isum_neg (f : Nat → Int) (n : Nat) :
    isum (fun i => -f i) n = -isum f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [isum, ih]; omega

/-- A separate color witness for each i bounds the whole range of the
anchor residual vector. Quantification over w i is finite in the caller. -/
theorem transfer_spread (n : Nat) (r : Nat → Int) (w : Nat → Nat)
    (atW : Nat → Nat → Int) (e : Int)
    (hmax : ∀ i, i < n → ∀ j, j < n → atW (w i) j ≤ atW (w i) i)
    (hclose : ∀ i, i < n → ∀ j, j < n →
      r j ≤ atW (w i) j + e ∧ atW (w i) j ≤ r j + e) :
    ∀ i, i < n → ∀ j, j < n → r j ≤ r i + 2 * e := by
  intro i hi j hj
  have h1 := (hclose i hi j hj).1
  have h2 := hmax i hi j hj
  have h3 := (hclose i hi i hi).2
  omega

/-- If all coordinate differences are at most c and the sum is zero,
every absolute coordinate is at most c. -/
theorem from_spread (n : Nat) (r : Nat → Int) (c : Int)
    (hz : isum r n = 0)
    (h : ∀ i, i < n → ∀ j, j < n → r j ≤ r i + c) :
    ∀ i, i < n → -c ≤ r i ∧ r i ≤ c := by
  intro i hi
  constructor
  · by_cases hc : -c ≤ r i
    · exact hc
    · have hle (j : Nat) (hj : j < n) : r j ≤ 0 := by
        have := h i hi j hj
        omega
      have hh := isum_one_free n r 0 hle i hi
      simp only [hz, Int.mul_zero, Int.add_zero] at hh
      have := h i hi i hi
      omega
  · by_cases hc : r i ≤ c
    · exact hc
    · have hle (j : Nat) (hj : j < n) : -r j ≤ 0 := by
        have := h j hj i hi
        omega
      have hh := isum_one_free n (fun j => -r j) 0 hle i hi
      simp only [isum_neg, hz, Int.neg_zero, Int.mul_zero, Int.add_zero] at hh
      have := h i hi i hi
      omega

/-- Sharp finite-dimensional version, using integer products only. -/
theorem from_spread_sharp (d : Nat) (r : Nat → Int) (c : Int)
    (hz : isum r (d + 1) = 0)
    (h : ∀ i, i < d + 1 → ∀ j, j < d + 1 → r j ≤ r i + c) :
    ∀ i, i < d + 1 →
      -((d : Int) * c) ≤ ((d : Int) + 1) * r i ∧
      ((d : Int) + 1) * r i ≤ (d : Int) * c := by
  intro i hi
  have he : ((↑(d + 1) : Int) - 1) = (d : Int) := by omega
  have lo := isum_one_free (d + 1) r (r i + c) (h i hi) i hi
  have hh (j : Nat) (hj : j < d + 1) : -r j ≤ -r i + c := by
    have := h j hj i hi
    omega
  have up := isum_one_free (d + 1) (fun j => -r j) (-r i + c) hh i hi
  simp only [isum_neg, hz, Int.neg_zero, he, Int.mul_add, Int.mul_neg] at lo up
  simp only [Int.add_mul, Int.one_mul]
  constructor <;> omega

/-- The first true index precedes every other true index in the range. -/
theorem first?_least {p : Nat → Bool} (n i : Nat) (h : first? p n = some i)
    (j : Nat) (hj : j < n) (hp : p j = true) : i ≤ j := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases he : first? p n with
    | some z =>
      simp [first?, he] at h
      subst i
      by_cases hlt : j < n
      · exact ih he hlt
      · have := (first?_some n z he).1
        omega
    | none =>
      cases hl : p n <;> simp [first?, he, hl] at h
      subst i
      by_cases hlt : j < n
      · have := first?_none n he j hlt
        simp_all
      · omega

def cubeTest (x q : Nat → Int) (i : Nat) : Bool :=
  decide (x i = 0 ∨ x i < q i)

def cubeLabel (d : Nat) (x q : Nat → Int) : Nat :=
  (first? (cubeTest x q) d).getD d

/-- Boundary requirements of ProveIt's cubical Sperner theorem, plus the
two residual signs used by the approximate fixed-point extraction. -/
theorem cubeLabel_correct (d : Nat) (x q : Nat → Int) (scale : Int)
    (hp : 0 < scale) (hq : ∀ i, i < d → 0 ≤ q i ∧ q i ≤ scale) :
    cubeLabel d x q ≤ d ∧
    (∀ j, j < d → x j = 0 → cubeLabel d x q ≤ j) ∧
    (∀ j, j < d → x j = scale → cubeLabel d x q ≠ j) ∧
    (∀ j, j < d → cubeLabel d x q = j → x j ≤ q j) ∧
    (cubeLabel d x q = d → ∀ j, j < d → q j ≤ x j) := by
  cases he : first? (cubeTest x q) d with
  | none =>
    have hnone (j : Nat) (hj : j < d) : ¬(x j = 0 ∨ x j < q j) :=
      of_decide_eq_false (first?_none d he j hj)
    simp only [cubeLabel, he, Option.getD_none]
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · intro j hj hx
      exact False.elim (hnone j hj (Or.inl hx))
    · intro j hj _
      omega
    · intro j hj hj'
      omega
    · intro _ j hj
      have := hnone j hj
      omega
  | some k =>
    obtain ⟨hk, htest⟩ := first?_some d k he
    have htk : x k = 0 ∨ x k < q k := of_decide_eq_true htest
    simp only [cubeLabel, he, Option.getD_some]
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · intro j hj hx
      have ht : cubeTest x q j = true := decide_eq_true (Or.inl hx)
      exact first?_least d k he j hj ht
    · intro j hj hx hjk
      subst j
      have := hq k hk
      omega
    · intro j hj hjk
      subst j
      have := hq k hk
      omega
    · intro h
      omega

/-- The d ordinary colors and the special color d give opposite signs
for each cube-coordinate residual. Transport each to the anchor. -/
theorem cube_anchor (d : Nat) (r : Nat → Int) (w : Nat → Nat)
    (atW : Nat → Nat → Int) (e : Int)
    (hord : ∀ i, i < d → atW (w i) i ≤ 0)
    (hspecial : ∀ i, i < d → 0 ≤ atW (w d) i)
    (hclose : ∀ t, t ≤ d → ∀ i, i < d →
      r i ≤ atW (w t) i + e ∧ atW (w t) i ≤ r i + e) :
    ∀ i, i < d → -e ≤ r i ∧ r i ≤ e := by
  intro i hi
  have h1 := hord i hi
  have h2 := hspecial i hi
  have h3 := (hclose i (by omega) i hi).1
  have h4 := (hclose d (by omega) i hi).2
  constructor <;> omega

/-- A color certificate for steps 0,...,n-1 and colors 0,...,n-1. -/
def step? (color : Nat → Option Nat) (n i : Nat) : Option Nat :=
  first? (fun t => decide (color t = some i)) n

def stepOf (color : Nat → Option Nat) (n i : Nat) : Nat :=
  (step? color n i).getD n

def full? (color : Nat → Option Nat) (n : Nat) : Bool :=
  (List.range n).all fun i => (step? color n i).isSome

theorem full?_spec (color : Nat → Option Nat) (n : Nat) (h : full? color n = true)
    (i : Nat) (hi : i < n) : stepOf color n i < n ∧
    color (stepOf color n i) = some i := by
  have hs := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  cases he : step? color n i with
  | none => simp [he] at hs
  | some t =>
    obtain ⟨ht, hc⟩ := first?_some n t he
    simp only [stepOf, he, Option.getD_some]
    exact ⟨ht, of_decide_eq_true hc⟩

/-- At a fully labeled cell, compare each vertex with a possibly
higher-precision sample qA at the anchor x 0. -/
theorem certified_error (d : Nat) (x q : Nat → Nat → Int) (qA : Nat → Int)
    (h u : Int)
    (hq : ∀ t, t ≤ d → ∀ i, i ≤ d → 0 ≤ q t i)
    (hmass : ∀ t, t ≤ d → 0 < isum (x t) (d + 1))
    (hsum : ∀ t, t ≤ d → isum (q t) (d + 1) = isum (x t) (d + 1))
    (ha : isum qA (d + 1) = isum (x 0) (d + 1))
    (hfull : full? (fun t => maxLabel? (d + 1) (x t) (q t)) (d + 1) = true)
    (hm : ∀ t, t ≤ d → ∀ i, i ≤ d → x 0 i ≤ x t i + h ∧ x t i ≤ x 0 i + h)
    (hu : ∀ t, t ≤ d → ∀ i, i ≤ d → qA i ≤ q t i + u ∧ q t i ≤ qA i + u) :
    ∀ i, i ≤ d →
      let r := x 0 i - qA i
      (-(2 * (h + u)) ≤ r ∧ r ≤ 2 * (h + u)) ∧
      (-((d : Int) * (2 * (h + u))) ≤ ((d : Int) + 1) * r ∧
        ((d : Int) + 1) * r ≤ (d : Int) * (2 * (h + u))) := by
  let col := fun t => maxLabel? (d + 1) (x t) (q t)
  let w := stepOf col (d + 1)
  let r := fun i => x 0 i - qA i
  let atW := fun t i => x t i - q t i
  have hw (i : Nat) (hi : i < d + 1) : w i < d + 1 ∧ col (w i) = some i :=
    full?_spec col (d + 1) hfull i hi
  have hzero : isum r (d + 1) = 0 := by simp [r, isum_sub, ha]
  have hmax (i : Nat) (hi : i < d + 1) (j : Nat) (hj : j < d + 1) :
      atW (w i) j ≤ atW (w i) i := by
    obtain ⟨ht, hc⟩ := hw i hi
    have ht' : w i ≤ d := by omega
    obtain ⟨a, he, _, _, hbest⟩ := maxLabel_correct (d + 1) (x (w i)) (q (w i))
      (fun a ha' => hq (w i) ht' a (by omega)) (hmass _ ht') (hsum _ ht')
    change col (w i) = some a at he
    rw [hc] at he
    cases he
    exact hbest j hj
  have hclose (i : Nat) (hi : i < d + 1) (j : Nat) (hj : j < d + 1) :
      r j ≤ atW (w i) j + (h + u) ∧ atW (w i) j ≤ r j + (h + u) := by
    have ht := (hw i hi).1
    have := hm (w i) (by omega) j (by omega)
    have := hu (w i) (by omega) j (by omega)
    dsimp [r, atW]
    constructor <;> omega
  have hspread := transfer_spread (d + 1) r w atW (h + u) hmax hclose
  intro i hi
  exact ⟨from_spread (d + 1) r _ hzero hspread i (by omega),
    from_spread_sharp d r _ hzero hspread i (by omega)⟩

/-- Word digits, most significant first. Valid meshes have N positive
and word codes less than N^d. -/
def digit (N d word t : Nat) : Nat :=
  word / N ^ (d - 1 - t) % N

/-- Coordinate order by nondecreasing digit, with decreasing time on
ties. Read the listed times in order to recover the base entries. -/
def timeLE (a : Nat → Nat) (s t : Nat) : Bool :=
  decide (a s < a t ∨ (a s = a t ∧ t ≤ s))

def sortedTimes (d : Nat) (a : Nat → Nat) : List Nat :=
  (List.range d).mergeSort (timeLE a)

theorem sortedTimes_sorted (d : Nat) (a : Nat → Nat) :
    (sortedTimes d a).Pairwise (fun s t => timeLE a s t = true) := by
  apply List.sorted_mergeSort
  · intro i j k h₁ h₂
    simp [timeLE] at h₁ h₂ ⊢
    rcases h₁ with h₁ | ⟨h₁, p₁⟩ <;> rcases h₂ with h₂ | ⟨h₂, p₂⟩
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega⟩
  · intro i j
    simp [timeLE]
    by_cases h₁ : a i < a j
    · exact Or.inl (Or.inl h₁)
    · by_cases h₂ : a j < a i
      · exact Or.inr (Or.inl h₂)
      · by_cases h₃ : j ≤ i
        · exact Or.inl (Or.inr ⟨by omega, h₃⟩)
        · exact Or.inr (Or.inr ⟨by omega, by omega⟩)

/-- Cumulative coordinate i at step k. The two sentinel coordinates
i = 0 and i = d+1 evaluate to 0 and N for a list of length d. -/
def stop (N : Nat) (a : Nat → Nat) (times : List Nat) (k : Nat) : Nat → Int
  | 0 => 0
  | j + 1 =>
    match times[j]? with
    | none => (N : Int)
    | some t => (a t : Int) + (if t < k then 1 else 0)

def gap (N : Nat) (a : Nat → Nat) (times : List Nat) (k i : Nat) : Int :=
  stop N a times k (i + 1) - stop N a times k i

theorem stop_mesh (N : Nat) (a : Nat → Nat) (times : List Nat)
    (k l : Nat) (h : k ≤ l) (i : Nat) :
    stop N a times k i ≤ stop N a times l i ∧
    stop N a times l i ≤ stop N a times k i + 1 := by
  cases i with
  | zero => simp [stop]
  | succ j =>
    cases he : times[j]? with
    | none => simp [stop, he]; omega
    | some t =>
      by_cases hk : t < k <;> by_cases hl : t < l <;>
        simp [stop, he, hk, hl] <;> omega

theorem gap_mesh (N : Nat) (a : Nat → Nat) (times : List Nat) (k l i : Nat) :
    gap N a times k i ≤ gap N a times l i + 1 ∧
    gap N a times l i ≤ gap N a times k i + 1 := by
  simp only [gap]
  by_cases h : k ≤ l
  · have := stop_mesh N a times k l h i
    have := stop_mesh N a times k l h (i + 1)
    constructor <;> omega
  · have := stop_mesh N a times l k (by omega) i
    have := stop_mesh N a times l k (by omega) (i + 1)
    constructor <;> omega

/-- Materialize the cumulative coordinates used to address the sample table. -/
def wordVertex (N d word k : Nat) : List Nat :=
  let a := digit N d word
  let times := sortedTimes d a
  (List.range d).map fun j => (stop N a times k (j + 1)).toNat

/-- Integer barycentric numerators of total mass N * B. -/
def wordInput (N d word : Nat) (B : Int) (k i : Nat) : Int :=
  let a := digit N d word
  gap N a (sortedTimes d a) k i * B

/-- Raw rational samples are given in common units. Multiplication by B
puts the integer grid gaps in the same units. The sample table uses
lists of cumulative integer coordinates as keys. -/
def wordColor (N d word : Nat) (B : Int) (sample : List Nat → Nat → Int)
    (k : Nat) : Option Nat :=
  maxLabel? (d + 1) (wordInput N d word B k) (sample (wordVertex N d word k))

def solveWord? (N d : Nat) (B : Int) (sample : List Nat → Nat → Int) : Option Nat :=
  first? (fun word => full? (wordColor N d word B sample) (d + 1)) (N ^ d)

theorem solveWord_sound (N d : Nat) (B : Int) (sample : List Nat → Nat → Int)
    (word : Nat) (he : solveWord? N d B sample = some word) :
    word < N ^ d ∧ full? (wordColor N d word B sample) (d + 1) = true :=
  first?_some (N ^ d) word he

/-- The combinatorial proof of the paper supplies the only existence
hypothesis here. This lemma implements its bounded search extraction. -/
theorem solveWord_complete (N d : Nat) (B : Int) (sample : List Nat → Nat → Int)
    (hex : ∃ w, w < N ^ d ∧ full? (wordColor N d w B sample) (d + 1) = true) :
    ∃ word, solveWord? N d B sample = some word := by
  cases he : solveWord? N d B sample with
  | some word => exact ⟨word, rfl⟩
  | none =>
    obtain ⟨w, hbound, hfull⟩ := hex
    have hno := first?_none (N ^ d) he w hbound
    change full? (wordColor N d w B sample) (d + 1) = false at hno
    rw [hfull] at hno
    contradiction

/-- Count true entries in the same order as the bounded search. -/
def countTrue (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => countTrue p n + (if p n then 1 else 0)

theorem no_hits_count_zero (p : Nat → Bool) (n : Nat)
    (he : first? p n = none) : countTrue p n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases hp : first? p n with
    | some i => simp [first?, hp] at he
    | none =>
      cases hv : p n with
      | true => simp [first?, hp, hv] at he
      | false => simp [countTrue, hv, ih hp]

/-- The exact interface to the general odd-count Sperner assertion. -/
theorem solveWord_of_odd (N d : Nat) (B : Int) (sample : List Nat → Nat → Int)
    (hodd : countTrue (fun w => full? (wordColor N d w B sample) (d + 1))
      (N ^ d) % 2 = 1) : ∃ word, solveWord? N d B sample = some word := by
  cases he : solveWord? N d B sample with
  | some word => exact ⟨word, rfl⟩
  | none =>
    have hz := no_hits_count_zero _ _ he
    rw [hz] at hodd
    contradiction

theorem isum_gap (N : Nat) (a : Nat → Nat) (times : List Nat) (k r : Nat) :
    isum (gap N a times k) r = stop N a times k r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [isum, ih, gap]; omega

theorem isum_scale (f : Nat → Int) (B : Int) (r : Nat) :
    isum (fun i => f i * B) r = isum f r * B := by
  induction r with
  | zero => simp [isum]
  | succ r ih => simp only [isum, ih, Int.add_mul]

theorem wordInput_mass (N d word : Nat) (B : Int) (k : Nat) :
    isum (wordInput N d word B k) (d + 1) = (N : Int) * B := by
  let a := digit N d word
  let times := sortedTimes d a
  have hl : times.length = d := by simp [times, sortedTimes]
  have he : times[d]? = none := List.getElem?_eq_none (by omega)
  change isum (fun i => gap N a times k i * B) (d + 1) = (N : Int) * B
  simp only [isum_scale, isum_gap, stop, he]

theorem stop_mono (N d : Nat) (a : Nat → Nat) (ha : ∀ t, a t < N)
    (k i : Nat) :
    stop N a (sortedTimes d a) k i ≤ stop N a (sortedTimes d a) k (i + 1) := by
  let times := sortedTimes d a
  change stop N a times k i ≤ stop N a times k (i + 1)
  cases i with
  | zero =>
    cases he : times[0]? with
    | none => simp [stop, he]
    | some t => by_cases ht : t < k <;> simp [stop, he, ht] <;> omega
  | succ j =>
    cases h1 : times[j]? with
    | none =>
      have hj := List.getElem?_eq_none_iff.mp h1
      have h2 : times[j+1]? = none := List.getElem?_eq_none (by omega)
      simp [stop, h1, h2]
    | some t =>
      cases h2 : times[j+1]? with
      | none =>
        have hN := ha t
        by_cases ht : t < k <;> simp [stop, h1, h2, ht] <;> omega
      | some s =>
        obtain ⟨hj, ep⟩ := List.getElem?_eq_some_iff.mp h1
        obtain ⟨hj', ep'⟩ := List.getElem?_eq_some_iff.mp h2
        have hsort := List.pairwise_iff_getElem.mp (sortedTimes_sorted d a)
          j (j+1) hj hj' (by omega)
        change timeLE a times[j] times[j+1] = true at hsort
        rw [ep, ep'] at hsort
        have hts : a t < a s ∨ (a t = a s ∧ s ≤ t) := of_decide_eq_true hsort
        by_cases ht : t < k <;> by_cases hs : s < k <;>
          simp [stop, h1, h2, ht, hs] <;> omega

theorem wordInput_nonneg (N d word : Nat) (B : Int) (hn : 0 < N) (hb : 0 ≤ B)
    (k i : Nat) : 0 ≤ wordInput N d word B k i := by
  let a := digit N d word
  have ha (t : Nat) : a t < N := Nat.mod_lt _ hn
  have hg := stop_mono N d a ha k i
  exact Int.mul_nonneg (Int.sub_nonneg_of_le hg) hb

/-- Successful execution gives the sharp residual bound against any
additional sample qA satisfying the stated mixed-precision bound. -/
theorem solveWord_error (N d word : Nat) (B u : Int)
    (sample : List Nat → Nat → Int) (qA : Nat → Int)
    (hn : 0 < N) (hb : 0 < B)
    (he : solveWord? N d B sample = some word)
    (hq : ∀ t, t ≤ d → ∀ i, i ≤ d → 0 ≤ sample (wordVertex N d word t) i)
    (hm : ∀ t, t ≤ d → isum (sample (wordVertex N d word t)) (d + 1) = (N : Int) * B)
    (ha : isum qA (d + 1) = (N : Int) * B)
    (hu : ∀ t, t ≤ d → ∀ i, i ≤ d →
      qA i ≤ sample (wordVertex N d word t) i + u ∧
      sample (wordVertex N d word t) i ≤ qA i + u) :
    ∀ i, i ≤ d →
      let r := wordInput N d word B 0 i - qA i
      (-((d : Int) * (2 * (B + u))) ≤ ((d : Int) + 1) * r ∧
        ((d : Int) + 1) * r ≤ (d : Int) * (2 * (B + u))) := by
  let a := digit N d word
  have hfull := (solveWord_sound N d B sample word he).2
  have hB : 0 ≤ B := by omega
  have hpos : (0 : Int) < (N : Int) * B := Int.mul_pos (by omega) hb
  have hmesh (t : Nat) (_ : t ≤ d) (i : Nat) (_ : i ≤ d) :
      wordInput N d word B 0 i ≤ wordInput N d word B t i + B ∧
      wordInput N d word B t i ≤ wordInput N d word B 0 i + B := by
    have ⟨hl,hr⟩ := gap_mesh N a (sortedTimes d a) 0 t i
    constructor
    · simpa [wordInput, a, Int.add_mul] using Int.mul_le_mul_of_nonneg_right hl hB
    · simpa [wordInput, a, Int.add_mul] using Int.mul_le_mul_of_nonneg_right hr hB
  have h := certified_error d (wordInput N d word B)
    (fun t => sample (wordVertex N d word t)) qA B u hq
    (fun t _ => by simpa only [wordInput_mass] using hpos)
    (fun t ht => by simpa only [wordInput_mass] using hm t ht)
    (by simpa only [wordInput_mass] using ha) hfull hmesh hu
  intro i hi
  exact (h i hi).2

end ApproxBrouwer

namespace ApproxBrouwer.Example

/-- Rotation of barycentric coordinates, with numerators over five. -/
def cyclic5 (v : List Nat) (i : Nat) : Int :=
  let u : Int := (v[0]?.getD 0 : Nat)
  let z : Int := (v[1]?.getD 0 : Nat)
  if i = 0 then z - u else if i = 1 then 5 - z else u

#guard solveWord? 5 2 1 cyclic5 == some 8

#guard (List.range 3).map (wordVertex 5 2 8) == [[1, 3], [2, 3], [2, 4]]

#guard (List.range 3).map (wordColor 5 2 8 1 cyclic5) ==
    [some 2, some 0, some 1]

end ApproxBrouwer.Example
