import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card

/-!
# Jones 1974, "Recursive undecidability — an exposition": Turing machines

The machines of the paper (after Kleene and Radó): a two-way infinite tape over
the alphabet `{0, 1}`, `n` active states `1, …, n` (here `Fin n`) and the halting
state `0` (here `none`).  Each card gives, for the scanned symbol, the symbol to
overprint, a shift `L`/`R`, and the next state.  A machine is started in state
`1` (here `0 : Fin n`).

* `Machine n`, `Config n`, `step`, `run`;
* the unary input/output convention of the paper's Definition:
  `x` is represented by `x + 1` consecutive ones scanned at the leftmost one;
  `Computes M f` says that `M` started on the representation of `x` halts on the
  representation of `f x` (all other squares blank);
* `Halts`, `HaltsWithScore` (the busy-beaver score: the number of ones on the
  tape when the machine, started on a blank tape, halts);
* shift invariance, and the sequential composition `seq N M` of two machines
  (run `N`, then hand its halting configuration to `M`), used for the paper's
  composite `M[T[M^(x)]]`.

The tape is a function `ℤ → Bool` (`true` = the symbol `1`).
-/

namespace Jones1974

/-- A head shift. -/
inductive Move
  | L
  | R
  deriving DecidableEq, Fintype

/-- Apply a shift to the head position. -/
def Move.apply : Move → ℤ → ℤ
  | .L, p => p - 1
  | .R, p => p + 1

/-- One instruction: overprint, shift, next state (`none` = the halting state `0`). -/
structure Action (n : ℕ) where
  write : Bool
  move : Move
  next : Option (Fin n)
  deriving DecidableEq, Fintype

/-- An `n`-state machine: one card per active state and scanned symbol. -/
structure Machine (n : ℕ) where
  card : Fin n → Bool → Action n
  deriving DecidableEq, Fintype

/-- A configuration: current state (`none` = halted), head position, tape. -/
structure Config (n : ℕ) where
  state : Option (Fin n)
  head : ℤ
  tape : ℤ → Bool

variable {n : ℕ}

/-- The blank tape. -/
def blank : ℤ → Bool := fun _ => false

/-- The starting state `1` (here `0`), when there is at least one active state. -/
def startState (n : ℕ) : Option (Fin n) :=
  if h : 0 < n then some ⟨0, h⟩ else none

/-- One step. A halted configuration stays fixed. -/
def step (M : Machine n) (c : Config n) : Config n :=
  match c.state with
  | none => c
  | some q =>
      let a := M.card q (c.tape c.head)
      { state := a.next
        head := a.move.apply c.head
        tape := Function.update c.tape c.head a.write }

/-- `t` steps. -/
def run (M : Machine n) (c : Config n) : ℕ → Config n
  | 0 => c
  | t + 1 => step M (run M c t)

@[simp] theorem run_zero (M : Machine n) (c : Config n) : run M c 0 = c := rfl

theorem run_succ (M : Machine n) (c : Config n) (t : ℕ) :
    run M c (t + 1) = step M (run M c t) := rfl

theorem run_add (M : Machine n) (c : Config n) (s t : ℕ) :
    run M c (s + t) = run M (run M c s) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [← Nat.add_assoc, run_succ, ih, run_succ]

theorem step_of_halted {M : Machine n} {c : Config n} (h : c.state = none) : step M c = c := by
  unfold step; rw [h]

theorem run_of_halted {M : Machine n} {c : Config n} (h : c.state = none) (t : ℕ) :
    run M c t = c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih, step_of_halted h]

/-- Any two halted runs from the same initial configuration agree, regardless of
their halting times or the number of active states. -/
theorem run_eq_of_halted {M : Machine n} {c : Config n} {s t : ℕ}
    (hs : (run M c s).state = none) (ht : (run M c t).state = none) :
    run M c s = run M c t := by
  rcases le_total s t with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [run_add, run_of_halted hs]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [run_add, run_of_halted ht]

/-! ### The unary convention -/

/-- The tape carrying `y + 1` consecutive ones at positions `p, …, p + y`. -/
def unary (p : ℤ) (y : ℕ) : ℤ → Bool := fun q => decide (p ≤ q ∧ q ≤ p + y)

/-- The input configuration for `x`: state `1`, scanning the leftmost of `x + 1` ones. -/
def input (n : ℕ) (x : ℕ) : Config n := ⟨startState n, 0, unary 0 x⟩

/-- `c` is the output configuration for `y`: halted, scanning the leftmost of exactly
`y + 1` ones, all other squares blank. -/
def IsOutput (c : Config n) (y : ℕ) : Prop := c.state = none ∧ c.tape = unary c.head y

/-- `M` computes `f` in the sense of the paper's Definition. -/
def Computes (M : Machine n) (f : ℕ → ℕ) : Prop :=
  ∀ x, ∃ t, IsOutput (run M (input n x) t) (f x)

/-- Turing computability of a total function (the paper's Definition). -/
def TMComputable (f : ℕ → ℕ) : Prop := ∃ (n : ℕ) (M : Machine n), Computes M f

/-- `M`, started on the blank tape, halts on the representation of `y`. -/
def PrintsFromBlank (M : Machine n) (y : ℕ) : Prop :=
  ∃ t, IsOutput (run M ⟨startState n, 0, blank⟩ t) y

/-! ### Halting and the score -/

/-- The set of positions carrying a `1`. -/
def ones (c : Config n) : Set ℤ := {p | c.tape p = true}

/-- The initial (blank-tape) configuration. -/
def init (n : ℕ) : Config n := ⟨startState n, 0, blank⟩

/-- `M` halts when started on the blank tape. -/
def Halts (M : Machine n) : Prop := ∃ t, (run M (init n) t).state = none

/-- `M` halts (from the blank tape) with exactly `s` ones on the tape: its score is `s`. -/
def HaltsWithScore (M : Machine n) (s : ℕ) : Prop :=
  ∃ t, (run M (init n) t).state = none ∧ (ones (run M (init n) t)).ncard = s

/-- After `t` steps from a configuration whose ones lie in `[a, b]`, the ones lie in
`[a - t, b + t]`. -/
theorem ones_subset_run {M : Machine n} {c : Config n} {a b : ℤ}
    (h : ∀ p, c.tape p = true → a ≤ p ∧ p ≤ b) (hh : a ≤ c.head ∧ c.head ≤ b) (t : ℕ) :
    (∀ p, (run M c t).tape p = true → a - t ≤ p ∧ p ≤ b + t) ∧
      (a - t ≤ (run M c t).head ∧ (run M c t).head ≤ b + t) := by
  induction t with
  | zero => simpa using ⟨h, hh⟩
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [run_succ]
    unfold step
    cases hs : (run M c t).state with
    | none =>
      simp only
      refine ⟨fun p hp => ?_, ?_⟩
      · have := ih1 p hp; push_cast; constructor <;> linarith
      · push_cast; constructor <;> linarith
    | some q =>
      simp only
      refine ⟨fun p hp => ?_, ?_⟩
      · by_cases hpq : p = (run M c t).head
        · subst hpq; push_cast; constructor <;> linarith
        · rw [Function.update_of_ne hpq] at hp
          have := ih1 p hp; push_cast; constructor <;> linarith
      · cases (M.card q ((run M c t).tape (run M c t).head)).move <;>
          simp only [Move.apply] <;> push_cast <;> constructor <;> linarith

/-- The ones of a blank-tape run form a finite set. -/
theorem ones_finite (M : Machine n) (t : ℕ) : (ones (run M (init n) t)).Finite := by
  have h := (ones_subset_run (M := M) (c := init n) (a := 0) (b := 0)
    (fun p hp => by simp [init, blank] at hp) (by simp [init]) t).1
  apply Set.Finite.subset (Set.finite_Icc (0 - (t : ℤ)) (0 + t))
  intro p hp
  exact Set.mem_Icc.2 (h p hp)

/-- Halting configurations are stationary, so the score is unique. -/
theorem score_unique {M : Machine n} {s s' : ℕ} (h : HaltsWithScore M s) (h' : HaltsWithScore M s') :
    s = s' := by
  obtain ⟨t, ht, hs⟩ := h
  obtain ⟨t', ht', hs'⟩ := h'
  rw [← hs, ← hs', run_eq_of_halted ht ht']

/-- The number of ones of the output configuration for `y` is `y + 1`. -/
theorem ncard_unary (p : ℤ) (y : ℕ) : ({q | unary p y q = true} : Set ℤ).ncard = y + 1 := by
  have : ({q | unary p y q = true} : Set ℤ) = Set.Icc p (p + y) := by
    ext q; simp [unary, Set.mem_Icc]
  rw [this, Set.ncard_eq_toFinset_card', Set.toFinset_Icc, Int.card_Icc]
  omega

/-- A machine that prints the representation of `y` from the blank tape has score `y + 1`. -/
theorem haltsWithScore_of_prints {M : Machine n} {y : ℕ} (h : PrintsFromBlank M y) :
    HaltsWithScore M (y + 1) := by
  obtain ⟨t, hst, htape⟩ := h
  refine ⟨t, hst, ?_⟩
  show ({p | (run M (init n) t).tape p = true} : Set ℤ).ncard = y + 1
  rw [show (init n) = ⟨startState n, 0, blank⟩ from rfl, htape]
  exact ncard_unary _ _

/-! ### Shift invariance -/

/-- Translate a configuration by `d`. -/
def Config.shift (c : Config n) (d : ℤ) : Config n :=
  ⟨c.state, c.head + d, fun q => c.tape (q - d)⟩

theorem step_shift (M : Machine n) (c : Config n) (d : ℤ) :
    step M (c.shift d) = (step M c).shift d := by
  cases hs : c.state with
  | none => simp [step, Config.shift, hs]
  | some q =>
    simp only [step, Config.shift, hs, add_sub_cancel_right, Config.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · first | trivial | rfl
    · cases (M.card q (c.tape c.head)).move <;> simp [Move.apply] <;> ring
    · funext p
      by_cases hp : p = c.head + d
      · subst hp; simp
      · have : p - d ≠ c.head := fun h => hp (by omega)
        rw [Function.update_of_ne this, Function.update_of_ne hp]

theorem run_shift (M : Machine n) (c : Config n) (d : ℤ) (t : ℕ) :
    run M (c.shift d) t = (run M c t).shift d := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih, step_shift, run_succ]

theorem unary_shift (p : ℤ) (y : ℕ) (d : ℤ) : (fun q => unary p y (q - d)) = unary (p + d) y := by
  funext q
  unfold unary
  have h : (p ≤ q - d ∧ q - d ≤ p + (y : ℤ)) ↔ (p + d ≤ q ∧ q ≤ p + d + (y : ℤ)) := by omega
  simp only [h]

theorem isOutput_shift {c : Config n} {y : ℕ} (h : IsOutput c y) (d : ℤ) :
    IsOutput (c.shift d) y := by
  obtain ⟨hs, ht⟩ := h
  refine ⟨hs, ?_⟩
  show (fun q => c.tape (q - d)) = unary (c.head + d) y
  rw [ht, unary_shift]

/-- The input configuration for `x` placed with its leftmost one at `p`. -/
theorem input_shift (x : ℕ) (p : ℤ) : (input n x).shift p = ⟨startState n, p, unary p x⟩ := by
  simp only [input, Config.shift, zero_add]
  congr 1
  rw [unary_shift, zero_add]

/-! ### Sequential composition -/

/-- The start state of the second machine inside the composite, as a state of `Fin (m + n)`. -/
def secondStart (m n : ℕ) : Option (Fin (m + n)) :=
  if h : 0 < n then some ⟨m, by omega⟩ else none

/-- `seq N M`: run `N` (states `0, …, m-1`); its halting transitions enter the start state of
`M` (states `m, …, m+n-1`); then run `M`. -/
def seq {m n : ℕ} (N : Machine m) (M : Machine n) : Machine (m + n) where
  card q b :=
    if hq : q.val < m then
      let a := N.card ⟨q.val, hq⟩ b
      { write := a.write
        move := a.move
        next := match a.next with
          | some q' => some (Fin.castAdd n q')
          | none => secondStart m n }
    else
      let a := M.card ⟨q.val - m, by omega⟩ b
      { write := a.write
        move := a.move
        next := a.next.map (fun q' => ⟨m + q'.val, by omega⟩) }

/-- Embedding of a configuration of the first machine (its halting state becomes the start
state of the second machine). -/
def emb₁ {m : ℕ} (n : ℕ) (c : Config m) : Config (m + n) :=
  ⟨match c.state with
    | some q => some (Fin.castAdd n q)
    | none => secondStart m n, c.head, c.tape⟩

/-- Embedding of a configuration of the second machine. -/
def emb₂ (m : ℕ) {n : ℕ} (c : Config n) : Config (m + n) :=
  ⟨c.state.map (fun q' => ⟨m + q'.val, by omega⟩), c.head, c.tape⟩

theorem step_emb₁ {m n : ℕ} (N : Machine m) (M : Machine n) {c : Config m}
    (hc : c.state ≠ none) : step (seq N M) (emb₁ n c) = emb₁ n (step N c) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 hc
  have hlt : q.val < m := q.isLt
  simp only [step, emb₁, seq, hq, Fin.val_castAdd, dif_pos hlt, Fin.eta]

theorem step_emb₂ {m n : ℕ} (N : Machine m) (M : Machine n) (c : Config n) :
    step (seq N M) (emb₂ m c) = emb₂ m (step M c) := by
  cases hs : c.state with
  | none => simp [step, emb₂, hs]
  | some q =>
    have hnlt : ¬ (m + q.val < m) := by omega
    simp only [step, emb₂, seq, hs, Option.map_some, dif_neg hnlt, Nat.add_sub_cancel_left, Fin.eta]

/-- A halted configuration of the first machine embeds as the start configuration of the
second machine. -/
theorem emb₁_halted {m : ℕ} (n : ℕ) {c : Config m} (hc : c.state = none) :
    emb₁ n c = emb₂ m (⟨startState n, c.head, c.tape⟩ : Config n) := by
  unfold emb₁ emb₂ secondStart startState
  simp only [hc]
  split_ifs <;> rfl

theorem run_emb₁ {m n : ℕ} (N : Machine m) (M : Machine n) (c : Config m) (t : ℕ)
    (hact : ∀ s < t, (run N c s).state ≠ none) :
    run (seq N M) (emb₁ n c) t = emb₁ n (run N c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, ih (fun s hs => hact s (by omega)), run_succ]
    exact step_emb₁ N M (hact t (by omega))

theorem run_emb₂ {m n : ℕ} (N : Machine m) (M : Machine n) (c : Config n) (t : ℕ) :
    run (seq N M) (emb₂ m c) t = emb₂ m (run M c t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih, run_succ, step_emb₂]

theorem isOutput_emb₂ {m n : ℕ} {c : Config n} {y : ℕ} (h : IsOutput c y) :
    IsOutput (emb₂ m c) y := by
  refine ⟨?_, h.2⟩
  show c.state.map _ = none
  rw [h.1]; rfl

/-- The first halting time of a run that halts. -/
theorem exists_first_halt {M : Machine n} {c : Config n} (h : ∃ t, (run M c t).state = none) :
    ∃ t, (run M c t).state = none ∧ ∀ s < t, (run M c s).state ≠ none := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, fun s hs => ?_⟩
  exact Nat.find_min h hs

/-- If `N` computes `g` and `M` computes `f`, then `seq N M` computes `f ∘ g`. -/
theorem computes_seq {m n : ℕ} {N : Machine m} {M : Machine n} {g f : ℕ → ℕ}
    (hN : Computes N g) (hM : Computes M f) : Computes (seq N M) (f ∘ g) := by
  intro x
  obtain ⟨t₁, ht₁⟩ := hN x
  obtain ⟨t, ht, hact⟩ := exists_first_halt ⟨t₁, ht₁.1⟩
  -- the output of N at time t (halting configurations are stationary)
  have hout : IsOutput (run N (input m x) t) (g x) := by
    rw [run_eq_of_halted ht ht₁.1]
    exact ht₁
  -- the composite: input embeds as emb₁ of N's input
  have hinput : (input (m + n) x) = emb₁ n (input m x) := by
    unfold input emb₁ startState secondStart
    by_cases hm : 0 < m
    · have hmn : 0 < m + n := by omega
      simp only [dif_pos hm, dif_pos hmn]
      rfl
    · have hm0 : m = 0 := by omega
      subst hm0
      simp
  set p := (run N (input m x) t).head with hp
  obtain ⟨t₂, ht₂⟩ := hM (g x)
  refine ⟨t + t₂, ?_⟩
  rw [hinput, run_add, run_emb₁ N M _ t hact, emb₁_halted n ht]
  -- the second phase starts on the input for g x shifted to p
  have hstart : (⟨startState n, p, (run N (input m x) t).tape⟩ : Config n) = (input n (g x)).shift p := by
    rw [input_shift]
    congr 1
    exact hout.2
  rw [hstart, run_emb₂, run_shift]
  exact isOutput_emb₂ (isOutput_shift ht₂ p)

/-- If `P` prints `y` from the blank tape and `M` computes `f`, then `seq P M` prints `f y`
from the blank tape. -/
theorem prints_seq {m n : ℕ} {P : Machine m} {M : Machine n} {y : ℕ} {f : ℕ → ℕ}
    (hP : PrintsFromBlank P y) (hM : Computes M f) : PrintsFromBlank (seq P M) (f y) := by
  obtain ⟨t₁, ht₁⟩ := hP
  obtain ⟨t, ht, hact⟩ := exists_first_halt ⟨t₁, ht₁.1⟩
  have hout : IsOutput (run P ⟨startState m, 0, blank⟩ t) y := by
    rw [run_eq_of_halted ht ht₁.1]
    exact ht₁
  have hinit : (⟨startState (m + n), 0, blank⟩ : Config (m + n)) = emb₁ n ⟨startState m, 0, blank⟩ := by
    unfold emb₁ startState secondStart
    by_cases hm : 0 < m
    · have hmn : 0 < m + n := by omega
      simp only [dif_pos hm, dif_pos hmn]
      rfl
    · have hm0 : m = 0 := by omega
      subst hm0
      simp
  set p := (run P ⟨startState m, 0, blank⟩ t).head with hp
  obtain ⟨t₂, ht₂⟩ := hM y
  refine ⟨t + t₂, ?_⟩
  rw [hinit, run_add, run_emb₁ P M _ t hact, emb₁_halted n ht]
  have hstart : (⟨startState n, p, (run P ⟨startState m, 0, blank⟩ t).tape⟩ : Config n)
      = (input n y).shift p := by
    rw [input_shift]
    congr 1
    exact hout.2
  rw [hstart, run_emb₂, run_shift]
  exact isOutput_emb₂ (isOutput_shift ht₂ p)

end Jones1974
