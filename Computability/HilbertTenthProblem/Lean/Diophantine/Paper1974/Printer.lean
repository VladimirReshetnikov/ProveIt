import Diophantine.Paper1974.Machine

/-!
# Jones 1974: the machines `M^(x)` and a successor machine

* `printer x` (`x + 1` states) prints `x + 1` consecutive ones on a blank tape and halts
  scanning the leftmost of them (the machine `M^(x)` of the proof of Theorem 1; the
  paper displays `M^(2)`): states `1, …, x` write a one, move left and enter the next
  state; state `x + 1` writes a one on a zero and moves right in the same state, and on
  a one leaves it, moves left and halts.  Needs `x ≥ 1` (for `x = 0` the paper's card
  would never halt).
* `succ1` (3 states) computes `x ↦ x + 1`; it is used to obtain the odd numbers of
  ones in the proof of Corollary 1.
-/

namespace Jones1974

/-- The interval tape: ones exactly at `a, …, b`. -/
def ival (a b : ℤ) : ℤ → Bool := fun q => decide (a ≤ q ∧ q ≤ b)

theorem unary_eq_ival (p : ℤ) (y : ℕ) : unary p y = ival p (p + y) := rfl

/-! ### The printer `M^(x)` -/

/-- The machine `M^(x)`. -/
def printer (x : ℕ) : Machine (x + 1) where
  card q b :=
    if h : q.val < x then ⟨true, .L, some ⟨q.val + 1, by omega⟩⟩
    else if b then ⟨true, .L, none⟩ else ⟨true, .R, some q⟩

/-- The configuration of `M^(x)` after `i ≤ x` steps: state `i + 1`, head `-i`, ones at
`-(i-1), …, 0`. -/
def pcfg (x i : ℕ) (hi : i ≤ x) : Config (x + 1) :=
  ⟨some ⟨i, by omega⟩, -(i : ℤ), fun q => decide (-(i : ℤ) < q ∧ q ≤ 0)⟩

theorem printer_run (x : ℕ) :
    ∀ i (hi : i ≤ x), run (printer x) (init (x + 1)) i = pcfg x i hi := by
  intro i
  induction i with
  | zero =>
    intro _
    simp only [run_zero, init, pcfg, startState, dif_pos (Nat.succ_pos x), Config.mk.injEq]
    refine ⟨by first | trivial | rfl, by simp, ?_⟩
    funext q
    simp [blank] <;> omega
  | succ i ih =>
    intro hi
    rw [run_succ, ih (by omega)]
    simp only [step, pcfg, printer, dif_pos (show i < x by omega)]
    have hread : decide (-(i : ℤ) < -(i : ℤ) ∧ -(i : ℤ) ≤ 0) = false := by simp
    simp only [hread, Config.mk.injEq]
    refine ⟨by first | trivial | rfl, by push_cast; simp [Move.apply]; try ring, ?_⟩
    funext q
    by_cases hq : q = -(i : ℤ)
    · subst hq; simp
    · rw [Function.update_of_ne hq]
      have : (-(i : ℤ) < q ∧ q ≤ 0) ↔ (-((i + 1 : ℕ) : ℤ) < q ∧ q ≤ 0) := by
        push_cast; omega
      simp only [this]

/-- `M^(x)` prints `x + 1` ones (for `x ≥ 1`) and halts scanning the leftmost one. -/
theorem printer_prints {x : ℕ} (hx : 1 ≤ x) : PrintsFromBlank (printer x) x := by
  refine ⟨x + 2, ?_⟩
  have h := printer_run x x le_rfl
  show IsOutput (run (printer x) (init (x + 1)) (x + 2)) x
  rw [show x + 2 = x + 1 + 1 by ring, run_succ, run_succ, h]
  -- first extra step: state x+1 on a zero writes a one and moves right
  have hread1 : decide (-(x : ℤ) < -(x : ℤ) ∧ -(x : ℤ) ≤ 0) = false := by simp
  have hc1 : step (printer x) (pcfg x x le_rfl)
      = ⟨some ⟨x, by omega⟩, -(x : ℤ) + 1, unary (-(x : ℤ)) x⟩ := by
    simp only [step, pcfg, printer, dif_neg (lt_irrefl x), hread1, Config.mk.injEq]
    refine ⟨by first | trivial | rfl, by simp [Move.apply], ?_⟩
    funext q
    by_cases hq : q = -(x : ℤ)
    · subst hq; simp [unary]
    · rw [Function.update_of_ne hq]
      have : (-(x : ℤ) < q ∧ q ≤ 0) ↔ (-(x : ℤ) ≤ q ∧ q ≤ -(x : ℤ) + x) := by omega
      simp only [unary, this]
  rw [hc1]
  -- second extra step: state x+1 on a one moves left and halts
  have hread2 : unary (-(x : ℤ)) x (-(x : ℤ) + 1) = true := by
    simp only [unary]
    have : (1 : ℤ) ≤ x := by exact_mod_cast hx
    simp; omega
  simp only [step, printer, dif_neg (lt_irrefl x), hread2, ↓reduceIte]
  refine ⟨by first | trivial | rfl, ?_⟩
  show Function.update (unary (-(x : ℤ)) x) (-(x : ℤ) + 1) true = unary (-(x : ℤ) + 1 - 1) x
  rw [add_sub_cancel_right]
  funext q
  by_cases hq : q = -(x : ℤ) + 1
  · subst hq; simp [hread2]
  · rw [Function.update_of_ne hq]

/-! ### The successor machine -/

/-- A 3-state machine computing `x ↦ x + 1`: move left, write a one, move right, move left
and halt. -/
def succ1 : Machine 3 where
  card q b :=
    match q.val, b with
    | 0, true => ⟨true, .L, some ⟨1, by norm_num⟩⟩
    | 1, false => ⟨true, .R, some ⟨2, by norm_num⟩⟩
    | 2, true => ⟨true, .L, none⟩
    | _, _ => ⟨false, .R, none⟩

theorem succ1_computes : Computes succ1 (fun x => x + 1) := by
  intro x
  refine ⟨3, ?_⟩
  have hs : startState 3 = some ⟨0, by norm_num⟩ := by simp [startState]
  -- step 1
  have h1 : run succ1 (input 3 x) 1 = ⟨some ⟨1, by norm_num⟩, -1, unary 0 x⟩ := by
    simp only [run_succ, run_zero, input, hs, step]
    have : unary 0 x 0 = true := by simp [unary]
    simp only [this, succ1, Config.mk.injEq]
    refine ⟨by first | trivial | rfl, by simp [Move.apply], ?_⟩
    funext q
    by_cases hq : q = 0
    · subst hq; simp [this]
    · rw [Function.update_of_ne hq]
  -- step 2
  have h2 : run succ1 (input 3 x) 2 = ⟨some ⟨2, by norm_num⟩, 0, unary (-1) (x + 1)⟩ := by
    rw [run_succ, h1]
    have : unary 0 x (-1) = false := by simp [unary]
    simp only [step, this, succ1, Config.mk.injEq]
    refine ⟨by first | trivial | rfl, by simp [Move.apply], ?_⟩
    funext q
    by_cases hq : q = -1
    · subst hq; simp [unary]
    · rw [Function.update_of_ne hq]
      have : (0 ≤ q ∧ q ≤ 0 + (x : ℤ)) ↔ (-1 ≤ q ∧ q ≤ -1 + ((x + 1 : ℕ) : ℤ)) := by
        push_cast; omega
      simp only [unary, this]
  -- step 3
  show IsOutput (run succ1 (input 3 x) (2 + 1)) (x + 1)
  rw [run_succ, h2]
  have : unary (-1) (x + 1) 0 = true := by simp [unary]
  simp only [step, this, succ1]
  refine ⟨by first | trivial | rfl, ?_⟩
  show Function.update (unary (-1) (x + 1)) 0 true = unary (0 - 1) (x + 1)
  rw [zero_sub]
  funext q
  by_cases hq : q = 0
  · subst hq; simp [this]
  · rw [Function.update_of_ne hq]

end Jones1974
