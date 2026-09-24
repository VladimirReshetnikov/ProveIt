import Diophantine.Paper1980.GraphHistory100

/-!
# Compiling a three-counter program into a graph controller

`EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md`, §§4–6.  A logical three-counter
program has increments, zero-or-decrement tests with two successors, an accepting halt and a
dead stop.  Its compiled graph represents a logical value `n` by the physical value `2n`, and
each logical instruction by two banks of three serial lanes:

* increment of `r`: every register `+1`, then `r` `+1` and the others `−1`;
* the zero branch of a test of `r`: a zero request on `r` and every register `+1`, then every
  register `−1`;
* the nonzero branch: `r` `−1` and the others `+1`, then every register `−1`, which is legal
  only when the logical value is positive;
* the accepting halt: zero requests on all three registers and every register `+1`, then every
  register `−1`, then back to the entry.

A two-bank prefix (`+1` then `−1`) makes the first sign plus.  Predecessor banks may enter
either branch of a test; the counter arithmetic admits only the numerically valid one (§4).

Unlike the note, the run of the counter certificate is cyclic, so the accepting halt's last
lane has an edge back to the entry rather than being a separate final vertex, and the halt
tests all three registers for zero instead of relying on a cleanup that the graph cannot see.

Vertices are `3 s + l` for slot `s` and lane `l < 3`.  Slot `0` and `1` are the prefix; slots
`2 + 4ℓ + k` are location `ℓ`'s banks: `k = 0, 1` the main pair (increment, zero branch, halt)
and `k = 2, 3` the nonzero branch of a test.

`accepts_of_run` is §6's soundness: every accepting serial run of the compiled graph on input
`x` passes through a logical computation from `(x, 0, 0)` to the accepting halt with all
registers zero.
-/

namespace Jones1980

/-- A logical instruction of a three-counter program. -/
inductive CInstr where
  /-- Increment a register and go on. -/
  | inc (r : Fin 3) (next : ℕ)
  /-- Zero-or-decrement: on zero go to the first successor, else decrement and go to the
  second. -/
  | test (r : Fin 3) (zero nonzero : ℕ)
  /-- The accepting halt. -/
  | accept
  /-- A dead stop. -/
  | stop

/-- A three-counter program, with entry location zero. -/
structure CProgram where
  /-- The number of locations. -/
  len : ℕ
  /-- The instruction at each location. -/
  code : ℕ → CInstr

namespace CProgram

variable (M : CProgram)

/-- One logical step. -/
inductive Step (M : CProgram) : ℕ × (Fin 3 → ℕ) → ℕ × (Fin 3 → ℕ) → Prop
  | inc {ℓ : ℕ} {r : Fin 3} {nx : ℕ} {v : Fin 3 → ℕ} (hℓ : ℓ < M.len)
      (hc : M.code ℓ = .inc r nx) : Step M (ℓ, v) (nx, Function.update v r (v r + 1))
  | zero {ℓ : ℕ} {r : Fin 3} {z nz : ℕ} {v : Fin 3 → ℕ} (hℓ : ℓ < M.len)
      (hc : M.code ℓ = .test r z nz) (hv : v r = 0) : Step M (ℓ, v) (z, v)
  | dec {ℓ : ℕ} {r : Fin 3} {z nz : ℕ} {v : Fin 3 → ℕ} (hℓ : ℓ < M.len)
      (hc : M.code ℓ = .test r z nz) (hv : v r ≠ 0) :
      Step M (ℓ, v) (nz, Function.update v r (v r - 1))

/-- The initial registers `(x, 0, 0)`. -/
def start (x : ℕ) : Fin 3 → ℕ := fun i => if i = 0 then x else 0

/-- The program accepts `x`: from `(x, 0, 0)` at the entry it reaches an accepting halt with
all registers zero. -/
def Accepts (x : ℕ) : Prop :=
  ∃ ℓ, ℓ < M.len ∧ M.code ℓ = .accept ∧
    Relation.ReflTransGen M.Step (0, start x) (ℓ, fun _ => 0)

/-! ### The compiled graph -/

/-- The number of vertices. -/
def nv : ℕ := 3 * (2 + 4 * M.len)

/-- The first-bank slots through which location `ℓ` may be entered. -/
def entry (ℓ t : ℕ) : Bool :=
  decide (ℓ < M.len) && match M.code ℓ with
    | .inc _ _ => t == 2 + 4 * ℓ
    | .accept => t == 2 + 4 * ℓ
    | .test _ _ _ => t == 2 + 4 * ℓ || t == 2 + 4 * ℓ + 2
    | .stop => false

/-- The permitted bank successions. -/
def bankNext (s t : ℕ) : Bool :=
  if s = 0 then t == 1 else if s = 1 then M.entry 0 t else
  match M.code ((s - 2) / 4) with
    | .inc _ nx => ((s - 2) % 4 == 0 && t == s + 1) || ((s - 2) % 4 == 1 && M.entry nx t)
    | .test _ z nz => ((s - 2) % 4 == 0 && t == s + 1) || ((s - 2) % 4 == 2 && t == s + 1)
        || ((s - 2) % 4 == 1 && M.entry z t) || ((s - 2) % 4 == 3 && M.entry nz t)
    | .accept => ((s - 2) % 4 == 0 && t == s + 1) || ((s - 2) % 4 == 1 && t == 0)
    | .stop => false

/-- The permitted edges: along the lanes of a bank, and from a bank's last lane to the first
lane of a permitted successor bank. -/
def adj (v w : ℕ) : Bool :=
  decide (v < M.nv) && decide (w < M.nv) &&
    (if v % 3 = 2 then w % 3 == 0 && M.bankNext (v / 3) (w / 3) else w == v + 1)

/-- The sign of lane `l` of slot `s`. -/
def sgnSL (s l : ℕ) : Bool :=
  if s = 0 then true else if s = 1 then false else
  match M.code ((s - 2) / 4) with
    | .inc r _ => (s - 2) % 4 == 0 || ((s - 2) % 4 == 1 && l == r.val)
    | .test r _ _ => (s - 2) % 4 == 0 || ((s - 2) % 4 == 2 && l != r.val)
    | .accept => (s - 2) % 4 == 0
    | .stop => false

/-- Whether lane `l` of slot `s` requests a zero test. -/
def zeroSL (s l : ℕ) : Bool :=
  if s ≤ 1 then false else
  match M.code ((s - 2) / 4) with
    | .test r _ _ => (s - 2) % 4 == 0 && l == r.val
    | .accept => (s - 2) % 4 == 0
    | _ => false

/-- **The compiled graph controller.** -/
def graph : Graph where
  n := M.nv
  two_le := by unfold nv; omega
  sp := M.nv + 2
  sp_ge := by omega
  n_lt := lt_of_lt_of_le (Ternary.lt_three_pow _)
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  adj := M.adj
  adj_lt := fun i j h => by
    unfold adj at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2⟩
  adj_irrefl := fun i => by
    unfold adj
    split_ifs with h
    · simp [h]
    · simp
  sgn := fun v => M.sgnSL (v / 3) (v % 3)
  zreq := fun v => !M.zeroSL (v / 3) (v % 3)
  bs := 2 * 3 ^ (M.nv - 1) + 1
  bz := 3 ^ (M.nv - 1) + (2 * 3 ^ (M.nv - 1) + 1) + 1
  bs_high := by omega
  bz_high := by omega

/-! ### Reading the tables -/

theorem adj_true {v w : ℕ} (h : M.adj v w = true) :
    (v % 3 = 2 → w % 3 = 0 ∧ M.bankNext (v / 3) (w / 3) = true) ∧
      (v % 3 ≠ 2 → w = v + 1) := by
  unfold adj at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, h3⟩ := h
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · rw [if_pos hv] at h3
    simpa using h3
  · rw [if_neg hv] at h3
    simpa using h3

theorem entry_true {ℓ t : ℕ} (h : M.entry ℓ t = true) :
    ℓ < M.len ∧ ((∃ r nx, M.code ℓ = .inc r nx ∧ t = 2 + 4 * ℓ) ∨
      (∃ r z nz, M.code ℓ = .test r z nz ∧ (t = 2 + 4 * ℓ ∨ t = 2 + 4 * ℓ + 2)) ∨
      (M.code ℓ = .accept ∧ t = 2 + 4 * ℓ)) := by
  unfold entry at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hℓ, h⟩ := h
  refine ⟨hℓ, ?_⟩
  cases hc : M.code ℓ with
  | inc r nx => rw [hc] at h; exact Or.inl ⟨r, nx, rfl, by simpa using h⟩
  | test r z nz => rw [hc] at h; exact Or.inr (Or.inl ⟨r, z, nz, rfl, by simpa using h⟩)
  | accept => rw [hc] at h; exact Or.inr (Or.inr ⟨rfl, by simpa using h⟩)
  | stop => rw [hc] at h; simp at h

theorem entry_zero (ℓ : ℕ) : M.entry ℓ 0 = false := by
  unfold entry
  cases M.code ℓ <;> simp <;> omega

theorem slot_div {ℓ k : ℕ} : (2 + 4 * ℓ + k - 2) / 4 = ℓ + k / 4 := by omega

theorem bankNext_slot {ℓ k t : ℕ} (hk : k < 4) :
    M.bankNext (2 + 4 * ℓ + k) t = match M.code ℓ with
      | .inc _ nx => (k == 0 && t == 2 + 4 * ℓ + k + 1) || (k == 1 && M.entry nx t)
      | .test _ z nz => (k == 0 && t == 2 + 4 * ℓ + k + 1) || (k == 2 && t == 2 + 4 * ℓ + k + 1)
          || (k == 1 && M.entry z t) || (k == 3 && M.entry nz t)
      | .accept => (k == 0 && t == 2 + 4 * ℓ + k + 1) || (k == 1 && t == 0)
      | .stop => false := by
  unfold bankNext
  rw [if_neg (by omega), if_neg (by omega), show (2 + 4 * ℓ + k - 2) / 4 = ℓ by omega,
    show (2 + 4 * ℓ + k - 2) % 4 = k by omega]

theorem sgnSL_slot {ℓ k l : ℕ} (hk : k < 4) :
    M.sgnSL (2 + 4 * ℓ + k) l = match M.code ℓ with
      | .inc r _ => k == 0 || (k == 1 && l == r.val)
      | .test r _ _ => k == 0 || (k == 2 && l != r.val)
      | .accept => k == 0
      | .stop => false := by
  unfold sgnSL
  rw [if_neg (by omega), if_neg (by omega), show (2 + 4 * ℓ + k - 2) / 4 = ℓ by omega,
    show (2 + 4 * ℓ + k - 2) % 4 = k by omega]

theorem zeroSL_slot {ℓ k l : ℕ} (hk : k < 4) :
    M.zeroSL (2 + 4 * ℓ + k) l = match M.code ℓ with
      | .test r _ _ => k == 0 && l == r.val
      | .accept => k == 0
      | _ => false := by
  unfold zeroSL
  rw [if_neg (by omega), show (2 + 4 * ℓ + k - 2) / 4 = ℓ by omega,
    show (2 + 4 * ℓ + k - 2) % 4 = k by omega]

/-- Only the halt's second bank leads back to the entry. -/
theorem bankNext_to_zero {s : ℕ} (h : M.bankNext s 0 = true) :
    ∃ ℓ, s = 2 + 4 * ℓ + 1 ∧ M.code ℓ = .accept := by
  have hs2 : 2 ≤ s := by
    by_contra hc
    unfold bankNext at h
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
    · simp at h
    · simp [M.entry_zero] at h
  obtain ⟨ℓ, k, hk, rfl⟩ : ∃ ℓ k, k < 4 ∧ s = 2 + 4 * ℓ + k :=
    ⟨(s - 2) / 4, (s - 2) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  rw [M.bankNext_slot hk] at h
  cases hc : M.code ℓ with
  | inc r nx => rw [hc] at h; simp [M.entry_zero] at h
  | test r z nz => rw [hc] at h; simp [M.entry_zero] at h
  | accept =>
    rw [hc] at h
    simp at h
    exact ⟨ℓ, by omega, hc⟩
  | stop => rw [hc] at h; simp at h

end CProgram

end Jones1980
