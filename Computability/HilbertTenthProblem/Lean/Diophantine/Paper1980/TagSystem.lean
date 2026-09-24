import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/-!
# Binary tag systems with the productions `0 → 0`, `1 → u`

The machine model of the tag-system route (`Papers/1980/EXPLORATION_TAG_QUEUE_HISTORY.md`
and its successors).  A *normalized binary tag system* has a deletion number `β ≥ 1`
and a fixed appendant word `u`; a step on a queue `W` of length at least `β` reads the
first symbol `s`, deletes the first `β` symbols and appends `0` (if `s = 0`) or `u`
(if `s = 1`).  The system halts when the queue has fewer than `β` symbols.

Queues are encoded numerically: the *content* of `W = w₀ w₁ … w_{ℓ−1}` is the ternary
number `Σ wᵢ 3ⁱ` (first symbol least significant) and its *length marker* is `3^ℓ`.
The transport identities of one step are `K·N' = N − d + U·M₁` and `K·L' = 3L +
(3^a − 3)M₁`, where `K = 3^β`, `d = N mod K` is the deleted prefix, `U` and `a` are the
value and length of `u`, and `M₁ = s·L`.
-/

namespace Jones1980

/-- A normalized binary tag system. -/
structure TagSys where
  /-- The deletion number. -/
  β : ℕ
  /-- The appendant for the symbol `1`. -/
  u : List Bool

namespace TagSys

/-- The bit of a symbol. -/
def bit (b : Bool) : ℕ := if b then 1 else 0

theorem bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> simp [bit]

/-- The ternary content of a queue (first symbol least significant). -/
def content (W : List Bool) : ℕ := Nat.ofDigits 3 (W.map bit)

/-- The length marker `3^|W|`. -/
def marker (W : List Bool) : ℕ := 3 ^ W.length

theorem content_nil : content [] = 0 := by simp [content]

theorem content_cons (b : Bool) (W : List Bool) : content (b :: W) = bit b + 3 * content W := by
  simp [content, Nat.ofDigits_cons]

theorem content_append (V W : List Bool) :
    content (V ++ W) = content V + 3 ^ V.length * content W := by
  simp [content, Nat.ofDigits_append]

theorem content_lt (W : List Bool) : content W < 3 ^ W.length := by
  induction W with
  | nil => simp [content_nil]
  | cons b W ih =>
    rw [content_cons, List.length_cons, pow_succ]
    have := bit_le_one b
    omega

/-- One step: if the queue has at least `β` symbols, delete them and append the
production of the first symbol; otherwise the queue is unchanged (halted). -/
def step (T : TagSys) (W : List Bool) : List Bool :=
  match W with
  | [] => []
  | s :: W' =>
    if (s :: W').length < T.β then s :: W'
    else (s :: W').drop T.β ++ (if s then T.u else [false])

/-- The queue is short (the system has halted). -/
def Short (T : TagSys) (W : List Bool) : Prop := W.length < T.β

/-- The system eventually halts from `W`. -/
def Halts (T : TagSys) (W : List Bool) : Prop := ∃ n, T.Short (T.step^[n] W)

theorem step_of_short (T : TagSys) {W : List Bool} (h : T.Short W) : T.step W = W := by
  cases W with
  | nil => rfl
  | cons s W' =>
    show (if (s :: W').length < T.β then s :: W' else _) = s :: W'
    exact if_pos h

theorem step_of_long (T : TagSys) {s : Bool} {W' : List Bool} (h : T.β ≤ (s :: W').length) :
    T.step (s :: W') = (s :: W').drop T.β ++ (if s then T.u else [false]) := by
  show (if (s :: W').length < T.β then s :: W' else _) = _
  exact if_neg (Nat.not_lt.2 h)

/-- The content transport of one (non-halted) step:
`3^β · content W' = content W − content W mod 3^β + 3^(ℓ − β) · U · s`. -/
theorem content_step (T : TagSys) {s : Bool} {W' : List Bool} (h : T.β ≤ (s :: W').length) :
    3 ^ T.β * content (T.step (s :: W')) =
      content (s :: W') - content (s :: W') % 3 ^ T.β +
        3 ^ (s :: W').length * (if s then content T.u else 0) := by
  rw [step_of_long T h, content_append, List.length_drop]
  set W := s :: W' with hW
  have hsplit : content W = content (W.take T.β) + 3 ^ T.β * content (W.drop T.β) := by
    conv_lhs => rw [← List.take_append_drop T.β W]
    rw [content_append, List.length_take, min_eq_left h]
  have hlt : content (W.take T.β) < 3 ^ T.β := by
    have := content_lt (W.take T.β)
    rwa [List.length_take, min_eq_left h] at this
  have hmod : content W % 3 ^ T.β = content (W.take T.β) := by
    rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have e : 3 ^ W.length = 3 ^ T.β * 3 ^ (W.length - T.β) := by
    rw [← pow_add, Nat.add_sub_cancel' h]
  rw [hmod, hsplit, Nat.add_sub_cancel_left, e]
  cases s
  · simp only [Bool.false_eq_true, if_false, content_cons, content_nil, bit, mul_zero, add_zero]
    try ring
  · simp only [if_true]
    ring

/-- The length transport of one (non-halted) step: `3^β · 3^|W'| = 3^|W| · 3^(a·s) / 3^(β−1)`…
in the form `|step W| + β = |W| + (if s then |u| else 1)`. -/
theorem length_step (T : TagSys) {s : Bool} {W' : List Bool} (h : T.β ≤ (s :: W').length) :
    (T.step (s :: W')).length + T.β = (s :: W').length + (if s then T.u.length else 1) := by
  rw [step_of_long T h, List.length_append, List.length_drop]
  simp only [List.length_cons] at h ⊢
  cases s <;>
    simp only [Bool.false_eq_true, if_false, if_true, List.length_cons, List.length_nil] <;> omega

end TagSys

end Jones1980
