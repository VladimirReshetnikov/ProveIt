import DiophantineConsistency.ArithmeticCommandCircuitPerm222

/-! # Double-exponential levels for C222 command words

`lev s = 2 * 2^(2^s)` with an *internal* level `s`. Squaring raises the level
by one (`lev s * lev s = 2 * lev (s+1)`), so a fixed number of Cantor pairings
raises it by a fixed amount, and conversely the tail of a nonempty word sits
one level below the word (`tail_le_lev`).

The main estimate is the append law `append_le`:
`l ≤ lev a → r ≤ lev b → appendValue l r ≤ lev (b + 6*a + 30)`.
It is linear in the level of the left word, not in its value, which is what
keeps the compiled proof word of a C222 code `n` below `lev (K*n)`.
It is proved by IΣ1 (Π1) induction on the level `a`, with the crude
value-linear bound `append_le_crude` closing the base case.

`eval_le` bounds every fixed finite `Circuit` evaluation by
`lev (cb e * (m+1))` when all four inputs are below `lev m`; `cb` is an
explicit structural recursion on the external circuit syntax.
Only bound lemmas are proved here; no run, checker or halting statement. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticProofWordBoundLevel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor ArithmeticCode254
open ArithmeticCommandWordPerm222 ArithmeticCommandReplacePerm222
open ArithmeticCommandAppendPerm222 ArithmeticCommandBlockPerm222
open ArithmeticCommandCircuitPerm222

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The explicit elementary level function `2 * 2^(2^s)`. -/
noncomputable def lev (s : V) : V := 2 * Exp.exp (Exp.exp s)

noncomputable def levDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y s. ∃ e, !expDef e s ∧ ∃ f, !expDef f e ∧ y = 2 * f”

instance lev_defined : 𝚺₁-Function₁[V] lev via levDef := .mk fun v => by
  simp [levDef, lev]

instance lev_definable : 𝚺₁-Function₁ (lev : V → V) := lev_defined.to_definable

/-! ## Elementary facts about `lev` -/

private theorem mm {a b c d : V} (h1 : a ≤ b) (h2 : c ≤ d) : a * c ≤ b * d :=
  mul_le_mul h1 h2 (Arithmetic.zero_le c) (Arithmetic.zero_le b)

private theorem cancel {k a b : V} (hk : 0 < k) (h : k * a ≤ k * b) : a ≤ b :=
  le_of_mul_le_mul_left h hk

theorem lev_sq (s : V) : lev s * lev s = 2 * lev (s + 1) := by
  unfold lev
  rw [exp_succ, exp_even, sq]
  ring

theorem lev_mono {s t : V} (h : s ≤ t) : lev s ≤ lev t := by
  unfold lev
  exact mul_le_mul_of_nonneg_left (exp_monotone_le.mpr (exp_monotone_le.mpr h))
    (Arithmetic.zero_le 2)

theorem le_lev_of {x s t : V} (hx : x ≤ lev s) (h : s ≤ t) : x ≤ lev t :=
  le_trans hx (lev_mono h)

theorem le_lev (s : V) : s ≤ lev s := by
  unfold lev
  have h1 : s ≤ Exp.exp (Exp.exp s) :=
    le_trans (le_of_lt (lt_exp s)) (le_of_lt (lt_exp _))
  exact le_trans h1 (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))

theorem lev_zero : lev (0 : V) = 4 := by
  simp only [lev, exp_zero, exp_one]
  norm_num

theorem four_le_lev (s : V) : 4 ≤ lev s := by
  rw [← lev_zero]
  exact lev_mono (Arithmetic.zero_le s)

theorem lev_one : lev (1 : V) = 8 := by
  have h := lev_sq (0 : V)
  rw [zero_add, lev_zero] at h
  have h2 : (2 : V) * lev 1 = 2 * 8 := by rw [← h]; norm_num
  exact mul_left_cancel₀ (by norm_num) h2

theorem eight_le_lev {s : V} (hs : 1 ≤ s) : 8 ≤ lev s := by
  rw [← lev_one]
  exact lev_mono hs

theorem add_le_lev {x y n : V} (hx : x ≤ lev n) (hy : y ≤ lev n) :
    x + y ≤ lev (n + 1) := by
  have h4 : 4 ≤ lev n := four_le_lev n
  apply cancel (k := 2) (by norm_num)
  rw [← lev_sq]
  calc 2 * (x + y) ≤ 2 * (lev n + lev n) :=
        mul_le_mul_of_nonneg_left (_root_.add_le_add hx hy) (Arithmetic.zero_le 2)
    _ = 4 * lev n := by ring
    _ ≤ lev n * lev n := mul_le_mul_of_nonneg_right h4 (Arithmetic.zero_le _)

/-- Two levels pay for one Cantor pairing plus one. -/
theorem pair_le {x y n : V} (hn : 1 ≤ n) (hx : x ≤ lev n) (hy : y ≤ lev n) :
    cantor x y + 1 ≤ lev (n + 2) := by
  have hL : 8 ≤ lev n := eight_le_lev hn
  have hc : cantor x y ≤ (x + y + 1) * (x + y + 1) := by
    rw [show (x + y + 1) * (x + y + 1) = (x + y) * (x + y + 1) + (x + y + 1) by ring]
    exact le_trans (cantor_polybound x y)
      (_root_.add_le_add le_rfl (le_trans le_add_self le_self_add))
  have hs : x + y + 1 ≤ 2 * lev n + 1 := by
    calc x + y + 1 ≤ lev n + lev n + 1 := _root_.add_le_add (_root_.add_le_add hx hy) le_rfl
      _ = 2 * lev n + 1 := by ring
  have h42 : 4 * lev n + 2 ≤ lev n * lev n := by
    have h2 : (2 : V) ≤ 4 * lev n :=
      le_trans (by norm_num : (2 : V) ≤ 4 * 8)
        (mul_le_mul_of_nonneg_left hL (Arithmetic.zero_le 4))
    calc 4 * lev n + 2 ≤ 4 * lev n + 4 * lev n := _root_.add_le_add le_rfl h2
      _ = 8 * lev n := by ring
      _ ≤ lev n * lev n := mul_le_mul_of_nonneg_right hL (Arithmetic.zero_le _)
  have h5 : cantor x y + 1 ≤ 5 * (lev n * lev n) := by
    calc cantor x y + 1 ≤ (2 * lev n + 1) * (2 * lev n + 1) + 1 :=
          _root_.add_le_add (le_trans hc (mm hs hs)) le_rfl
      _ = 4 * (lev n * lev n) + (4 * lev n + 2) := by ring
      _ ≤ 4 * (lev n * lev n) + lev n * lev n := _root_.add_le_add le_rfl h42
      _ = 5 * (lev n * lev n) := by ring
  have h40 : 40 * (lev n * lev n) ≤ (lev n * lev n) * (lev n * lev n) :=
    mul_le_mul_of_nonneg_right (le_trans (by norm_num : (40 : V) ≤ 8 * 8) (mm hL hL))
      (Arithmetic.zero_le _)
  have he : (lev n * lev n) * (lev n * lev n) = 8 * lev (n + 2) := by
    rw [lev_sq, show n + 2 = n + 1 + 1 by ring]
    calc 2 * lev (n + 1) * (2 * lev (n + 1)) = 4 * (lev (n + 1) * lev (n + 1)) := by ring
      _ = 4 * (2 * lev (n + 1 + 1)) := by rw [lev_sq]
      _ = 8 * lev (n + 1 + 1) := by ring
  apply cancel (k := 8) (by norm_num)
  calc 8 * (cantor x y + 1) ≤ 8 * (5 * (lev n * lev n)) :=
        mul_le_mul_of_nonneg_left h5 (Arithmetic.zero_le 8)
    _ = 40 * (lev n * lev n) := by ring
    _ ≤ (lev n * lev n) * (lev n * lev n) := h40
    _ = 8 * lev (n + 2) := he

theorem pair_le' {x y n : V} (hn : 1 ≤ n) (hx : x ≤ lev n) (hy : y ≤ lev n) :
    cantor x y ≤ lev (n + 2) :=
  le_trans le_self_add (pair_le hn hx hy)

theorem shift_le (n : V) {i j : V} (h : i ≤ j) : n + i ≤ n + j :=
  _root_.add_le_add le_rfl h

/-! ## Word tails sit one level lower -/

theorem tail_le_second (raw : V) : tailValue raw ≤ second raw := by
  unfold tailValue
  split_ifs
  · exact le_rfl
  · exact second_le _
  · exact le_trans (second_le _) (second_le _)

theorem tail_sq_le (raw : V) : tailValue raw * tailValue raw ≤ 2 * raw := by
  have ht := tail_le_second raw
  have hb : second raw * second raw ≤ 2 * raw := by
    have h := cantor_double (first raw) (second raw)
    rw [cantor_projections] at h
    rw [h]
    calc second raw * second raw ≤
          (first raw + second raw) * (first raw + second raw + 1) :=
          mm le_add_self (le_trans le_add_self le_self_add)
      _ ≤ _ := le_self_add
  exact le_trans (mm ht ht) hb

/-- The tail of a word below `lev (a+1)` lies below `lev a`. -/
theorem tail_le_lev {raw a : V} (h : raw + 1 ≤ lev (a + 1)) : tailValue raw ≤ lev a := by
  apply nonneg_le_nonneg_of_sq_le_sq (Arithmetic.zero_le _)
  apply le_trans (tail_sq_le raw)
  rw [lev_sq]
  exact mul_le_mul_of_nonneg_left (le_trans (by simp) h) (Arithmetic.zero_le 2)

/-- One replaced command costs six levels. -/
theorem replace_le {raw y n : V} (hn : 1 ≤ n) (hr : raw ≤ lev n) (hy : y ≤ lev n) :
    replaceValue raw y + 1 ≤ lev (n + 6) := by
  have hk : first raw ≤ lev n := le_trans (first_le raw) hr
  have hx1 : first (second raw) ≤ lev n :=
    le_trans (first_le _) (le_trans (second_le raw) hr)
  have hx2 : first (second (second raw)) ≤ lev n :=
    le_trans (first_le _) (le_trans (second2_le raw) hr)
  have hn2 : (1 : V) ≤ n + 2 := le_trans hn le_self_add
  have hn4 : (1 : V) ≤ n + 2 + 2 := le_trans hn2 le_self_add
  unfold replaceValue
  split_ifs
  · exact le_lev_of (pair_le hn hk hy) (shift_le n (by norm_num))
  · have h1 := pair_le' hn hx1 hy
    have h2 := pair_le hn2 (le_lev_of hk le_self_add) h1
    refine le_lev_of h2 ?_
    rw [add_assoc]
    exact shift_le n (by norm_num)
  · have h1 := pair_le' hn hx2 hy
    have h2 := pair_le' hn2 (le_lev_of hx1 le_self_add) h1
    have h3 := pair_le hn4 (le_lev_of hk (le_trans le_self_add le_self_add)) h2
    refine le_lev_of h3 ?_
    rw [add_assoc, add_assoc]
    exact shift_le n (by norm_num)

/-! ## The append law -/

/-- Crude bound, linear in the value of the left word. -/
theorem append_le_crude (r b : V) (hr : r ≤ lev b) :
    ∀ l, appendValue l r ≤ lev (b + 6 * l + 1) := by
  intro l
  induction l using ISigma1.sigma1_order_induction
  · definability
  case ind l ih =>
    rcases zero_or_succ l with (rfl | ⟨raw, rfl⟩)
    · rw [appendValue_zero]
      exact le_lev_of hr (le_trans le_self_add le_self_add)
    · rw [appendValue_succ]
      have hz : tailValue raw ≤ raw := ArithmeticCommandWordPerm222.tail_le raw
      have h1 := ih (tailValue raw) (lt_succ_iff_le.mpr hz)
      have hm : b + 6 * tailValue raw + 1 ≤ b + 6 * raw + 1 :=
        _root_.add_le_add (shift_le b (mul_le_mul_of_nonneg_left hz (Arithmetic.zero_le 6)))
          le_rfl
      have hraw : raw ≤ b + 6 * raw + 1 :=
        le_trans (le_mul_of_one_le_left (Arithmetic.zero_le raw) (by norm_num : (1 : V) ≤ 6))
          (le_trans le_add_self le_self_add)
      have h2 : raw ≤ lev (b + 6 * raw + 1) := le_trans (le_lev raw) (lev_mono hraw)
      have h3 := replace_le (n := b + 6 * raw + 1) le_add_self h2 (le_lev_of h1 hm)
      have he : b + 6 * (raw + 1) + 1 = b + 6 * raw + 1 + 6 := by ring
      rw [he]
      exact h3

/-- **Append law.** Linear in the level of the left word. -/
theorem append_le_level (r b : V) (hr : r ≤ lev b) :
    ∀ a l, l ≤ lev a → appendValue l r ≤ lev (b + 6 * a + 30) := by
  intro a
  induction a using ISigma1.pi1_succ_induction
  · definability
  case zero =>
    intro l hl
    rw [lev_zero] at hl
    refine le_lev_of (append_le_crude r b hr l) ?_
    calc b + 6 * l + 1 ≤ b + 6 * 4 + 1 :=
          _root_.add_le_add (shift_le b (mul_le_mul_of_nonneg_left hl (Arithmetic.zero_le 6)))
            le_rfl
      _ ≤ b + 6 * 0 + 30 := by
          rw [mul_zero, add_zero, add_assoc]
          exact shift_le b (by norm_num)
  case succ a ih =>
    intro l hl
    rcases zero_or_succ l with (rfl | ⟨raw, rfl⟩)
    · rw [appendValue_zero]
      exact le_lev_of hr (le_trans le_self_add le_self_add)
    · rw [appendValue_succ]
      have hz := tail_le_lev hl
      have h1 := ih _ hz
      have ha : a + 1 ≤ b + 6 * a + 30 :=
        _root_.add_le_add
          (le_trans (le_mul_of_one_le_left (Arithmetic.zero_le a) (by norm_num : (1 : V) ≤ 6))
            le_add_self) (by norm_num)
      have h2 : raw ≤ lev (b + 6 * a + 30) := le_trans le_self_add (le_lev_of hl ha)
      have h3 := replace_le (n := b + 6 * a + 30) (le_trans (by norm_num) le_add_self) h2 h1
      have he : b + 6 * (a + 1) + 30 = b + 6 * a + 30 + 6 := by ring
      rw [he]
      exact h3

theorem append_le {l r a b : V} (hl : l ≤ lev a) (hr : r ≤ lev b) :
    appendValue l r ≤ lev (b + 6 * a + 30) :=
  append_le_level r b hr a l hl

/-! ## Single commands -/

theorem nipWord_le {r n : V} (hn : 1 ≤ n) (hr : r ≤ lev n) : nipWord r ≤ lev (n + 2) :=
  pair_le hn (Arithmetic.zero_le _) hr

theorem dropWord_le {r n : V} (hn : 1 ≤ n) (hr : r ≤ lev n) : dropWord r ≤ lev (n + 2) :=
  pair_le hn (le_trans (by norm_num) (four_le_lev n)) hr

theorem axWord_le {c x y r n : V} (hn : 1 ≤ n) (hc : c + 3 ≤ lev n) (hx : x ≤ lev n)
    (hy : y ≤ lev n) (hr : r ≤ lev n) : axWord c x y r ≤ lev (n + 6) := by
  have hn2 : (1 : V) ≤ n + 2 := le_trans hn le_self_add
  have hn4 : (1 : V) ≤ n + 2 + 2 := le_trans hn2 le_self_add
  have h1 := pair_le' hn hx hr
  have h2 := pair_le' hn2 (le_lev_of hy le_self_add) h1
  have h3 := pair_le hn4 (le_lev_of hc (le_trans le_self_add le_self_add)) h2
  unfold axWord
  refine le_lev_of h3 ?_
  rw [add_assoc, add_assoc]
  exact shift_le n (by norm_num)

theorem Jword_le {v n : V} (hn : 1 ≤ n) (hv : v ≤ lev n) : Jword v ≤ lev (n + 4) := by
  unfold Jword
  split_ifs
  · exact Arithmetic.zero_le _
  · have h1 : cantor v 0 ≤ lev (n + 2) := pair_le' hn hv (Arithmetic.zero_le _)
    have h2 : (2 : V) ≤ lev (n + 2) := le_trans (by norm_num) (four_le_lev _)
    have h3 := pair_le (le_trans hn le_self_add) h2 h1
    unfold mpWord
    rw [show n + 4 = n + 2 + 2 by ring]
    exact h3

theorem wim_le {x y n : V} (hn : 1 ≤ n) (hx : x ≤ lev n) (hy : y ≤ lev n) :
    wim x y ≤ lev (n + 4) := by
  have hc := pair_le' hn hx hy
  have h1 := add_le_lev hc hc
  have h2 := add_le_lev h1 h1
  unfold wim tagged
  rw [add_zero, show 4 * cantor x y = (cantor x y + cantor x y) + (cantor x y + cantor x y) by ring,
    show n + 4 = n + 2 + 1 + 1 by ring]
  exact h2

/-! ## Fixed circuits -/

/-- Explicit level coefficient of a fixed circuit. -/
def cb : Circuit → ℕ
  | .input0 => 1
  | .input1 => 1
  | .input2 => 1
  | .input3 => 1
  | .zero => 1
  | .one => 1
  | .plus x y => cb x + cb y + 1
  | .sub x _ => cb x
  | .pair x y => cb x + cb y + 2
  | .imp x y => cb x + cb y + 4
  | .append x y => 6 * cb x + cb y + 30
  | .load x => cb x + 4

theorem one_le_cb (e : Circuit) : 1 ≤ cb e := by
  induction e <;> simp only [cb] <;> omega

theorem one_le_level (e : Circuit) (m : V) : (1 : V) ≤ (cb e : V) * (m + 1) := by
  have h : (1 : V) ≤ (cb e : V) := by exact_mod_cast one_le_cb e
  exact le_trans h (le_mul_of_one_le_right (Arithmetic.zero_le _) le_add_self)

private theorem lift_left (cx cy m : V) : cx * (m + 1) ≤ (cx + cy) * (m + 1) :=
  mul_le_mul_of_nonneg_right le_self_add (Arithmetic.zero_le _)

private theorem lift_right (cx cy m : V) : cy * (m + 1) ≤ (cx + cy) * (m + 1) :=
  mul_le_mul_of_nonneg_right le_add_self (Arithmetic.zero_le _)

theorem add_const_le (S m : V) (k : V) : S * (m + 1) + k ≤ (S + k) * (m + 1) := by
  rw [add_mul]
  exact _root_.add_le_add le_rfl (le_mul_of_one_le_right (Arithmetic.zero_le k) le_add_self)

/-- Every fixed circuit raises the input level by an explicit affine factor. -/
theorem eval_le (e : Circuit) {a b c u m : V} (ha : a ≤ lev m) (hb : b ≤ lev m)
    (hc : c ≤ lev m) (hu : u ≤ lev m) :
    e.eval a b c u ≤ lev ((cb e : V) * (m + 1)) := by
  have hm : ∀ x : V, x ≤ lev m → x ≤ lev ((1 : V) * (m + 1)) := fun x hx =>
    le_lev_of hx (by rw [one_mul]; exact le_self_add)
  induction e with
  | input0 => simpa only [cb, Circuit.eval, Nat.cast_one] using hm a ha
  | input1 => simpa only [cb, Circuit.eval, Nat.cast_one] using hm b hb
  | input2 => simpa only [cb, Circuit.eval, Nat.cast_one] using hm c hc
  | input3 => simpa only [cb, Circuit.eval, Nat.cast_one] using hm u hu
  | zero => exact Arithmetic.zero_le _
  | one => exact le_trans (by simp only [Circuit.eval]; norm_num) (four_le_lev _)
  | plus x y ihx ihy | pair x y ihx ihy | imp x y ihx ihy =>
    simp only [cb, Circuit.eval]
    push_cast
    have hx' := le_lev_of ihx (lift_left (cb x : V) (cb y) m)
    have hy' := le_lev_of ihy (lift_right (cb x : V) (cb y) m)
    first
    | case plus => exact le_lev_of (add_le_lev hx' hy') (add_const_le _ m 1)
    | case pair =>
      have h1 : (1 : V) ≤ ((cb x : V) + cb y) * (m + 1) :=
        le_trans (one_le_level x m) (lift_left _ _ m)
      exact le_lev_of (pair_le' h1 hx' hy') (add_const_le _ m 2)
    | case imp =>
      have h1 : (1 : V) ≤ ((cb x : V) + cb y) * (m + 1) :=
        le_trans (one_le_level x m) (lift_left _ _ m)
      exact le_lev_of (wim_le h1 hx' hy') (add_const_le _ m 4)
  | sub x y ihx _ =>
    simp only [cb, Circuit.eval]
    exact le_trans tsub_le_self ihx
  | append x y ihx ihy =>
    simp only [cb, Circuit.eval]
    push_cast
    refine le_lev_of (append_le ihx ihy) ?_
    have he : (6 * (cb x : V) + cb y + 30) * (m + 1) =
        (cb y : V) * (m + 1) + 6 * ((cb x : V) * (m + 1)) + 30 * (m + 1) := by ring
    rw [he]
    exact _root_.add_le_add le_rfl (le_mul_of_one_le_right (Arithmetic.zero_le 30) le_add_self)
  | load x ihx =>
    simp only [cb, Circuit.eval]
    push_cast
    exact le_lev_of (Jword_le (one_le_level x m) ihx) (add_const_le _ m 4)

end DiophantineConsistency.ArithmeticProofWordBoundLevel
