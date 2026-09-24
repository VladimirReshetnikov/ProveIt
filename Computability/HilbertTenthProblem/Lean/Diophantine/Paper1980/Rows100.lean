import Diophantine.Paper1980.Controller100

/-!
# The rows of the state word

`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §4: *"Divide the actual state pair by two.  Both
words are Boolean and their sum is `S(H/2)`.  A sum of two Boolean ternary words has no
carries.  It follows that `C/2` is supported on the allowed state columns, and each row of
`C` is at most `2S`."*

`Borrow100.bool_pair_first_row` is that statement for the lowest row.  Here it is proved
for every row.  Two Boolean words add digitwise, so their quotients and remainders at any
power add as well; and `S · heads m u`, the fixed state word repeated once per row, has
quotient `S · heads m (u − i)` at the `i`-th row boundary whenever `S < 3^m`.  Putting the
two together, every row of the halved state word and of its complement add to `S`, so each
row of the state word is a sub-word of the fixed state columns.

This is the support hypothesis of the row transport: the projection of
`Controller100.dg_romK_shift` reads one selected state at a time, and it is this that says
each row selects from the fixed columns.
-/

namespace Jones1980

open Ternary

/-! ### Boolean words add without carries -/

/-- Two Boolean words have disjoint enough digits that their remainders never overflow. -/
theorem Ternary.add_mod_of_bool {c cb N : ℕ} (hc : Bool3 c) (hcb : Bool3 cb) :
    (c + cb) % 3 ^ N = c % 3 ^ N + cb % 3 ^ N := by
  have h1 := hc.mod_le_rep N
  have h2 := hcb.mod_le_rep N
  have h3 := two_mul_rep_add_one N
  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega)]

/-- Hence their quotients add too. -/
theorem Ternary.add_div_of_bool {c cb N : ℕ} (hc : Bool3 c) (hcb : Bool3 cb) :
    (c + cb) / 3 ^ N = c / 3 ^ N + cb / 3 ^ N := by
  have h1 := hc.mod_le_rep N
  have h2 := hcb.mod_le_rep N
  have h3 := two_mul_rep_add_one N
  have hdc := Nat.div_add_mod c (3 ^ N)
  have hdb := Nat.div_add_mod cb (3 ^ N)
  have hx : 3 ^ N * (c / 3 ^ N + cb / 3 ^ N)
      = 3 ^ N * (c / 3 ^ N) + 3 ^ N * (cb / 3 ^ N) := by ring
  have hsum : c + cb
      = 3 ^ N * (c / 3 ^ N + cb / 3 ^ N) + (c % 3 ^ N + cb % 3 ^ N) := by omega
  rw [hsum, Nat.mul_add_div (show 0 < 3 ^ N by positivity),
    Nat.div_eq_of_lt (show c % 3 ^ N + cb % 3 ^ N < 3 ^ N by omega), add_zero]

/-- **The digitwise support test.**  When two Boolean words add to a third, each is
digitwise below the sum.  This is the exact support and disjointness test of the routing
note's §2: a Boolean field whose complement is also Boolean is supported inside whatever
their sum marks. -/
theorem Ternary.dg_le_of_add {V Vbar Z : ℕ} (hV : Bool3 V) (hVb : Bool3 Vbar)
    (h : V + Vbar = Z) (p : ℕ) : dg V p ≤ dg Z p := by
  have hle : ∀ j, dg V j + dg Vbar j ≤ 2 := by
    intro j
    have h1 := hV j
    have h2 := hVb j
    omega
  rw [← h, Ternary.dg_add_of_le_two hle]
  omega

/-- In particular a Boolean field vanishes wherever the sum does. -/
theorem Ternary.dg_eq_zero_of_add {V Vbar Z p : ℕ} (hV : Bool3 V) (hVb : Bool3 Vbar)
    (h : V + Vbar = Z) (hZ : dg Z p = 0) : dg V p = 0 := by
  have := Ternary.dg_le_of_add hV hVb h p
  omega

/-! ### The rows of the fixed state word -/

/-- The fixed state word repeated once per row: its quotient at the `i`-th row boundary
drops the first `i` rows. -/
theorem heads_div {S m : ℕ} (hS : S < 3 ^ m) :
    ∀ {u i : ℕ}, i ≤ u → S * heads m u / 3 ^ (m * i) = S * heads m (u - i) := by
  intro u i
  induction i generalizing u with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    obtain ⟨u', hu'⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
    subst hu'
    have hpow : (3 : ℕ) ^ (m * (i + 1)) = 3 ^ m * 3 ^ (m * i) := by
      rw [← pow_add]; congr 1; ring
    have hpeel : S * heads m (u' + 1) = S + 3 ^ m * (S * heads m u') := by
      rw [heads_succ']; ring
    rw [hpow, ← Nat.div_div_eq_div_mul, hpeel,
      Nat.add_mul_div_left _ _ (show 0 < 3 ^ m by positivity),
      Nat.div_eq_of_lt hS, zero_add, ih (by omega),
      show u' + 1 - (i + 1) = u' - i from by omega]

/-- The `i`-th row of the fixed state word is `S`. -/
theorem heads_row {S m u i : ℕ} (hS : S < 3 ^ m) (hi : i < u) :
    S * heads m u / 3 ^ (m * i) % 3 ^ m = S := by
  rw [heads_div hS (le_of_lt hi)]
  obtain ⟨k, hk⟩ : ∃ k, u - i = k + 1 := ⟨u - i - 1, by omega⟩
  rw [hk, heads_succ']
  have : S * (1 + 3 ^ m * heads m k) = S + 3 ^ m * (S * heads m k) := by ring
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hS]

/-! ### Every row of the state word selects from the fixed columns -/

/-- **§4, for every row.**  The halved state pair splits each row of the fixed state word
between its two halves. -/
theorem state_row {c cbar S m u i : ℕ} (hc : Bool3 c) (hcb : Bool3 cbar)
    (hS : S < 3 ^ m) (hi : i < u) (h : c + cbar = S * heads m u) :
    c / 3 ^ (m * i) % 3 ^ m + cbar / 3 ^ (m * i) % 3 ^ m = S := by
  have hdiv : (c + cbar) / 3 ^ (m * i) = c / 3 ^ (m * i) + cbar / 3 ^ (m * i) :=
    Ternary.add_div_of_bool hc hcb
  have hmod : (c / 3 ^ (m * i) + cbar / 3 ^ (m * i)) % 3 ^ m
      = c / 3 ^ (m * i) % 3 ^ m + cbar / 3 ^ (m * i) % 3 ^ m :=
    Ternary.add_mod_of_bool (hc.div_pow _) (hcb.div_pow _)
  have hrow := heads_row (S := S) (u := u) (i := i) hS hi
  rw [← h, hdiv, hmod] at hrow
  exact hrow

/-- Hence each row of the state word is at most `S`, so the doubled state word has rows at
most `2S`. -/
theorem state_row_le {c cbar S m u i : ℕ} (hc : Bool3 c) (hcb : Bool3 cbar)
    (hS : S < 3 ^ m) (hi : i < u) (h : c + cbar = S * heads m u) :
    c / 3 ^ (m * i) % 3 ^ m ≤ S := by
  have := state_row hc hcb hS hi h
  omega

/-- **Every row of the state word is digitwise below the fixed state word.**  Combining the
row split with the digitwise support test: the two halves of a row add to the fixed state
word without carries, so each is digitwise below it.  This is the support hypothesis the
one-hot run consumes. -/
theorem state_row_support {c cbar S m u i : ℕ} (hc : Bool3 c) (hcb : Bool3 cbar)
    (hS : S < 3 ^ m) (hi : i < u) (h : c + cbar = S * heads m u) (p : ℕ) :
    dg (row c m i) p ≤ dg S p :=
  Ternary.dg_le_of_add (hc.row m i) (hcb.row m i) (state_row hc hcb hS hi h) p

end Jones1980
