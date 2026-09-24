import Diophantine.Paper1980.Transport100

/-!
# The one-hot run

`EXPLORATION_FIXED_PROGRAM_ROUTING.md`, §5: *"The first `C` row is the single monomial `I`.
Its `K` product is Boolean, and the target coefficient calculation in Section 1 proves the
first `Next` row is exactly the successor of `i₀`.  It follows that the second `C` row is
one-hot.  Repeat through all time rows, using (10) to prevent inter-row carries at each
stage.  Every `C` row is one-hot, every transition is `f`."*

That induction is proved here, from the route `K C = g·Next + V` and four support facts:
the rows of the state word are sub-words of the fixed state word (so the table's product
has no carry between rows), the junk avoids the target columns, the rows of the next-state
word are sub-words of the fixed state word, and the next-state word's rows are the state
word's later rows.

`onehot_step` is one stage: if row `i` selects the single state `s`, then row `i` of the
next-state word selects the single state `f s`.  `onehot_run` iterates it: row `i` of the
state word is the monomial at `f^[i] i₀`.

This is the fixed ROM and count-marker argument that §5 of
`EXPLORATION_STATE_TOP_DOUBLED_GRID.md` hands to the published 101 and 102 predecessors.
Here it is proved for a compiled controller, with those four support facts as its
hypotheses.
-/

namespace Jones1980

open Ternary Finset

/-- Equal digits mean equal numbers. -/
theorem Ternary.eq_of_dg_eq {X Y N : ℕ} (hX : X < 3 ^ N) (hY : Y < 3 ^ N)
    (h : ∀ p, dg X p = dg Y p) : X = Y := by
  rw [← Ternary.val_dg hX, ← Ternary.val_dg hY]
  exact congrArg (fun c => Ternary.val c N) (funext h)

/-! ### Rows of a scaled word, and the ports -/

/-- **No carry between time rows, for any scalar.**  Each row of a scaled word is that row's
own scaling, as long as every row's scaling fits inside a row. -/
theorem row_mul {A X m u i : ℕ} (hfit : ∀ k, A * row X m k < 3 ^ m)
    (hX : X < 3 ^ (m * u)) (hi : i < u) : row (A * X) m i = A * row X m i := by
  have hsum := sum_rows u hX
  have hmul : A * X = rowsum (fun k => A * row X m k) m u := by
    unfold rowsum
    conv_lhs => rw [hsum]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hmul]
  exact row_rowsum hfit u i hi

/-- **A port term reaches nothing below its port column.**  The sign and zero-request terms
of the route sit at `d + bs` and `d + bz` inside their rows, both above every target column
`d + a j`, so neither disturbs the transport. -/
theorem dg_port_row {X m u i p b : ℕ} (hfit : ∀ k, 3 ^ b * row X m k < 3 ^ m)
    (hX : X < 3 ^ (m * u)) (hi : i < u) (hp : p < b) (hpm : p < m) :
    dg (3 ^ b * X) (m * i + p) = 0 := by
  rw [← Ternary.dg_row _ i hpm, row_mul hfit hX hi]
  exact Ternary.dg_mul_pow_of_lt _ hp

namespace Controller

variable (P : Controller)

theorem coord_inj {i j : ℕ} (h : coord i = coord j) : i = j :=
  Nat.pow_right_injective (by norm_num) h

/-- The digits of the fixed state word: a `1` exactly at the state columns. -/
theorem dg_romS (p : ℕ) : dg P.romS p = if p ∈ (range P.n).image coord then 1 else 0 := by
  have himg : P.romS = ∑ e ∈ (range P.n).image coord, 3 ^ e := by
    unfold romS
    exact (Finset.sum_image (fun i _ j _ h => coord_inj h)).symm
  rw [himg]
  exact Ternary.dg_sum_pow _ p

/-- A word supported on the state columns whose column digits are the indicator of one
state is that state's monomial. -/
theorem onehot_of_dg {X j0 N : ℕ} (hj0 : j0 < P.n) (hXN : X < 3 ^ N)
    (hmon : 3 ^ coord j0 < 3 ^ N)
    (hsup : ∀ p, dg X p ≤ dg P.romS p)
    (hcol : ∀ j, j < P.n → dg X (coord j) = if j = j0 then 1 else 0) :
    X = 3 ^ coord j0 := by
  refine Ternary.eq_of_dg_eq hXN hmon fun p => ?_
  rw [Ternary.dg_pow]
  by_cases hp : ∃ j, j < P.n ∧ p = coord j
  · obtain ⟨j, hj, rfl⟩ := hp
    rw [hcol j hj]
    by_cases hjj : j = j0
    · rw [if_pos hjj, if_pos (by rw [hjj])]
    · rw [if_neg hjj, if_neg fun hc => hjj (coord_inj hc)]
  · push_neg at hp
    have h0 : dg P.romS p = 0 := by
      rw [dg_romS, if_neg]
      intro hmem
      obtain ⟨j, hj, hje⟩ := Finset.mem_image.1 hmem
      exact hp j (Finset.mem_range.1 hj) hje.symm
    have hle := hsup p
    rw [if_neg fun hc => hp j0 hj0 hc]
    omega

/-- **No carry between time rows.**  Each row of the table's product with a word is that
row's own product, as long as every row's product fits inside a row. -/
theorem row_romK_mul {C m u i : ℕ} (hfit : ∀ k, P.romK * row C m k < 3 ^ m)
    (hC : C < 3 ^ (m * u)) (hi : i < u) :
    row (P.romK * C) m i = P.romK * row C m i := by
  have hsum := sum_rows u hC
  have hmul : P.romK * C = rowsum (fun k => P.romK * row C m k) m u := by
    unfold rowsum
    conv_lhs => rw [hsum]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hmul]
  exact row_rowsum hfit u i hi

/-- **One stage of the run.**  If row `i` of the state word selects the single state `s`,
the route makes row `i` of the next-state word select the single state `f s`. -/
theorem onehot_step {C Next V m u i s : ℕ}
    (hroute : P.romK * C = P.romg * Next + V)
    (hCfit : ∀ k, P.romK * row C m k < 3 ^ m)
    (hCb : C < 3 ^ (m * u)) (hi : i < u)
    (hs : s < P.n) (hrow : row C m i = 3 ^ coord s)
    (hadd : ∀ p, dg (P.romg * Next) p + dg V p ≤ 2)
    (hVsup : ∀ j, j < P.n → dg V (m * i + (P.mark + coord j)) = 0)
    (hNsup : ∀ p, dg (row Next m i) p ≤ dg P.romS p)
    (hspan : ∀ j, j < P.n → P.mark + coord j < m)
    (hNlt : row Next m i < 3 ^ m) (hmonlt : 3 ^ coord (P.f s) < 3 ^ m) :
    row Next m i = 3 ^ coord (P.f s) := by
  refine P.onehot_of_dg (P.f_lt s hs) hNlt hmonlt hNsup fun j hj => ?_
  have hsp := hspan j hj
  have hcj : coord j < m := by omega
  have hL : dg (P.romK * C) (m * i + (P.mark + coord j)) = if j = P.f s then 1 else 0 := by
    rw [← Ternary.dg_row _ i hsp, P.row_romK_mul hCfit hCb hi, hrow, Nat.mul_comm,
      P.dg_romK_shift hs hj]
  have hR : dg (P.romg * Next + V) (m * i + (P.mark + coord j))
      = dg (row Next m i) (coord j) := by
    rw [Ternary.dg_add_of_le_two hadd, hVsup j hj, Nat.add_zero,
      show m * i + (P.mark + coord j) = P.mark + (m * i + coord j) from by ring]
    show dg (3 ^ P.mark * Next) (P.mark + (m * i + coord j)) = _
    rw [Ternary.dg_mul_pow_add, ← Ternary.dg_row _ i hcj]
  rw [hroute, hR] at hL
  exact hL

/-- The iterated successor stays a state. -/
theorem iterate_lt {i0 : ℕ} (h0 : i0 < P.n) : ∀ i, P.f^[i] i0 < P.n := by
  intro i
  induction i with
  | zero => simpa using h0
  | succ i ih => rw [Function.iterate_succ_apply']; exact P.f_lt _ ih

/-- **The one-hot run.**  Every row of the state word selects a single state, and the state
of row `i` is the `i`-th iterate of the successor from the entry state. -/
theorem onehot_run {C Next V m u i0 : ℕ}
    (hroute : P.romK * C = P.romg * Next + V)
    (hCfit : ∀ k, P.romK * row C m k < 3 ^ m)
    (hCb : C < 3 ^ (m * u))
    (h0 : i0 < P.n) (hrow0 : row C m 0 = 3 ^ coord i0)
    (hadd : ∀ p, dg (P.romg * Next) p + dg V p ≤ 2)
    (hVsup : ∀ i j, i + 1 < u → j < P.n → dg V (m * i + (P.mark + coord j)) = 0)
    (hNsup : ∀ i p, i + 1 < u → dg (row Next m i) p ≤ dg P.romS p)
    (hspan : ∀ j, j < P.n → P.mark + coord j < m)
    (hmonlt : ∀ s, s < P.n → 3 ^ coord s < 3 ^ m)
    (hshift : ∀ i, i + 1 < u → row Next m i = row C m (i + 1)) :
    ∀ i, i < u → row C m i = 3 ^ coord (P.f^[i] i0) := by
  intro i
  induction i with
  | zero => intro _; simpa using hrow0
  | succ i ih =>
    intro hi
    have hiu : i < u := by omega
    have hrowi := ih hiu
    have hNlt : row Next m i < 3 ^ m := by unfold row; exact Nat.mod_lt _ (by positivity)
    have hstep := P.onehot_step hroute hCfit hCb hiu (P.iterate_lt h0 i) hrowi hadd
      (fun j hj => hVsup i j hi hj) (fun p => hNsup i p hi) hspan hNlt
      (hmonlt _ (P.f_lt _ (P.iterate_lt h0 i)))
    rw [← hshift i hi, hstep, Function.iterate_succ_apply']

end Controller

end Jones1980
