import IPRADerivations.Core.IntCertificates

/-!
# `R(3,3) ≤ 6` in iPRA

Packet: `combinatorics/ramsey_ipra`, `ramsey.tex`, Section "Graph bounds and two exact thresholds":
"In particular `R(3,3) ≤ C(4,2) = 6`". The derivation here is by counting (Goodman's identity) rather than by
the pivot argument, because the count is a single polynomial certificate:

* the colouring of the edges of `K_6` is given by terms `x i j` (red indicator) and `y i j` (blue indicator)
  for `i < j`, with `x i j * x i j ≐ x i j` and `x i j + y i j ≐ 1`;
* the indicator of a monochromatic triangle `{a, b, c}` is `mono = x_ab x_ac x_bc + y_ab y_ac y_bc`;
* `quad`: `5 r ≤ r² + 6` for every natural term, that is `(r − 2)(r − 3) ≥ 0`, by a case split on `r ≤ 2`;
* `goodman`: `2 ≤ ∑ mono` over the twenty triangles, from the identity
  `2 ∑ mono − 4 − ∑_v (r_v² − 5 r_v + 6) = 2 ∑_e (x_e − x_e²)`, where `r_v` is the red degree of `v`;
* `pos_of_sum`: a sum of terms that is at least one has a positive term, as an object-level disjunction
  (`anyPos`);
* `ramsey33`: some triangle has a positive indicator;
* `tri_cases`: a positive indicator means that all three red indicators or all three blue indicators are
  positive.
-/

namespace LeanProofs.IPRA.Combinatorics.RamseyTriangle

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The sum of a list of terms. -/
def sumL : List (PTm n) → PTm n
  | [] => zero
  | a :: L => a + sumL L

/-- Some term of the list is positive. -/
def anyPos : List (PTm n) → Fm PTm n
  | [] => Fm.bot
  | a :: L => lt zero a ⋎ anyPos L

/-- A sum that is at least one has a positive term. -/
theorem pos_of_sum : {Γ : List (Fm PTm n)} → (L : List (PTm n)) → (Γ ⊢[PRAAx] le (succ zero) (sumL L)) →
    (Γ ⊢[PRAAx] anyPos L)
  | _, [], h => not_succ_le_self zero _ h
  | Γ, a :: L, h => by
    show Γ ⊢[PRAAx] lt zero a ⋎ anyPos L
    refine .orE (lt_or_le zero a) (.orI₁ Prf.hyp0) (.orI₂ ?_)
    have h0 : (le a zero :: Γ) ⊢[PRAAx] le a zero := Prf.hyp0
    have h' : (le a zero :: Γ) ⊢[PRAAx] le (succ zero) (a + sumL L) := h.wk
    refine pos_of_sum L ?_
    ipra_le sl h' + sl h0

/-- `(r − 2)(r − 3) ≥ 0` for a natural term: `5 r ≤ r² + 6`. -/
theorem quad (r : PTm n) : Γ ⊢[PRAAx] le (num 5 * r) (r * r + num 6) := by
  refine .orE (lt_or_le (num 2) r) ?_ ?_
  · have h : (lt (num 2) r :: Γ) ⊢[PRAAx] le (succ (num 2)) r := Prf.hyp0
    ipra_le sl h * (sl h + 1)
  · have h : (le r (num 2) :: Γ) ⊢[PRAAx] le r (num 2) := Prf.hyp0
    ipra_le sl h * (sl h + 1)

/-- The indicator of a monochromatic triangle. -/
def mono (x y : Fin 6 → Fin 6 → PTm n) (a b c : Fin 6) : PTm n :=
  x a b * x a c * x b c + y a b * y a c * y b c

/-- The twenty triangles of `K_6`. -/
def tris (x y : Fin 6 → Fin 6 → PTm n) : List (PTm n) :=
  [mono x y 0 1 2, mono x y 0 1 3, mono x y 0 1 4, mono x y 0 1 5,
    mono x y 0 2 3, mono x y 0 2 4, mono x y 0 2 5, mono x y 0 3 4,
    mono x y 0 3 5, mono x y 0 4 5, mono x y 1 2 3, mono x y 1 2 4,
    mono x y 1 2 5, mono x y 1 3 4, mono x y 1 3 5, mono x y 1 4 5,
    mono x y 2 3 4, mono x y 2 3 5, mono x y 2 4 5, mono x y 3 4 5]

/-- Goodman's count: every red/blue colouring of the edges of `K_6` has at least two monochromatic
triangles. -/
theorem goodman (x y : Fin 6 → Fin 6 → PTm n) (hx : ∀ i j, Γ ⊢[PRAAx] x i j * x i j ≐ x i j)
    (hy : ∀ i j, Γ ⊢[PRAAx] x i j + y i j ≐ succ zero) : Γ ⊢[PRAAx] le (num 2) (sumL (tris x y)) := by
  have q0 := quad (Γ := Γ) (x 0 1 + x 0 2 + x 0 3 + x 0 4 + x 0 5)
  have q1 := quad (Γ := Γ) (x 0 1 + x 1 2 + x 1 3 + x 1 4 + x 1 5)
  have q2 := quad (Γ := Γ) (x 0 2 + x 1 2 + x 2 3 + x 2 4 + x 2 5)
  have q3 := quad (Γ := Γ) (x 0 3 + x 1 3 + x 2 3 + x 3 4 + x 3 5)
  have q4 := quad (Γ := Γ) (x 0 4 + x 1 4 + x 2 4 + x 3 4 + x 4 5)
  have q5 := quad (Γ := Γ) (x 0 5 + x 1 5 + x 2 5 + x 3 5 + x 4 5)
  have ex01 := natEq (hx 0 1)
  have ex02 := natEq (hx 0 2)
  have ex03 := natEq (hx 0 3)
  have ex04 := natEq (hx 0 4)
  have ex05 := natEq (hx 0 5)
  have ex12 := natEq (hx 1 2)
  have ex13 := natEq (hx 1 3)
  have ex14 := natEq (hx 1 4)
  have ex15 := natEq (hx 1 5)
  have ex23 := natEq (hx 2 3)
  have ex24 := natEq (hx 2 4)
  have ex25 := natEq (hx 2 5)
  have ex34 := natEq (hx 3 4)
  have ex35 := natEq (hx 3 5)
  have ex45 := natEq (hx 4 5)
  have ey01 := natEq (hy 0 1)
  have ey02 := natEq (hy 0 2)
  have ey03 := natEq (hy 0 3)
  have ey04 := natEq (hy 0 4)
  have ey05 := natEq (hy 0 5)
  have ey12 := natEq (hy 1 2)
  have ey13 := natEq (hy 1 3)
  have ey14 := natEq (hy 1 4)
  have ey15 := natEq (hy 1 5)
  have ey23 := natEq (hy 2 3)
  have ey24 := natEq (hy 2 4)
  have ey25 := natEq (hy 2 5)
  have ey34 := natEq (hy 3 4)
  have ey35 := natEq (hy 3 5)
  have ey45 := natEq (hy 4 5)
  apply le_of_two_mul
  show Γ ⊢[PRAAx] le (num 2 * num 2) (num 2 *
    ((x 0 1 * x 0 2 * x 1 2 + y 0 1 * y 0 2 * y 1 2) +
      ((x 0 1 * x 0 3 * x 1 3 + y 0 1 * y 0 3 * y 1 3) +
      ((x 0 1 * x 0 4 * x 1 4 + y 0 1 * y 0 4 * y 1 4) +
      ((x 0 1 * x 0 5 * x 1 5 + y 0 1 * y 0 5 * y 1 5) +
      ((x 0 2 * x 0 3 * x 2 3 + y 0 2 * y 0 3 * y 2 3) +
      ((x 0 2 * x 0 4 * x 2 4 + y 0 2 * y 0 4 * y 2 4) +
      ((x 0 2 * x 0 5 * x 2 5 + y 0 2 * y 0 5 * y 2 5) +
      ((x 0 3 * x 0 4 * x 3 4 + y 0 3 * y 0 4 * y 3 4) +
      ((x 0 3 * x 0 5 * x 3 5 + y 0 3 * y 0 5 * y 3 5) +
      ((x 0 4 * x 0 5 * x 4 5 + y 0 4 * y 0 5 * y 4 5) +
      ((x 1 2 * x 1 3 * x 2 3 + y 1 2 * y 1 3 * y 2 3) +
      ((x 1 2 * x 1 4 * x 2 4 + y 1 2 * y 1 4 * y 2 4) +
      ((x 1 2 * x 1 5 * x 2 5 + y 1 2 * y 1 5 * y 2 5) +
      ((x 1 3 * x 1 4 * x 3 4 + y 1 3 * y 1 4 * y 3 4) +
      ((x 1 3 * x 1 5 * x 3 5 + y 1 3 * y 1 5 * y 3 5) +
      ((x 1 4 * x 1 5 * x 4 5 + y 1 4 * y 1 5 * y 4 5) +
      ((x 2 3 * x 2 4 * x 3 4 + y 2 3 * y 2 4 * y 3 4) +
      ((x 2 3 * x 2 5 * x 3 5 + y 2 3 * y 2 5 * y 3 5) +
      ((x 2 4 * x 2 5 * x 4 5 + y 2 4 * y 2 5 * y 4 5) +
      ((x 3 4 * x 3 5 * x 4 5 + y 3 4 * y 3 5 * y 4 5) +
      zero)))))))))))))))))))))
  refine le_of_comb (sl q0 + sl q1 + sl q2 + sl q3 + sl q4 + sl q5) ?_ (by ipra_nonneg)
  simp only [sl_def]
  ipra_simps
  have fy01 : Groth.ι (Q.mk Γ (y 0 1)) = 1 - Groth.ι (Q.mk Γ (x 0 1)) := by linear_combination ey01
  have fy02 : Groth.ι (Q.mk Γ (y 0 2)) = 1 - Groth.ι (Q.mk Γ (x 0 2)) := by linear_combination ey02
  have fy03 : Groth.ι (Q.mk Γ (y 0 3)) = 1 - Groth.ι (Q.mk Γ (x 0 3)) := by linear_combination ey03
  have fy04 : Groth.ι (Q.mk Γ (y 0 4)) = 1 - Groth.ι (Q.mk Γ (x 0 4)) := by linear_combination ey04
  have fy05 : Groth.ι (Q.mk Γ (y 0 5)) = 1 - Groth.ι (Q.mk Γ (x 0 5)) := by linear_combination ey05
  have fy12 : Groth.ι (Q.mk Γ (y 1 2)) = 1 - Groth.ι (Q.mk Γ (x 1 2)) := by linear_combination ey12
  have fy13 : Groth.ι (Q.mk Γ (y 1 3)) = 1 - Groth.ι (Q.mk Γ (x 1 3)) := by linear_combination ey13
  have fy14 : Groth.ι (Q.mk Γ (y 1 4)) = 1 - Groth.ι (Q.mk Γ (x 1 4)) := by linear_combination ey14
  have fy15 : Groth.ι (Q.mk Γ (y 1 5)) = 1 - Groth.ι (Q.mk Γ (x 1 5)) := by linear_combination ey15
  have fy23 : Groth.ι (Q.mk Γ (y 2 3)) = 1 - Groth.ι (Q.mk Γ (x 2 3)) := by linear_combination ey23
  have fy24 : Groth.ι (Q.mk Γ (y 2 4)) = 1 - Groth.ι (Q.mk Γ (x 2 4)) := by linear_combination ey24
  have fy25 : Groth.ι (Q.mk Γ (y 2 5)) = 1 - Groth.ι (Q.mk Γ (x 2 5)) := by linear_combination ey25
  have fy34 : Groth.ι (Q.mk Γ (y 3 4)) = 1 - Groth.ι (Q.mk Γ (x 3 4)) := by linear_combination ey34
  have fy35 : Groth.ι (Q.mk Γ (y 3 5)) = 1 - Groth.ι (Q.mk Γ (x 3 5)) := by linear_combination ey35
  have fy45 : Groth.ι (Q.mk Γ (y 4 5)) = 1 - Groth.ι (Q.mk Γ (x 4 5)) := by linear_combination ey45
  simp only [fy01, fy02, fy03, fy04, fy05, fy12, fy13, fy14, fy15, fy23, fy24, fy25, fy34, fy35, fy45]
  linear_combination (-2) * (ex01 + ex02 + ex03 + ex04 + ex05 + ex12 + ex13 + ex14 + ex15 + ex23 + ex24 + ex25 + ex34 + ex35 + ex45)

/-- `R(3,3) ≤ 6`: some triangle of a red/blue colouring of `K_6` has a positive monochromatic indicator. -/
theorem ramsey33 (x y : Fin 6 → Fin 6 → PTm n) (hx : ∀ i j, Γ ⊢[PRAAx] x i j * x i j ≐ x i j)
    (hy : ∀ i j, Γ ⊢[PRAAx] x i j + y i j ≐ succ zero) : Γ ⊢[PRAAx] anyPos (tris x y) := by
  refine pos_of_sum _ ?_
  have h := goodman x y hx hy
  ipra_le sl h + 1

theorem pos_left {a b : PTm n} (h : Γ ⊢[PRAAx] lt zero (a * b)) : Γ ⊢[PRAAx] lt zero a := by
  refine .orE (lt_or_le zero a) Prf.hyp0 ?_
  have h0 : (le a zero :: Γ) ⊢[PRAAx] le a zero := Prf.hyp0
  have h' : (le a zero :: Γ) ⊢[PRAAx] le (succ zero) (a * b) := h.wk
  refine not_succ_le_self zero _ ?_
  ipra_le sl h' with 𝔟 b * natEq (le_antisymm h0 (zero_le a))

theorem pos_right {a b : PTm n} (h : Γ ⊢[PRAAx] lt zero (a * b)) : Γ ⊢[PRAAx] lt zero b := by
  refine .orE (lt_or_le zero b) Prf.hyp0 ?_
  have h0 : (le b zero :: Γ) ⊢[PRAAx] le b zero := Prf.hyp0
  have h' : (le b zero :: Γ) ⊢[PRAAx] le (succ zero) (a * b) := h.wk
  refine not_succ_le_self zero _ ?_
  ipra_le sl h' with 𝔟 a * natEq (le_antisymm h0 (zero_le b))

/-- A positive indicator: all three red indicators or all three blue indicators are positive. -/
theorem tri_cases {a b c a' b' c' : PTm n} (h : Γ ⊢[PRAAx] lt zero (a * b * c + a' * b' * c')) :
    Γ ⊢[PRAAx] ((lt zero a ⋏ lt zero b) ⋏ lt zero c) ⋎ ((lt zero a' ⋏ lt zero b') ⋏ lt zero c') := by
  refine .orE (lt_or_le zero (a * b * c)) (.orI₁ ?_) (.orI₂ ?_)
  · have hp : (lt zero (a * b * c) :: Γ) ⊢[PRAAx] lt zero (a * b * c) := Prf.hyp0
    exact .andI (.andI (pos_left (pos_left hp)) (pos_right (pos_left hp))) (pos_right hp)
  · have h0 : (le (a * b * c) zero :: Γ) ⊢[PRAAx] le (a * b * c) zero := Prf.hyp0
    have h' : (le (a * b * c) zero :: Γ) ⊢[PRAAx] le (succ zero) (a * b * c + a' * b' * c') := h.wk
    have hp : (le (a * b * c) zero :: Γ) ⊢[PRAAx] lt zero (a' * b' * c') := by
      show (le (a * b * c) zero :: Γ) ⊢[PRAAx] le (succ zero) (a' * b' * c')
      ipra_le sl h' + sl h0
    exact .andI (.andI (pos_left (pos_left hp)) (pos_right (pos_left hp))) (pos_right hp)

end LeanProofs.IPRA.Combinatorics.RamseyTriangle
