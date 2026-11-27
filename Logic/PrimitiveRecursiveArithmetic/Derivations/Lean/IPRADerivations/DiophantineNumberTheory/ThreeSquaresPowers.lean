import IPRADerivations.DiophantineNumberTheory.ThreeSquares
import IPRADerivations.DiophantineNumberTheory.FourSquares

/-!
# The three-square obstruction for `4^a (8b + 7)`

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/quadratic.tex`,
`qr:three-obstruction`: no number of the form `4^a (8b + 7)` is a sum of three squares.

The statement quantifies over the three squares inside an induction on `a`, so it is first turned into an
equation between terms: `R3 n` is the bit of the bounded search for a triple `x, y, z ≤ n` with
`x² + y² + z² = n` (the four-digit codes of `FourSquares`, the fourth digit unused).

* `r3_intro`, `r3_elim`: the bit and its witnesses;
* `sq_par`: `x² = 4 (h² + h r) + r` with `h = ⌊x/2⌋`, `r = par x`;
* `bits_sum`: three bits are all `0`, or their sum is between `1` and `3`;
* `halve`: `x² + y² + z² = 4m` forces `x, y, z` even, and `m = (x/2)² + (y/2)² + (z/2)²`;
* `r3_base` (`ThreeSquares.three_squares_open`), `r3_step`, and `r3_zero`: `R3 (4^a (8b + 7)) = 0`, by
  induction on `a`;
* `obstruction_open`, and the closed sentence **`three_square_obstruction_powers`**:
  `∀ a b x y z. x² + y² + z² = 4^a (8b + 7) → ⊥`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.ThreeSquaresPowers

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb')
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dmu)
open LeanProofs.IPRA.DiophantineNumberTheory.FermatTwoSquares (four_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.FourSquaresAlgebra (le_sq_part)
open LeanProofs.IPRA.DiophantineNumberTheory.FourSquares (D0 D1 D2 code4 digs code_lt bd lt_succ_of_le)
open LeanProofs.IPRA.DiophantineNumberTheory.ThreeSquares (three_squares_open)
open LeanProofs.IPRA.Foundations.NumeralPrimes (subst_num num_lt num_pos)
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_cases ex_intro ex_elim eqb_cases eq_of_eqb
  one_ne_zero)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## The search for three squares -/

/-- `[D0² + D1² + D2² = n]` for the digits of `c` in base `n + 1`, over `0 = c`, `1 = n`. -/
abbrev r3B : PTm 2 :=
  eqb (D0 (var 0) (succ (var 1)) * D0 (var 0) (succ (var 1)) +
    D1 (var 0) (succ (var 1)) * D1 (var 0) (succ (var 1)) +
    D2 (var 0) (succ (var 1)) * D2 (var 0) (succ (var 1))) (var 1)

theorem inst2_r3B (c n : PTm k) : inst2 r3B c n =
    eqb (D0 c (succ n) * D0 c (succ n) + D1 c (succ n) * D1 c (succ n) + D2 c (succ n) * D2 c (succ n)) n := by
  simp [inst2]

/-- The bit of "`n` is a sum of three squares". -/
abbrev R3 (n : PTm k) : PTm k := exB r3B (bd n) n

theorem rearr1 {a b c n : PTm k} (e : Γ ⊢[PRAAx] a * a + b * b + c * c ≐ n) :
    Γ ⊢[PRAAx] a * a + (b * b + c * c) ≐ n := by
  ipra_lc natEq e

theorem rearr2 {a b c n : PTm k} (e : Γ ⊢[PRAAx] a * a + b * b + c * c ≐ n) :
    Γ ⊢[PRAAx] b * b + (a * a + c * c) ≐ n := by
  ipra_lc natEq e

theorem rearr3 {a b c n : PTm k} (e : Γ ⊢[PRAAx] a * a + b * b + c * c ≐ n) :
    Γ ⊢[PRAAx] c * c + (a * a + b * b) ≐ n := by
  ipra_lc natEq e

/-- Any representation makes the bit `1`. -/
theorem r3_intro {n a b c : PTm k} (e : Γ ⊢[PRAAx] a * a + b * b + c * c ≐ n) : Γ ⊢[PRAAx] R3 n ≐ one := by
  have hB : Γ ⊢[PRAAx] succ n ≐ succ (pred (succ n)) := congrSucc (pred_succ _).eqSymm
  have la := lt_succ_of_le (le_sq_part (rearr1 e)); have lb := lt_succ_of_le (le_sq_part (rearr2 e))
  have lc := lt_succ_of_le (le_sq_part (rearr3 e))
  have lz : Γ ⊢[PRAAx] lt (zero : PTm k) (succ n) := lt_succ_of_le (zero_le n)
  have dg := digs (d := zero) hB la lb lc
  have d0 := Prf.andE₁ dg; have d1 := Prf.andE₁ (Prf.andE₂ dg)
  have d2 := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ dg))
  have val : Γ ⊢[PRAAx] inst2 r3B (code4 (succ n) a b c zero) n ≐ one := by
    rw [inst2_r3B]
    exact (congrEqb' (congrAdd (congrAdd (congrMul d0 d0) (congrMul d1 d1)) (congrMul d2 d2))
      (.eqRefl n)).eqTrans (eqb_of_eq e)
  exact ex_intro r3B (.impI (one_ne_zero _ (val.wk.eqSymm.eqTrans Prf.hyp0))) (code_lt la lb lc lz)

/-- The three witnesses. -/
abbrev X3 (n : PTm k) : PTm k := D0 (wit r3B (bd n) n) (succ n)
abbrev Y3 (n : PTm k) : PTm k := D1 (wit r3B (bd n) n) (succ n)
abbrev Z3 (n : PTm k) : PTm k := D2 (wit r3B (bd n) n) (succ n)

/-- The bit `1` gives the witnesses. -/
theorem r3_elim {n : PTm k} (h : Γ ⊢[PRAAx] R3 n ≐ one) :
    Γ ⊢[PRAAx] X3 n * X3 n + Y3 n * Y3 n + Z3 n * Z3 n ≐ n := by
  have ne := Prf.andE₂ (ex_elim r3B h)
  rw [inst2_r3B] at ne
  refine .orE (eqb_cases (X3 n * X3 n + Y3 n * Y3 n + Z3 n * Z3 n) n) ?_ ?_
  · exact .botE _ (.impE ne.wk Prf.hyp0)
  · exact eq_of_eqb Prf.hyp0

/-! ## Halving -/

theorem sq_par_alg {x h r : PTm k} (e : Γ ⊢[PRAAx] x ≐ two * h + r) (hr : Γ ⊢[PRAAx] r * r ≐ r) :
    Γ ⊢[PRAAx] x * x ≐ (two * two) * (h * h + h * r) + r := by
  ipra_lc (𝔞 x + 2 * 𝔞 h + 𝔞 r) * natEq e + natEq hr

theorem par_idem (x : PTm k) : Γ ⊢[PRAAx] par x * par x ≐ par x :=
  Common.mul_self_eq_of_zero_or_one (par_cases x)

/-- `x² = 4 (h² + h r) + r` with `h = ⌊x/2⌋`, `r = par x`. -/
theorem sq_par (x : PTm k) :
    Γ ⊢[PRAAx] x * x ≐ (two * two) * (half x * half x + half x * par x) + par x :=
  sq_par_alg (half_par x) (par_idem x)

/-- `4m = 4U + s` with `1 ≤ s < 4` is impossible. -/
theorem four_absurd {m U s : PTm k} (e : Γ ⊢[PRAAx] (two * two) * m ≐ (two * two) * U + s)
    (h1 : Γ ⊢[PRAAx] le one s) (h3 : Γ ⊢[PRAAx] lt s (two * two)) : Γ ⊢[PRAAx] Fm.bot := by
  have r := Prf.andE₂ (dmu four_pos e h3)
  have z : Γ ⊢[PRAAx] rem ((two * two) * m) (two * two) ≐ zero :=
    (congrAp2 remF (add_zero _).eqSymm (.eqRefl _)).eqTrans ((rem_add_mul four_pos m zero).eqTrans (rem_zero _))
  have s0 := natEq (r.eqSymm.eqTrans z)
  have bad : Γ ⊢[PRAAx] le one zero := by ipra_le sl h1 with s0
  exact lt_zero_absurd _ bad

/-- Three bits with given values: all zero, or the sum is between `1` and `3`. -/
theorem leaf {rx ry rz : PTm k} (i j l : ℕ) (hi : i ≤ 1) (hj : j ≤ 1) (hl : l ≤ 1)
    (ex : Γ ⊢[PRAAx] rx ≐ num i) (ey : Γ ⊢[PRAAx] ry ≐ num j) (ez : Γ ⊢[PRAAx] rz ≐ num l) :
    Γ ⊢[PRAAx] ((rx ≐ zero) ⋏ ((ry ≐ zero) ⋏ (rz ≐ zero))) ⋎
      (le one (rx + ry + rz) ⋏ lt (rx + ry + rz) (two * two)) := by
  by_cases h0 : i + j + l = 0
  · have i0 : i = 0 := by omega
    have j0 : j = 0 := by omega
    have l0 : l = 0 := by omega
    subst i0; subst j0; subst l0
    exact .orI₁ (.andI ex (.andI ey ez))
  · obtain ⟨c, hc⟩ : ∃ c, i + j + l = 1 + c := ⟨i + j + l - 1, by omega⟩
    obtain ⟨d, hd⟩ : ∃ d, i + j + l + 1 + d = 4 := ⟨3 - (i + j + l), by omega⟩
    have a := natEq ex; have b := natEq ey; have e := natEq ez
    refine .orI₂ (.andI ?_ ?_)
    · ipra_le (c : Groth (Q Γ)) using
        (have k2 := congrArg (fun t : ℕ => (t : Groth (Q Γ))) hc
         push_cast at k2
         linear_combination a + b + e + k2)
    · ipra_le (d : Groth (Q Γ)) using
        (have k2 := congrArg (fun t : ℕ => (t : Groth (Q Γ))) hd
         push_cast at k2
         linear_combination (-1 : Groth (Q Γ)) * a - b - e - k2)

theorem bits_sum (x y z : PTm k) :
    Γ ⊢[PRAAx] ((par x ≐ zero) ⋏ ((par y ≐ zero) ⋏ (par z ≐ zero))) ⋎
      (le one (par x + par y + par z) ⋏ lt (par x + par y + par z) (two * two)) := by
  refine .orE (par_cases x) ?_ ?_
  · refine .orE (par_cases y) ?_ ?_
    · refine .orE (par_cases z) ?_ ?_
      · exact leaf 0 0 0 (by norm_num) (by norm_num) (by norm_num) hyp2 Prf.hyp1 Prf.hyp0
      · exact leaf 0 0 1 (by norm_num) (by norm_num) (by norm_num) hyp2 Prf.hyp1 Prf.hyp0
    · refine .orE (par_cases z) ?_ ?_
      · exact leaf 0 1 0 (by norm_num) (by norm_num) (by norm_num) hyp2 Prf.hyp1 Prf.hyp0
      · exact leaf 0 1 1 (by norm_num) (by norm_num) (by norm_num) hyp2 Prf.hyp1 Prf.hyp0
  · refine .orE (par_cases y) ?_ ?_
    · refine .orE (par_cases z) ?_ ?_
      · exact leaf 1 0 0 (by norm_num) (by norm_num) (by norm_num) hyp2 Prf.hyp1 Prf.hyp0
      · exact leaf 1 0 1 (by norm_num) (by norm_num) (by norm_num) hyp2 Prf.hyp1 Prf.hyp0
    · refine .orE (par_cases z) ?_ ?_
      · exact leaf 1 1 0 (by norm_num) (by norm_num) (by norm_num) hyp2 Prf.hyp1 Prf.hyp0
      · exact leaf 1 1 1 (by norm_num) (by norm_num) (by norm_num) hyp2 Prf.hyp1 Prf.hyp0

theorem sum_alg {x y z m ux uy uz rx ry rz : PTm k} (e : Γ ⊢[PRAAx] x * x + y * y + z * z ≐ (two * two) * m)
    (sx : Γ ⊢[PRAAx] x * x ≐ (two * two) * ux + rx) (sy : Γ ⊢[PRAAx] y * y ≐ (two * two) * uy + ry)
    (sz : Γ ⊢[PRAAx] z * z ≐ (two * two) * uz + rz) :
    Γ ⊢[PRAAx] (two * two) * m ≐ (two * two) * (ux + uy + uz) + (rx + ry + rz) := by
  ipra_lc natEq sx + natEq sy + natEq sz - natEq e

theorem half_alg {x y z m hx hy hz : PTm k} (e : Γ ⊢[PRAAx] x * x + y * y + z * z ≐ (two * two) * m)
    (ex : Γ ⊢[PRAAx] x ≐ two * hx + zero) (ey : Γ ⊢[PRAAx] y ≐ two * hy + zero)
    (ez : Γ ⊢[PRAAx] z ≐ two * hz + zero) :
    Γ ⊢[PRAAx] (two * two) * (hx * hx + hy * hy + hz * hz) ≐ (two * two) * m := by
  ipra_lc natEq e - (𝔞 x + 2 * 𝔞 hx) * natEq ex - (𝔞 y + 2 * 𝔞 hy) * natEq ey - (𝔞 z + 2 * 𝔞 hz) * natEq ez

/-- `x² + y² + z² = 4m` gives `(x/2)² + (y/2)² + (z/2)² = m`. -/
theorem halve {x y z m : PTm k} (e : Γ ⊢[PRAAx] x * x + y * y + z * z ≐ (two * two) * m) :
    Γ ⊢[PRAAx] half x * half x + half y * half y + half z * half z ≐ m := by
  have se := sum_alg e (sq_par x) (sq_par y) (sq_par z)
  refine .orE (bits_sum x y z) ?_ ?_
  · have hx : (((par x ≐ zero) ⋏ ((par y ≐ zero) ⋏ (par z ≐ zero))) :: Γ) ⊢[PRAAx] _ := Prf.hyp0
    have ex := (half_par x).eqTrans (congrAdd (.eqRefl _) (Prf.andE₁ hx))
    have ey := (half_par y).eqTrans (congrAdd (.eqRefl _) (Prf.andE₁ (Prf.andE₂ hx)))
    have ez := (half_par z).eqTrans (congrAdd (.eqRefl _) (Prf.andE₂ (Prf.andE₂ hx)))
    exact mul_cancel four_pos (half_alg e.wk ex ey ez)
  · have hs : ((le one (par x + par y + par z) ⋏ lt (par x + par y + par z) (two * two)) :: Γ) ⊢[PRAAx] _ :=
      Prf.hyp0
    exact .botE _ (four_absurd se.wk (Prf.andE₁ hs) (Prf.andE₂ hs))

/-! ## The induction -/

theorem base_alg (b : PTm k) :
    Γ ⊢[PRAAx] pw (two * two) zero * (num 8 * b + num 7) ≐ num 8 * b + num 7 :=
  (congrMul (pw_zero _) (.eqRefl _)).eqTrans (one_mul _)

theorem r3_base (b : PTm k) : Γ ⊢[PRAAx] R3 (pw (two * two) zero * (num 8 * b + num 7)) ≐ zero := by
  refine .orE (ex_cases r3B (bd (pw (two * two) zero * (num 8 * b + num 7)))
    (pw (two * two) zero * (num 8 * b + num 7))) Prf.hyp0 ?_
  have e := r3_elim (Prf.hyp0 (Γ := Γ) (φ := R3 (pw (two * two) zero * (num 8 * b + num 7)) ≐ one))
  have h7 := Prf.andE₂ (dmu (Γ := (R3 (pw (two * two) zero * (num 8 * b + num 7)) ≐ one) :: Γ)
    (num_pos (by norm_num)) (base_alg b) (num_lt (by norm_num : 7 < 8)))
  exact .botE _ (three_squares_open e h7)

theorem step_alg (a c : PTm k) :
    Γ ⊢[PRAAx] pw (two * two) (succ a) * c ≐ (two * two) * (pw (two * two) a * c) := by
  ipra_lc 𝔞 c * natEq (pw_succ (two * two) a)

theorem r3_step {a c : PTm k} (ih : Γ ⊢[PRAAx] R3 (pw (two * two) a * c) ≐ zero) :
    Γ ⊢[PRAAx] R3 (pw (two * two) (succ a) * c) ≐ zero := by
  refine .orE (ex_cases r3B (bd (pw (two * two) (succ a) * c)) (pw (two * two) (succ a) * c)) Prf.hyp0 ?_
  have e := r3_elim (Prf.hyp0 (Γ := Γ) (φ := R3 (pw (two * two) (succ a) * c) ≐ one))
  have r := r3_intro (halve (e.eqTrans (step_alg a c)))
  exact one_ne_zero _ (r.eqSymm.eqTrans ih.wk)

/-- Variables: `0 = a` (induction), `1 = b`. -/
private abbrev obsF : Fm PTm 2 := R3 (pw (two * two) (var 0) * (num 8 * var 1 + num 7)) ≐ zero

private theorem obs₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] obsF := by
  ipra_ind [subst_ap2, Syn.inst_succ, subst_num, Syn.repl_succ]
  · exact r3_base _
  · exact r3_step (Prf.hyp0 : [obsF] ⊢[PRAAx] _)

/-- `R3 (4^a (8b + 7)) = 0`. -/
theorem r3_zero (a b : PTm k) : Γ ⊢[PRAAx] R3 (pw (two * two) a * (num 8 * b + num 7)) ≐ zero := by
  simpa [subst_num] using inst (Γ := Γ) obs₀ (![a, b] : Fin 2 → PTm k)

/-- `qr:three-obstruction`: no `4^a (8b + 7)` is a sum of three squares. -/
theorem obstruction_open {a b x y z : PTm k}
    (e : Γ ⊢[PRAAx] x * x + y * y + z * z ≐ pw (two * two) a * (num 8 * b + num 7)) : Γ ⊢[PRAAx] Fm.bot :=
  one_ne_zero _ ((r3_intro e).eqSymm.eqTrans (r3_zero a b))

/-- `∀ a b x y z. x² + y² + z² = 4^a (8b + 7) → ⊥`; variables `0 = a`, `1 = b`, `2 = x`, `3 = y`, `4 = z`. -/
abbrev sentence : Fm PTm 0 :=
  univ 5 ((var 2 * var 2 + var 3 * var 3 + var 4 * var 4 ≐ pw (two * two) (var 0) * (num 8 * var 1 + num 7)) ⟶
    Fm.bot)

/-- **The three-square obstruction for `4^a (8b + 7)`** as a closed sentence of iPRA. -/
theorem three_square_obstruction_powers : ([] : List (Fm PTm 0)) ⊢[PRAAx] sentence :=
  closeUniv 5 (.impI (obstruction_open Prf.hyp0))

end LeanProofs.IPRA.DiophantineNumberTheory.ThreeSquaresPowers
