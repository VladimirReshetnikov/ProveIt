import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Algebra.QuadraticRingFive
import IPRADerivations.Core.CertificateTactics

/-!
# Irreducibility of `2`, `3` and `1 ± θ` in `ℤ[√−5]`

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/algebraic.tex`, Theorem `ag:nonufd`:
"In `R` the four elements `2, 3, 1 + θ, 1 − θ` are irreducible, and `6 = 2 · 3 = (1 + θ)(1 − θ)` are
factorizations with no matching associates. In particular `2` is irreducible but is not prime."

The packet reads irreducibility through the norm: "A nontrivial factorization of `2`, of norm `4`, would require
norms `2, 2` […]". Since the norm is multiplicative (`QuadraticExtension.norm_mul`), a factorization `u v` of an
element of norm `c` has `N(u) N(v) = c`. Here, with `N(a + bθ) = a² + 5b²` as in `QuadraticRingFive`:

* `ge_four_cases`, `norm_cases`: a norm is `0`, `1` or at least `4` (no norm is `2` or `3`);
* `core`: if `x`, `y` are each `0`, `1` or `≥ 4`, and `1 ≤ x y < 16`, then `x = 1` or `y = 1`;
* **`irreducible_two`**, **`irreducible_three`**, **`irreducible_theta`**: `N(u) N(v) = 4`, `9`, `6` give
  `N(u) = 1` or `N(v) = 1`, so that one factor is a unit (`QuadraticRingFive.unit_norm`: `u = ±1`);
* `norm_values`: `N(2) = 4`, `N(3) = 9`, `N(1 ± θ) = 6`;
* `norms_distinct`: `4 ≠ 6` and `9 ≠ 6`: neither `2` nor `3` is an associate of `1 ± θ` (associates have equal
  norms);
* **`two_not_dvd`**: `2a ≠ 1`: `2` divides neither `1 + θ` nor `1 − θ` (a multiple of `2` has even first
  coordinate), although it divides their product `6`; so `2` is not prime.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticRingFiveIrreducible

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.QuadraticRingFive (N5 no_norm_two no_norm_three)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The numeral `4`. -/
abbrev four : PTm n := succ (succ two)

/-! ## A norm is `0`, `1` or at least `4` -/

/-- A number that is neither `2` nor `3` is `0`, `1` or at least `4`. -/
theorem ge_four_cases (x : PTm n) (h2 : Γ ⊢[PRAAx] neg (x ≐ two)) (h3 : Γ ⊢[PRAAx] neg (x ≐ succ two)) :
    Γ ⊢[PRAAx] (x ≐ zero) ⋎ ((x ≐ one) ⋎ le four x) := by
  refine .orE (lt_or_le x four) ?_ (.orI₂ (.orI₂ Prf.hyp0))
  refine .orE (lt_succ_cases (Prf.hyp0 (Γ := Γ) (φ := lt x four))) ?_ ?_
  · refine .orE (lt_succ_cases (Prf.hyp0 (Γ := lt x four :: Γ) (φ := lt x (succ two)))) ?_ ?_
    · refine .orE (lt_succ_cases (Prf.hyp0 (Γ := lt x (succ two) :: lt x four :: Γ) (φ := lt x two))) ?_ ?_
      · refine .orE (lt_succ_cases
          (Prf.hyp0 (Γ := lt x two :: lt x (succ two) :: lt x four :: Γ) (φ := lt x one))) ?_ ?_
        · exact lt_zero_absurd _ Prf.hyp0
        · exact .orI₁ Prf.hyp0
      · exact .orI₂ (.orI₁ Prf.hyp0)
    · exact .botE _ (.impE h2.wk.wk.wk Prf.hyp0)
  · exact .botE _ (.impE h3.wk.wk Prf.hyp0)

/-- A norm is `0`, `1` or at least `4`. -/
theorem norm_cases (a b : PTm n) : Γ ⊢[PRAAx] (N5 a b ≐ zero) ⋎ ((N5 a b ≐ one) ⋎ le four (N5 a b)) :=
  ge_four_cases (N5 a b) (no_norm_two a b) (no_norm_three a b)

/-! ## Products below `16` -/

theorem zero_l {x y c : PTm n} (x0 : Γ ⊢[PRAAx] x ≐ zero) (h : Γ ⊢[PRAAx] x * y ≐ c)
    (hc1 : Γ ⊢[PRAAx] le one c) : Γ ⊢[PRAAx] Fm.bot := by
  have a := natEq x0; have hn := natEq h
  have bad : Γ ⊢[PRAAx] le one zero := by
    ipra_le sl hc1 with hn - 𝔞 y * a
  exact lt_zero_absurd _ bad

theorem zero_r {x y c : PTm n} (y0 : Γ ⊢[PRAAx] y ≐ zero) (h : Γ ⊢[PRAAx] x * y ≐ c)
    (hc1 : Γ ⊢[PRAAx] le one c) : Γ ⊢[PRAAx] Fm.bot := by
  have a := natEq y0; have hn := natEq h
  have bad : Γ ⊢[PRAAx] le one zero := by
    ipra_le sl hc1 with hn - 𝔞 x * a
  exact lt_zero_absurd _ bad

theorem big {x y c : PTm n} (hx : Γ ⊢[PRAAx] le four x) (hy : Γ ⊢[PRAAx] le four y)
    (h : Γ ⊢[PRAAx] x * y ≐ c) (hc : Γ ⊢[PRAAx] lt c (four * four)) : Γ ⊢[PRAAx] Fm.bot := by
  have hn := natEq h
  have bad : Γ ⊢[PRAAx] le one zero := by
    ipra_le sl hx * sl hy + 4 * sl hx + 4 * sl hy + sl hc with -hn
  exact lt_zero_absurd _ bad

/-- If `x`, `y` are each `0`, `1` or `≥ 4` and `1 ≤ x y < 16`, then `x = 1` or `y = 1`. -/
theorem core {x y c : PTm n} (hx : Γ ⊢[PRAAx] (x ≐ zero) ⋎ ((x ≐ one) ⋎ le four x))
    (hy : Γ ⊢[PRAAx] (y ≐ zero) ⋎ ((y ≐ one) ⋎ le four y)) (h : Γ ⊢[PRAAx] x * y ≐ c)
    (hc1 : Γ ⊢[PRAAx] le one c) (hc : Γ ⊢[PRAAx] lt c (four * four)) :
    Γ ⊢[PRAAx] (x ≐ one) ⋎ (y ≐ one) := by
  refine .orE hx (.botE _ (zero_l Prf.hyp0 h.wk hc1.wk)) ?_
  refine .orE Prf.hyp0 (.orI₁ Prf.hyp0) ?_
  refine .orE hy.wk.wk (.botE _ (zero_r Prf.hyp0 h.wk.wk.wk hc1.wk.wk.wk)) ?_
  refine .orE Prf.hyp0 (.orI₂ Prf.hyp0) ?_
  exact .botE _ (big hyp2 Prf.hyp0 h.wk.wk.wk.wk hc.wk.wk.wk.wk)

/-! ## The three norms -/

theorem one_le_4 : Γ ⊢[PRAAx] le (one : PTm n) (two * two) :=
  le_of_eq_add (d := succ two) (by ipra_ring)

theorem lt_4 : Γ ⊢[PRAAx] lt (two * two : PTm n) (four * four) :=
  le_of_eq_add (d := num 11) (by apply deriveNat; ipra_simps; push_cast; ring)

theorem one_le_9 : Γ ⊢[PRAAx] le (one : PTm n) (succ two * succ two) :=
  le_of_eq_add (d := num 8) (by apply deriveNat; ipra_simps; push_cast; ring)

theorem lt_9 : Γ ⊢[PRAAx] lt (succ two * succ two : PTm n) (four * four) :=
  le_of_eq_add (d := num 6) (by apply deriveNat; ipra_simps; push_cast; ring)

theorem one_le_6 : Γ ⊢[PRAAx] le (one : PTm n) (two * succ two) :=
  le_of_eq_add (d := num 5) (by apply deriveNat; ipra_simps; push_cast; ring)

theorem lt_6 : Γ ⊢[PRAAx] lt (two * succ two : PTm n) (four * four) :=
  le_of_eq_add (d := num 9) (by apply deriveNat; ipra_simps; push_cast; ring)

/-- **`2` is irreducible**: `N(u) N(v) = 4` gives `N(u) = 1` or `N(v) = 1`. -/
theorem irreducible_two {a b c d : PTm n} (h : Γ ⊢[PRAAx] N5 a b * N5 c d ≐ two * two) :
    Γ ⊢[PRAAx] (N5 a b ≐ one) ⋎ (N5 c d ≐ one) :=
  core (norm_cases a b) (norm_cases c d) h one_le_4 lt_4

/-- **`3` is irreducible**: `N(u) N(v) = 9` gives `N(u) = 1` or `N(v) = 1`. -/
theorem irreducible_three {a b c d : PTm n} (h : Γ ⊢[PRAAx] N5 a b * N5 c d ≐ succ two * succ two) :
    Γ ⊢[PRAAx] (N5 a b ≐ one) ⋎ (N5 c d ≐ one) :=
  core (norm_cases a b) (norm_cases c d) h one_le_9 lt_9

/-- **`1 ± θ` are irreducible**: `N(u) N(v) = 6` gives `N(u) = 1` or `N(v) = 1`. -/
theorem irreducible_theta {a b c d : PTm n} (h : Γ ⊢[PRAAx] N5 a b * N5 c d ≐ two * succ two) :
    Γ ⊢[PRAAx] (N5 a b ≐ one) ⋎ (N5 c d ≐ one) :=
  core (norm_cases a b) (norm_cases c d) h one_le_6 lt_6

/-- `N(2) = 4`, `N(3) = 9`, `N(1 ± θ) = 6`. -/
theorem norm_values :
    Γ ⊢[PRAAx] (N5 (two : PTm n) zero ≐ two * two) ⋏ ((N5 (succ two : PTm n) zero ≐ succ two * succ two) ⋏
      (N5 (one : PTm n) one ≐ two * succ two)) := by
  refine .andI ?_ (.andI ?_ ?_)
  · ipra_lc
  · ipra_lc
  · ipra_lc

/-! ## No matching associates, and `2` is not prime -/

/-- `4 ≠ 6` and `9 ≠ 6`: neither `2` nor `3` has the norm of `1 ± θ`. -/
theorem norms_distinct :
    Γ ⊢[PRAAx] neg ((two * two : PTm n) ≐ two * succ two) ⋏ neg ((succ two * succ two : PTm n) ≐ two * succ two) := by
  refine .andI (.impI ?_) (.impI ?_)
  · have e := natEq (Prf.hyp0 (Γ := Γ) (φ := (two * two : PTm n) ≐ two * succ two))
    refine succ_ne_zero' _ (a := one) ?_
    ipra_lc -e
  · have e := natEq (Prf.hyp0 (Γ := Γ) (φ := (succ two * succ two : PTm n) ≐ two * succ two))
    refine succ_ne_zero' _ (a := two) ?_
    ipra_lc e

/-- **`2` is not prime**: `2a ≠ 1`, so `2` divides neither `1 + θ` nor `1 − θ`. -/
theorem two_not_dvd (a : PTm n) : Γ ⊢[PRAAx] neg (two * a ≐ one) := by
  refine .impI ?_
  have e : ((two * a ≐ one) :: Γ) ⊢[PRAAx] two * a ≐ one := Prf.hyp0
  refine .orE (zero_or_succ a) ?_ ?_
  · have x := natEq (e.wk (ψ := a ≐ zero))
    refine succ_ne_zero' _ (a := zero) ?_
    ipra_lc -x + 2 * natEq (Prf.hyp0 (Γ := (two * a ≐ one) :: Γ) (φ := a ≐ zero))
  · have x := natEq (e.wk (ψ := a ≐ succ (pred a)))
    refine succ_ne_zero' _ (a := two * pred a) ?_
    ipra_lc x - 2 * natEq (Prf.hyp0 (Γ := (two * a ≐ one) :: Γ) (φ := a ≐ succ (pred a)))

end LeanProofs.IPRA.Algebra.QuadraticRingFiveIrreducible
