import IPRADerivations.Foundations.NumeralPrimes

/-!
# The three-square obstruction

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/quadratic.tex`, "The three-square
obstruction and optimality": a number `n ≡ 7 (mod 8)` is not a sum of three squares.

* `sq_ee`, `sq_eo`, `sq_oe`, `sq_oo`: by the parities of `x` and of `⌊x/2⌋`, `x² = 8u + e` with `e ∈ {0, 4, 1, 1}`;
* `sq_cases`: the case analysis, passing the residue `e ∈ {0, 1, 4}` (a number of the metatheory) and the
  quotient `u` to a continuation;
* `num_ne`: distinct numerals are different;
* `comb`: three squares with residues `e₁, e₂, e₃` sum to `n` with `n mod 8 = (e₁ + e₂ + e₃) mod 8`, which is
  not `7` (the 27 combinations are checked by `decide` in the metatheory);
* `three_squares_open`, and the closed sentence **`three_square_obstruction`**:
  `∀ a b c n. a² + b² + c² = n → n mod 8 = 7 → ⊥`.

With `FourSquares.lagrange` this is the optimality of four squares: every number is a sum of four squares, and
the numbers `8k + 7` are not sums of three.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.ThreeSquares

open_ipra exports
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dmu)
open LeanProofs.IPRA.Foundations.NumeralPrimes (num_lt num_pos)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## Squares modulo `8` -/

theorem sq_ee {x h g : PTm k} (ex : Γ ⊢[PRAAx] x ≐ two * h) (eh : Γ ⊢[PRAAx] h ≐ two * g) :
    Γ ⊢[PRAAx] x * x ≐ num 8 * (two * (g * g)) + num 0 := by
  ipra_lc (𝔞 x + 2 * 𝔞 h) * natEq ex + 4 * (𝔞 h + 2 * 𝔞 g) * natEq eh

theorem sq_eo {x h g : PTm k} (ex : Γ ⊢[PRAAx] x ≐ two * h) (eh : Γ ⊢[PRAAx] h ≐ two * g + one) :
    Γ ⊢[PRAAx] x * x ≐ num 8 * (two * (g * g) + two * g) + num 4 := by
  ipra_lc (𝔞 x + 2 * 𝔞 h) * natEq ex + 4 * (𝔞 h + 2 * 𝔞 g + 1) * natEq eh

theorem sq_oe {x h g : PTm k} (ex : Γ ⊢[PRAAx] x ≐ two * h + one) (eh : Γ ⊢[PRAAx] h ≐ two * g) :
    Γ ⊢[PRAAx] x * x ≐ num 8 * (g * (two * g + one)) + num 1 := by
  ipra_lc (𝔞 x + 2 * 𝔞 h + 1) * natEq ex + 4 * (𝔞 h + 2 * 𝔞 g + 1) * natEq eh

theorem sq_oo {x h g : PTm k} (ex : Γ ⊢[PRAAx] x ≐ two * h + one) (eh : Γ ⊢[PRAAx] h ≐ two * g + one) :
    Γ ⊢[PRAAx] x * x ≐ num 8 * ((two * g + one) * (g + one)) + num 1 := by
  ipra_lc (𝔞 x + 2 * 𝔞 h + 1) * natEq ex + 4 * (𝔞 h + 2 * 𝔞 g + 2) * natEq eh

/-- A square is `8u + e` with `e ∈ {0, 1, 4}`. -/
theorem sq_cases {φ : Fm PTm k} (x : PTm k)
    (K : ∀ (e : ℕ), (e = 0 ∨ e = 1 ∨ e = 4) → ∀ (u : PTm k) (Δ : List (Fm PTm k)), Γ ⊆ Δ →
      (Δ ⊢[PRAAx] x * x ≐ num 8 * u + num e) → (Δ ⊢[PRAAx] φ)) : Γ ⊢[PRAAx] φ := by
  refine .orE (even_or_odd x) ?_ ?_
  · refine .orE (even_or_odd (half x)) ?_ ?_
    · exact K 0 (Or.inl rfl) _ _ (by intro a ha; simp [ha]) (sq_ee Prf.hyp1 Prf.hyp0)
    · exact K 4 (Or.inr (Or.inr rfl)) _ _ (by intro a ha; simp [ha]) (sq_eo Prf.hyp1 Prf.hyp0)
  · refine .orE (even_or_odd (half x)) ?_ ?_
    · exact K 1 (Or.inr (Or.inl rfl)) _ _ (by intro a ha; simp [ha]) (sq_oe Prf.hyp1 Prf.hyp0)
    · exact K 1 (Or.inr (Or.inl rfl)) _ _ (by intro a ha; simp [ha]) (sq_oo Prf.hyp1 Prf.hyp0)

/-! ## Numerals -/

/-- Distinct numerals are different. -/
theorem num_ne {a b : ℕ} (h : a ≠ b) (e : Γ ⊢[PRAAx] (num a : PTm k) ≐ num b) : Γ ⊢[PRAAx] Fm.bot := by
  rcases Nat.lt_or_gt_of_ne h with hlt | hgt
  · exact lt_irrefl (num b) _ (lt_congr e (.eqRefl _) (num_lt hlt))
  · exact lt_irrefl (num b) _ (lt_congr (.eqRefl _) e (num_lt hgt))

/-! ## Three residues -/

theorem comb {a b c n u1 u2 u3 : PTm k} (e1 e2 e3 : ℕ) (hS : (e1 + e2 + e3) % 8 ≠ 7)
    (h1 : Γ ⊢[PRAAx] a * a ≐ num 8 * u1 + num e1) (h2 : Γ ⊢[PRAAx] b * b ≐ num 8 * u2 + num e2)
    (h3 : Γ ⊢[PRAAx] c * c ≐ num 8 * u3 + num e3) (hn : Γ ⊢[PRAAx] a * a + b * b + c * c ≐ n)
    (h7 : Γ ⊢[PRAAx] rem n (num 8) ≐ num 7) : Γ ⊢[PRAAx] Fm.bot := by
  have key : e1 + e2 + e3 = 8 * ((e1 + e2 + e3) / 8) + (e1 + e2 + e3) % 8 := (Nat.div_add_mod _ 8).symm
  have hz : Γ ⊢[PRAAx] n ≐ num 8 * (u1 + u2 + u3 + num ((e1 + e2 + e3) / 8)) + num ((e1 + e2 + e3) % 8) := by
    have x1 := natEq h1; have x2 := natEq h2; have x3 := natEq h3; have xn := natEq hn
    apply deriveNat; ipra_simps
    have k2 := congrArg (fun t : ℕ => (t : Groth (Q Γ))) key
    push_cast at k2 x1 x2 x3 ⊢
    linear_combination x1 + x2 + x3 - xn + k2
  have r := Prf.andE₂ (dmu (num_pos (by norm_num)) hz (num_lt (Nat.mod_lt _ (by norm_num))))
  exact num_ne hS (r.eqSymm.eqTrans h7)

/-- A sum of three squares is not `≡ 7 (mod 8)`. -/
theorem three_squares_open {a b c n : PTm k} (hn : Γ ⊢[PRAAx] a * a + b * b + c * c ≐ n)
    (h7 : Γ ⊢[PRAAx] rem n (num 8) ≐ num 7) : Γ ⊢[PRAAx] Fm.bot := by
  refine sq_cases a (fun e1 he1 u1 _ s1 h1 => ?_)
  refine sq_cases b (fun e2 he2 u2 _ s2 h2 => ?_)
  refine sq_cases c (fun e3 he3 u3 _ s3 h3 => ?_)
  have hS : (e1 + e2 + e3) % 8 ≠ 7 := by
    rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl <;> rcases he3 with rfl | rfl | rfl <;>
      decide
  exact comb e1 e2 e3 hS ((h1.weaken s2).weaken s3) (h2.weaken s3) h3
    (((hn.weaken s1).weaken s2).weaken s3) (((h7.weaken s1).weaken s2).weaken s3)

/-- `∀ a b c n. a² + b² + c² = n → n mod 8 = 7 → ⊥`; variables `0 = n`, `1 = a`, `2 = b`, `3 = c`. -/
abbrev sentence : Fm PTm 0 :=
  univ 4 ((var 1 * var 1 + var 2 * var 2 + var 3 * var 3 ≐ var 0) ⟶ (rem (var 0) (num 8) ≐ num 7) ⟶ Fm.bot)

/-- **The three-square obstruction** as a closed sentence of iPRA. -/
theorem three_square_obstruction : ([] : List (Fm PTm 0)) ⊢[PRAAx] sentence :=
  closeUniv 4 (.impI (.impI (three_squares_open Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.DiophantineNumberTheory.ThreeSquares
