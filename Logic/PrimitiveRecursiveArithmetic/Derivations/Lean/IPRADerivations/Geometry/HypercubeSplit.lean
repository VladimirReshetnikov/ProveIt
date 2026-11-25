import IPRADerivations.Core.Tactic
import IPRADerivations.Core.ProdLemmas
import IPRADerivations.Core.SumOrder
import IPRADerivations.AnalyticNumberTheory.LocalFactor
import IPRADerivations.AnalyticNumberTheory.PowerCleared
import IPRADerivations.Probability.Expectation
import IPRADerivations.Core.LinearCombination

/-!
# The split inequality of the hypercube edge theorem

Packet: `geometry/isoperimetric_ipra_constructive_2026-11-15` (hypercube part: the finite AM–GM
lemma for two and four inputs, `lem:cube-split`, the induction step of `thm:cube-edge`;
Euclidean part: `lem:box-product` for two factors). Powers are `pw a m = a^m`, with `0^0 = 1`.

* `amgm2`, `amgm4`: `4 u v ≤ (u + v)²` and `256 x₁ x₂ x₃ x₄ ≤ (x₁ + x₂ + x₃ + x₄)⁴`, the first
  two levels of the binary tree in the packet's proof;
* `box_product2`: `q² ≤ t₁ t₂` gives `(D + q)² ≤ (D + t₁)(D + t₂)`, the two-factor product
  inequality for fractions with the common denominator `D`;
* `bernoulli`: `(y + 1)^(n+1) ≤ y^n (y + 1) + n (y + 1)^n`, i.e.
  `(1 − 1/(y+1))^n ≥ 1 − n/(y+1)` without subtraction;
* `log_convex`: `((x + 1)^(x+1))² ≤ (x + 2)^(x+2) · x^x`, the discrete log-convexity of `x^x`;
* `chain`: `(a + 1)^(a+1) (a + b)^(a+b) ≤ (a + b + 1)^(a+b+1) a^a`;
* `split_eq`: `4^b b^b b^b = (2b)^(2b)`, the equality case `a = b`;
* `cube_split`: for `b ≤ a`, `4^b a^a b^b ≤ (a + b)^(a+b)`;
* `edge_step`: from `2^(2e₀) ≤ a^a`, `2^(2e₁) ≤ b^b`, `c ≤ b ≤ a`:
  `2^(2(e₀ + e₁ + c)) ≤ (a + b)^(a+b)`, the induction step of `thm:cube-edge` for sections of
  sizes `a, b` with `c` common vertices.
* `subcube_eq`: `2^(r · 2^r) = (2^r)^(2^r)`, the equality case for a subcube;
* `edge_integer_form`: with `d k = 2e + b`, `2^(2e) ≤ k^k` reads `2^(d k) ≤ 2^b k^k`;
* `half_cube_expansion`: if moreover `k ≤ 2^(d−1)`, then `b ≥ k` (sharp expansion at half
  volume).

The packet derives the split inequality from AM–GM with padding. Here it follows from
log-convexity, which follows from Bernoulli's inequality at `y + 1 = (x + 1)²`, `n = x + 1`.
The equality classification, the induction over subsets of the cube and the Euclidean
(Brunn–Minkowski) part are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.HypercubeSplit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (four_mul_le two_mul_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples (pw_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {N : ℕ} {Γ : List (Fm PTm N)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `4 = 2 · 2`. -/
abbrev four {N : ℕ} : PTm N := two * two

/-! ## Helpers -/

theorem pw_congr {a a' m m' : PTm N} (ha : Γ ⊢[PRAAx] a ≐ a') (hm : Γ ⊢[PRAAx] m ≐ m') :
    Γ ⊢[PRAAx] pw a m ≐ pw a' m' := congrAp2 powF hm ha

/-- Cancellation of a positive factor in `≤`. -/
theorem le_cancel_pos {c a b : PTm N} (hc : Γ ⊢[PRAAx] c ≐ succ (pred c))
    (h : Γ ⊢[PRAAx] le (c * a) (c * b)) : Γ ⊢[PRAAx] le a b :=
  mul_le_cancel (le_congr (congrMul hc (.eqRefl _)) (congrMul hc (.eqRefl _)) h)

theorem le_mul_pos (u : PTm N) {v : PTm N} (hv : Γ ⊢[PRAAx] v ≐ succ (pred v)) :
    Γ ⊢[PRAAx] le u (u * v) := by
  refine le_of_eq_add (d := u * pred v) ?_
  ipra_lc 𝔞(u) * natEq hv

/-- `x^x ≥ 1`, with `0^0 = 1`. -/
theorem pw_self_pos (x : PTm N) : Γ ⊢[PRAAx] pw x x ≐ succ (pred (pw x x)) := by
  refine .orE (zero_or_succ x) ?_ ?_
  · exact pos_of_eq_succ (c := zero) ((pw_congr Prf.hyp0 Prf.hyp0).eqTrans (pw_zero zero))
  · exact pos_of_eq_succ ((pw_congr Prf.hyp0 (.eqRefl x)).eqTrans (pw_pos (pred x) x))

/-! ## AM–GM for two and four inputs, and the two-factor product inequality -/

theorem amgm2 (u v : PTm N) : Γ ⊢[PRAAx] le (four * (u * v)) ((u + v) * (u + v)) := four_mul_le u v

theorem amgm4 (x₁ x₂ x₃ x₄ : PTm N) :
    Γ ⊢[PRAAx] le (four * four * (four * four) * (x₁ * x₂ * (x₃ * x₄)))
      ((x₁ + x₂ + (x₃ + x₄)) * (x₁ + x₂ + (x₃ + x₄)) * ((x₁ + x₂ + (x₃ + x₄)) * (x₁ + x₂ + (x₃ + x₄)))) := by
  have hA := four_mul_le (Γ := Γ) x₁ x₂; have hB := four_mul_le (Γ := Γ) x₃ x₄
  have hC := four_mul_le (Γ := Γ) (x₁ + x₂) (x₃ + x₄)
  have hAB := mul_le_mul_right (four * four) (le_mul_mono hA hB)
  have hCC := le_mul_mono hC hC
  refine le_trans (le_congr ?_ ?_ hAB) (le_congr (.eqRefl _) (.eqRefl _) hCC)
  all_goals (ipra_ring)

/-- `lem:box-product` for two factors: with `tᵢ = Tᵢ / D` and `q = Q / D`, `t₁ t₂ ≥ q²` gives
`(1 + t₁)(1 + t₂) ≥ (1 + q)²`. -/
theorem box_product2 {q t₁ t₂ : PTm N} (D : PTm N) (h : Γ ⊢[PRAAx] le (q * q) (t₁ * t₂)) :
    Γ ⊢[PRAAx] le ((D + q) * (D + q)) ((D + t₁) * (D + t₂)) := by
  have h2 := two_mul_le h
  have m := add_le_add₂ (add_le_add₂ (le_refl (D * D)) (mul_le_mul_right D h2)) h
  refine le_congr ?_ ?_ m
  all_goals (ipra_ring)

/-! ## Bernoulli's inequality -/

theorem bern_base (y : PTm N) :
    Γ ⊢[PRAAx] le (pw (succ y) (succ zero)) (pw y zero * succ y + zero * pw (succ y) zero) := by
  refine le_of_eq_add (d := zero) ?_
  ipra_lc (𝔞(y) + 1) * natEq (pw_zero (Γ := Γ) y) - natEq (pw_succ (Γ := Γ) (succ y) zero) -
    (𝔞(y) + 1) * natEq (pw_zero (Γ := Γ) (succ y))

theorem bern_step {y k : PTm N}
    (ih : Γ ⊢[PRAAx] le (pw (succ y) (succ k)) (pw y k * succ y + k * pw (succ y) k)) :
    Γ ⊢[PRAAx] le (pw (succ y) (succ (succ k)))
      (pw y (succ k) * succ y + succ k * pw (succ y) (succ k)) := by
  refine le_of_eq_add (d := y * monus (pw y k * succ y + k * pw (succ y) k) (pw (succ y) (succ k)) +
    k * pw (succ y) k) ?_
  ipra_lc (𝔞(y) + 1) * natEq (pw_succ (Γ := Γ) y k) - natEq (pw_succ (Γ := Γ) (succ y) (succ k)) +
    𝔞(y) * natEq (eq_add_of_le ih) + 𝔞(k) * natEq (pw_succ (Γ := Γ) (succ y) k)

/-- Variables: `0 = k` (induction), `1 = y`. -/
private abbrev bernF : Fm PTm 2 :=
  le (pw (succ (var 1)) (succ (var 0))) (pw (var 1) (var 0) * succ (var 1) + var 0 * pw (succ (var 1)) (var 0))

private theorem bern₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] bernF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact bern_base _
  · simp only [subst_le, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact bern_step Prf.hyp0

/-- `(y + 1)^(k+1) ≤ y^k (y + 1) + k (y + 1)^k`. -/
theorem bernoulli (y k : PTm N) :
    Γ ⊢[PRAAx] le (pw (succ y) (succ k)) (pw y k * succ y + k * pw (succ y) k) := by
  have h := inst (Γ := Γ) bern₀ (![k, y] : Fin 2 → PTm N)
  simpa using h

/-! ## Log-convexity of `x^x` -/

theorem lc_zero : Γ ⊢[PRAAx] le (pw (succ zero) (succ zero) * pw (succ zero) (succ zero))
    (pw (succ (succ zero)) (succ (succ zero)) * pw (zero : PTm N) zero) := by
  refine le_of_eq_add (d := succ (succ (succ zero))) ?_
  ipra_lc 𝔞(pw (zero : PTm N) zero) * natEq (pw_succ (Γ := Γ) (succ (succ zero)) (succ zero)) +
    2 * 𝔞(pw (zero : PTm N) zero) * natEq (pw_one (Γ := Γ) (succ (succ zero))) + 4 * natEq (pw_zero (Γ := Γ) zero) -
    (𝔞(pw (succ (zero : PTm N)) (succ zero)) + 1) * natEq (pw_one (Γ := Γ) (succ zero))

/-- The positive case, from Bernoulli at `y = x (x + 2)`, `n = x + 1`. -/
theorem lc_pos {x : PTm N} (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) :
    Γ ⊢[PRAAx] le (pw (succ x) (succ x) * pw (succ x) (succ x))
      (pw (succ (succ x)) (succ (succ x)) * pw x x) := by
  -- `y + 1 = n²`.
  have s : Γ ⊢[PRAAx] succ (x * succ (succ x)) ≐ succ x * succ x := by
    ipra_ring
  have B0 := bernoulli (Γ := Γ) (x * succ (succ x)) (succ x)
  -- `W n² ≤ A n² + n W`, with `W = (n²)^n`, `A = y^n`.
  have B1 : Γ ⊢[PRAAx] le (pw (succ x * succ x) (succ x) * (succ x * succ x))
      (pw (x * succ (succ x)) (succ x) * (succ x * succ x) + succ x * pw (succ x * succ x) (succ x)) :=
    le_congr ((pw_succ _ _).eqTrans (congrMul (pw_congr s (.eqRefl _)) s))
      (congrAdd (congrMul (.eqRefl _) s) (congrMul (.eqRefl _) (pw_congr s (.eqRefl _)))) B0
  have B2 : Γ ⊢[PRAAx] le (succ x * (pw (succ x * succ x) (succ x) * x) + succ x * pw (succ x * succ x) (succ x))
      (succ x * (pw (x * succ (succ x)) (succ x) * succ x) + succ x * pw (succ x * succ x) (succ x)) := by
    refine le_congr ?_ ?_ B1
    all_goals (ipra_ring)
  -- `W x ≤ A n`.
  have B3 : Γ ⊢[PRAAx] le (pw (succ x * succ x) (succ x) * x) (pw (x * succ (succ x)) (succ x) * succ x) :=
    mul_le_cancel (le_of_add_le_add_right B2)
  have e₄ : Γ ⊢[PRAAx] pw (succ x * succ x) (succ x) * x ≐
      x * (pw (succ x) (succ x) * pw (succ x) (succ x)) := by
    ipra_lc 𝔞(x) * natEq (pw_mul_base (Γ := Γ) (succ x) (succ x) (succ x))
  have e₅ : Γ ⊢[PRAAx] pw (x * succ (succ x)) (succ x) * succ x ≐
      x * (pw x x * pw (succ (succ x)) (succ x) * succ x) := by
    ipra_lc (𝔞(x) + 1) * natEq (pw_mul_base (Γ := Γ) x (succ (succ x)) (succ x)) +
      𝔞(pw (succ (succ x)) (succ x)) * (𝔞(x) + 1) * natEq (pw_succ (Γ := Γ) x x)
  have B5 : Γ ⊢[PRAAx] le (pw (succ x) (succ x) * pw (succ x) (succ x))
      (pw x x * pw (succ (succ x)) (succ x) * succ x) := le_cancel_pos hx (le_congr e₄ e₅ B3)
  refine le_trans B5 (le_of_eq_add (d := pw x x * pw (succ (succ x)) (succ x)) ?_)
  ipra_lc 𝔞(pw x x) * natEq (pw_succ (Γ := Γ) (succ (succ x)) (succ x))

/-- Variable: `0 = x`. The induction is used only as a case distinction. -/
private abbrev lcF : Fm PTm 1 :=
  le (pw (succ (var 0)) (succ (var 0)) * pw (succ (var 0)) (succ (var 0)))
    (pw (succ (succ (var 0))) (succ (succ (var 0))) * pw (var 0) (var 0))

private theorem lc₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] lcF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.inst_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact lc_zero
  · simp only [subst_le, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.repl_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact lc_pos (pos_of_eq_succ (.eqRefl _))

/-- `((x + 1)^(x+1))² ≤ (x + 2)^(x+2) · x^x`. -/
theorem log_convex (x : PTm N) :
    Γ ⊢[PRAAx] le (pw (succ x) (succ x) * pw (succ x) (succ x))
      (pw (succ (succ x)) (succ (succ x)) * pw x x) := by
  have h := inst (Γ := Γ) lc₀ (![x] : Fin 1 → PTm N)
  simpa using h

/-! ## The chain `h(a) ≤ h(a + b)` for `h(x) = (x + 1)^(x+1) / x^x` -/

theorem chain_step {a x : PTm N}
    (ih : Γ ⊢[PRAAx] le (pw (succ a) (succ a) * pw x x) (pw (succ x) (succ x) * pw a a)) :
    Γ ⊢[PRAAx] le (pw (succ a) (succ a) * pw (succ x) (succ x))
      (pw (succ (succ x)) (succ (succ x)) * pw a a) := by
  have c := log_convex (Γ := Γ) x
  have h₁ := le_mul_mono ih (le_refl (pw (succ x) (succ x)))
  have h₂ := le_mul_mono c (le_refl (pw a a))
  refine le_cancel_pos (pw_self_pos x) ?_
  refine le_trans (le_congr ?_ ?_ h₁) (le_congr (.eqRefl _) ?_ h₂)
  all_goals (ipra_ring)

theorem chain_base (a : PTm N) :
    Γ ⊢[PRAAx] le (pw (succ a) (succ a) * pw (a + zero) (a + zero))
      (pw (succ (a + zero)) (succ (a + zero)) * pw a a) := by
  have z := (add_zero (Γ := Γ) a).eqSymm
  exact le_congr (congrMul (.eqRefl _) (pw_congr z z))
    (congrMul (pw_congr (congrSucc z) (congrSucc z)) (.eqRefl _)) (le_refl _)

theorem chain_succ {a b : PTm N}
    (ih : Γ ⊢[PRAAx] le (pw (succ a) (succ a) * pw (a + b) (a + b))
      (pw (succ (a + b)) (succ (a + b)) * pw a a)) :
    Γ ⊢[PRAAx] le (pw (succ a) (succ a) * pw (a + succ b) (a + succ b))
      (pw (succ (a + succ b)) (succ (a + succ b)) * pw a a) := by
  have s := (add_succ (Γ := Γ) a b).eqSymm
  exact le_congr (congrMul (.eqRefl _) (pw_congr s s))
    (congrMul (pw_congr (congrSucc s) (congrSucc s)) (.eqRefl _)) (chain_step ih)

/-- Variables: `0 = b` (induction), `1 = a`. -/
private abbrev chF : Fm PTm 2 :=
  le (pw (succ (var 1)) (succ (var 1)) * pw (var 1 + var 0) (var 1 + var 0))
    (pw (succ (var 1 + var 0)) (succ (var 1 + var 0)) * pw (var 1) (var 1))

private theorem ch₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] chF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact chain_base _
  · simp only [subst_le, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact chain_succ Prf.hyp0

/-- `(a + 1)^(a+1) (a + b)^(a+b) ≤ (a + b + 1)^(a+b+1) a^a`. -/
theorem chain (a b : PTm N) :
    Γ ⊢[PRAAx] le (pw (succ a) (succ a) * pw (a + b) (a + b))
      (pw (succ (a + b)) (succ (a + b)) * pw a a) := by
  have h := inst (Γ := Γ) ch₀ (![b, a] : Fin 2 → PTm N)
  simpa using h

/-! ## The split inequality -/

theorem four_pow (b : PTm N) : Γ ⊢[PRAAx] pw four b ≐ pw two b * pw two b := pw_mul_base two two b

/-- The equality case: `4^b b^b b^b = (2b)^(2b)`. -/
theorem split_eq (b : PTm N) : Γ ⊢[PRAAx] pw four b * pw b b * pw b b ≐ pw (b + b) (b + b) := by
  have t : Γ ⊢[PRAAx] b + b ≐ two * b := by ipra_ring
  ipra_lc 𝔞(pw b b) * 𝔞(pw b b) * natEq (four_pow (Γ := Γ) b) - natEq (pw_add (Γ := Γ) (b + b) b b) -
    (𝔞(pw (b + b) b) + 𝔞(pw two b) * 𝔞(pw b b)) * natEq ((pw_congr t (.eqRefl b)).eqTrans (pw_mul_base two b b))

theorem split_step {a b : PTm N}
    (ih : Γ ⊢[PRAAx] le (pw four b * pw a a * pw b b) (pw (a + b) (a + b))) :
    Γ ⊢[PRAAx] le (pw four b * pw (succ a) (succ a) * pw b b) (pw (succ (a + b)) (succ (a + b))) := by
  have c := chain (Γ := Γ) a b
  have h₁ := le_mul_mono ih (le_refl (pw (succ a) (succ a)))
  refine le_cancel_pos (pw_self_pos a) ?_
  refine le_trans (le_congr ?_ ?_ h₁) (le_congr (.eqRefl _) ?_ c)
  all_goals (ipra_ring)

theorem split_base (b : PTm N) :
    Γ ⊢[PRAAx] le (pw four b * pw (b + zero) (b + zero) * pw b b) (pw (b + zero + b) (b + zero + b)) := by
  have z := (add_zero (Γ := Γ) b).eqSymm
  have z' : Γ ⊢[PRAAx] b + b ≐ b + zero + b := congrAdd z (.eqRefl b)
  refine le_congr (congrMul (congrMul (.eqRefl _) (pw_congr z z)) (.eqRefl _)) (pw_congr z' z') ?_
  exact le_congr (.eqRefl _) (split_eq b) (le_refl _)

theorem split_succ {b d : PTm N}
    (ih : Γ ⊢[PRAAx] le (pw four b * pw (b + d) (b + d) * pw b b) (pw (b + d + b) (b + d + b))) :
    Γ ⊢[PRAAx] le (pw four b * pw (b + succ d) (b + succ d) * pw b b)
      (pw (b + succ d + b) (b + succ d + b)) := by
  have s := (add_succ (Γ := Γ) b d).eqSymm
  have s' : Γ ⊢[PRAAx] succ (b + d + b) ≐ b + succ d + b := by ipra_ring
  exact le_congr (congrMul (congrMul (.eqRefl _) (pw_congr s s)) (.eqRefl _)) (pw_congr s' s')
    (split_step ih)

/-- Variables: `0 = d` (induction), `1 = b`. -/
private abbrev spF : Fm PTm 2 :=
  le (pw four (var 1) * pw (var 1 + var 0) (var 1 + var 0) * pw (var 1) (var 1))
    (pw (var 1 + var 0 + var 1) (var 1 + var 0 + var 1))

private theorem sp₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] spF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact split_base _
  · simp only [subst_le, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact split_succ Prf.hyp0

/-- `4^b (b + d)^(b+d) b^b ≤ (2b + d)^(2b+d)`. -/
theorem cube_split_add (b d : PTm N) :
    Γ ⊢[PRAAx] le (pw four b * pw (b + d) (b + d) * pw b b) (pw (b + d + b) (b + d + b)) := by
  have h := inst (Γ := Γ) sp₀ (![d, b] : Fin 2 → PTm N)
  simpa using h

/-- `lem:cube-split`: for `b ≤ a`, `4^b a^a b^b ≤ (a + b)^(a+b)`. -/
theorem cube_split {a b : PTm N} (h : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] le (pw four b * pw a a * pw b b) (pw (a + b) (a + b)) := by
  have e := (eq_add_of_le h).eqSymm
  exact le_congr (congrMul (congrMul (.eqRefl _) (pw_congr e e)) (.eqRefl _))
    (pw_congr (congrAdd e (.eqRefl b)) (congrAdd e (.eqRefl b))) (cube_split_add b (monus a b))

/-! ## The induction step of the edge inequality -/

/-- `4^c ≤ 4^b` for `c ≤ b`. -/
theorem pw_four_le {c b : PTm N} (h : Γ ⊢[PRAAx] le c b) : Γ ⊢[PRAAx] le (pw four c) (pw four b) := by
  have e := eq_add_of_le h
  have p : Γ ⊢[PRAAx] pw four (monus b c) ≐ succ (pred (pw four (monus b c))) :=
    pos_of_eq_succ ((four_pow _).eqTrans (pos_mul' (pw_pos one _) (pw_pos one _)))
  exact le_congr (.eqRefl _) ((pw_congr (.eqRefl four) e).eqTrans (pw_add four c (monus b c))).eqSymm
    (le_mul_pos (pw four c) p)

/-- `2^(2c) = 4^c`. -/
theorem four_pow' (c : PTm N) : Γ ⊢[PRAAx] pw two (two * c) ≐ pw four c := by
  have t : Γ ⊢[PRAAx] two * c ≐ c + c := by ipra_ring
  exact ((pw_congr (.eqRefl two) t).eqTrans (pw_add two c c)).eqTrans (four_pow c).eqSymm

/-- The step of `thm:cube-edge`: sections with `a ≥ b` vertices, `e₀` and `e₁` internal edges
and `c ≤ b` common vertices, so that `e = e₀ + e₁ + c`. -/
theorem edge_step {a b c e₀ e₁ : PTm N} (h₀ : Γ ⊢[PRAAx] le (pw two (two * e₀)) (pw a a))
    (h₁ : Γ ⊢[PRAAx] le (pw two (two * e₁)) (pw b b)) (hc : Γ ⊢[PRAAx] le c b)
    (hba : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] le (pw two (two * (e₀ + e₁ + c))) (pw (a + b) (a + b)) := by
  have t : Γ ⊢[PRAAx] two * (e₀ + e₁ + c) ≐ two * e₀ + two * e₁ + two * c := by
    ipra_ring
  have hE : Γ ⊢[PRAAx] pw two (two * (e₀ + e₁ + c)) ≐
      pw two (two * e₀) * pw two (two * e₁) * pw four c :=
    (pw_congr (.eqRefl two) t).eqTrans ((pw_add two (two * e₀ + two * e₁) (two * c)).eqTrans
      (congrMul (pw_add two (two * e₀) (two * e₁)) (four_pow' c)))
  have m := le_mul_mono (le_mul_mono h₀ h₁) (pw_four_le hc)
  refine le_trans (le_congr hE.eqSymm ?_ m) (cube_split hba)
  ipra_ring

/-! ## Consequences of the edge inequality -/

/-- A subcube with `r` free coordinates has `k = 2^r` vertices and `2e = r · 2^r`; then
`2^(2e) = k^k`, the equality case of `thm:cube-edge`. -/
theorem subcube_eq (r : PTm N) : Γ ⊢[PRAAx] pw two (r * pw two r) ≐ pw (pw two r) (pw two r) :=
  (pw_mul two r (pw two r)).eqSymm

/-- With the degree count `d k = 2e + b`, the edge inequality `2^(2e) ≤ k^k` reads
`2^(d k) ≤ 2^b k^k`. -/
theorem edge_integer_form {d k e b : PTm N} (hdeg : Γ ⊢[PRAAx] d * k ≐ two * e + b)
    (h : Γ ⊢[PRAAx] le (pw two (two * e)) (pw k k)) :
    Γ ⊢[PRAAx] le (pw two (d * k)) (pw two b * pw k k) :=
  le_congr ((pw_congr (.eqRefl two) hdeg).eqTrans (pw_add two (two * e) b)).eqSymm (mul_comm _ _)
    (mul_le_mul_right (pw two b) h)

theorem two_pos : Γ ⊢[PRAAx] (two : PTm N) ≐ succ (pred two) := pos_of_eq_succ (.eqRefl _)

/-- `2^u ≤ 2^v` gives `u ≤ v`. -/
theorem exp_le_of_pw_le {u v : PTm N} (h : Γ ⊢[PRAAx] le (pw two u) (pw two v)) : Γ ⊢[PRAAx] le u v := by
  refine .orE (lt_or_le v u) ?_ Prf.hyp0
  have h' : (lt v u :: Γ) ⊢[PRAAx] le (pw two u) (pw two v) := h.wk
  have m : (lt v u :: Γ) ⊢[PRAAx] le (pw two (succ v)) (pw two u) := pw_le_exp two_pos Prf.hyp0
  have g : (lt v u :: Γ) ⊢[PRAAx] le (succ (pw two v)) (pw two (succ v)) := by
    refine le_of_eq_add (d := pred (pw two v)) ?_
    ipra_lc natEq (pw_succ (Γ := lt v u :: Γ) two v) + natEq (pw_pos (Γ := lt v u :: Γ) one v)
  exact not_succ_le_self (pw two v) _ (le_trans g (le_trans m h'))

/-- Sharp expansion at half volume: in `Q_d` with `d = d' + 1`, a family of `k ≤ 2^(d−1)` vertices
with `e` internal and `b` boundary edges, `d k = 2e + b` and `2^(2e) ≤ k^k`, has `b ≥ k`. -/
theorem half_cube_expansion {d' k e b : PTm N} (hdeg : Γ ⊢[PRAAx] succ d' * k ≐ two * e + b)
    (h : Γ ⊢[PRAAx] le (pw two (two * e)) (pw k k)) (hk : Γ ⊢[PRAAx] le k (pw two d')) :
    Γ ⊢[PRAAx] le k b := by
  have I := edge_integer_form hdeg h
  have J : Γ ⊢[PRAAx] le (pw k k) (pw two (d' * k)) :=
    le_congr (.eqRefl _) (pw_mul two d' k) (pw_le_pw k hk)
  have K := le_mul_mono (le_refl (pw two b)) J
  have L : Γ ⊢[PRAAx] le (pw two (succ d' * k)) (pw two (b + d' * k)) :=
    le_trans I (le_congr (.eqRefl _) (pw_add two b (d' * k)).eqSymm K)
  have M := exp_le_of_pw_le L
  refine le_of_add_le_add_right (c := d' * k) (le_congr ?_ (.eqRefl _) M)
  ipra_ring

end LeanProofs.IPRA.Geometry.HypercubeSplit
