import IPRADerivations.Analysis.Pochhammer

/-!
# The rising-factorial form of a hypergeometric term, and the Lambert polynomials

Packets: `analysis/meijer_g_ipra_2026-11-16` (`lem:rising`) and
`analysis/lambert_w_ipra_2026-11-16` (`thm:higher-derivatives` with its displayed polynomials,
the fixed-point equation behind `thm:W-series`).

A hypergeometric term is produced by its ratio recurrence. Cleared of denominators, with one
upper parameter `A` and one lower parameter `B`, the numerator and denominator are

  `hn 0 = 1`, `hn (k + 1) = hn k · ((A + k) w)`;  `hd 0 = 1`, `hd (k + 1) = hd k · ((B + k)(k + 1))`.

* `rising_num`: `hn A w k = (A)_k w^k`;
* `rising_den`: `hd B k = (B)_k k!`;
* `rising_term`: hence `t_k = hn/hd` has the form `(A)_k w^k / ((B)_k k!)`, stated as
  `hn A w k · ((B)_k k!) = (A)_k w^k · hd B k`.

Several parameters multiply such factors.

For Lambert `W`, with `P₁ = 1` and `P_{n+1} = (1 + w) P_n' + (1 − 3n − n w) P_n`:

* `lambert_coeff`: `−n (1 + w) − (2n − 1) = 1 − 3n − n w`, the collection of the numerator when
  `d/dw` is applied to `P_n e^{−n w} (1 + w)^{−(2n−1)}`;
* `lambert_P2`, `lambert_P3`, `lambert_P4`: the recurrence gives the displayed
  `P₂ = −(w + 2)`, `P₃ = 2w² + 8w + 9`, `P₄ = −(6w³ + 36w² + 79w + 64)`;
* `lambert_fix2`, `lambert_fix3`: the truncations `X − X²` and `X − X² + (3/2) X³` satisfy
  `W = X e^{−W}` modulo `X³` and `X⁴`, with explicit remainders, so the first coefficients are
  `(−n)^(n−1)/n!`.

The convergence theorems, the contour representation, the general Lagrange formula and the
analytic statements are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.HypergeometricTerm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Analysis.Pochhammer (poch poch_zero poch_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The ratio recurrence -/

/-- Step of the numerator: variables `0 = k`, `1 = hn k`, `2 = ⟨A, w⟩`. -/
abbrev hnStep : PTm 3 := var 1 * ((fstT (var 2) + var 0) * sndT (var 2))
abbrev hnF : PR 2 := rec2 one hnStep
/-- The numerator `∏_{j<k} (A + j) w`. -/
abbrev hn (A w k : PTm n) : PTm n := ap2 hnF k (pairT A w)

/-- Step of the denominator: variables `0 = k`, `1 = hd k`, `2 = B`. -/
abbrev hdStep : PTm 3 := var 1 * ((var 2 + var 0) * succ (var 0))
abbrev hdF : PR 2 := rec2 one hdStep
/-- The denominator `∏_{j<k} (B + j)(j + 1)`. -/
abbrev hd (B k : PTm n) : PTm n := ap2 hdF k B

theorem hn_zero (A w : PTm n) : Γ ⊢[PRAAx] hn A w zero ≐ one := by
  have h := rec2_zero (Γ := Γ) one hnStep (pairT A w)
  simpa using h

theorem hn_succ (A w k : PTm n) : Γ ⊢[PRAAx] hn A w (succ k) ≐ hn A w k * ((A + k) * w) := by
  have h := rec2_succ (Γ := Γ) one hnStep k (pairT A w)
  have e : Syn.subst ![k, ap2 hnF k (pairT A w), pairT A w] hnStep =
      hn A w k * ((fstT (pairT A w) + k) * sndT (pairT A w)) := by simp
  rw [e] at h
  exact h.eqTrans (congrMul (.eqRefl _) (congrMul (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)))

theorem hd_zero (B : PTm n) : Γ ⊢[PRAAx] hd B zero ≐ one := by
  have h := rec2_zero (Γ := Γ) one hdStep B
  simpa using h

theorem hd_succ (B k : PTm n) : Γ ⊢[PRAAx] hd B (succ k) ≐ hd B k * ((B + k) * succ k) := by
  have h := rec2_succ (Γ := Γ) one hdStep k B
  have e : Syn.subst ![k, ap2 hdF k B, B] hdStep = hd B k * ((B + k) * succ k) := by simp
  rw [e] at h
  exact h

/-! ## The rising-factorial form -/

theorem num_step {A w k : PTm n} (ih : Γ ⊢[PRAAx] hn A w k ≐ poch A k * pw w k) :
    Γ ⊢[PRAAx] hn A w (succ k) ≐ poch A (succ k) * pw w (succ k) := by
  have e := natEq ih; have s := natEq (hn_succ (Γ := Γ) A w k)
  have sp := natEq (poch_succ (Γ := Γ) A k); have sw := natEq (pw_succ (Γ := Γ) w k)
  apply deriveNat; ipra_simps
  linear_combination s + (𝔞(A) + 𝔞(k)) * 𝔞(w) * e - 𝔞(pw w (succ k)) * sp -
    𝔞(poch A k) * (𝔞(A) + 𝔞(k)) * sw

/-- Variables: `0 = k` (induction), `1 = A`, `2 = w`. -/
private abbrev numF : Fm PTm 3 :=
  hn (var 1) (var 2) (var 0) ≐ poch (var 1) (var 0) * pw (var 2) (var 0)

private theorem num₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] numF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine (hn_zero _ _).eqTrans ?_
    have e₁ := natEq (poch_zero (Γ := []) (var 0 : PTm 2))
    have e₂ := natEq (pw_zero (Γ := []) (var 1 : PTm 2))
    apply deriveNat; ipra_simps
    linear_combination -e₁ - 𝔞(poch (var 0 : PTm 2) zero) * e₂
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
      repl_one, repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact num_step Prf.hyp0

/-- `hn A w k = (A)_k w^k`. -/
theorem rising_num (A w k : PTm n) : Γ ⊢[PRAAx] hn A w k ≐ poch A k * pw w k := by
  have h := inst (Γ := Γ) num₀ (![k, A, w] : Fin 3 → PTm n)
  simpa using h

theorem den_step {B k : PTm n} (ih : Γ ⊢[PRAAx] hd B k ≐ poch B k * fact k) :
    Γ ⊢[PRAAx] hd B (succ k) ≐ poch B (succ k) * fact (succ k) := by
  have e := natEq ih; have s := natEq (hd_succ (Γ := Γ) B k)
  have sp := natEq (poch_succ (Γ := Γ) B k); have sf := natEq (fact_succ (Γ := Γ) k zero)
  apply deriveNat; ipra_simps
  linear_combination s + (𝔞(B) + 𝔞(k)) * (𝔞(k) + 1) * e - 𝔞(fact (succ k)) * sp -
    𝔞(poch B k) * (𝔞(B) + 𝔞(k)) * sf

/-- Variables: `0 = k` (induction), `1 = B`. -/
private abbrev denF : Fm PTm 2 := hd (var 1) (var 0) ≐ poch (var 1) (var 0) * fact (var 0)

private theorem den₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] denF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine (hd_zero _).eqTrans ?_
    have e₁ := natEq (poch_zero (Γ := []) (var 0 : PTm 1))
    have e₂ := natEq (fact_zero (Γ := []) (zero : PTm 1))
    apply deriveNat; ipra_simps
    linear_combination -e₁ - 𝔞(poch (var 0 : PTm 1) zero) * e₂
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact den_step Prf.hyp0

/-- `hd B k = (B)_k k!`. -/
theorem rising_den (B k : PTm n) : Γ ⊢[PRAAx] hd B k ≐ poch B k * fact k := by
  have h := inst (Γ := Γ) den₀ (![k, B] : Fin 2 → PTm n)
  simpa using h

/-- `lem:rising`, cross-multiplied: `t_k = hn/hd = (A)_k w^k / ((B)_k k!)`. -/
theorem rising_term (A B w k : PTm n) :
    Γ ⊢[PRAAx] hn A w k * (poch B k * fact k) ≐ (poch A k * pw w k) * hd B k := by
  have e₁ := natEq (rising_num (Γ := Γ) A w k); have e₂ := natEq (rising_den (Γ := Γ) B k)
  apply deriveNat; ipra_simps
  linear_combination 𝔞(poch B k) * 𝔞(fact k) * e₁ - 𝔞(poch A k) * 𝔞(pw w k) * e₂

/-! ## The Lambert polynomials -/

section Lambert

abbrev w : ZT 4 := .var2 0 1
abbrev N : ZT 4 := .var2 2 3

abbrev lit (k : ℕ) : ZT 4 := ZT.natLit k

/-- `−n (1 + w) − (2n − 1) = 1 − 3n − n w`. -/
def coeffFormula : Fm PTm 4 :=
  ZT.eq (-(N * (lit 1 + w)) - (lit 2 * N - lit 1)) (lit 1 - lit 3 * N - N * w)

/-- `P₂ = (1 + w) P₁' + (1 − 3 − w) P₁` with `P₁ = 1`, `P₁' = 0`. -/
def p2Formula : Fm PTm 4 :=
  ZT.eq ((lit 1 + w) * lit 0 + (lit 1 - lit 3 - w) * lit 1) (-(w + lit 2))

/-- `P₃ = (1 + w) P₂' + (1 − 6 − 2w) P₂` with `P₂ = −(w + 2)`, `P₂' = −1`. -/
def p3Formula : Fm PTm 4 :=
  ZT.eq ((lit 1 + w) * (-(lit 1)) + (lit 1 - lit 6 - lit 2 * w) * (-(w + lit 2)))
    (lit 2 * (w * w) + lit 8 * w + lit 9)

/-- `P₄ = (1 + w) P₃' + (1 − 9 − 3w) P₃` with `P₃ = 2w² + 8w + 9`, `P₃' = 4w + 8`. -/
def p4Formula : Fm PTm 4 :=
  ZT.eq ((lit 1 + w) * (lit 4 * w + lit 8) + (lit 1 - lit 9 - lit 3 * w) * (lit 2 * (w * w) + lit 8 * w + lit 9))
    (-(lit 6 * (w * w * w) + lit 36 * (w * w) + lit 79 * w + lit 64))

/-- With `W₂ = X − X²` (here `X = w`): `2X (1 − W₂) + X W₂² = 2 W₂ + X³ (2 + (1 − X)²)`, i.e.
`X (1 − W + W²/2) ≡ W (mod X³)`. -/
def fix2Formula : Fm PTm 4 :=
  ZT.eq (lit 2 * w * (lit 1 - (w - w * w)) + w * ((w - w * w) * (w - w * w)))
    (lit 2 * (w - w * w) + w * w * w * (lit 2 + (lit 1 - w) * (lit 1 - w)))

/-- With `2 W₃ = v = 2X − 2X² + 3X³`: `8X − 4X v + X v² = 4v + X⁴ (9X³ − 12X² + 16X − 20)`, i.e.
`X (1 − W + W²/2) ≡ W (mod X⁴)` for `W = X − X² + (3/2) X³`. -/
def fix3Formula : Fm PTm 4 :=
  let v : ZT 4 := lit 2 * w - lit 2 * (w * w) + lit 3 * (w * w * w)
  ZT.eq (lit 8 * w - lit 4 * w * v + w * (v * v))
    (lit 4 * v + w * w * w * w * (lit 9 * (w * w * w) - lit 12 * (w * w) + lit 16 * w - lit 20))

theorem coeff_open : ([] : List (Fm PTm 4)) ⊢[PRAAx] coeffFormula := by unfold coeffFormula; ipra_ring
theorem p2_open : ([] : List (Fm PTm 4)) ⊢[PRAAx] p2Formula := by unfold p2Formula; ipra_ring
theorem p3_open : ([] : List (Fm PTm 4)) ⊢[PRAAx] p3Formula := by unfold p3Formula; ipra_ring
theorem p4_open : ([] : List (Fm PTm 4)) ⊢[PRAAx] p4Formula := by unfold p4Formula; ipra_ring
theorem fix2_open : ([] : List (Fm PTm 4)) ⊢[PRAAx] fix2Formula := by unfold fix2Formula; ipra_ring
theorem fix3_open : ([] : List (Fm PTm 4)) ⊢[PRAAx] fix3Formula := by unfold fix3Formula; ipra_ring

theorem lambert_coeff : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 4 coeffFormula := closeAll 4 coeff_open
theorem lambert_P2 : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 4 p2Formula := closeAll 4 p2_open
theorem lambert_P3 : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 4 p3Formula := closeAll 4 p3_open
theorem lambert_P4 : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 4 p4Formula := closeAll 4 p4_open
theorem lambert_fix2 : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 4 fix2Formula := closeAll 4 fix2_open
theorem lambert_fix3 : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 4 fix3Formula := closeAll 4 fix3_open

end Lambert

end LeanProofs.IPRA.Analysis.HypergeometricTerm
