import IPRADerivations.Analysis.Series.Basel.BaselCore

/-!
# The uniform finite Basel estimate

Packet: `analysis/basel_ipra`, `paper/basel_ipra.tex`, Theorems `thm:uniform` and `thm:main`:
for `n ≥ N ≥ 1`, `|6 S_n − 16 A_N²| ≤ (16 H_N + 4)/N` (`eq:uniform`); for `n ≥ 2^r`,
`|6 S_n − 16 A_{2^r}²| ≤ (8r + 20)/2^r` (`eq:dyadic`); and with `cut(k) = 2^{2k+7}`, `P_k = 4 A_{cut(k)}`,
`n ≥ cut(k) → |6 S_n − P_k²| ≤ 2^{−k}` (`eq:main`).

Everything is cleared by `F = L!` for a bound `L ≥ max(2N + 1, n)`, so that `S(n) = F² S_n`,
`A⁺ − A⁻ = F A_N` and `H(N) = F H_N` exactly. With `Y⁺ = 6 S(n) + 32 A⁺A⁻` and `Y⁻ = 16 (A⁺² + A⁻²)`
(so `Y⁺ − Y⁻ = F² (6 S_n − 16 A_N²)`):

* `uniform` (`eq:uniform`): `N Y⁺ ≤ N Y⁻ + 16 F H(N) + 4 F²` and conversely, from
  `6S − 16A² = 2(3S − 4O) + 8(O − 2A²)`, `lem:compare` and `prop:core`;
* `dyadic` (`eq:dyadic`): for `N = 2^r`, `N Y⁺ ≤ N Y⁻ + (8r + 20) F²` and conversely, by `lem:harmonic`
  (`2 H(2^r) ≤ (r + 2) F`);
* `main` (`thm:main`, `eq:main`): for `N = cut(k) = 2^{2k+7}`, `2^k Y⁺ ≤ 2^k Y⁻ + F²` and conversely, by
  `eq:growth` (`2^k (16k + 76) ≤ 2^{2k+7}`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BaselUniform

open_ipra
open LeanProofs.IPRA.Analysis.BaselCore (Ap Am core)
open LeanProofs.IPRA.Analysis.BaselSquares (S O compare)
open LeanProofs.IPRA.Analysis.BaselAverages (H)
open LeanProofs.IPRA.Analysis.BaselFinite (tB T harmonic_up growth)
open LeanProofs.IPRA.Analysis.Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `Y⁺ = 6 S(n) + 32 A⁺A⁻` and `Y⁻ = 16 (A⁺² + A⁻²)`. -/
abbrev Yp (N m L : PTm n) : PTm n := num 6 * S m L + num 32 * (Ap N L * Am N L)
abbrev Ym (N L : PTm n) : PTm n := num 16 * (Ap N L * Ap N L + Am N L * Am N L)

/-- `thm:uniform` (`eq:uniform`), cleared by `F = L!`: for `1 ≤ N = M + 1 ≤ m`, `2N + 1 ≤ L`, `m ≤ L`,
`N Y⁺ ≤ N Y⁻ + 16 F H(N) + 4 F²` and `N Y⁻ ≤ N Y⁺ + 16 F H(N) + 4 F²`, i.e.
`|6 S_m − 16 A_N²| ≤ (16 H_N + 4)/N`. -/
theorem uniform {M m L : PTm n} (hm : Γ ⊢[PRAAx] le (succ M) m) (hL : Γ ⊢[PRAAx] le (succ (two * succ M)) L)
    (hmL : Γ ⊢[PRAAx] le m L) :
    Γ ⊢[PRAAx] le (succ M * Yp (succ M) m L)
        (succ M * Ym (succ M) L + num 16 * (fact L * H (succ M) L) + num 4 * (fact L * fact L)) ⋏
      le (succ M * Ym (succ M) L)
        (succ M * Yp (succ M) m L + num 16 * (fact L * H (succ M) L) + num 4 * (fact L * fact L)) := by
  have h2 : Γ ⊢[PRAAx] le (two * succ M) L := le_trans (le_succ_self _) hL
  have c := compare hm h2 hmL
  have k := core hL
  have c1 := natEq (eq_add_of_le (Prf.andE₁ c)); have c2 := natEq (eq_add_of_le (Prf.andE₂ c))
  have k1 := natEq (eq_add_of_le (Prf.andE₁ k)); have k2 := natEq (eq_add_of_le (Prf.andE₂ k))
  refine .andI (le_of_eq_add (d := two * monus (succ M * (two * two * O (succ M) L) + two * (fact L * fact L))
        (succ M * (num 3 * S m L)) +
      num 8 * monus (succ M * (two * (Ap (succ M) L * Ap (succ M) L + Am (succ M) L * Am (succ M) L)) +
        two * (fact L * H (succ M) L))
        (succ M * (O (succ M) L + two * two * (Ap (succ M) L * Am (succ M) L)))) ?_)
    (le_of_eq_add (d := two * monus (succ M * (num 3 * S m L) + two * (fact L * fact L))
        (succ M * (two * two * O (succ M) L)) +
      num 8 * monus (succ M * (O (succ M) L + two * two * (Ap (succ M) L * Am (succ M) L)) +
        two * (fact L * H (succ M) L))
        (succ M * (two * (Ap (succ M) L * Ap (succ M) L + Am (succ M) L * Am (succ M) L)))) ?_)
  · ipra_lc 2 * c2 + 8 * k2
  · ipra_lc 2 * c1 + 8 * k1

/-- `eq:dyadic`, cleared by `F = L!`: for `N = 2^r ≤ m`, `2N + 1 ≤ L`, `m ≤ L`,
`N Y⁺ ≤ N Y⁻ + (8r + 20) F²` and conversely, i.e. `|6 S_m − 16 A_{2^r}²| ≤ (8r + 20)/2^r`. -/
theorem dyadic {r m L : PTm n} (hm : Γ ⊢[PRAAx] le (pw two r) m) (hL : Γ ⊢[PRAAx] le (succ (two * pw two r)) L)
    (hmL : Γ ⊢[PRAAx] le m L) :
    Γ ⊢[PRAAx] le (pw two r * Yp (pw two r) m L)
        (pw two r * Ym (pw two r) L + (num 8 * r + num 20) * (fact L * fact L)) ⋏
      le (pw two r * Ym (pw two r) L)
        (pw two r * Yp (pw two r) m L + (num 8 * r + num 20) * (fact L * fact L)) := by
  have e : Γ ⊢[PRAAx] succ (pred (pw two r)) ≐ pw two r :=
    (LeanProofs.IPRA.AnalyticNumberTheory.Harmonic.pw2_pos r).eqSymm
  have u := uniform (M := pred (pw two r)) (le_congr e.eqSymm (.eqRefl _) hm)
    (le_congr (congrSucc (congrMul (.eqRefl two) e)).eqSymm (.eqRefl _) hL) hmL
  have u' := Prf.eqSubst1 (le (var 0 * Yp (var 0) (Syn.shift m) (Syn.shift L))
      (var 0 * Ym (var 0) (Syn.shift L) + num 16 * (fact (Syn.shift L) * H (var 0) (Syn.shift L)) +
        num 4 * (fact (Syn.shift L) * fact (Syn.shift L))) ⋏
    le (var 0 * Ym (var 0) (Syn.shift L))
      (var 0 * Yp (var 0) (Syn.shift m) (Syn.shift L) + num 16 * (fact (Syn.shift L) * H (var 0) (Syn.shift L)) +
        num 4 * (fact (Syn.shift L) * fact (Syn.shift L)))) e (by simpa using u)
  simp at u'
  have u1 := natEq (eq_add_of_le (Prf.andE₁ u')); have u2 := natEq (eq_add_of_le (Prf.andE₂ u'))
  refine .andI (le_of_eq_add (d := monus (pw two r * Ym (pw two r) L +
        num 16 * (fact L * H (pw two r) L) + num 4 * (fact L * fact L))
        (pw two r * Yp (pw two r) m L) +
      num 8 * (fact L * monus ((two + r) * fact L) (two * T (pw two r) (fact L)))) ?_)
    (le_of_eq_add (d := monus (pw two r * Yp (pw two r) m L +
        num 16 * (fact L * H (pw two r) L) + num 4 * (fact L * fact L))
        (pw two r * Ym (pw two r) L) +
      num 8 * (fact L * monus ((two + r) * fact L) (two * T (pw two r) (fact L)))) ?_)
  · ipra_lc u1 + 8 * 𝔞 (fact L) * natEq (eq_add_of_le (harmonic_up (Γ := Γ) r (fact L)))
  · ipra_lc u2 + 8 * 𝔞 (fact L) * natEq (eq_add_of_le (harmonic_up (Γ := Γ) r (fact L)))

/-! ## The precision witness (`thm:main`) -/

/-- `cut(k) = 2^{2k+7}` (`eq:cutoff`). -/
abbrev cut (k : PTm n) : PTm n := pw two (two * k + num 7)

theorem pw_seven : Γ ⊢[PRAAx] pw (two : PTm n) (num 7) ≐ num 128 := by
  show Γ ⊢[PRAAx] pw two (succ (succ (succ (succ (succ (succ (succ zero))))))) ≐ num 128
  ipra_lc natEq (pw_succ (Γ := Γ) (two : PTm n) (succ (succ (succ (succ (succ (succ zero))))))) +
    2 * natEq (pw_succ (Γ := Γ) (two : PTm n) (succ (succ (succ (succ (succ zero)))))) +
    4 * natEq (pw_succ (Γ := Γ) (two : PTm n) (succ (succ (succ (succ zero))))) +
    8 * natEq (pw_succ (Γ := Γ) (two : PTm n) (succ (succ (succ zero)))) +
    16 * natEq (pw_succ (Γ := Γ) (two : PTm n) (succ (succ zero))) +
    32 * natEq (pw_succ (Γ := Γ) (two : PTm n) (succ zero)) + 64 * natEq (pw_succ (Γ := Γ) (two : PTm n) zero) +
    128 * natEq (pw_zero (Γ := Γ) (two : PTm n))

/-- `cut(k) = 128 (2^k)²`. -/
theorem cut_eq (k : PTm n) : Γ ⊢[PRAAx] cut k ≐ num 128 * (pw two k * pw two k) := by
  ipra_lc natEq (pw_add (Γ := Γ) two (two * k) (num 7)) +
    𝔞 (pw two (num 7)) * natEq ((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] two * k ≐ k + k) (.eqRefl two)).eqTrans (pw_add (Γ := Γ) two k k)) +
    𝔞 (pw two k) * 𝔞 (pw two k) * natEq (pw_seven (Γ := Γ))

/-- `2^k (8r + 20) ≤ 2^r` for `r = 2k + 7`, from `eq:growth`. -/
theorem growth_cut (k : PTm n) :
    Γ ⊢[PRAAx] le (pw two k * (num 8 * (two * k + num 7) + num 20)) (cut k) := by
  refine le_of_eq_add (d := pw two k * monus (num 128 * pw two k) (num 16 * k + num 76)) ?_
  ipra_lc natEq (cut_eq (Γ := Γ) k) + 𝔞 (pw two k) * natEq (eq_add_of_le (growth (Γ := Γ) k))

/-- `thm:main` (`eq:main`), cleared by `F = L!`: for `n ≥ cut(k)`, `2 cut(k) + 1 ≤ L`, `n ≤ L`, with
`P_k = 4 A_{cut(k)}` (so `16 A² = P_k²`), `2^k Y⁺ ≤ 2^k Y⁻ + F²` and `2^k Y⁻ ≤ 2^k Y⁺ + F²`, i.e.
`|6 S_n − P_k²| ≤ 2^{−k}`. -/
theorem main {k m L : PTm n} (hm : Γ ⊢[PRAAx] le (cut k) m) (hL : Γ ⊢[PRAAx] le (succ (two * cut k)) L)
    (hmL : Γ ⊢[PRAAx] le m L) :
    Γ ⊢[PRAAx] le (pw two k * Yp (cut k) m L) (pw two k * Ym (cut k) L + fact L * fact L) ⋏
      le (pw two k * Ym (cut k) L) (pw two k * Yp (cut k) m L + fact L * fact L) := by
  have d := dyadic (r := two * k + num 7) hm hL hmL
  have d1 := natEq (eq_add_of_le (Prf.andE₁ d)); have d2 := natEq (eq_add_of_le (Prf.andE₂ d))
  have hp := LeanProofs.IPRA.AnalyticNumberTheory.Harmonic.pw2_pos (Γ := Γ) (two * k + num 7)
  refine .andI (mul_le_cancel (d' := pred (cut k)) (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _))
      (le_of_eq_add (d := pw two k * monus (cut k * Ym (cut k) L + (num 8 * (two * k + num 7) + num 20) *
          (fact L * fact L)) (cut k * Yp (cut k) m L) +
        monus (cut k) (pw two k * (num 8 * (two * k + num 7) + num 20)) * (fact L * fact L)) ?_)))
    (mul_le_cancel (d' := pred (cut k)) (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _))
      (le_of_eq_add (d := pw two k * monus (cut k * Yp (cut k) m L + (num 8 * (two * k + num 7) + num 20) *
          (fact L * fact L)) (cut k * Ym (cut k) L) +
        monus (cut k) (pw two k * (num 8 * (two * k + num 7) + num 20)) * (fact L * fact L)) ?_)))
  · ipra_lc 𝔞 (pw two k) * d1 + 𝔞 (fact L) * 𝔞 (fact L) * natEq (eq_add_of_le (growth_cut (Γ := Γ) k))
  · ipra_lc 𝔞 (pw two k) * d2 + 𝔞 (fact L) * 𝔞 (fact L) * natEq (eq_add_of_le (growth_cut (Γ := Γ) k))

end LeanProofs.IPRA.Analysis.BaselUniform
