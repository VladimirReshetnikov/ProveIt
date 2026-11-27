import IPRADerivations.DiophantineNumberTheory.TwoSquaresDescent
import IPRADerivations.DiophantineNumberTheory.FourSquares

/-!
# Fermat's two-square theorem by bounded descent

Packet: `diophantine-number-theory/fermat_two_squares_ipra_2026-11-22`, `fermat_two_squares_ipra.tex`,
§"An independent construction by bounded descent" (`sec:descent`): from a root `t` of `−1` modulo a prime
`p ≡ 1 (mod 4)`, the state `(a₀, b₀, m₀) = (t, 1, (t² + 1)/p)` satisfies `1 ≤ m₀ < p` and `a₀² + b₀² = m₀ p`,
and each descent step replaces a state of multiplier `m > 1` by one of multiplier `1 ≤ m' < m`
(`TwoSquaresDescent.two_descent`).

As in `FourSquares`, the iteration with fuel is replaced by the least multiplier: let `m*` be the least `m ≥ 1`
below `p` with `m p` a sum of two squares (a bounded search). If `m* ≥ 2`, one descent step gives a smaller
multiplier, against leastness (`BoundedReflection.ex_least`); so `m* = 1`. The packet's clock `m_k + k ≤ m₀`
(`eq:clock`) is not used.

* `tB`, `T n`, `X n`, `Y n`: the bit of "`n` is a sum of two squares of numbers `≤ n`" (a bounded search over
  the codes `c < (n + 1)²`) and its two witnesses; `rep_intro`, `rep_elim`;
* `seed_bounds`: `t < p` and `t² + 1 = p m₀` give `1 ≤ m₀ < p` (the packet's "Initial state");
* `lB`, `ms`: the least multiplier;
* **`rep_mod4`**: `T p = 1` for a prime `p` with `p` odd and `⌊p/2⌋` even;
* **`two_squares_descent`**: `X(p)² + Y(p)² = p` for a prime `p ≡ 1 (mod 4)`.

The first proof (the grid collision) is `FermatTwoSquares.fermat_witness`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.TwoSquaresByDescent

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (one_le_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrEqb')
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm dmu)
open LeanProofs.IPRA.DiophantineNumberTheory.FourSquaresAlgebra (le_sq_part)
open LeanProofs.IPRA.DiophantineNumberTheory.FourSquares (lt_succ_of_le)
open LeanProofs.IPRA.DiophantineNumberTheory.TwoSquaresDescent (two_descent)
open LeanProofs.IPRA.DiophantineNumberTheory.FermatTwoSquares (rt root_minus_one mod4_parities)
open LeanProofs.IPRA.DiophantineNumberTheory.QuadraticSupplements (root_of_sign minus_one_law)
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_cases ex_intro ex_elim eqb_cases
  eq_of_eqb one_ne_zero signum_guard_nonzero least_positive_witness)
open LeanProofs.IPRA.Signum (sg)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## The bit of a two-square representation -/

/-- `[(c mod (n + 1))² + ⌊c/(n + 1)⌋² = n]`, over `0 = c`, `1 = n`. -/
abbrev tB : PTm 2 :=
  eqb (rem (var 0) (succ (var 1)) * rem (var 0) (succ (var 1)) +
    quo (var 0) (succ (var 1)) * quo (var 0) (succ (var 1))) (var 1)

theorem inst2_tB (c n : PTm k) : inst2 tB c n =
    eqb (rem c (succ n) * rem c (succ n) + quo c (succ n) * quo c (succ n)) n := by simp [inst2]

/-- The bound `(n + 1)²` of the search. -/
abbrev bd (n : PTm k) : PTm k := succ n * succ n

/-- The bit of "`n` is a sum of two squares of numbers `≤ n`". -/
abbrev T (n : PTm k) : PTm k := exB tB (bd n) n

/-- The two witnesses. -/
abbrev X (n : PTm k) : PTm k := rem (wit tB (bd n) n) (succ n)
abbrev Y (n : PTm k) : PTm k := quo (wit tB (bd n) n) (succ n)

theorem sq_comm {a b n : PTm k} (e : Γ ⊢[PRAAx] a * a + b * b ≐ n) : Γ ⊢[PRAAx] b * b + a * a ≐ n := by
  ipra_lc natEq e

theorem code_lt {B a b : PTm k} (ha : Γ ⊢[PRAAx] lt a B) (hb : Γ ⊢[PRAAx] lt b B) :
    Γ ⊢[PRAAx] lt (B * b + a) (B * B) := by
  ipra_le 𝔞 B * sl hb + sl ha

/-- Any representation makes the bit `1`. -/
theorem rep_intro {n a b : PTm k} (e : Γ ⊢[PRAAx] a * a + b * b ≐ n) : Γ ⊢[PRAAx] T n ≐ one := by
  have hB : Γ ⊢[PRAAx] succ n ≐ succ (pred (succ n)) := congrSucc (pred_succ _).eqSymm
  have la := lt_succ_of_le (le_sq_part e)
  have lb := lt_succ_of_le (le_sq_part (sq_comm e))
  have s := dmu hB (.eqRefl (succ n * b + a)) la
  have val : Γ ⊢[PRAAx] inst2 tB (succ n * b + a) n ≐ one := by
    rw [inst2_tB]
    exact (congrEqb' (congrAdd (congrMul (Prf.andE₂ s) (Prf.andE₂ s)) (congrMul (Prf.andE₁ s) (Prf.andE₁ s)))
      (.eqRefl n)).eqTrans (eqb_of_eq e)
  exact ex_intro tB (.impI (one_ne_zero _ (val.wk.eqSymm.eqTrans Prf.hyp0))) (code_lt la lb)

/-- The bit `1` gives the witnesses. -/
theorem rep_elim {n : PTm k} (h : Γ ⊢[PRAAx] T n ≐ one) : Γ ⊢[PRAAx] X n * X n + Y n * Y n ≐ n := by
  have ne := Prf.andE₂ (ex_elim tB h)
  rw [inst2_tB] at ne
  refine .orE (eqb_cases (X n * X n + Y n * Y n) n) ?_ ?_
  · exact .botE _ (.impE ne.wk Prf.hyp0)
  · exact eq_of_eqb Prf.hyp0

/-! ## The initial state -/

theorem seed_alg {r p m0 : PTm k} (es : Γ ⊢[PRAAx] r * r + one ≐ p * m0 + zero) :
    Γ ⊢[PRAAx] r * r + one * one ≐ m0 * p := by
  ipra_lc natEq es

/-- `t < p` and `t² + 1 = p m₀` give `1 ≤ m₀ < p`. -/
theorem seed_bounds {r p m0 : PTm k} (hp2 : Γ ⊢[PRAAx] le two p) (hr : Γ ⊢[PRAAx] lt r p)
    (es : Γ ⊢[PRAAx] r * r + one ≐ p * m0 + zero) : Γ ⊢[PRAAx] le one m0 ⋏ lt m0 p := by
  refine .andI ?_ ?_
  · refine .orE (zero_or_succ m0) ?_ (one_le_pos Prf.hyp0)
    have esn := natEq (es.wk (ψ := m0 ≐ zero))
    refine succ_ne_zero' (a := r * r) _ ?_
    ipra_lc esn + 𝔞 p * natEq (Prf.hyp0 (φ := m0 ≐ zero))
  · refine .orE (lt_or_le m0 p) Prf.hyp0 ?_
    have hle : (le p m0 :: Γ) ⊢[PRAAx] le p m0 := Prf.hyp0
    have hr' := hr.wk (ψ := le p m0)
    have hp2' := hp2.wk (ψ := le p m0)
    have esn := natEq (es.wk (ψ := le p m0))
    have bad : (le p m0 :: Γ) ⊢[PRAAx] le one zero := by
      ipra_le 𝔞 p * sl hle + sl hr' * (sl hp2' + 𝔞 r + 1) + 2 * sl hp2' + 1 with esn
    exact lt_zero_absurd _ bad

/-! ## The least multiplier -/

/-- `[i ≥ 1][i p is a sum of two squares]`, over `0 = i`, `1 = p`. -/
abbrev lB : PTm 2 := sg (var 0) * T (var 0 * var 1)

theorem inst2_lB (i p : PTm k) : inst2 lB i p = sg i * T (i * p) := by simp [inst2]

/-- The least multiplier `m ≥ 1` below `p` with `m p` a sum of two squares. -/
abbrev ms (p : PTm k) : PTm k := wit lB p p

theorem l_one {i p : PTm k} (hi : Γ ⊢[PRAAx] le one i) (hr : Γ ⊢[PRAAx] T (i * p) ≐ one) :
    Γ ⊢[PRAAx] neg (inst2 lB i p ≐ zero) :=
  signum_guard_nonzero (inst2_lB i p) hi hr

/-- **The descent**: a prime `p` with `p` odd and `⌊p/2⌋` even is a sum of two squares. -/
theorem rep_mod4 {p : PTm k} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] par p ≐ one)
    (hh : Γ ⊢[PRAAx] par (half p) ≐ zero) : Γ ⊢[PRAAx] T p ≐ one := by
  have hp2 := prime_two hp
  have hp1 := p_pos hp2
  have hr : Γ ⊢[PRAAx] lt (rt p) p := Prf.andE₁ (root_of_sign ((minus_one_law hp hodd).eqTrans hh))
  have es : Γ ⊢[PRAAx] rt p * rt p + one ≐ p * quo (rt p * rt p + one) p + zero :=
    (Prf.andE₁ (dm hp1 _)).eqTrans (congrAdd (.eqRefl _) (root_minus_one hp hodd hh))
  have sb := seed_bounds hp2 hr es
  have r0 := rep_intro (seed_alg es)
  have least := least_positive_witness lB (fun i => T (i * p)) (N := p) (x := p) (fun i => inst2_lB i p)
    (ex_cases tB (bd (ms p * p)) (ms p * p)) sb.andE₁ sb.andE₂ r0 (fun hlt hpass =>
      let d := two_descent hp.wk Prf.hyp0 hlt (rep_elim hpass)
      .andI (rep_intro d.andE₁) d.andE₂)
  exact rep_intro ((rep_elim least.andE₂).eqTrans ((congrMul least.andE₁ (.eqRefl p)).eqTrans (one_mul p)))

/-- **Fermat's two-square theorem by descent**: `X(p)² + Y(p)² = p` for a prime `p ≡ 1 (mod 4)`. -/
theorem two_squares_descent {p : PTm k} (hp : Γ ⊢[PRAAx] prime p)
    (h : Γ ⊢[PRAAx] rem p (two * two) ≐ one) : Γ ⊢[PRAAx] X p * X p + Y p * Y p ≐ p :=
  rep_elim (rep_mod4 hp (Prf.andE₁ (mod4_parities h)) (Prf.andE₂ (mod4_parities h)))

end LeanProofs.IPRA.DiophantineNumberTheory.TwoSquaresByDescent
