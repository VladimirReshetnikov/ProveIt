import IPRADerivations.DiophantineNumberTheory.TwoSquaresObstruction

/-!
# The valuation of a sum of two squares at a prime `q ≡ 3 (mod 4)`

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/quadratic.tex`, Lemma
`qr:two-obstruction`, second assertion: if `n = x² + y² > 0` and `q` is a prime `≡ 3 (mod 4)`, then `v_q(n)` is
even. This is the necessity half of the two-square classification `qr:two-classification`.

The proof of the packet: let `t` be the smaller of the valuations of the nonzero coordinates, `x = q^t u`,
`y = q^t w` with `q ∤ u` or `q ∤ w`. Then `n = q^{2t} (u² + w²)` and `q ∤ u² + w²` by
`TwoSquaresObstruction.two_obstruction`, so `v_q(n) = 2t` (`ValuationMul.val_unique`).

* `decomp_alg`: `n = q^{2t} (u² + w²)` from `x = q^t u`, `y = q^t w`;
* `val_of_decomp`: `v_q(n) = 2t` when `q ∤ u`; `val_of_decomp'`: the same when `q ∤ w`;
* `sq_case`: `v_q(z²)` is even (the case of a zero coordinate);
* `re_alg`, `shift_decomp`: `y = q^{t_y} u_y` and `t ≤ t_y` give `y = q^t (q^{t_y − t} u_y)`;
* **`two_squares_val_even`**: `par (v_q(n)) = 0`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.TwoSquaresValuation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val cof_eq cof_not_dvd)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (val_unique val_mul val_congr)
open LeanProofs.IPRA.DiophantineNumberTheory.TwoSquaresObstruction (two_obstruction)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The decomposition -/

theorem decomp_alg {n x y u w Pt P2 : PTm k} (en : Γ ⊢[PRAAx] x * x + y * y ≐ n)
    (ex : Γ ⊢[PRAAx] x ≐ Pt * u) (ey : Γ ⊢[PRAAx] y ≐ Pt * w) (pp : Γ ⊢[PRAAx] P2 ≐ Pt * Pt) :
    Γ ⊢[PRAAx] n ≐ P2 * (u * u + w * w) := by
  have a := natEq en; have b := natEq ex; have c := natEq ey; have d := natEq pp
  apply deriveNat; ipra_simps
  linear_combination -a + (𝔞 x + 𝔞 Pt * 𝔞 u) * b + (𝔞 y + 𝔞 Pt * 𝔞 w) * c - (𝔞 u * 𝔞 u + 𝔞 w * 𝔞 w) * d

theorem dbl (t : PTm k) : Γ ⊢[PRAAx] two * t ≐ t + t := by apply deriveNat; ipra_simps; ring

theorem pw_dbl (q t : PTm k) : Γ ⊢[PRAAx] pw q (two * t) ≐ pw q t * pw q t :=
  (congrAp2 powF (dbl t) (.eqRefl q)).eqTrans (pw_add q t t)

section Prime

variable {q : PTm k} (hq : Γ ⊢[PRAAx] prime q) (hodd : Γ ⊢[PRAAx] par q ≐ one)
  (h3 : Γ ⊢[PRAAx] par (half q) ≐ one)
include hq hodd h3

/-- `x = q^t u`, `y = q^t w`, `q ∤ u`, `n = x² + y² > 0` give `v_q(n) = 2t`. -/
theorem val_of_decomp {n x y t u w : PTm k} (en : Γ ⊢[PRAAx] x * x + y * y ≐ n)
    (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) (ex : Γ ⊢[PRAAx] x ≐ pw q t * u) (ey : Γ ⊢[PRAAx] y ≐ pw q t * w)
    (hu : Γ ⊢[PRAAx] neg (dvd q u)) : Γ ⊢[PRAAx] val q n ≐ two * t := by
  refine val_unique (prime_two hq) hn (c := u * u + w * w) (decomp_alg en ex ey (pw_dbl q t)) ?_
  refine .impI ?_
  have d : (dvd q (u * u + w * w) :: Γ) ⊢[PRAAx] dvd q (u * u + w * w) := Prf.hyp0
  exact .impE hu.wk (Prf.andE₁ (two_obstruction hq.wk hodd.wk h3.wk d))

/-- The same with `q ∤ w`. -/
theorem val_of_decomp' {n x y t u w : PTm k} (en : Γ ⊢[PRAAx] x * x + y * y ≐ n)
    (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) (ex : Γ ⊢[PRAAx] x ≐ pw q t * u) (ey : Γ ⊢[PRAAx] y ≐ pw q t * w)
    (hw : Γ ⊢[PRAAx] neg (dvd q w)) : Γ ⊢[PRAAx] val q n ≐ two * t :=
  val_of_decomp hq hodd h3 ((add_comm _ _).eqTrans en) hn ey ex hw

omit hodd h3 in
/-- `v_q(z²)` is even for `z ≥ 1`. -/
theorem sq_case {z n : PTm k} (hz : Γ ⊢[PRAAx] z ≐ succ (pred z)) (e : Γ ⊢[PRAAx] z * z ≐ n) :
    Γ ⊢[PRAAx] par (val q n) ≐ zero := by
  have v := (val_congr q e.eqSymm).eqTrans ((val_mul hq hz hz).eqTrans (dbl (val q z)).eqSymm)
  exact (congrAp1 parF v).eqTrans (par_double _)

end Prime

theorem re_alg {y A B C U : PTm k} (e0 : Γ ⊢[PRAAx] y ≐ A * U) (ep : Γ ⊢[PRAAx] A ≐ B * C) :
    Γ ⊢[PRAAx] y ≐ B * (C * U) := by
  have a := natEq e0; have b := natEq ep
  apply deriveNat; ipra_simps; linear_combination a + 𝔞 U * b

/-- `y = q^{s} U` and `t ≤ s` give `y = q^t (q^{s − t} U)`. -/
theorem shift_decomp {q y s t U : PTm k} (e0 : Γ ⊢[PRAAx] y ≐ pw q s * U) (h : Γ ⊢[PRAAx] le t s) :
    Γ ⊢[PRAAx] y ≐ pw q t * (pw q (monus s t) * U) :=
  re_alg e0 ((congrAp2 powF (eq_add_of_le h) (.eqRefl q)).eqTrans (pw_add q t (monus s t)))

theorem zero_sq_alg {x y n : PTm k} (e : Γ ⊢[PRAAx] x * x + y * y ≐ n) (hx : Γ ⊢[PRAAx] x ≐ zero) :
    Γ ⊢[PRAAx] y * y ≐ n := by
  have a := natEq e; have b := natEq hx
  apply deriveNat; ipra_simps; linear_combination a - 𝔞 x * b

theorem zero_zero_alg {x y n : PTm k} (e : Γ ⊢[PRAAx] x * x + y * y ≐ n) (hx : Γ ⊢[PRAAx] x ≐ zero)
    (hy : Γ ⊢[PRAAx] y ≐ zero) : Γ ⊢[PRAAx] n ≐ zero := by
  have a := natEq e; have b := natEq hx; have c := natEq hy
  apply deriveNat; ipra_simps; linear_combination -a + 𝔞 x * b + 𝔞 y * c

/-- **`qr:two-obstruction`, second assertion**: for a prime `q ≡ 3 (mod 4)` and `n = x² + y² > 0`, the valuation
`v_q(n)` is even. -/
theorem two_squares_val_even {q x y n : PTm k} (hq : Γ ⊢[PRAAx] prime q) (hodd : Γ ⊢[PRAAx] par q ≐ one)
    (h3 : Γ ⊢[PRAAx] par (half q) ≐ one) (en : Γ ⊢[PRAAx] x * x + y * y ≐ n)
    (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) : Γ ⊢[PRAAx] par (val q n) ≐ zero := by
  have h2 := prime_two hq
  refine .orE (zero_or_succ x) ?_ ?_
  · -- `x = 0`: `n = y²`
    have x0 : ((x ≐ zero) :: Γ) ⊢[PRAAx] x ≐ zero := Prf.hyp0
    refine .orE (zero_or_succ y) ?_ ?_
    · have y0 : ((y ≐ zero) :: (x ≐ zero) :: Γ) ⊢[PRAAx] y ≐ zero := Prf.hyp0
      have nz := zero_zero_alg en.wk.wk x0.wk y0
      exact succ_ne_zero' _ (a := pred n) (hn.wk.wk.eqSymm.eqTrans nz)
    · have yp : ((y ≐ succ (pred y)) :: (x ≐ zero) :: Γ) ⊢[PRAAx] y ≐ succ (pred y) := Prf.hyp0
      exact sq_case hq.wk.wk yp (zero_sq_alg en.wk.wk x0.wk)
  · have xp : ((x ≐ succ (pred x)) :: Γ) ⊢[PRAAx] x ≐ succ (pred x) := Prf.hyp0
    refine .orE (zero_or_succ y) ?_ ?_
    · -- `y = 0`: `n = x²`
      have y0 : ((y ≐ zero) :: (x ≐ succ (pred x)) :: Γ) ⊢[PRAAx] y ≐ zero := Prf.hyp0
      exact sq_case hq.wk.wk xp.wk (zero_sq_alg ((add_comm _ _).eqTrans en.wk.wk) y0)
    · -- both coordinates positive: compare the two valuations
      let C : List (Fm PTm k) := (y ≐ succ (pred y)) :: (x ≐ succ (pred x)) :: Γ
      have yp : C ⊢[PRAAx] y ≐ succ (pred y) := Prf.hyp0
      have xp' : C ⊢[PRAAx] x ≐ succ (pred x) := xp.wk
      have ex := cof_eq (Γ := C) (m := x) h2.wk.wk
      have ey := cof_eq (Γ := C) (m := y) h2.wk.wk
      have ux := cof_not_dvd h2.wk.wk xp'
      have uy := cof_not_dvd h2.wk.wk yp
      refine .orE (le_total (val q x) (val q y)) ?_ ?_
      · have hle : (le (val q x) (val q y) :: C) ⊢[PRAAx] le (val q x) (val q y) := Prf.hyp0
        have v := val_of_decomp hq.wk.wk.wk hodd.wk.wk.wk h3.wk.wk.wk en.wk.wk.wk hn.wk.wk.wk ex.wk
          (shift_decomp ey.wk hle) ux.wk
        exact (congrAp1 parF v).eqTrans (par_double _)
      · have hle : (le (val q y) (val q x) :: C) ⊢[PRAAx] le (val q y) (val q x) := Prf.hyp0
        have v := val_of_decomp' hq.wk.wk.wk hodd.wk.wk.wk h3.wk.wk.wk en.wk.wk.wk hn.wk.wk.wk
          (shift_decomp ex.wk hle) ey.wk uy.wk
        exact (congrAp1 parF v).eqTrans (par_double _)

end LeanProofs.IPRA.DiophantineNumberTheory.TwoSquaresValuation
