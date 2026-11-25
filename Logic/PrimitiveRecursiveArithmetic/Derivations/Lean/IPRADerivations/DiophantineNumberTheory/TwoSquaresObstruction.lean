import IPRADerivations.AnalyticNumberTheory.PrimesModFour
import IPRADerivations.AnalyticNumberTheory.PowerResidue
import IPRADerivations.Core.CertificateTactics

/-!
# Primes `q ≡ 3 (mod 4)` and sums of two squares

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/quadratic.tex`, Lemma
`qr:two-obstruction`, first assertion: if `q` is prime, `q ≡ 3 (mod 4)` and `q ∣ x² + y²`, then `q ∣ x` and
`q ∣ y`.

The class `3` modulo `4` enters as the two parities "`q` odd" and "`⌊q/2⌋` odd".

* `parities_three`: `q mod 4 = 3` gives these two parities;
* `no_root`: for such a prime, `z² + 1` is not divisible by `q` for any `z` (`QuadraticSupplements.minus_one_law`
  and `no_root_of_sign`, the root reduced modulo `q`);
* `scaled`: `(x² + y²) u² = (x u)² + (y u)²`;
* `unit_absurd`: if `y` is a unit modulo `q` with inverse `u` (`PowerResidue.inv`), then `q ∣ x² + y²` gives
  `q ∣ (x u)² + 1`, which is excluded;
* **`two_obstruction`**: `q ∣ x` and `q ∣ y`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.TwoSquaresObstruction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (rem_small)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidue (inv inv_spec)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm)
open LeanProofs.IPRA.Combinatorics.IndependentSets (half_double_succ)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gcd_comm_one dvd_sub' dvd_mul')
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_add_mul rem_add_congr rem_mul_congr2)
open LeanProofs.IPRA.DiophantineNumberTheory.ThueGrid (rem_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.QuadraticReciprocityGoal (signBit)
open LeanProofs.IPRA.DiophantineNumberTheory.QuadraticSupplements (minus_one_law no_root_of_sign)
open LeanProofs.IPRA.DiophantineNumberTheory.FermatTwoSquares (four_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The class `3` modulo `4` -/

/-- `q ≡ 3 (mod 4)` gives `q` odd and `⌊q/2⌋` odd. -/
theorem parities_three {q : PTm k} (h : Γ ⊢[PRAAx] rem q (two * two) ≐ succ two) :
    Γ ⊢[PRAAx] (par q ≐ one) ⋏ (par (half q) ≐ one) := by
  have d := natEq (Prf.andE₁ (dm (Γ := Γ) four_pos q)); have hn := natEq h
  have e : Γ ⊢[PRAAx] q ≐ two * (two * quo q (two * two) + one) + one := by
    ipra_lc d + hn
  refine .andI ((congrAp1 parF e).eqTrans (par_double_succ _)) ?_
  exact (congrAp1 parF ((congrAp1 halfF e).eqTrans (half_double_succ _))).eqTrans (par_double_succ _)

/-! ## No root of `−1` -/

theorem pred_alg {q : PTm k} (hq1 : Γ ⊢[PRAAx] q ≐ succ (pred q)) :
    Γ ⊢[PRAAx] pred q + one ≐ q * one + zero := by
  ipra_lc -natEq hq1

/-- For a prime `q` with `q` and `⌊q/2⌋` odd, no `z² + 1` is divisible by `q`. -/
theorem no_root {q : PTm k} (hq : Γ ⊢[PRAAx] prime q) (hodd : Γ ⊢[PRAAx] par q ≐ one)
    (h3 : Γ ⊢[PRAAx] par (half q) ≐ one) (z : PTm k) : Γ ⊢[PRAAx] neg (dvd q (z * z + one)) := by
  have hq1 := p_pos (prime_two hq)
  have hs : Γ ⊢[PRAAx] signBit q (pred q) ≐ one := (minus_one_law hq hodd).eqTrans h3
  have nr := no_root_of_sign hs (rem_lt' hq1 z)
  have rr : Γ ⊢[PRAAx] rem (rem z q) q ≐ rem z q := rem_small (rem_lt' hq1 z)
  have sq : Γ ⊢[PRAAx] rem (rem z q * rem z q) q ≐ rem (z * z) q := rem_mul_congr2 hq1 rr rr
  have pq : Γ ⊢[PRAAx] rem (pred q + one) q ≐ zero :=
    (congrAp2 remF (pred_alg hq1) (.eqRefl _)).eqTrans ((rem_add_mul hq1 one zero).eqTrans (rem_zero q))
  refine .impI ?_
  have h : (dvd q (z * z + one) :: Γ) ⊢[PRAAx] rem (z * z + one) q ≐ zero := Prf.hyp0
  have c : (dvd q (z * z + one) :: Γ) ⊢[PRAAx] rem (z * z) q ≐ rem (pred q) q :=
    rem_cancel hq1.wk ((congrAp2 remF (add_comm _ _) (.eqRefl _)).eqTrans
      (h.eqTrans (pq.wk.eqSymm.eqTrans (congrAp2 remF (add_comm _ _) (.eqRefl _)))))
  exact .impE nr.wk (sq.wk.eqTrans c)

/-! ## The unit case -/

theorem scaled (x y u : PTm k) :
    Γ ⊢[PRAAx] (x * x + y * y) * (u * u) ≐ (x * u) * (x * u) + (y * u) * (y * u) := by
  ipra_ring

theorem one_one : Γ ⊢[PRAAx] (one : PTm k) * one ≐ one := one_mul one

/-- If `y u ≡ 1 (mod q)` and `q ∣ x² + y²`, then `q ∣ (x u)² + 1`. -/
theorem root_of_unit {q x y u : PTm k} (hq1 : Γ ⊢[PRAAx] q ≐ succ (pred q))
    (iv : Γ ⊢[PRAAx] rem (y * u) q ≐ rem one q) (hd : Γ ⊢[PRAAx] dvd q (x * x + y * y)) :
    Γ ⊢[PRAAx] dvd q ((x * u) * (x * u) + one) := by
  have hd0 : Γ ⊢[PRAAx] rem (x * x + y * y) q ≐ rem zero q := hd.eqTrans (rem_zero q).eqSymm
  have m : Γ ⊢[PRAAx] rem ((x * x + y * y) * (u * u)) q ≐ zero :=
    (rem_mul_congr2 hq1 hd0 (.eqRefl (rem (u * u) q))).eqTrans
      ((congrAp2 remF (zero_mul _) (.eqRefl _)).eqTrans (rem_zero q))
  have a : Γ ⊢[PRAAx] rem ((x * u) * (x * u) + (y * u) * (y * u)) q ≐ rem ((x * u) * (x * u) + one * one) q :=
    rem_add_congr hq1 (.eqRefl _) (rem_mul_congr2 hq1 iv iv)
  have b : Γ ⊢[PRAAx] rem ((x * u) * (x * u) + one * one) q ≐ rem ((x * u) * (x * u) + one) q :=
    congrAp2 remF (congrAdd (.eqRefl _) one_one) (.eqRefl _)
  exact b.eqSymm.eqTrans (a.eqSymm.eqTrans ((congrAp2 remF (scaled x y u).eqSymm (.eqRefl _)).eqTrans m))

/-! ## The obstruction -/

/-- **`qr:two-obstruction`**: for a prime `q ≡ 3 (mod 4)`, `q ∣ x² + y²` gives `q ∣ x` and `q ∣ y`. -/
theorem two_obstruction {q x y : PTm k} (hq : Γ ⊢[PRAAx] prime q) (hodd : Γ ⊢[PRAAx] par q ≐ one)
    (h3 : Γ ⊢[PRAAx] par (half q) ≐ one) (hd : Γ ⊢[PRAAx] dvd q (x * x + y * y)) :
    Γ ⊢[PRAAx] dvd q x ⋏ dvd q y := by
  have hq2 := prime_two hq
  have hq1 := p_pos hq2
  refine .orE (eq_or_ne (rem y q) zero) ?_ ?_
  · -- `q ∣ y`, hence `q ∣ x²` and `q ∣ x`
    have dy : ((rem y q ≐ zero) :: Γ) ⊢[PRAAx] dvd q y := Prf.hyp0
    have dyy : ((rem y q ≐ zero) :: Γ) ⊢[PRAAx] dvd q (y * y) := dvd_mul' hq1.wk y dy
    have dxx : ((rem y q ≐ zero) :: Γ) ⊢[PRAAx] dvd q (x * x) := dvd_sub' hq1.wk hd.wk dyy
    exact .andI (.orE (euclid_lemma_at hq.wk dxx) Prf.hyp0 Prf.hyp0) dy
  · -- `q ∤ y`: `y` is a unit, and `x / y` would be a root of `−1`
    have hny : (neg (rem y q ≐ zero) :: Γ) ⊢[PRAAx] neg (dvd q y) := Prf.hyp0
    have g1 : (neg (rem y q ≐ zero) :: Γ) ⊢[PRAAx] gcd q y ≐ one := gcd_prime hq.wk hny
    have ypos : (neg (rem y q ≐ zero) :: Γ) ⊢[PRAAx] y ≐ succ (pred y) := by
      refine .orE (zero_or_succ y) ?_ Prf.hyp0
      have y0 : ((y ≐ zero) :: neg (rem y q ≐ zero) :: Γ) ⊢[PRAAx] y ≐ zero := Prf.hyp0
      exact .botE _ (.impE hny.wk ((congrAp2 remF y0 (.eqRefl _)).eqTrans (rem_zero q)))
    have g2 : (neg (rem y q ≐ zero) :: Γ) ⊢[PRAAx] gcd y q ≐ one := gcd_comm_one ypos g1
    have iv := inv_spec hq2.wk g2
    have r := root_of_unit hq1.wk iv hd.wk
    exact .botE _ (.impE (no_root hq.wk hodd.wk h3.wk (x * inv y q)) r)

/-- The same with the class given as `q mod 4 = 3`. -/
theorem two_obstruction_mod4 {q x y : PTm k} (hq : Γ ⊢[PRAAx] prime q)
    (h : Γ ⊢[PRAAx] rem q (two * two) ≐ succ two) (hd : Γ ⊢[PRAAx] dvd q (x * x + y * y)) :
    Γ ⊢[PRAAx] dvd q x ⋏ dvd q y :=
  two_obstruction hq (Prf.andE₁ (parities_three h)) (Prf.andE₂ (parities_three h)) hd

end LeanProofs.IPRA.DiophantineNumberTheory.TwoSquaresObstruction
