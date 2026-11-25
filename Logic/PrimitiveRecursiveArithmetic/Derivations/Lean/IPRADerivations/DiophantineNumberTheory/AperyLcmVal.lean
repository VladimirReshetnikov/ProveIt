import IPRADerivations.DiophantineNumberTheory.AperyMultinomial
import IPRADerivations.AnalyticNumberTheory.BinomialLcm
import IPRADerivations.Core.CertificateTactics

/-!
# The valuation of the Apéry multinomial

Packet: `diophantine-number-theory/apery_ipra`, Lemma `lem:lcm-div`, the valuation identity behind the proof:
for a prime `p`, with Legendre's formula `v_p(N!) = L(N) = ∑_{j<N} ⌊N/p^{j+1}⌋`
(`Combinatorics/LegendreFact.legendre_fact`),

  `v_p(M_m) + L(21m) + L(14m) + L(6m) + L(m) = L(42m)`

for `M_m = C(42m, 21m) C(21m, 14m) C(7m, 6m)` (`AperyMultinomial.Mm`).

* `binom_fact`, `binom_pos`: `n! = k! (n−k)! C(n, k)` and `C(n, k) ≥ 1` for `k ≤ n`;
* `val_binom`: `v_p(C(n, k)) + v_p(k!) + v_p((n−k)!) = v_p(n!)`;
* `val_Mm`: the identity above.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.AperyLcmVal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (val_mul val_congr)
open LeanProofs.IPRA.Combinatorics.Binomial (binom bden bden_pos binom_rem_zero eq_of_rem_zero pos_mul)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (qB')
open LeanProofs.IPRA.Combinatorics.LegendreFact (legendre_fact)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultinomial (Mm)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem binom_fact {n j : PTm k} (h : Γ ⊢[PRAAx] le j n) : Γ ⊢[PRAAx] fact n ≐ bden n j * binom n j :=
  eq_of_rem_zero (bden_pos n j) (binom_rem_zero h)

theorem binom_pos {n j : PTm k} (h : Γ ⊢[PRAAx] le j n) : Γ ⊢[PRAAx] binom n j ≐ succ (pred (binom n j)) := by
  refine .orE (zero_or_succ (binom n j)) ?_ Prf.hyp0
  have h0 : ((binom n j ≐ zero) :: Γ) ⊢[PRAAx] binom n j ≐ zero := Prf.hyp0
  have c : ((binom n j ≐ zero) :: Γ) ⊢[PRAAx] succ (pred (fact n)) ≐ zero := by
    ipra_lc -natEq ((fact_pos (Γ := (binom n j ≐ zero) :: Γ) n)) + natEq ((binom_fact h).wk (ψ := binom n j ≐ zero)) +
      𝔞 (fact j) * 𝔞 (fact (monus n j)) * natEq h0
  exact succ_ne_zero' _ c

/-- `v_p(C(n, j)) + v_p(j!) + v_p((n − j)!) = v_p(n!)`. -/
theorem val_binom {p n j : PTm k} (hp : Γ ⊢[PRAAx] prime p) (h : Γ ⊢[PRAAx] le j n) :
    Γ ⊢[PRAAx] val p (binom n j) + (val p (fact j) + val p (fact (monus n j))) ≐ val p (fact n) := by
  ipra_lc -natEq ((val_congr p (binom_fact (Γ := Γ) h)).eqTrans (val_mul hp (bden_pos n j) (binom_pos h))) -
    natEq (val_mul (Γ := Γ) hp (fact_pos j) (fact_pos (monus n j)))

/-- `L(N) = ∑_{j<N} ⌊N/p^{j+1}⌋`. -/
abbrev L (p N : PTm k) : PTm k := ap2 (sumF qB') N (pairT p N)

theorem monus_split {a b c : PTm k} (h : Γ ⊢[PRAAx] a ≐ c + b) : Γ ⊢[PRAAx] monus a b ≐ c :=
  (congrMonus h (.eqRefl b)).eqTrans (add_monus c b)

/-- `v_p(M_m) + L(21m) + L(14m) + L(6m) + L(m) = L(42m)`. -/
theorem val_Mm {p : PTm k} (hp : Γ ⊢[PRAAx] prime p) (m : PTm k) :
    Γ ⊢[PRAAx] val p (Mm m) + L p (num 21 * m) + L p (num 14 * m) + L p (num 6 * m) + L p m ≐ L p (num 42 * m) := by
  have l1 : Γ ⊢[PRAAx] le (num 21 * m) (num 42 * m) := by ipra_le 21 * 𝔞 m
  have l2 : Γ ⊢[PRAAx] le (num 14 * m) (num 21 * m) := by ipra_le 7 * 𝔞 m
  have l3 : Γ ⊢[PRAAx] le (num 6 * m) (num 7 * m) := by ipra_le 𝔞 m
  have p1 := binom_pos l1; have p2 := binom_pos l2; have p3 := binom_pos l3
  ipra_lc natEq (val_mul hp (pos_mul p1 p2) p3) + natEq (val_mul hp p1 p2) + natEq (val_binom hp l1) +
    natEq (val_binom hp l2) + natEq (val_binom hp l3) -
    natEq (val_congr p (congrAp2 factF (monus_split (Γ := Γ) (a := num 42 * m) (b := num 21 * m) (c := num 21 * m) (by ipra_ring)) (.eqRefl zero))) -
    natEq (val_congr p (congrAp2 factF (monus_split (Γ := Γ) (a := num 21 * m) (b := num 14 * m) (c := num 7 * m) (by ipra_ring)) (.eqRefl zero))) -
    natEq (val_congr p (congrAp2 factF (monus_split (Γ := Γ) (a := num 7 * m) (b := num 6 * m) (c := m) (by ipra_ring)) (.eqRefl zero))) -
    natEq (legendre_fact (Γ := Γ) hp (num 21 * m)) - natEq (legendre_fact (Γ := Γ) hp (num 14 * m)) -
    natEq (legendre_fact (Γ := Γ) hp (num 6 * m)) - natEq (legendre_fact (Γ := Γ) hp m) +
    natEq (legendre_fact (Γ := Γ) hp (num 42 * m))

end LeanProofs.IPRA.DiophantineNumberTheory.AperyLcmVal
