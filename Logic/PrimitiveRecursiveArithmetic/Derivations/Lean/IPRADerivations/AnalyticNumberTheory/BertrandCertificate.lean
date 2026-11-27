import IPRADerivations.AnalyticNumberTheory.BertrandSearch
import IPRADerivations.Foundations.NumeralPrimes

/-!
# Bertrand's postulate: the finite certificate

Packet: `analytic-number-theory/bertrand_ipra`, `bertrand.tex`, §"Covering every small input": the table of
ten primes, each serving a block of inputs `n` with `n < p < 2n − 2`:

    p     5   7   11     19      31      59      113       223        443        883
    n     4   5–6 7–10   11–18   19–30   31–58   59–112    113–222    223–442    443–882

* `prime_5`, …, `prime_883`: `prime (num p)`, by the trial-division certificate of
  `Foundations/NumeralPrimes.prime_num` (the remainders of the table are checked by `decide`);
* `interval`: for `lo ≤ x ≤ hi` with `hi < p` and `p + 3 ≤ 2 lo`, the prime `p` lies in `(x, 2x − 2)`, so the
  search cannot have failed;
* `small`: a failed search is impossible for `4 ≤ x ≤ 882`.

The paper stops the table at `n < 722`, where the integer inequality takes over; the last row serves the inputs
up to `882`, and the split here is made at `882`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.BertrandCertificate

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.BertrandSearch (found limit exclude_interval_prime)
open LeanProofs.IPRA.Foundations.NumeralPrimes (prime_num num_le num_lt)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The ten primes -/

theorem prime_5 : Γ ⊢[PRAAx] prime (num 5 : PTm n) := prime_num 5 2 (by norm_num) (by norm_num) (by decide)
theorem prime_7 : Γ ⊢[PRAAx] prime (num 7 : PTm n) := prime_num 7 2 (by norm_num) (by norm_num) (by decide)
theorem prime_11 : Γ ⊢[PRAAx] prime (num 11 : PTm n) := prime_num 11 3 (by norm_num) (by norm_num) (by decide)
theorem prime_19 : Γ ⊢[PRAAx] prime (num 19 : PTm n) := prime_num 19 4 (by norm_num) (by norm_num) (by decide)
theorem prime_31 : Γ ⊢[PRAAx] prime (num 31 : PTm n) := prime_num 31 5 (by norm_num) (by norm_num) (by decide)
theorem prime_59 : Γ ⊢[PRAAx] prime (num 59 : PTm n) := prime_num 59 7 (by norm_num) (by norm_num) (by decide)
theorem prime_113 : Γ ⊢[PRAAx] prime (num 113 : PTm n) :=
  prime_num 113 10 (by norm_num) (by norm_num) (by decide)
theorem prime_223 : Γ ⊢[PRAAx] prime (num 223 : PTm n) :=
  prime_num 223 14 (by norm_num) (by norm_num) (by decide)
theorem prime_443 : Γ ⊢[PRAAx] prime (num 443 : PTm n) :=
  prime_num 443 21 (by norm_num) (by norm_num) (by decide)
theorem prime_883 : Γ ⊢[PRAAx] prime (num 883 : PTm n) :=
  prime_num 883 29 (by norm_num) (by norm_num) (by decide)

/-! ## One block of the table -/

/-- For `lo ≤ x ≤ hi` with `hi < p` and `p + 3 ≤ 2 lo`, the prime `p` refutes the failure of the search. -/
theorem interval {x : PTm n} (p lo hi : ℕ) (h1 : hi < p) (h2 : p + 3 ≤ 2 * lo)
    (hp : Γ ⊢[PRAAx] prime (num p)) (fail : Γ ⊢[PRAAx] found x ≐ zero)
    (hlo : Γ ⊢[PRAAx] le (num lo) x) (hhi : Γ ⊢[PRAAx] le x (num hi)) : Γ ⊢[PRAAx] Fm.bot := by
  obtain ⟨c, hc⟩ : ∃ c, 2 * lo = p + 3 + c := ⟨2 * lo - (p + 3), by omega⟩
  have l2 : Γ ⊢[PRAAx] le two (two * x) := by
    ipra_le 2 * sl hlo + ((p + 1 + c : ℕ) : Groth (Q Γ)) using
      (have k := congrArg (fun t : ℕ => (t : Groth (Q Γ))) hc
       push_cast at k ⊢
       linear_combination k)
  have e := natEq (eq_add_of_le l2)
  have up : Γ ⊢[PRAAx] lt (num p) (limit x) := by
    ipra_le 2 * sl hlo + (c : Groth (Q Γ)) using
      (have k := congrArg (fun t : ℕ => (t : Groth (Q Γ))) hc
       push_cast at k ⊢
       linear_combination k - e)
  exact exclude_interval_prime fail (lt_of_le_of_lt hhi (num_lt h1)) up hp

/-- One row: either `x` is beyond the block, or the block's prime refutes the failure. -/
theorem row {x : PTm n} (p lo hi : ℕ) (h1 : hi < p) (h2 : p + 3 ≤ 2 * lo)
    (hp : Γ ⊢[PRAAx] prime (num p)) (fail : Γ ⊢[PRAAx] found x ≐ zero)
    (hlo : Γ ⊢[PRAAx] le (num lo) x) (rest : (lt (num hi) x :: Γ) ⊢[PRAAx] Fm.bot) : Γ ⊢[PRAAx] Fm.bot :=
  .orE (lt_or_le (num hi) x) rest (interval p lo hi h1 h2 hp.wk fail.wk hlo.wk Prf.hyp0)

/-! ## The table -/

/-- A failed search is impossible for `4 ≤ x ≤ 882`. -/
theorem small {x : PTm n} (fail : Γ ⊢[PRAAx] found x ≐ zero) (h4 : Γ ⊢[PRAAx] le (num 4) x)
    (hle : Γ ⊢[PRAAx] le x (num 882)) : Γ ⊢[PRAAx] Fm.bot := by
  refine row 5 4 4 (by norm_num) (by norm_num) prime_5 fail h4 ?_
  have f1 := fail.wk (ψ := lt (num 4) x)
  refine row 7 5 6 (by norm_num) (by norm_num) prime_7 f1 Prf.hyp0 ?_
  have f2 := f1.wk (ψ := lt (num 6) x)
  refine row 11 7 10 (by norm_num) (by norm_num) prime_11 f2 Prf.hyp0 ?_
  have f3 := f2.wk (ψ := lt (num 10) x)
  refine row 19 11 18 (by norm_num) (by norm_num) prime_19 f3 Prf.hyp0 ?_
  have f4 := f3.wk (ψ := lt (num 18) x)
  refine row 31 19 30 (by norm_num) (by norm_num) prime_31 f4 Prf.hyp0 ?_
  have f5 := f4.wk (ψ := lt (num 30) x)
  refine row 59 31 58 (by norm_num) (by norm_num) prime_59 f5 Prf.hyp0 ?_
  have f6 := f5.wk (ψ := lt (num 58) x)
  refine row 113 59 112 (by norm_num) (by norm_num) prime_113 f6 Prf.hyp0 ?_
  have f7 := f6.wk (ψ := lt (num 112) x)
  refine row 223 113 222 (by norm_num) (by norm_num) prime_223 f7 Prf.hyp0 ?_
  have f8 := f7.wk (ψ := lt (num 222) x)
  refine row 443 223 442 (by norm_num) (by norm_num) prime_443 f8 Prf.hyp0 ?_
  have f9 := f8.wk (ψ := lt (num 442) x)
  refine row 883 443 882 (by norm_num) (by norm_num) prime_883 f9 Prf.hyp0 ?_
  exact le_lt_absurd _ (hle.weaken (by intro a ha; simp [ha])) Prf.hyp0

end LeanProofs.IPRA.AnalyticNumberTheory.BertrandCertificate
