import IPRADerivations.Combinatorics.CatalanBallot
import IPRADerivations.Core.CertificateTactics

/-!
# Ballot, two-fold and Fuss–Catalan identities (`catalan_numbers_ipra_2026-11-16`, Section 7)

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16`, Section "Ballot, convolution, rational,
Fuss, and super-Catalan extensions":

* (7.1) "`(1/(2n + 1)) C(2n + 1, n) = Cat_n`" (Bertrand's ballot theorem at excess one);
* (7.3) "`Σ_{i_1 + ⋯ + i_k = n} Cat_{i_1} ⋯ Cat_{i_k} = (k/(2n + k)) C(2n + k, n)`";
* (7.5) "`(1/((p − 1)k + 1)) C(pk, k) = (1/k) C(pk, k − 1)` (`k ≥ 1`)" (the two forms of the
  Fuss–Catalan numbers).

Derived, cleared of denominators, from the ratio `(N − j) C(N, j) = (j + 1) C(N, j + 1)` of
`Combinatorics/CatalanBallot`, Pascal's rule and `(n + 1) Cat_n = C(2n, n)`:

* `two_fold`: `C(2n + 2, n) = (n + 1) Cat_{n+1}`, the right side of (7.3) for `k = 2`
  (`(2/(2n + 2)) C(2n + 2, n) = Cat_{n+1}`, the value of the two-fold convolution by Segner's
  recurrence of `Combinatorics/CatalanConvolution`);
* `ballot_zero`, `ballot_succ`, `ballot`: (7.1), `C(2n + 1, n) = (2n + 1) Cat_n`, for every `n`
  (the uniform statement by a quantifier-free induction whose step does not use its
  hypothesis);
* `ballot_closed`: (7.1) as a closed sentence;
* `fuss`: (7.5), `k C(pk, k) = ((p − 1)k + 1) C(pk, k − 1)` with `p = p' + 1`, `k = k' + 1`.

Not derived: the cycle lemma and the word bijection behind (7.1), and the generating-function
statements (7.6)–(7.13). The `k`-fold convolution (7.3) for every `k` is
`Combinatorics/CatalanKFold`, and the integrality of the super-Catalan numbers (7.14) is
`Combinatorics/SuperCatalanIntegral`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CatalanExtensions

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_zero' mul_cancel pascal_at)
open LeanProofs.IPRA.Combinatorics.Catalan (cb cat cat_spec cat_zero succ_pos)
open LeanProofs.IPRA.Combinatorics.CatalanBallot (binom_ratio)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `m < 2(m + 1)`. -/
theorem lt_double (m : PTm n) : Γ ⊢[PRAAx] lt m (two * succ m) :=
  le_of_eq_add (d := succ m) (by ipra_ring)

/-- (7.3) for `k = 2`, right side: `C(2m + 2, m) = (m + 1) Cat_{m+1}`. -/
theorem two_fold (m : PTm n) :
    Γ ⊢[PRAAx] binom (two * succ m) m ≐ succ m * cat (succ m) := by
  have hm : Γ ⊢[PRAAx] monus (two * succ m) m ≐ succ (succ m) :=
    (congrMonus (by ipra_ring :
      Γ ⊢[PRAAx] two * succ m ≐ succ (succ m) + m) (.eqRefl _)).eqTrans (add_monus _ _)
  refine mul_cancel (D := succ (succ m)) (succ_pos _) ?_
  ipra_lc natEq (binom_ratio (lt_double (Γ := Γ) m)) - 𝔞 (binom (two * succ m) m) * natEq hm -
    (𝔞 m + 1) * natEq (cat_spec (Γ := Γ) (succ m))

/-- (7.1) at `n = 0`. -/
theorem ballot_zero :
    Γ ⊢[PRAAx] binom (succ (two * (zero : PTm n))) zero ≐ succ (two * zero) * cat zero := by
  refine (binom_zero' _).eqTrans ?_
  ipra_lc -natEq (cat_zero (Γ := Γ) (n := n))

/-- (7.1) at a successor: `C(2k + 3, k + 1) = (2k + 3) Cat_{k+1}`. -/
theorem ballot_succ (m : PTm n) :
    Γ ⊢[PRAAx] binom (succ (two * succ m)) (succ m) ≐ succ (two * succ m) * cat (succ m) := by
  ipra_lc natEq (pascal_at (lt_double (Γ := Γ) m)) + natEq (two_fold (Γ := Γ) m) - natEq (cat_spec (Γ := Γ) (succ m))

/-- Variables: `0 = n`. -/
private abbrev ballotF : Fm PTm 1 :=
  binom (succ (two * var 0)) (var 0) ≐ succ (two * var 0) * cat (var 0)

private theorem ballot₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] ballotF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_mul, PTm.subst_monus, subst_ap2, Syn.subst_var,
      Syn.inst_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact ballot_zero
  · simp only [Fm.subst_eq, PTm.subst_mul, PTm.subst_monus, subst_ap2, Syn.subst_var,
      Syn.repl_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact ballot_succ _

/-- (7.1), Bertrand's ballot theorem at excess one: `C(2n + 1, n) = (2n + 1) Cat_n`. -/
theorem ballot (m : PTm n) :
    Γ ⊢[PRAAx] binom (succ (two * m)) m ≐ succ (two * m) * cat m := by
  have h := inst (Γ := Γ) ballot₀ (![m] : Fin 1 → PTm n)
  simpa using h

/-- (7.1) as a closed sentence. -/
theorem ballot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (binom (succ (two * var 0)) (var 0) ≐ succ (two * var 0) * cat (var 0)) :=
  closeUniv 1 (ballot _)

/-- (7.5), the two forms of the Fuss–Catalan numbers:
`k C(pk, k) = ((p − 1)k + 1) C(pk, k − 1)` with `p = p' + 1`, `k = k' + 1`. -/
theorem fuss (p' k' : PTm n) :
    Γ ⊢[PRAAx] succ k' * binom (succ p' * succ k') (succ k') ≐
      succ (p' * succ k') * binom (succ p' * succ k') k' := by
  have hlt : Γ ⊢[PRAAx] lt k' (succ p' * succ k') :=
    le_of_eq_add (d := p' * succ k') (by ipra_ring)
  have hm : Γ ⊢[PRAAx] monus (succ p' * succ k') k' ≐ succ (p' * succ k') :=
    (congrMonus (by ipra_ring :
      Γ ⊢[PRAAx] succ p' * succ k' ≐ succ (p' * succ k') + k') (.eqRefl _)).eqTrans
      (add_monus _ _)
  exact (binom_ratio hlt).eqSymm.eqTrans (congrMul hm (.eqRefl _))

end LeanProofs.IPRA.Combinatorics.CatalanExtensions
