import IPRADerivations.Combinatorics.BellPeriodNp
import IPRADerivations.Core.CertificateTactics

/-!
# The order-`m` recurrence of the Bell numbers modulo `m` (`bell_numbers_ipra`, `thm:all-moduli-period`)

Packet: `combinatorics/bell_numbers_ipra`, `paper/04_congruences.tex`, theorem
`thm:all-moduli-period`. Its proof starts from the finite shift identity for
`Q_m(X) = (X)_m − 1 = X^m + c_{m−1} X^{m−1} + ⋯ + c_1 X − 1`: "Taking `f = X^n` yields the
order-`m` recurrence `B_{n+m} ≡ B_n − ∑_{j=1}^{m−1} c_j B_{n+j} (mod m)`
(`eq:composite-recurrence`)."

Modulo `m` the falling factorial `(X)_m = X(X − 1) ⋯ (X − m + 1)` is `(X + 1)(X + 2) ⋯ (X + m)`,
whose coefficients are the natural numbers `cyc m K` of `Combinatorics/LinearFactorTable`. The
two steps of `Combinatorics/BellPeriodNp` that do not use primality give, for every `m ≥ 1`:

* `bell_recurrence_mod`: `∑_{K ≤ m} c(m, K) B_{N+K} ≡ B_N (mod m)`
  (`G(N, m) ≡ B_N` and `G(N, m) ≡ ((E + 1) ⋯ (E + m) B)_N`);
* `cyc_self`: the leading coefficient `c(N, N) = 1`;
* `act_split`: the sum with its first and last terms separated;
* `recurrence_split` (`eq:composite-recurrence`, with the subtraction moved to the left):
  `B_{N+m} + ∑_{0 < K < m} c(m, K) B_{N+K} ≡ B_N (mod m)`; the term `K = 0` drops because
  `c(m, 0) = m!` is a multiple of `m`.

The recurrence can be read forwards (`B_{N+m}` from the `m` preceding values) and backwards
(`B_N` from the `m` following values), which is the invertibility of the transition used in
the packet. Not derived here: the state vectors, the pigeonhole collision and the period.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BellModularRecurrence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Bell (bell)
open LeanProofs.IPRA.Combinatorics.BellPascalInversion (congrBell)
open LeanProofs.IPRA.Combinatorics.BellTouchardPower (cong_of_eq)
open LeanProofs.IPRA.Combinatorics.BellPrimePeriod (cong_drop)
open LeanProofs.IPRA.Combinatorics.BellPeriodNp (bellB inst2_bellB G_prime tele2_pos)
open LeanProofs.IPRA.Combinatorics.LinearFactorTable (cyc congrCyc cyc_zero cyc_above
  cyc_succ_zero cyc_succ_succ actB Act act_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `eq:composite-recurrence`: `∑_{K ≤ m} c(m, K) B_{N+K} ≡ B_N (mod m)` for `m ≥ 1`. -/
theorem bell_recurrence_mod {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (N : PTm n) :
    Γ ⊢[PRAAx] rem (Act bellB m N zero) m ≐ rem (bell N) m :=
  (tele2_pos hm N).eqSymm.eqTrans (G_prime hm N)

/-- The leading coefficient: `c(N, N) = 1`. -/
theorem cyc_self (N : PTm n) : Γ ⊢[PRAAx] cyc N N ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (cyc (var 0) (var 0) ≐ one) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa using cyc_zero (Γ := Γ)
    · have st : ((cyc (var 0 : PTm (n + 1)) (var 0) ≐ one) :: Γ.map Fm.shift) ⊢[PRAAx]
          cyc (succ (var 0)) (succ (var 0)) ≐ one :=
        (cyc_succ_succ (le_refl _)).eqTrans
          ((congrAdd ((congrMul (.eqRefl _) (cyc_above (le_refl _))).eqTrans (mul_zero _))
            Prf.hyp0).eqTrans (zero_add one))
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE N hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2

/-- The middle terms `∑_{0 < K < m} c(m, K) B_{N+K}`. -/
abbrev MidB (m N : PTm n) : PTm n :=
  ap2 (sumF (shiftBody (actB bellB))) (pred m) (LinearFactorTable.par m N zero)

/-- The sum with its first and last terms separated. -/
theorem act_split {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (N : PTm n) :
    Γ ⊢[PRAAx] Act bellB m N zero ≐ cyc m zero * bell N + MidB m N + bell (N + m) := by
  have s1 := sum_shift (Γ := Γ) (actB bellB) m (LinearFactorTable.par m N zero)
  have s2 : Γ ⊢[PRAAx] ap2 (sumF (shiftBody (actB bellB))) m (LinearFactorTable.par m N zero) ≐
      ap2 (sumF (shiftBody (actB bellB))) (succ (pred m)) (LinearFactorTable.par m N zero) :=
    congrAp2 _ hm (.eqRefl _)
  have s3 := sum_succ' (Γ := Γ) (shiftBody (actB bellB)) (pred m)
    (LinearFactorTable.par m N zero)
  rw [inst2_shiftBody] at s3
  have t0 : Γ ⊢[PRAAx] inst2 (actB bellB) zero (LinearFactorTable.par m N zero) ≐
      cyc m zero * bell N := by
    have a := act_at (Γ := Γ) bellB zero m N zero
    rw [inst2_bellB] at a
    exact a.eqTrans (congrMul (.eqRefl _) (congrBell (add_zero N)))
  have tq : Γ ⊢[PRAAx] inst2 (actB bellB) (succ (pred m)) (LinearFactorTable.par m N zero) ≐
      bell (N + m) := by
    have a := act_at (Γ := Γ) bellB (succ (pred m)) m N zero
    rw [inst2_bellB] at a
    exact a.eqTrans ((congrMul ((congrCyc (.eqRefl m) hm.eqSymm).eqTrans (cyc_self m))
      (congrBell (congrAdd (.eqRefl N) hm.eqSymm))).eqTrans (one_mul _))
  have a := natEq s1
  have b := natEq s2
  have c := natEq s3
  have d := natEq t0
  have e := natEq tq
  apply deriveNat; ipra_simps
  linear_combination a + b + c + d + e

/-- `eq:composite-recurrence`: `B_{N+m} + ∑_{0 < K < m} c(m, K) B_{N+K} ≡ B_N (mod m)`. -/
theorem recurrence_split {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (N : PTm n) :
    Γ ⊢[PRAAx] rem (bell (N + m) + MidB m N) m ≐ rem (bell N) m := by
  have cz : Γ ⊢[PRAAx] cyc m zero ≐ m * cyc (pred m) zero :=
    (congrCyc hm (.eqRefl _)).eqTrans
      ((cyc_succ_zero (pred m)).eqTrans (congrMul hm.eqSymm (.eqRefl _)))
  have e : Γ ⊢[PRAAx] Act bellB m N zero ≐
      bell (N + m) + MidB m N + m * (cyc (pred m) zero * bell N) := by
    ipra_lc natEq (act_split hm N) + 𝔞 (bell N) * natEq cz
  exact (cong_drop _ _ hm).eqSymm.eqTrans
    ((cong_of_eq e).eqSymm.eqTrans (bell_recurrence_mod hm N))

end LeanProofs.IPRA.Combinatorics.BellModularRecurrence
