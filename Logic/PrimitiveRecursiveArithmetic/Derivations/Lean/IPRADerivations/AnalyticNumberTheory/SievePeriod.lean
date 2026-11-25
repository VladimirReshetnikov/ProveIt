import IPRADerivations.AnalyticNumberTheory.SieveRecursion
import IPRADerivations.AnalyticNumberTheory.Multiplicative
import IPRADerivations.DiophantineNumberTheory.ModularCertificate
import IPRADerivations.Core.CertificateTactics

/-!
# The period of the sieve count

Packet: `analytic-number-theory/prime-counting-ipra`, `sections/sieve.tex`, after `eq:sv-ie`: "Put
`Q = ∏_i q_i` and `D = ∏_i (q_i − 1)`. […] `F(N + Q) − F(N) = D`. In particular `F(tQ + u) = tD + F(u)`."

For the count `Φ(x; P) = #{1 ≤ m ≤ x : gcd(m, P) = 1}` of `SieveRecursion` and every modulus `P ≥ 1`
(`D = φ(P)`; for a product of distinct primes `φ(P) = ∏ (q_i − 1)`):

    Φ(x + P; P) = Φ(x; P) + φ(P)                                                  (**`phi_period`**).

The packet sums the changes of the floors in the inclusion-exclusion formula. Here it is an induction on `x`:
the term at `m + P` equals the term at `m ≥ 1` (`cop_period`, from `Multiplicative.gcd_rem`), and a full period
`1 ≤ m ≤ P` has `φ(P)` coprime members (`period_one`: the residues `0` and `P` have the same bit).

* `rem_self'`, `cop_period`: `P mod P = 0` and `[gcd(m + P, P) = 1] = [gcd(m, P) = 1]`;
* `period_one`: `Φ(P; P) = φ(P)`;
* **`phi_period`**: `Φ(x + P; P) = Φ(x; P) + φ(P)`, by induction on `x` (`period_zero`, `period_succ`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SievePeriod

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody inst2_tot)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (gcd_rem)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg congrEqb' zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.LegendreSieve (coB inst2_coB)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveRecursion (Phi)
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_add_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Periodicity of the term -/

theorem add_alg (m P : PTm n) : Γ ⊢[PRAAx] m + P ≐ P * one + m := by ipra_ring

theorem self_alg (P : PTm n) : Γ ⊢[PRAAx] P ≐ P * one + zero := by ipra_ring

/-- `P mod P = 0`. -/
theorem rem_self' {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) : Γ ⊢[PRAAx] rem P P ≐ zero :=
  (congrAp2 remF (self_alg P) (.eqRefl _)).eqTrans ((rem_add_mul hP one zero).eqTrans (rem_zero P))

/-- `[gcd(m + P, P) = 1] = [gcd(m, P) = 1]`. -/
theorem cop_period {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (m : PTm n) :
    Γ ⊢[PRAAx] eqb (gcd (m + P) P) one ≐ eqb (gcd m P) one := by
  have r : Γ ⊢[PRAAx] rem (m + P) P ≐ rem m P :=
    (congrAp2 remF (add_alg m P) (.eqRefl _)).eqTrans (rem_add_mul hP one m)
  exact congrEqb' ((gcd_rem hP (m + P)).eqSymm.eqTrans ((congrGcd r (.eqRefl _)).eqTrans (gcd_rem hP m)))
    (.eqRefl _)

/-! ## One period -/

theorem one_mul_l {s X : PTm n} (h : Γ ⊢[PRAAx] s ≐ one) : Γ ⊢[PRAAx] s * X ≐ X := by
  ipra_lc 𝔞 X * natEq h

theorem cancel_alg {A t0 B C tP : PTm n} (h1 : Γ ⊢[PRAAx] A ≐ t0 + B) (h2 : Γ ⊢[PRAAx] A ≐ C + tP)
    (ht : Γ ⊢[PRAAx] t0 ≐ tP) : Γ ⊢[PRAAx] B ≐ C := by
  ipra_lc -natEq h1 + natEq h2 - natEq ht

/-- `Φ(P; P) = φ(P)`: a full period has `φ(P)` members coprime to `P`. -/
theorem period_one {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) : Γ ⊢[PRAAx] Phi P P ≐ phi P := by
  have a := sum_shift (Γ := Γ) coB P P
  have t0 : Γ ⊢[PRAAx] inst2 coB zero P ≐ zero := by
    rw [inst2_coB]
    exact zero_mul_l sg_zero _
  have c : Γ ⊢[PRAAx] ap2 (sumF (shiftBody coB)) P P ≐ ap2 (sumF (shiftBody totBody)) P P := by
    refine sum_congr_bounded (shiftBody coB) (shiftBody totBody) P P P (.allI (.impI ?_))
    rw [inst2_shiftBody, inst2_shiftBody, inst2_coB, inst2_tot]
    exact one_mul_l (sg_succ _)
  have b1 := sum_shift (Γ := Γ) totBody P P
  have b2 := sum_succ' (Γ := Γ) totBody P P
  rw [inst2_tot] at b1 b2
  have ht : Γ ⊢[PRAAx] eqb (gcd zero P) one ≐ eqb (gcd P P) one :=
    congrEqb' ((congrGcd (rem_self' hP).eqSymm (.eqRefl _)).eqTrans (gcd_rem hP P)) (.eqRefl _)
  exact a.eqTrans ((congrAdd t0 (c.eqTrans (cancel_alg b1 b2 ht))).eqTrans (zero_add _))

/-! ## The induction on `x` -/

theorem step_alg {U' U T1 V' V T2 ph : PTm n} (a : Γ ⊢[PRAAx] U' ≐ U + T1) (b : Γ ⊢[PRAAx] V' ≐ V + T2)
    (ih : Γ ⊢[PRAAx] U ≐ V + ph) (t : Γ ⊢[PRAAx] T1 ≐ T2) : Γ ⊢[PRAAx] U' ≐ V' + ph := by
  have a' := natEq a; have b' := natEq b; have c := natEq ih; have d := natEq t
  apply deriveNat; ipra_simps; linear_combination a' - b' + c + d

theorem period_zero {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) :
    Γ ⊢[PRAAx] Phi (zero + P) P ≐ Phi zero P + phi P := by
  have ss := sum_succ' (Γ := Γ) coB zero P
  rw [inst2_coB] at ss
  have U0 : Γ ⊢[PRAAx] Phi zero P ≐ zero :=
    ss.eqTrans ((congrAdd (sum_zero coB P) (zero_mul_l sg_zero _)).eqTrans (zero_add zero))
  have e : Γ ⊢[PRAAx] Phi (zero + P) P ≐ phi P :=
    (congrAp2 (sumF coB) (congrSucc (zero_add P)) (.eqRefl _)).eqTrans (period_one hP)
  exact e.eqTrans ((zero_add _).eqSymm.eqTrans (congrAdd U0.eqSymm (.eqRefl _)))

theorem period_succ {x P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P))
    (ih : Γ ⊢[PRAAx] Phi (x + P) P ≐ Phi x P + phi P) :
    Γ ⊢[PRAAx] Phi (succ x + P) P ≐ Phi (succ x) P + phi P := by
  have e1 : Γ ⊢[PRAAx] Phi (succ x + P) P ≐ Phi (succ (x + P)) P :=
    congrAp2 (sumF coB) (congrSucc (succ_add x P)) (.eqRefl _)
  have s1 := sum_succ' (Γ := Γ) coB (succ (x + P)) P
  have s2 := sum_succ' (Γ := Γ) coB (succ x) P
  rw [inst2_coB] at s1 s2
  have per : Γ ⊢[PRAAx] eqb (gcd (succ (x + P)) P) one ≐ eqb (gcd (succ x) P) one :=
    (congrEqb' (congrGcd (succ_add x P).eqSymm (.eqRefl _)) (.eqRefl _)).eqTrans (cop_period hP (succ x))
  have t : Γ ⊢[PRAAx] sg (succ (x + P)) * eqb (gcd (succ (x + P)) P) one ≐
      sg (succ x) * eqb (gcd (succ x) P) one :=
    congrMul ((sg_succ _).eqTrans (sg_succ _).eqSymm) per
  exact e1.eqTrans (step_alg s1 s2 ih t)

/-- Variables: `0 = x`, `1 = P`. -/
abbrev perF : Fm PTm 2 :=
  (var 1 ≐ succ (pred (var 1))) ⟶
    (ap2 (sumF coB) (succ (var 0 + var 1)) (var 1) ≐ ap2 (sumF coB) (succ (var 0)) (var 1) + phi (var 1))

theorem per_open : ([] : List (Fm PTm 2)) ⊢[PRAAx] perF := by
  refine ind _ ⟨trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_pred, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (period_zero Prf.hyp0)
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_pred, Syn.subst_var,
      Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (period_succ Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

/-- **The period of the sieve count**: `Φ(x + P; P) = Φ(x; P) + φ(P)` for `P ≥ 1`. -/
theorem phi_period {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (x : PTm n) :
    Γ ⊢[PRAAx] Phi (x + P) P ≐ Phi x P + phi P := by
  have i := inst (Γ := Γ) per_open (![x, P] : Fin 2 → PTm n)
  simp only [perF, Fm.subst_imp, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_pred, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at i
  exact .impE i hP

end LeanProofs.IPRA.AnalyticNumberTheory.SievePeriod
