import IPRADerivations.Combinatorics.Vandermonde
import IPRADerivations.AnalyticNumberTheory.Fermat
import IPRADerivations.AnalyticNumberTheory.Multiplicative
import IPRADerivations.AnalyticNumberTheory.EulerProduct
import IPRADerivations.AnalyticNumberTheory.FactorVector
import IPRADerivations.DiophantineNumberTheory.ModularCertificate
import IPRADerivations.Foundations.BoundedReflection

/-!
# Lucas's congruence, one digit at a time

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, `el:lucas`:

  "Let `p` be prime and write `n = ∑ n_i p^i` and `k = ∑ k_i p^i` with digits in `[0, p)` … Then
  `C(n, k) ≡ ∏_i C(n_i, k_i) (mod p)`, where a binomial coefficient with lower index exceeding the upper is zero."

This module derives the step that removes the last digit: for a prime `p` and all `N`, `K`,

    C(N, K) ≡ C(⌊N/p⌋, ⌊K/p⌋) · C(N mod p, K mod p)   (mod p)                         (**`lucas_step`**),

with the guarded coefficient `gb` of `Combinatorics/Vandermonde` (zero when the lower index exceeds the upper).

The proof is not the coefficient comparison of the packet. It is an induction on `N` by Pascal's rule
`C(N + 1, K + 1) = C(N, K + 1) + C(N, K)`: with `T(N, K) = C(⌊N/p⌋, ⌊K/p⌋) C(N mod p, K mod p)`,

    T(N + 1, K + 1) ≡ T(N, K + 1) + T(N, K)   (mod p)                                   (`T_step`)

by the four cases "carry / no carry" of the two successors (`dig_no`, `dig_carry`, from the recursion equations
`rem_succ`, `quo_succ` of `Core/Division`). Three cases are Pascal's rule or a vanishing coefficient; in the case
where only `N` carries the right side is `C(n, k) C(p, b + 1)` with `1 ≤ b + 1 ≤ p − 1`, which is divisible by `p`
(`Fermat.prime_dvd_binom`). The induction formula is the vanishing of the count of violations over `K < R`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.LucasStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.Stirling (gle_of_le)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero gb_self gb_above gb_pascal zB inst2_z zsum)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (isP prime_of_isP isP_of_prime)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (subst_isP)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (prime_dvd_binom prime_shift)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eq_of_viol viol_of_eq)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_mul' pos_of_eq_mul eq_of_dvd' one_le_of_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_add_congr)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb one_ne_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The digits of a successor -/

theorem mul_one_r (X : PTm n) : Γ ⊢[PRAAx] X * one ≐ X := by apply deriveNat; ipra_simps; ring
theorem add_one_r (X : PTm n) : Γ ⊢[PRAAx] X + one ≐ succ X := by apply deriveNat; ipra_simps; ring

/-- No carry: when `(z mod K) + 1 ≠ K`, the quotient is unchanged and the remainder increases by one. -/
theorem dig_no {z K : PTm n} (h : Γ ⊢[PRAAx] eqb (succ (rem z K)) K ≐ zero) :
    Γ ⊢[PRAAx] (quo (succ z) K ≐ quo z K) ⋏ (rem (succ z) K ≐ succ (rem z K)) :=
  .andI ((quo_succ z K).eqTrans ((congrAdd (.eqRefl _) h).eqTrans (add_zero _)))
    ((rem_succ z K).eqTrans ((congrMul (.eqRefl _)
      ((congrMonus (.eqRefl _) h).eqTrans (monus_zero one))).eqTrans (mul_one_r _)))

/-- Carry: when `(z mod K) + 1 = K`, the quotient increases by one and the remainder is zero. -/
theorem dig_carry {z K : PTm n} (h : Γ ⊢[PRAAx] eqb (succ (rem z K)) K ≐ one) :
    Γ ⊢[PRAAx] (quo (succ z) K ≐ succ (quo z K)) ⋏ (rem (succ z) K ≐ zero) :=
  .andI ((quo_succ z K).eqTrans ((congrAdd (.eqRefl _) h).eqTrans (add_one_r _)))
    ((rem_succ z K).eqTrans ((congrMul (.eqRefl _)
      ((congrMonus (.eqRefl _) h).eqTrans (monus_self one))).eqTrans (mul_zero _)))

/-- `x < p` and `x + 1 ≠ p` give `x + 1 < p`. -/
theorem lt_succ_of_ne {x p : PTm n} (hx : Γ ⊢[PRAAx] lt x p) (h : Γ ⊢[PRAAx] eqb (succ x) p ≐ zero) :
    Γ ⊢[PRAAx] lt (succ x) p := by
  have hle : Γ ⊢[PRAAx] le (succ x) p := hx
  refine .orE (lt_or_eq_of_le hle) Prf.hyp0 ?_
  exact one_ne_zero _ ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans (h.wk (ψ := succ x ≐ p)))

/-- `x + 1 < p = y + 1` gives `x + 1 ≤ y`. -/
theorem le_of_lt_succ {x y p : PTm n} (h : Γ ⊢[PRAAx] lt (succ x) p) (e : Γ ⊢[PRAAx] succ y ≐ p) :
    Γ ⊢[PRAAx] le (succ x) y := by
  have h' : Γ ⊢[PRAAx] le (succ (succ x)) (succ y) := le_congr (.eqRefl _) e.eqSymm h
  exact (succ_monus_succ _ _).eqSymm.eqTrans h'

/-! ## The digit product -/

/-- `T(N, K) = C(⌊N/p⌋, ⌊K/p⌋) · C(N mod p, K mod p)`. -/
abbrev T (p N K : PTm n) : PTm n := gb (quo N p) (quo K p) * gb (rem N p) (rem K p)

theorem congrT {p p' N N' K K' : PTm n} (hp : Γ ⊢[PRAAx] p ≐ p') (hN : Γ ⊢[PRAAx] N ≐ N')
    (hK : Γ ⊢[PRAAx] K ≐ K') : Γ ⊢[PRAAx] T p N K ≐ T p' N' K' :=
  congrMul (congrGb (congrAp2 quoF hN hp) (congrAp2 quoF hK hp))
    (congrGb (congrAp2 remF hN hp) (congrAp2 remF hK hp))

theorem T_zero_K (p N : PTm n) : Γ ⊢[PRAAx] T p N zero ≐ one :=
  (congrMul ((congrGb (.eqRefl _) (quo_zero p)).eqTrans (gb_zero _))
    ((congrGb (.eqRefl _) (rem_zero p)).eqTrans (gb_zero _))).eqTrans (one_mul one)

/-- `C(0, K) = T(0, K)`: both are `[K = 0]`. -/
theorem T_zero_N {p : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (K : PTm n) :
    Γ ⊢[PRAAx] gb zero K ≐ T p zero K := by
  have eT : Γ ⊢[PRAAx] T p zero K ≐ gb zero (quo K p) * gb zero (rem K p) :=
    congrMul (congrGb (quo_zero p) (.eqRefl _)) (congrGb (rem_zero p) (.eqRefl _))
  refine Prf.eqTrans ?_ eT.eqSymm
  refine .orE (zero_or_succ K) ?_ ?_
  · have e : ((K ≐ zero) :: Γ) ⊢[PRAAx] K ≐ zero := Prf.hyp0
    have e1 : ((K ≐ zero) :: Γ) ⊢[PRAAx] gb zero (quo K p) ≐ one :=
      (congrGb (.eqRefl _) ((congrAp2 quoF e (.eqRefl _)).eqTrans (quo_zero p))).eqTrans (gb_zero _)
    have e2 : ((K ≐ zero) :: Γ) ⊢[PRAAx] gb zero (rem K p) ≐ one :=
      (congrGb (.eqRefl _) ((congrAp2 remF e (.eqRefl _)).eqTrans (rem_zero p))).eqTrans (gb_zero _)
    exact ((congrGb (.eqRefl _) e).eqTrans (gb_zero _)).eqTrans
      ((congrMul e1 e2).eqTrans (one_mul one)).eqSymm
  · let C : List (Fm PTm n) := (K ≐ succ (pred K)) :: Γ
    have hK : C ⊢[PRAAx] K ≐ succ (pred K) := Prf.hyp0
    have z0 : C ⊢[PRAAx] gb zero K ≐ zero := gb_above (one_le_of_pos hK)
    refine z0.eqTrans (Prf.eqSymm ?_)
    refine .orE (zero_or_succ (rem K p)) ?_ ?_
    · have hr : ((rem K p ≐ zero) :: C) ⊢[PRAAx] dvd p K := Prf.hyp0
      have e := eq_of_dvd' hp.wk.wk hr
      have qpos := pos_of_eq_mul hK.wk e
      exact (congrMul (gb_above (one_le_of_pos qpos)) (.eqRefl _)).eqTrans (zero_mul _)
    · exact (congrMul (.eqRefl _) (gb_above (one_le_of_pos Prf.hyp0))).eqTrans (mul_zero _)

/-! ## The four cases of the step -/

theorem dist_alg {X P A B : PTm n} (h : Γ ⊢[PRAAx] P ≐ A + B) : Γ ⊢[PRAAx] X * P ≐ X * A + X * B := by
  have x := natEq h
  apply deriveNat; ipra_simps; linear_combination 𝔞 X * x

theorem alg01 {X Y u v w : PTm n} (hu : Γ ⊢[PRAAx] u ≐ one) (hv : Γ ⊢[PRAAx] v ≐ one)
    (hw : Γ ⊢[PRAAx] w ≐ zero) : Γ ⊢[PRAAx] X * u ≐ X * v + Y * w := by
  have a := natEq hu; have b := natEq hv; have c := natEq hw
  apply deriveNat; ipra_simps; linear_combination 𝔞 X * a - 𝔞 X * b - 𝔞 Y * c

theorem alg11 {P A B u v w : PTm n} (hP : Γ ⊢[PRAAx] P ≐ A + B) (hu : Γ ⊢[PRAAx] u ≐ one)
    (hv : Γ ⊢[PRAAx] v ≐ one) (hw : Γ ⊢[PRAAx] w ≐ one) : Γ ⊢[PRAAx] P * u ≐ A * v + B * w := by
  have x := natEq hP; have a := natEq hu; have b := natEq hv; have c := natEq hw
  apply deriveNat; ipra_simps; linear_combination x + 𝔞 P * a - 𝔞 A * b - 𝔞 B * c

/-- Only `N` carries: both sides vanish modulo `p`. -/
theorem case10 {p X Y a b : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ea : Γ ⊢[PRAAx] succ a ≐ p)
    (hb : Γ ⊢[PRAAx] lt (succ b) p) :
    Γ ⊢[PRAAx] rem (Y * gb zero (succ b)) p ≐ rem (X * gb a (succ b) + X * gb a b) p := by
  have ppos := prime_eq_succ_pred hp
  have zL : Γ ⊢[PRAAx] Y * gb zero (succ b) ≐ zero :=
    (congrMul (.eqRefl _) (gb_above ((succ_monus_succ _ _).eqTrans (zero_le b)))).eqTrans (mul_zero _)
  have hba : Γ ⊢[PRAAx] lt b a := le_of_lt_succ hb ea
  have hle : Γ ⊢[PRAAx] le (succ b) p := le_trans (le_succ_self _) hb
  have eg : Γ ⊢[PRAAx] gb p (succ b) ≐ binom p (succ b) :=
    (congrMul (gle_of_le hle) (.eqRefl _)).eqTrans (one_mul _)
  have d0 : Γ ⊢[PRAAx] dvd p (binom p (succ b)) := prime_dvd_binom hp ea.eqSymm hba
  have d1 : Γ ⊢[PRAAx] dvd p (X * gb p (succ b)) :=
    dvd_congr ((mul_comm _ _).eqTrans (congrMul (.eqRefl _) eg.eqSymm)) (dvd_mul' ppos X d0)
  have eR : Γ ⊢[PRAAx] X * gb a (succ b) + X * gb a b ≐ X * gb p (succ b) :=
    (dist_alg (gb_pascal a b)).eqSymm.eqTrans (congrMul (.eqRefl _) (congrGb ea (.eqRefl _)))
  have rR : Γ ⊢[PRAAx] rem (X * gb a (succ b) + X * gb a b) p ≐ zero :=
    (congrAp2 remF eR (.eqRefl _)).eqTrans d1
  exact ((congrAp2 remF zL (.eqRefl _)).eqTrans (rem_zero p)).eqTrans rR.eqSymm

/-- **The step of the digit product**: `T(N + 1, K + 1) ≡ T(N, K + 1) + T(N, K) (mod p)`. -/
theorem T_step {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N K : PTm n) :
    Γ ⊢[PRAAx] rem (T p (succ N) (succ K)) p ≐ rem (T p N (succ K) + T p N K) p := by
  have ppos := prime_eq_succ_pred hp
  have ha : Γ ⊢[PRAAx] lt (rem N p) p := rem_lt' ppos N
  have hb : Γ ⊢[PRAAx] lt (rem K p) p := rem_lt' ppos K
  refine .orE (eqb_cases (succ (rem N p)) p) ?_ ?_
  · -- `N` does not carry
    let C : List (Fm PTm n) := (eqb (succ (rem N p)) p ≐ zero) :: Γ
    have cN : C ⊢[PRAAx] eqb (succ (rem N p)) p ≐ zero := Prf.hyp0
    have qN := Prf.andE₁ (dig_no cN); have rN := Prf.andE₂ (dig_no cN)
    refine .orE (eqb_cases (succ (rem K p)) p) ?_ ?_
    · let D : List (Fm PTm n) := (eqb (succ (rem K p)) p ≐ zero) :: C
      have cK : D ⊢[PRAAx] eqb (succ (rem K p)) p ≐ zero := Prf.hyp0
      have qK := Prf.andE₁ (dig_no cK); have rK := Prf.andE₂ (dig_no cK)
      have eL : D ⊢[PRAAx] T p (succ N) (succ K) ≐
          gb (quo N p) (quo K p) * gb (succ (rem N p)) (succ (rem K p)) :=
        congrMul (congrGb qN.wk qK) (congrGb rN.wk rK)
      have eM : D ⊢[PRAAx] T p N (succ K) ≐ gb (quo N p) (quo K p) * gb (rem N p) (succ (rem K p)) :=
        congrMul (congrGb (.eqRefl _) qK) (congrGb (.eqRefl _) rK)
      exact congrAp2 remF (eL.eqTrans ((dist_alg (gb_pascal _ _)).eqTrans
        (congrAdd eM.eqSymm (.eqRefl _)))) (.eqRefl _)
    · let D : List (Fm PTm n) := (eqb (succ (rem K p)) p ≐ one) :: C
      have cK : D ⊢[PRAAx] eqb (succ (rem K p)) p ≐ one := Prf.hyp0
      have qK := Prf.andE₁ (dig_carry cK); have rK := Prf.andE₂ (dig_carry cK)
      have eL : D ⊢[PRAAx] T p (succ N) (succ K) ≐
          gb (quo N p) (succ (quo K p)) * gb (succ (rem N p)) zero :=
        congrMul (congrGb qN.wk qK) (congrGb rN.wk rK)
      have eM : D ⊢[PRAAx] T p N (succ K) ≐ gb (quo N p) (succ (quo K p)) * gb (rem N p) zero :=
        congrMul (congrGb (.eqRefl _) qK) (congrGb (.eqRefl _) rK)
      have hlt : D ⊢[PRAAx] le (succ (rem N p)) (rem K p) :=
        le_of_lt_succ (lt_succ_of_ne ha.wk.wk cN.wk) (eq_of_eqb cK)
      exact congrAp2 remF (eL.eqTrans ((alg01 (gb_zero _) (gb_zero _) (gb_above hlt)).eqTrans
        (congrAdd eM.eqSymm (.eqRefl _)))) (.eqRefl _)
  · -- `N` carries
    let C : List (Fm PTm n) := (eqb (succ (rem N p)) p ≐ one) :: Γ
    have cN : C ⊢[PRAAx] eqb (succ (rem N p)) p ≐ one := Prf.hyp0
    have qN := Prf.andE₁ (dig_carry cN); have rN := Prf.andE₂ (dig_carry cN)
    have ea : C ⊢[PRAAx] succ (rem N p) ≐ p := eq_of_eqb cN
    refine .orE (eqb_cases (succ (rem K p)) p) ?_ ?_
    · let D : List (Fm PTm n) := (eqb (succ (rem K p)) p ≐ zero) :: C
      have cK : D ⊢[PRAAx] eqb (succ (rem K p)) p ≐ zero := Prf.hyp0
      have qK := Prf.andE₁ (dig_no cK); have rK := Prf.andE₂ (dig_no cK)
      have eL : D ⊢[PRAAx] T p (succ N) (succ K) ≐
          gb (succ (quo N p)) (quo K p) * gb zero (succ (rem K p)) :=
        congrMul (congrGb qN.wk qK) (congrGb rN.wk rK)
      have eM : D ⊢[PRAAx] T p N (succ K) ≐ gb (quo N p) (quo K p) * gb (rem N p) (succ (rem K p)) :=
        congrMul (congrGb (.eqRefl _) qK) (congrGb (.eqRefl _) rK)
      have c := case10 (X := gb (quo N p) (quo K p)) (Y := gb (succ (quo N p)) (quo K p)) hp.wk.wk ea.wk
        (lt_succ_of_ne hb.wk.wk cK)
      exact (congrAp2 remF eL (.eqRefl _)).eqTrans
        (c.eqTrans (congrAp2 remF (congrAdd eM.eqSymm (.eqRefl _)) (.eqRefl _)))
    · let D : List (Fm PTm n) := (eqb (succ (rem K p)) p ≐ one) :: C
      have cK : D ⊢[PRAAx] eqb (succ (rem K p)) p ≐ one := Prf.hyp0
      have qK := Prf.andE₁ (dig_carry cK); have rK := Prf.andE₂ (dig_carry cK)
      have eL : D ⊢[PRAAx] T p (succ N) (succ K) ≐ gb (succ (quo N p)) (succ (quo K p)) * gb zero zero :=
        congrMul (congrGb qN.wk qK) (congrGb rN.wk rK)
      have eM : D ⊢[PRAAx] T p N (succ K) ≐ gb (quo N p) (succ (quo K p)) * gb (rem N p) zero :=
        congrMul (congrGb (.eqRefl _) qK) (congrGb (.eqRefl _) rK)
      have eab : D ⊢[PRAAx] rem K p ≐ rem N p :=
        (pred_succ _).eqSymm.eqTrans ((congrPred ((eq_of_eqb cK).eqTrans ea.wk.eqSymm)).eqTrans (pred_succ _))
      have e1 : D ⊢[PRAAx] gb (rem N p) (rem K p) ≐ one := (congrGb (.eqRefl _) eab).eqTrans (gb_self _)
      exact congrAp2 remF (eL.eqTrans ((alg11 (gb_pascal _ _) (gb_zero _) (gb_zero _) e1).eqTrans
        (congrAdd eM.eqSymm (.eqRefl _)))) (.eqRefl _)

/-! ## The induction on `N` -/

/-- `1 ∸ [C(N, K) mod p = T(N, K) mod p]`, over `0 = K`, `1 = ⟨p, N⟩`. -/
abbrev violB : PTm 2 :=
  monus one (eqb (rem (gb (sndT (var 1)) (var 0)) (fstT (var 1)))
    (rem (T (fstT (var 1)) (sndT (var 1)) (var 0)) (fstT (var 1))))

theorem inst2_viol (K y : PTm n) :
    inst2 violB K y =
      monus one (eqb (rem (gb (sndT y) K) (fstT y)) (rem (T (fstT y) (sndT y) K) (fstT y))) := by
  simp [inst2]

theorem viol_at (K p N : PTm n) :
    Γ ⊢[PRAAx] inst2 violB K (pairT p N) ≐ monus one (eqb (rem (gb N K) p) (rem (T p N K) p)) := by
  rw [inst2_viol]
  exact congrMonus (.eqRefl _) (AnalyticNumberTheory.Euler.congrEqb
    (congrAp2 remF (congrGb (snd_pair _ _) (.eqRefl _)) (fst_pair _ _))
    (congrAp2 remF (congrT (fst_pair _ _) (snd_pair _ _) (.eqRefl _)) (fst_pair _ _)))

theorem eq_at {p N s R : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF violB) R (pairT p N) ≐ zero)
    (hs : Γ ⊢[PRAAx] lt s R) : Γ ⊢[PRAAx] rem (gb N s) p ≐ rem (T p N s) p :=
  eq_of_viol ((viol_at s p N).eqSymm.eqTrans (sum_zero_elim violB ih hs))

theorem viol_point {p N r R : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (ih : Γ ⊢[PRAAx] ap2 (sumF violB) R (pairT p N) ≐ zero) (hr : Γ ⊢[PRAAx] lt r R) :
    Γ ⊢[PRAAx] inst2 violB r (pairT p (succ N)) ≐ zero := by
  have ppos := prime_eq_succ_pred hp
  refine (viol_at r p (succ N)).eqTrans (viol_of_eq ?_)
  refine .orE (zero_or_succ r) ?_ ?_
  · have e : ((r ≐ zero) :: Γ) ⊢[PRAAx] r ≐ zero := Prf.hyp0
    exact congrAp2 remF (((congrGb (.eqRefl _) e).eqTrans (gb_zero _)).eqTrans
      ((congrT (.eqRefl _) (.eqRefl _) e).eqTrans (T_zero_K p (succ N))).eqSymm) (.eqRefl _)
  · let C : List (Fm PTm n) := (r ≐ succ (pred r)) :: Γ
    have e : C ⊢[PRAAx] r ≐ succ (pred r) := Prf.hyp0
    have l₁ : C ⊢[PRAAx] lt (succ (pred r)) R := lt_congr e (.eqRefl _) hr.wk
    have l₀ : C ⊢[PRAAx] lt (pred r) R := le_trans (le_succ_self _) l₁
    have s1 : C ⊢[PRAAx] rem (gb (succ N) (succ (pred r))) p ≐ rem (gb N (succ (pred r)) + gb N (pred r)) p :=
      congrAp2 remF (gb_pascal N (pred r)) (.eqRefl _)
    have s2 := rem_add_congr ppos.wk (eq_at ih.wk l₁) (eq_at ih.wk l₀)
    have s3 : C ⊢[PRAAx] rem (T p (succ N) (succ (pred r))) p ≐ rem (T p N (succ (pred r)) + T p N (pred r)) p :=
      T_step hp.wk N (pred r)
    exact (congrAp2 remF (congrGb (.eqRefl _) e) (.eqRefl _)).eqTrans
      (s1.eqTrans (s2.eqTrans (s3.eqSymm.eqTrans
        (congrAp2 remF (congrT (.eqRefl _) (.eqRefl _) e.eqSymm) (.eqRefl _)))))

theorem viol_step {p N R : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (ih : Γ ⊢[PRAAx] ap2 (sumF violB) R (pairT p N) ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF violB) R (pairT p (succ N)) ≐ zero := by
  refine (sum_congr_bounded violB zB (pairT p (succ N)) (pairT p N) R (.allI (.impI ?_))).eqTrans (zsum _ _)
  have ih' : Γ.map Fm.shift ⊢[PRAAx]
      ap2 (sumF violB) (Syn.shift R) (pairT (Syn.shift p) (Syn.shift N)) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using ih.shift
  have hp' := prime_shift hp
  have e₁ : Syn.shift (pairT p (succ N)) = pairT (Syn.shift p) (succ (Syn.shift N)) := by simp [Syn.shift]
  rw [e₁, inst2_z]
  exact viol_point hp'.wk ih'.wk Prf.hyp0

theorem viol_base {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (R : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF violB) R (pairT p zero) ≐ zero := by
  refine (sum_congr_bounded violB zB (pairT p zero) (pairT p zero) R (.allI (.impI ?_))).eqTrans (zsum _ _)
  have ppos' := prime_eq_succ_pred (prime_shift hp)
  have e₁ : Syn.shift (pairT p (zero : PTm n)) = pairT (Syn.shift p) zero := by simp [Syn.shift]
  rw [e₁, inst2_z]
  exact (viol_at _ _ _).eqTrans (viol_of_eq (congrAp2 remF (T_zero_N ppos'.wk _) (.eqRefl _)))

/-- Variables: `0 = N` (induction), `1 = p`, `2 = R`. -/
abbrev lucasF : Fm PTm 3 :=
  (isP (var 1) ≐ one) ⟶ (ap2 (sumF violB) (var 2) (pairT (var 1) (var 0)) ≐ zero)

theorem lucas_open : ([] : List (Fm PTm 3)) ⊢[PRAAx] lucasF := by
  refine ind _ ⟨trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_isP, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two]
    simp only [subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (viol_base (prime_of_isP Prf.hyp0) _)
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_isP, Syn.subst_var, Syn.repl_zero, repl_one, repl_two]
    simp only [subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero, repl_one, repl_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (viol_step (prime_of_isP Prf.hyp0) (.impE Prf.hyp1 Prf.hyp0))

/-- **Lucas's congruence, last digit**: for a prime `p`,
`C(N, K) ≡ C(⌊N/p⌋, ⌊K/p⌋) · C(N mod p, K mod p) (mod p)`. -/
theorem lucas_step {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N K : PTm n) :
    Γ ⊢[PRAAx] rem (gb N K) p ≐ rem (gb (quo N p) (quo K p) * gb (rem N p) (rem K p)) p := by
  have i := inst (Γ := Γ) lucas_open (![N, p, succ K] : Fin 3 → PTm n)
  simp only [lucasF, Fm.subst_imp, Fm.subst_eq, subst_isP, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at i
  simp only [subst_ap2, subst_pairT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at i
  exact eq_at (.impE i (isP_of_prime hp)) ((succ_monus_succ _ _).eqTrans (le_refl _))

end LeanProofs.IPRA.Combinatorics.LucasStep
