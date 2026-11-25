import IPRADerivations.AnalyticNumberTheory.SummatoryPhi
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Core.SumOrder
import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination

/-!
# Many coprime pairs in a square

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Lemma `lem:conic-coprime-count`: for the number
`G(N)` of pairs `1 ≤ s, t ≤ N` with `gcd(s, t) = 1`, `4 G(N) ≥ N²` for every `N ≥ 1`. "Every pair with gcd
greater than one belongs to at least one of the sets `E_d` ... `#E_d = ⌊N/d⌋²`."

The union bound is read off the Möbius form of the count (`AnalyticNumberTheory/SummatoryPhi.summatory_phi`):
`D⁺(N) = D⁻(N) + G(N)` with `D^±(N) = ∑_{1 ≤ d ≤ N} μ^±(d) ⌊N/d⌋²`. The `d = 1` term gives `D⁺ ≥ N²`; the
`d = 0, 1` terms of `D⁻` vanish and `μ⁻ ≤ 1`, so `D⁻ ≤ ∑_{2 ≤ d ≤ N} ⌊N/d⌋² = Q(N − 1)`, with
`Q(L) = ∑_{i<L} ⌊N/(i+2)⌋²`. Finally `4 Q(N − 1) ≤ 3N²`:

* `mul_quo_le`, `term_bound`: `d ⌊N/d⌋ ≤ N`, and `(M+2)(M+1) ⌊N/(M+2)⌋² ≤ N²`;
* `qinv_step`, `qinv` (the integer form of `∑_{d≥2} 1/d² ≤ 1/4 + ∑_{d≥3} (1/(d−1) − 1/d)`): for every `L`,
  `4 (L+2) Q(L+1) + 4N² ≤ 3N² (L+2)`, by induction (each step multiplies by `L + 2` and cancels it);
* `coprime_count` (`lem:conic-coprime-count`): `N² ≤ 4 G(N)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.ConicCoprimeCount

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.SummatoryPhi (DPB DNB inst2_DP inst2_DN summatory_phi)
open LeanProofs.IPRA.AnalyticNumberTheory.CoprimePairs (gB3)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (muP muN om_two_one sq_two_one congrEqb' zero_ne_one')
open LeanProofs.IPRA.AnalyticNumberTheory.TotientCorollaries (eqb_le_one)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `d ⌊N/d⌋ ≤ N` for `d = d' + 1`. -/
theorem mul_quo_le (N d' : PTm k) : Γ ⊢[PRAAx] le (succ d' * quo N (succ d')) N := by
  have e := natEq (Prf.andE₁ (div_mod (Γ := Γ) N d'))
  ipra_le 𝔞 (rem N (succ d')) using linear_combination e

/-- `(M+2)(M+1) ⌊N/(M+2)⌋² ≤ N²`. -/
theorem term_bound (N M : PTm k) :
    Γ ⊢[PRAAx] le (succ (succ M) * succ M * (quo N (succ (succ M)) * quo N (succ (succ M)))) (N * N) := by
  have a := mul_quo_le (Γ := Γ) N (succ M)
  have b : Γ ⊢[PRAAx] le (succ M * quo N (succ (succ M))) N := by
    ipra_le sl a + 𝔞 (quo N (succ (succ M)))
  have c := le_mul_mono a b
  ipra_le sl c

/-- The body `⌊N/(i+2)⌋²`, with `N` the parameter. -/
abbrev qB : PTm 2 := quo (var 1) (succ (succ (var 0))) * quo (var 1) (succ (succ (var 0)))

theorem inst2_q (i N : PTm k) : inst2 qB i N = quo N (succ (succ i)) * quo N (succ (succ i)) := by
  simp [inst2]

/-- The invariant `4 (L+2) Q(L+1) + 4N² ≤ 3N² (L+2)`. -/
abbrev QInv (N L : PTm k) : Fm PTm k :=
  le (num 4 * succ (succ L) * ap2 (sumF qB) (succ L) N + num 4 * (N * N))
    (num 3 * (N * N) * succ (succ L))

theorem qinv_base (N : PTm k) : Γ ⊢[PRAAx] QInv N zero := by
  have s1 := natEq (sum_succ' (Γ := Γ) qB zero N)
  have z := natEq (sum_zero (Γ := Γ) qB N)
  have a := mul_quo_le (Γ := Γ) N one
  have c := le_mul_mono a a
  rw [inst2_q] at s1
  ipra_le 2 * sl c using rw [s1, z]; ring

theorem qinv_step {N L : PTm k} (ih : Γ ⊢[PRAAx] QInv N L) : Γ ⊢[PRAAx] QInv N (succ L) := by
  have tb := term_bound (Γ := Γ) N (succ L)
  have s := natEq (sum_succ' (Γ := Γ) qB (succ L) N)
  rw [inst2_q] at s
  refine mul_le_cancel (d' := succ L) ?_
  ipra_le (𝔞 L + 3) * sl ih + 4 * sl tb using rw [s]; ring

theorem qinv (N L : PTm k) : Γ ⊢[PRAAx] QInv N L := by
  have hall : Γ ⊢[PRAAx] Fm.all (QInv (Syn.shift N) (Syn.var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_num, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact qinv_base N
    · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_num, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact qinv_step Prf.hyp0
  have h2 := Prf.allE L hall
  simpa only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_num, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ] using h2

/-- The shifted terms of `D⁻`: `[d ≥ 1] μ⁻(d) ⌊N/d⌋² ≤ ⌊N/d⌋²` at `d = i + 2`. -/
theorem shifted_le {m : ℕ} {Δ : List (Fm PTm m)} (v x : PTm m) :
    Δ ⊢[PRAAx] le (inst2 (shiftBody (shiftBody DNB)) v x) (inst2 qB v x) := by
  rw [inst2_shiftBody, inst2_shiftBody, inst2_DN, inst2_q]
  have es := natEq (sg_succ (Γ := Δ) (succ v))
  have h1 := eqb_le_one (Γ := Δ) (AnalyticNumberTheory.Mobius.sq (succ (succ (succ v))) (succ (succ v))) zero
  have h2 := eqb_le_one (Γ := Δ) (rem (AnalyticNumberTheory.Mobius.om (succ (succ (succ v))) (succ (succ v))) two) one
  have hm := le_mul_mono h1 h2
  ipra_le 𝔞 (quo x (succ (succ v))) * 𝔞 (quo x (succ (succ v))) * sl hm using
    linear_combination (-(𝔞 (quo x (succ (succ v))) * 𝔞 (quo x (succ (succ v))) *
      (𝔞 (eqb (AnalyticNumberTheory.Mobius.sq (succ (succ (succ v))) (succ (succ v))) zero) *
        𝔞 (eqb (rem (AnalyticNumberTheory.Mobius.om (succ (succ (succ v))) (succ (succ v))) two) one)))) * es

/-- `lem:conic-coprime-count`: for `N = N₁ + 1`, `N² ≤ 4 G(N)`, with `G(N)` the count of coprime pairs
`1 ≤ s, t ≤ N` (`CoprimePairs`, `SquareLayers.Sq gB3`). -/
theorem coprime_count (N₁ : PTm k) :
    Γ ⊢[PRAAx] le (succ N₁ * succ N₁) (num 4 * SquareLayers.Sq gB3 (succ (succ N₁)) zero) := by
  have hN : Γ ⊢[PRAAx] succ N₁ ≐ succ (pred (succ N₁)) := congrSucc (pred_succ N₁).eqSymm
  have sp := Prf.andE₂ (summatory_phi hN)
  -- Möbius values at `1`
  have s0 : Γ ⊢[PRAAx] eqb (AnalyticNumberTheory.Mobius.sq (succ one) (one : PTm k)) zero ≐ one :=
    (congrEqb' sq_two_one (.eqRefl _)).eqTrans (eqb_of_eq (.eqRefl _))
  have o0 : Γ ⊢[PRAAx] rem (AnalyticNumberTheory.Mobius.om (succ one) (one : PTm k)) two ≐ zero :=
    (congrAp2 remF om_two_one (.eqRefl _)).eqTrans (rem_zero _)
  have mp : Γ ⊢[PRAAx] muP (succ one) (one : PTm k) ≐ one :=
    (congrMul s0 ((congrEqb' o0 (.eqRefl _)).eqTrans (eqb_of_eq (.eqRefl _)))).eqTrans
      (by ipra_ring)
  have mn : Γ ⊢[PRAAx] muN (succ one) (one : PTm k) ≐ zero :=
    (congrMul s0 ((congrEqb' o0 (.eqRefl _)).eqTrans (eqb_of_ne zero_ne_one'))).eqTrans
      (by ipra_ring)
  -- `D⁺ ≥ N²` from the term `d = 1`
  have q1 := Prf.andE₁ (div_mod_unique (Γ := Γ) (z := succ N₁) (q := succ N₁) (r := zero) (K' := zero)
    (by ipra_ring) (zero_lt_succ zero))
  have t := term_le_sum (Γ := Γ) DPB (i := one) (M := succ (succ N₁)) (x := succ N₁)
    (by show Γ ⊢[PRAAx] le (succ one) (succ (succ N₁)); ipra_le 𝔞 N₁)
  rw [inst2_DP] at t
  have ev : Γ ⊢[PRAAx] (sg one * muP (succ one) one) * (quo (succ N₁) one * quo (succ N₁) one) ≐
      succ N₁ * succ N₁ := by
    ipra_lc (𝔞 (eqb (AnalyticNumberTheory.Mobius.sq (succ one) (one : PTm k)) zero) * 𝔞 (eqb (rem (AnalyticNumberTheory.Mobius.om (succ one) (one : PTm k)) two) zero) * 𝔞 (quo (succ N₁) one) * 𝔞 (quo (succ N₁) one)) * natEq (sg_succ (Γ := Γ) (zero : PTm k)) +
      (𝔞 (quo (succ N₁) one) * 𝔞 (quo (succ N₁) one)) * natEq mp + (𝔞 (quo (succ N₁) one) + 𝔞 N₁ + 1) * natEq q1
  have tP := le_congr ev (.eqRefl _) t
  -- `D⁻ = 0 + 0 + ∑_{i<N₁} DNB(i+2)`
  have e1 := natEq (sum_shift (Γ := Γ) DNB (succ N₁) (succ N₁))
  have e2' := sum_shift (Γ := Γ) (shiftBody DNB) N₁ (succ N₁)
  rw [inst2_shiftBody] at e2'
  have e2 := natEq e2'
  have z0 : Γ ⊢[PRAAx] inst2 DNB zero (succ N₁) ≐ zero := by
    rw [inst2_DN]
    ipra_lc (𝔞 (eqb (AnalyticNumberTheory.Mobius.sq (succ zero) zero) zero) * 𝔞 (eqb (rem (AnalyticNumberTheory.Mobius.om (succ zero) zero) two) one) * 𝔞 (quo (succ N₁) zero) * 𝔞 (quo (succ N₁) zero)) * natEq (sg_zero (Γ := Γ) (n := k))
  have z1 : Γ ⊢[PRAAx] inst2 DNB (succ zero) (succ N₁) ≐ zero := by
    rw [inst2_DN]
    ipra_lc (𝔞 (sg (succ zero)) * 𝔞 (quo (succ N₁) (succ zero)) * 𝔞 (quo (succ N₁) (succ zero))) * natEq mn
  have ez0 := natEq z0
  have ez1 := natEq z1
  have tS := sum_le_params (Γ := Γ) (shiftBody (shiftBody DNB)) qB (succ N₁) (succ N₁) N₁
    (.allI (.impI (shifted_le _ _)))
  -- `4 Q(N₁) ≤ 3 N²`
  have tQ : Γ ⊢[PRAAx] le (num 4 * ap2 (sumF qB) N₁ (succ N₁)) (num 3 * (succ N₁ * succ N₁)) := by
    refine .orE (zero_or_succ N₁) ?_ ?_
    · have h0 : ((N₁ ≐ zero) :: Γ) ⊢[PRAAx] N₁ ≐ zero := Prf.hyp0
      have ez := natEq ((congrAp2 (sumF qB) h0 (.eqRefl _)).eqTrans (sum_zero (Γ := (N₁ ≐ zero) :: Γ) qB (succ N₁)))
      ipra_le 3 * (𝔞 N₁ + 1) * (𝔞 N₁ + 1) using linear_combination -4 * ez
    · have hL : ((N₁ ≐ succ (pred N₁)) :: Γ) ⊢[PRAAx] N₁ ≐ succ (pred N₁) := Prf.hyp0
      have I := qinv (Γ := (N₁ ≐ succ (pred N₁)) :: Γ) (succ N₁) (pred N₁)
      have eL := natEq hL
      have eQ := natEq (congrAp2 (sumF qB) hL (.eqRefl (succ N₁)))
      refine mul_le_cancel (d' := N₁) ?_
      ipra_le sl I + 4 * (𝔞 N₁ + 1) * (𝔞 N₁ + 1) using
        linear_combination (3 * (𝔞 N₁ + 1) * (𝔞 N₁ + 1) - 4 * 𝔞 (ap2 (sumF qB) (succ (pred N₁)) (succ N₁))) * eL -
          4 * (𝔞 N₁ + 1) * eQ
  have eDP := natEq sp
  ipra_le 4 * sl tP + 4 * sl tS + sl tQ using
    linear_combination -4 * eDP - 4 * e1 - 4 * e2 - 4 * ez0 - 4 * ez1

end LeanProofs.IPRA.DiophantineNumberTheory.ConicCoprimeCount
