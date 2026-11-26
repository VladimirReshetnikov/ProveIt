import IPRADerivations.Analysis.Exponential.ExponentialSeries
import IPRADerivations.AnalyticNumberTheory.LocalFactor
import IPRADerivations.AnalyticNumberTheory.PowerCleared
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.DiophantineNumberTheory.CoprimeModulus
import IPRADerivations.Core.LinearCombination

/-!
# The finite schedule of the eta certificate checker

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/foundations.tex`, §"A concrete negative RH
coding: the eta function" (`sec:etacert`). The packet specifies a primitive-recursive checker `Bad(c)` for zeros of
`η` in rational rectangles right of the critical line and states that its analytic adequacy (argument principle,
homotopy, completeness) is a separate, open proof obligation. What the specification itself asserts about its
explicit schedule is finite arithmetic, derived here in object iPRA with cleared denominators:

* the Taylor cutoff: "for `|z| ≤ D` … `K = 2 max(2D², p + 4)` … the tail after degree `K` is at most `2^{−p−3}`"
  (`taylor_tail`): with `K = 2h`, `h ≥ 2D²`, `h ≥ p + 4`, `D ≥ 1`,
  `Σ_{K<j≤K+T} D^j/j! ≤ 2^{−p−3}(1 − 2^{−T})`, as `2^{p+3} 2^T A_T + (K+T)! ≤ 2^T (K+T)!` for the cleared partial sum
  `A_T = (K+T)! Σ_{K<j≤K+T} D^j/j!` (`Av`, `A_succ`). The proof is the packet's: "the factorial lower bound from the
  final half of the factors" (`fact_shift`: `h! h^i ≤ (h+i)!`, `first_term`: `2^{p+4} D^{K+1} ≤ (K+1)!`) "and a
  geometric ratio bound" (`term_bound`: the terms decrease by a factor `≤ 1/2`, `tail_inv`);
* the series tail schedule `N = 8M²2^{2k}` of `eq:eta-tail`: `2N = (4M 2^k)²`, i.e. `2M/√(2N) = ε/2` for
  `ε = 2^{−k}` (`tail_schedule`);
* the per-term budget `p = k + ℓ(N) + 4`: `2^{−p} < ε/(4N)` whenever `N ≤ 2^{ℓ(N)}` (`term_schedule`);
* the perturbation budget `h = p + ℓ(M) + 2(D+1) + 4`: `3^{D+1} M 2^{−h} < 2^{−p−4}` whenever `M ≤ 2^{ℓ(M)}`
  (`perturb_schedule`).

The analytic estimates `eq:eta-tail`, `eq:eta-derivative`, the homotopy and argument-principle soundness, and the
completeness of the coding remain the packet's open obligations; they are not claimed here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.EtaSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Analysis.ExponentialSeries (fact_succ' fact_zero')
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem two_pos : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := congrSucc (pred_succ _).eqSymm

/-! ## The factorial lower bound from the final half of the factors -/

theorem fs_step {h i : PTm n} (ih : Γ ⊢[PRAAx] le (fact h * pw h i) (fact (h + i))) :
    Γ ⊢[PRAAx] le (fact h * pw h (succ i)) (fact (h + succ i)) := by
  refine le_of_eq_add (d := succ (h + i) * monus (fact (h + i)) (fact h * pw h i) + fact h * pw h i * succ i) ?_
  ipra_lc natEq (congrAp2 (Γ := Γ) factF (add_succ h i) (.eqRefl zero)) + natEq (fact_succ' (Γ := Γ) (h + i)) +
    (𝔞 h + 𝔞 i + 1) * natEq (eq_add_of_le ih) - 𝔞 (fact h) * natEq (pw_succ (Γ := Γ) h i)

/-- `h! h^i ≤ (h + i)!`. -/
theorem fact_shift (h i : PTm n) : Γ ⊢[PRAAx] le (fact h * pw h i) (fact (h + i)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (fact (Syn.shift h) * pw (Syn.shift h) (var 0)) (fact (Syn.shift h + var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_le, subst_ap2, PTm.subst_mul, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine le_of_eq_add (d := zero) ?_
      ipra_lc natEq (congrAp2 (Γ := Γ) factF (add_zero h) (.eqRefl zero)) - 𝔞 (fact h) * natEq (pw_zero (Γ := Γ) h)
    · simp only [subst_le, subst_ap2, PTm.subst_mul, PTm.subst_add, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      let D : List (Fm PTm (n + 1)) :=
        le (fact (Syn.shift h) * pw (Syn.shift h) (var 0)) (fact (Syn.shift h + var 0)) :: Γ.map Fm.shift
      exact fs_step (Prf.hyp0 : D ⊢[PRAAx] _)
  have r := Prf.allE i hall
  simp only [subst_le, subst_ap2, PTm.subst_mul, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at r
  exact r

/-- `2^q D^{2h+1} ≤ (2h+1)!` for `D ≥ 1`, `2D² ≤ h`, `q ≤ h`: `2^q D^{2h+1} ≤ (2D²)^{h+1} ≤ h^{h+1} ≤ h! h^{h+1}
≤ (2h+1)!`. -/
theorem first_term {D h q : PTm n} (hD : Γ ⊢[PRAAx] D ≐ succ (pred D)) (hh : Γ ⊢[PRAAx] le (two * (D * D)) h)
    (hq : Γ ⊢[PRAAx] le q h) :
    Γ ⊢[PRAAx] le (pw two q * pw D (succ (two * h))) (fact (succ (two * h))) := by
  have a1 : Γ ⊢[PRAAx] le (pw two q) (pw two (succ h)) :=
    PowerCleared.pw_le_exp two_pos (le_trans hq (le_succ_self h))
  have a2 : Γ ⊢[PRAAx] le (pw D (succ (two * h))) (pw D (two * succ h)) :=
    PowerCleared.pw_le_exp hD (le_of_eq_add (d := one) (by ipra_ring))
  have e3 : Γ ⊢[PRAAx] pw (two * (D * D)) (succ h) ≐ pw two (succ h) * pw D (two * succ h) :=
    (LocalFactor.pw_mul_base two (D * D) (succ h)).eqTrans
      (congrMul (.eqRefl _) (DiophantineNumberTheory.CoprimeModulus.pw_sq D (succ h)))
  have b1 := le_congr (.eqRefl _) e3.eqSymm (le_mul_mono a1 a2)
  have b2 := pw_le_pw (succ h) hh
  have fp := natEq (Primes.fact_pos (Γ := Γ) h)
  have b3 : Γ ⊢[PRAAx] le (pw h (succ h)) (fact h * pw h (succ h)) :=
    le_of_eq_add (d := pred (fact h) * pw h (succ h))
      (by apply deriveNat; ipra_simps; linear_combination 𝔞 (pw h (succ h)) * fp)
  have eh : Γ ⊢[PRAAx] h + succ h ≐ succ (two * h) := by ipra_ring
  have b4 := le_congr (.eqRefl _) (congrAp2 factF eh (.eqRefl zero)) (fact_shift h (succ h))
  exact le_trans b1 (le_trans b2 (le_trans b3 b4))

/-! ## The geometric ratio bound -/

theorem tb_step {c D K i : PTm n} (hk : Γ ⊢[PRAAx] le (two * D) (succ (succ K)))
    (ih : Γ ⊢[PRAAx] le (pw two i * (c * pw D (succ K + i))) (fact (succ K + i))) :
    Γ ⊢[PRAAx] le (pw two (succ i) * (c * pw D (succ K + succ i))) (fact (succ K + succ i)) := by
  have hk' : Γ ⊢[PRAAx] le (two * D) (succ (succ K + i)) :=
    le_trans hk (le_of_eq_add (d := i) (by ipra_ring))
  have m := le_mul_mono ih hk'
  refine le_congr ?_ ?_ m
  · ipra_lc (-(𝔞 c * 𝔞 (pw D (succ K + succ i)))) * natEq (pw_succ (Γ := Γ) two i) -
      2 * 𝔞 (pw two i) * 𝔞 c * natEq ((congrAp2 (Γ := Γ) powF (add_succ (succ K) i) (.eqRefl D)).eqTrans (pw_succ D (succ K + i)))
  · exact ((congrAp2 factF (add_succ (succ K) i) (.eqRefl zero)).eqTrans (fact_succ' _)).eqSymm

/-- If `c D^{K+1} ≤ (K+1)!` and `2D ≤ K + 2`, then `2^i c D^{K+1+i} ≤ (K+1+i)!` for every `i`. -/
theorem term_bound {c D K : PTm n} (hB : Γ ⊢[PRAAx] le (c * pw D (succ K)) (fact (succ K)))
    (hk : Γ ⊢[PRAAx] le (two * D) (succ (succ K))) (i : PTm n) :
    Γ ⊢[PRAAx] le (pw two i * (c * pw D (succ K + i))) (fact (succ K + i)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (pw two (var 0) * (Syn.shift c * pw (Syn.shift D) (succ (Syn.shift K) + var 0)))
      (fact (succ (Syn.shift K) + var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_le, subst_ap2, PTm.subst_mul, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine le_congr ?_ (congrAp2 factF (add_zero (succ K)) (.eqRefl zero)).eqSymm hB
      ipra_lc (-(𝔞 c * 𝔞 (pw D (succ K + zero)))) * natEq (pw_zero (Γ := Γ) (two : PTm n)) -
        𝔞 c * natEq (congrAp2 (Γ := Γ) powF (add_zero (succ K)) (.eqRefl D))
    · simp only [subst_le, subst_ap2, PTm.subst_mul, PTm.subst_add, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      let Δ : List (Fm PTm (n + 1)) := le (pw two (var 0) * (Syn.shift c * pw (Syn.shift D) (succ (Syn.shift K) + var 0)))
        (fact (succ (Syn.shift K) + var 0)) :: Γ.map Fm.shift
      have hk' : Δ ⊢[PRAAx] le (two * Syn.shift D) (succ (succ (Syn.shift K))) := by
        have b := hk.shift
        simp only [Fm.shift, subst_le, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at b
        exact b.wk
      exact tb_step hk' (Prf.hyp0 : Δ ⊢[PRAAx] _)
  have r := Prf.allE i hall
  simp only [subst_le, subst_ap2, PTm.subst_mul, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at r
  exact r

/-! ## The cleared partial sums of the tail -/

/-- Step: `0 = T`, `1 = A_T`, `2 = ⟨K, D⟩`: `A_{T+1} = (K+T+1) A_T + D^{K+T+1}`. -/
abbrev aStep : PTm 3 :=
  succ (fstT (var 2) + var 0) * var 1 + pw (sndT (var 2)) (succ (fstT (var 2) + var 0))
def Af : PR 2 := rec2 zero aStep
/-- `A_T = (K+T)! Σ_{K<j≤K+T} D^j/j!`. -/
abbrev Av (T K D : PTm n) : PTm n := ap2 Af T (pairT K D)

theorem A_zero (K D : PTm n) : Γ ⊢[PRAAx] Av zero K D ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero aStep (pairT K D)
  simp only [ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem A_succ (T K D : PTm n) :
    Γ ⊢[PRAAx] Av (succ T) K D ≐ succ (K + T) * Av T K D + pw D (succ (K + T)) := by
  have h : Γ ⊢[PRAAx] ap2 Af (succ T) (pairT K D) ≐ Syn.subst ![T, ap2 Af T (pairT K D), pairT K D] aStep :=
    rec2_succ (Γ := Γ) zero _ T (pairT K D)
  have e : Syn.subst ![T, ap2 Af T (pairT K D), pairT K D] aStep =
      succ (fstT (pairT K D) + T) * ap2 Af T (pairT K D) + pw (sndT (pairT K D)) (succ (fstT (pairT K D) + T)) := by
    simp
  rw [e] at h
  have f := fst_pair (Γ := Γ) K D
  have s := snd_pair (Γ := Γ) K D
  exact h.eqTrans (congrAdd (congrMul (congrSucc (congrAdd f (.eqRefl _))) (.eqRefl _))
    (congrAp2 powF (congrSucc (congrAdd f (.eqRefl _))) s))

/-- The tail invariant `c 2^T A_T + (K+T)! ≤ 2^T (K+T)!`, i.e. `Σ_{K<j≤K+T} D^j/j! ≤ (1 − 2^{−T})/c`. -/
abbrev TI (c K D T : PTm n) : Fm PTm n :=
  le (c * pw two T * Av T K D + fact (K + T)) (pw two T * fact (K + T))

theorem ti_step {c K D T : PTm n}
    (tb : Γ ⊢[PRAAx] le (pw two T * (two * c * pw D (succ K + T))) (fact (succ K + T)))
    (ih : Γ ⊢[PRAAx] TI c K D T) : Γ ⊢[PRAAx] TI c K D (succ T) := by
  have sa : Γ ⊢[PRAAx] succ K + T ≐ succ (K + T) := by ipra_ring
  refine le_of_eq_add (d := monus (fact (succ K + T)) (pw two T * (two * c * pw D (succ K + T))) +
    two * succ (K + T) * monus (pw two T * fact (K + T)) (c * pw two T * Av T K D + fact (K + T))) ?_
  ipra_lc (𝔞 (fact (K + succ T)) - 𝔞 c * 𝔞 (Av (succ T) K D)) * natEq (pw_succ (Γ := Γ) two T) +
    (2 * 𝔞 (pw two T) - 1) * natEq ((congrAp2 (Γ := Γ) factF (add_succ K T) (.eqRefl zero)).eqTrans (fact_succ' (K + T))) -
    2 * 𝔞 (pw two T) * 𝔞 c * natEq (A_succ (Γ := Γ) T K D) + 2 * (𝔞 K + 𝔞 T + 1) * natEq (eq_add_of_le ih) -
    natEq ((congrAp2 (Γ := Γ) factF sa (.eqRefl zero)).eqTrans (fact_succ' (K + T))) + natEq (eq_add_of_le tb) +
    2 * 𝔞 c * 𝔞 (pw two T) * natEq (congrAp2 (Γ := Γ) powF sa (.eqRefl D))

/-- If `2c D^{K+1} ≤ (K+1)!` and `2D ≤ K + 2`, the tail invariant holds for every `T`. -/
theorem tail_inv {c K D : PTm n} (hB : Γ ⊢[PRAAx] le (two * c * pw D (succ K)) (fact (succ K)))
    (hk : Γ ⊢[PRAAx] le (two * D) (succ (succ K))) (T : PTm n) : Γ ⊢[PRAAx] TI c K D T := by
  have hall : Γ ⊢[PRAAx] Fm.all (TI (Syn.shift c) (Syn.shift K) (Syn.shift D) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_mul, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine le_of_eq_add (d := zero) ?_
      ipra_lc 𝔞 (fact (K + zero)) * natEq (pw_zero (Γ := Γ) (two : PTm n)) -
        𝔞 c * 𝔞 (pw two zero) * natEq (A_zero (Γ := Γ) K D)
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_mul, PTm.subst_add, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      let Δ : List (Fm PTm (n + 1)) := TI (Syn.shift c) (Syn.shift K) (Syn.shift D) (var 0) :: Γ.map Fm.shift
      have hB' : Δ ⊢[PRAAx] le (two * Syn.shift c * pw (Syn.shift D) (succ (Syn.shift K))) (fact (succ (Syn.shift K))) := by
        have b := hB.shift
        simp only [Fm.shift, subst_le, subst_ap2, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
          ConciseIPRA.PTm.subst_zero] at b
        exact b.wk
      have hk' : Δ ⊢[PRAAx] le (two * Syn.shift D) (succ (succ (Syn.shift K))) := by
        have b := hk.shift
        simp only [Fm.shift, subst_le, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at b
        exact b.wk
      have tb := term_bound (c := two * Syn.shift c) hB' hk' (var 0)
      exact ti_step tb (Prf.hyp0 : Δ ⊢[PRAAx] _)
  have r := Prf.allE T hall
  simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_mul, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at r
  exact r

/-- The packet's Taylor cutoff: for `D ≥ 1`, `h ≥ 2D²`, `h ≥ p + 4` and `K = 2h`,
`2^{p+3} 2^T A_T + (K+T)! ≤ 2^T (K+T)!` for every `T`, i.e. `Σ_{K<j≤K+T} D^j/j! ≤ 2^{−p−3}(1 − 2^{−T})`. -/
theorem taylor_tail {D h p : PTm n} (hD : Γ ⊢[PRAAx] D ≐ succ (pred D)) (hh : Γ ⊢[PRAAx] le (two * (D * D)) h)
    (hp : Γ ⊢[PRAAx] le (succ (succ (succ (succ p)))) h) (T : PTm n) :
    Γ ⊢[PRAAx] TI (pw two (succ (succ (succ p)))) (two * h) D T := by
  have ft := first_term hD hh hp
  have hB : Γ ⊢[PRAAx] le (two * pw two (succ (succ (succ p))) * pw D (succ (two * h))) (fact (succ (two * h))) :=
    le_congr (congrMul ((pw_succ two (succ (succ (succ p)))).eqTrans (mul_comm _ _)) (.eqRefl _)) (.eqRefl _) ft
  have fp := natEq hD
  have dd : Γ ⊢[PRAAx] le (two * D) (two * (D * D)) :=
    le_of_eq_add (d := two * (D * pred D)) (by apply deriveNat; ipra_simps; linear_combination 2 * 𝔞 D * fp)
  have hk : Γ ⊢[PRAAx] le (two * D) (succ (succ (two * h))) :=
    le_trans dd (le_trans hh (le_of_eq_add (d := h + two) (by ipra_ring)))
  exact tail_inv hB hk T

/-! ## The error budget of the schedule -/

/-- `eq:eta-tail` with `N = 8M² 2^{2k}`: `2N = (4M 2^k)²`, so `2M/√(2N) = 2^{−k}/2 = ε/2`. -/
theorem tail_schedule (M k : PTm n) :
    Γ ⊢[PRAAx] two * (num 8 * (M * M) * (pw two k * pw two k)) ≐
      (num 4 * M * pw two k) * (num 4 * M * pw two k) := by
  ipra_ring

/-- The per-term budget `p = k + L + 4` with `N ≤ 2^L`: `4N 2^k < 2^p`, i.e. `2^{−p} < ε/(4N)` for `ε = 2^{−k}`. -/
theorem term_schedule {N L : PTm n} (hN : Γ ⊢[PRAAx] le N (pw two L)) (k : PTm n) :
    Γ ⊢[PRAAx] lt (num 4 * N * pw two k) (pw two (succ (succ (succ (succ (k + L)))))) := by
  refine le_of_eq_add (d := num 4 * pw two k * monus (pw two L) N + num 12 * (pred (pw two k) * pred (pw two L)) +
    num 12 * pred (pw two k) + num 12 * pred (pw two L) + num 11) ?_
  ipra_lc natEq (pw_succ (Γ := Γ) two (succ (succ (succ (k + L))))) +
    2 * natEq (pw_succ (Γ := Γ) two (succ (succ (k + L)))) + 4 * natEq (pw_succ (Γ := Γ) two (succ (k + L))) +
    8 * natEq (pw_succ (Γ := Γ) two (k + L)) + 16 * natEq (pw_add (Γ := Γ) two k L) +
    4 * 𝔞 (pw two k) * natEq (eq_add_of_le hN) + 12 * 𝔞 (pw two L) * natEq (pw_pos' (Γ := Γ) two_pos k) +
    12 * (𝔞 (pred (pw two k)) + 1) * natEq (pw_pos' (Γ := Γ) two_pos L)

/-- The perturbation budget `h = p + L + 2(D+1) + 4` with `1 ≤ M ≤ 2^L`: `3^{D+1} M 2^{p+4} < 2^h`, i.e.
`3^{D+1} M 2^{−h} < 2^{−p−4}`. -/
theorem perturb_schedule {M L : PTm n} (hM : Γ ⊢[PRAAx] le M (pw two L)) (p D : PTm n) :
    Γ ⊢[PRAAx] lt (pw (succ two) (succ D) * M * pw two (succ (succ (succ (succ p)))))
      (pw two (succ (succ (succ (succ (p + L + two * succ D)))))) := by
  have t3 : Γ ⊢[PRAAx] le (pw (succ two) D) (pw (two * two) D) :=
    pw_le_pw D (le_of_eq_add (d := one) (by ipra_ring))
  refine le_of_eq_add (d := num 48 * pw two p * (M * monus (pw (two * two) D) (pw (succ two) D) +
      monus (pw two L) M * pw (succ two) D + monus (pw two L) M * monus (pw (two * two) D) (pw (succ two) D)) +
    num 16 * (pred (pw two p) * pred (pw two L) * pred (pw (two * two) D) + pred (pw two p) * pred (pw two L) +
      pred (pw two p) * pred (pw (two * two) D) + pred (pw two L) * pred (pw (two * two) D) + pred (pw two p) +
      pred (pw two L) + pred (pw (two * two) D)) + num 15) ?_
  ipra_lc natEq (pw_succ (Γ := Γ) two (succ (succ (succ (p + L + two * succ D))))) +
    2 * natEq (pw_succ (Γ := Γ) two (succ (succ (p + L + two * succ D)))) +
    4 * natEq (pw_succ (Γ := Γ) two (succ (p + L + two * succ D))) +
    8 * natEq (pw_succ (Γ := Γ) two (p + L + two * succ D)) +
    16 * natEq (pw_add (Γ := Γ) two (p + L) (two * succ D)) +
    16 * 𝔞 (pw two (two * succ D)) * natEq (pw_add (Γ := Γ) two p L) -
    16 * 𝔞 (pw two p) * 𝔞 (pw two L) * natEq (DiophantineNumberTheory.CoprimeModulus.pw_sq (Γ := Γ) two (succ D)) +
    16 * 𝔞 (pw two p) * 𝔞 (pw two L) * natEq (pw_succ (Γ := Γ) (two * two) D) -
    3 * 𝔞 (pw (succ two) D) * 𝔞 M * (natEq (pw_succ (Γ := Γ) two (succ (succ (succ p)))) + 2 * natEq (pw_succ (Γ := Γ) two (succ (succ p))) + 4 * natEq (pw_succ (Γ := Γ) two (succ p)) + 8 * natEq (pw_succ (Γ := Γ) two p)) -
    𝔞 M * 𝔞 (pw two (succ (succ (succ (succ p))))) * natEq (pw_succ (Γ := Γ) (succ two) D) +
    48 * 𝔞 (pw two p) * 𝔞 (pw (two * two) D) * natEq (eq_add_of_le hM) +
    48 * 𝔞 (pw two p) * (𝔞 M + 𝔞 (monus (pw two L) M)) * natEq (eq_add_of_le t3) +
    16 * 𝔞 (pw two L) * 𝔞 (pw (two * two) D) * natEq (pw_pos' (Γ := Γ) two_pos p) +
    16 * (𝔞 (pred (pw two p)) + 1) * 𝔞 (pw (two * two) D) * natEq (pw_pos' (Γ := Γ) two_pos L) +
    16 * (𝔞 (pred (pw two p)) + 1) * (𝔞 (pred (pw two L)) + 1) * natEq (pw_pos' (Γ := Γ) (Combinatorics.Binomial.pos_mul two_pos two_pos) D)

end LeanProofs.IPRA.AnalyticNumberTheory.EtaSchedule
