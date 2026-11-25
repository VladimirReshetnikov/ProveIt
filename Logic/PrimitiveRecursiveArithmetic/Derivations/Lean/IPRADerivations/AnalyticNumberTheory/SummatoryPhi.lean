import IPRADerivations.AnalyticNumberTheory.CoprimePairs
import IPRADerivations.AnalyticNumberTheory.MobiusInversion
import IPRADerivations.Core.LinearCombination

/-!
# The summatory floor-square identity

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:summatory-phi`:
`2 ∑_{n ≤ N} φ(n) − 1 = ∑_{d ≤ N} μ(d) ⌊N/d⌋²` for `N ≥ 1`.

Instead of the triple sum over `(a, b, d)`, both sides are compared by their increments in `N`:

* `quo_succ`: `⌊(N+1)/d⌋ = ⌊N/d⌋ + [d ∣ N+1]`, so `⌊N/d⌋²` grows by `[d ∣ N+1](2⌊N/d⌋ + 1)`
  (`sq_step`, `dp_step`, `D_step`); `D^±(N) = ∑_{d ≤ N} μ^±(d) ⌊N/d⌋²` with `μ(d)` at its own bound;
* `inc_pt`, `inc_sum`: for `M = N + 1` the increment is `∑_{d ∣ M} μ(d) (2M/d − 1)`, i.e.
  `∑ inc + ∑_{d ∣ M} μ(d) = 2 ∑_{d ∣ M} μ(d) M/d` (`MobiusBounds.mu_bound` moves the bounds);
* with `phi_mobius` and `∑_{d ∣ M} μ(d) = [M = 1]` (`pb_cancel`), the increment is `2 φ(M) − [M = 1]`;
* `summatory_phi`: by induction `D⁺(N) + 1 = D⁻(N) + 2 ∑_{n ≤ N} φ(n)`; with
  `CoprimePairs.coprime_pairs` both sides also equal the coprime-pair count `C_N`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SummatoryPhi

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (mu_bound shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_eq' rem_lt' zero_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq phi totBody)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Floor arithmetic -/

/-- `⌊(N+1)/d⌋ = ⌊N/d⌋ + [d ∣ N+1]` for `d ≥ 1`. -/
theorem quo_succ {N d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] quo (succ N) d ≐ quo N d + eqb (rem (succ N) d) zero := by
  have dv := natEq (div_eq (j := N) hd)
  have rl := rem_lt' hd N
  refine .orE (lt_or_le (succ (rem N d)) d) ?_ ?_
  · let C : List (Fm PTm n) := lt (succ (rem N d)) d :: Γ
    have h : C ⊢[PRAAx] lt (succ (rem N d)) d := Prf.hyp0
    have dv' := natEq ((div_eq (j := N) hd).wk : C ⊢[PRAAx] _)
    have q : C ⊢[PRAAx] quo (succ N) d ≐ quo N d :=
      quo_eq hd.wk (r := succ (rem N d)) (by apply deriveNat; ipra_simps; linear_combination dv') h
    have r : C ⊢[PRAAx] rem (succ N) d ≐ succ (rem N d) :=
      rem_eq' hd.wk (q := quo N d) (by apply deriveNat; ipra_simps; linear_combination dv') h
    have e : C ⊢[PRAAx] eqb (rem (succ N) d) zero ≐ zero :=
      (congrEqb' r (.eqRefl _)).eqTrans (eqb_of_ne (.impI (succ_ne_zero' _ Prf.hyp0)))
    exact q.eqTrans ((add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) e.eqSymm))
  · let C : List (Fm PTm n) := le d (succ (rem N d)) :: Γ
    have e₁ : C ⊢[PRAAx] succ (rem N d) ≐ d := le_antisymm rl.wk Prf.hyp0
    have dv' := natEq ((div_eq (j := N) hd).wk : C ⊢[PRAAx] _)
    have a := natEq e₁
    have q : C ⊢[PRAAx] quo (succ N) d ≐ succ (quo N d) :=
      quo_eq hd.wk (r := zero) (by apply deriveNat; ipra_simps; linear_combination dv' + a) (zero_lt' hd.wk)
    have r : C ⊢[PRAAx] rem (succ N) d ≐ zero :=
      rem_eq' hd.wk (q := succ (quo N d)) (by apply deriveNat; ipra_simps; linear_combination dv' + a) (zero_lt' hd.wk)
    have e : C ⊢[PRAAx] eqb (rem (succ N) d) zero ≐ one := eqb_of_eq r
    exact q.eqTrans ((succ_eq_add_one _).eqTrans (congrAdd (.eqRefl _) e.eqSymm))

/-- `e · e = e` for an equality indicator. -/
theorem eqb_sq (a b : PTm n) : Γ ⊢[PRAAx] eqb a b * eqb a b ≐ eqb a b := by
  refine .orE (zero_or_succ (eqb a b)) ?_ ?_
  · have h : ((eqb a b ≐ zero) :: Γ) ⊢[PRAAx] eqb a b ≐ zero := Prf.hyp0
    exact (congrMul h h).eqTrans ((by ipra_ring : ((eqb a b ≐ zero) :: Γ) ⊢[PRAAx]
      zero * zero ≐ zero).eqTrans h.eqSymm)
  · let C : List (Fm PTm n) := (eqb a b ≐ succ (pred (eqb a b))) :: Γ
    have h : C ⊢[PRAAx] eqb a b ≐ succ (pred (eqb a b)) := Prf.hyp0
    have h' := natEq h
    have z : C ⊢[PRAAx] monus one (eqb a b) + pred (eqb a b) ≐ zero := by
      have e : C ⊢[PRAAx] succ (monus one (eqb a b) + pred (eqb a b)) ≐ succ zero := by
        ipra_lc natEq (eqb_split (Γ := C) a b) - h'
      exact (pred_succ _).eqSymm.eqTrans ((congrPred e).eqTrans (pred_succ _))
    have p0 := add_eq_zero_right z
    have e1 : C ⊢[PRAAx] eqb a b ≐ one := h.eqTrans (congrSucc p0)
    exact (congrMul e1 e1).eqTrans ((by ipra_ring : C ⊢[PRAAx] one * one ≐ one).eqTrans e1.eqSymm)

/-- `[N + 1 = 1] + sg N = 1`. -/
theorem eqb_sg (N : PTm n) : Γ ⊢[PRAAx] eqb (succ N) one + sg N ≐ one := by
  refine .orE (zero_or_succ N) ?_ ?_
  · have h : ((N ≐ zero) :: Γ) ⊢[PRAAx] N ≐ zero := Prf.hyp0
    exact (congrAdd (eqb_of_eq (congrSucc h)) ((congrSg h).eqTrans sg_zero)).eqTrans (add_zero _)
  · let C : List (Fm PTm n) := (N ≐ succ (pred N)) :: Γ
    have h : C ⊢[PRAAx] N ≐ succ (pred N) := Prf.hyp0
    have ne : C ⊢[PRAAx] neg (succ N ≐ one) := by
      refine .impI ?_
      have e : ((succ N ≐ one) :: C) ⊢[PRAAx] N ≐ zero :=
        (pred_succ _).eqSymm.eqTrans ((congrPred Prf.hyp0).eqTrans (pred_succ _))
      exact succ_ne_zero' _ (h.wk.eqSymm.eqTrans e)
    exact (congrAdd (eqb_of_ne ne) ((congrSg h).eqTrans (sg_succ _))).eqTrans (zero_add _)

/-! ## The floor-square sums -/

/-- `[d ≥ 1] μ⁺(d) ⌊N/d⌋²`, over `0 = d`, `1 = N`. -/
abbrev DPB : PTm 2 := (sg (var 0) * muP (succ (var 0)) (var 0)) * (quo (var 1) (var 0) * quo (var 1) (var 0))
/-- `[d ≥ 1] μ⁻(d) ⌊N/d⌋²`. -/
abbrev DNB : PTm 2 := (sg (var 0) * muN (succ (var 0)) (var 0)) * (quo (var 1) (var 0) * quo (var 1) (var 0))
/-- The increment `[d ≥ 1] μ⁺(d) [d ∣ N+1] (2⌊N/d⌋ + 1)`. -/
abbrev IPB : PTm 2 :=
  (sg (var 0) * muP (succ (var 0)) (var 0)) * (eqb (rem (succ (var 1)) (var 0)) zero * (two * quo (var 1) (var 0) + one))
abbrev INB : PTm 2 :=
  (sg (var 0) * muN (succ (var 0)) (var 0)) * (eqb (rem (succ (var 1)) (var 0)) zero * (two * quo (var 1) (var 0) + one))

theorem inst2_DP (d N : PTm n) : inst2 DPB d N = (sg d * muP (succ d) d) * (quo N d * quo N d) := by simp [inst2]
theorem inst2_DN (d N : PTm n) : inst2 DNB d N = (sg d * muN (succ d) d) * (quo N d * quo N d) := by simp [inst2]
theorem inst2_IP (d N : PTm n) :
    inst2 IPB d N = (sg d * muP (succ d) d) * (eqb (rem (succ N) d) zero * (two * quo N d + one)) := by simp [inst2]
theorem inst2_IN (d N : PTm n) :
    inst2 INB d N = (sg d * muN (succ d) d) * (eqb (rem (succ N) d) zero * (two * quo N d + one)) := by simp [inst2]

/-- `X ⌊(N+1)/d⌋² = X ⌊N/d⌋² + X [d ∣ N+1] (2⌊N/d⌋ + 1)` for `d ≥ 1`. -/
theorem sq_step {N d : PTm n} (X : PTm n) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] X * (quo (succ N) d * quo (succ N) d) ≐
      X * (quo N d * quo N d) + X * (eqb (rem (succ N) d) zero * (two * quo N d + one)) := by
  ipra_lc 𝔞 X * (𝔞 (quo (succ N) d) + 𝔞 (quo N d) + 𝔞 (eqb (rem (succ N) d) zero)) * natEq (quo_succ (N := N) hd) +
    𝔞 X * natEq (eqb_sq (Γ := Γ) (rem (succ N) d) zero)

theorem sg_zero_case {d : PTm n} (h : Γ ⊢[PRAAx] d ≐ zero) (Y Z : PTm n) : Γ ⊢[PRAAx] (sg d * Y) * Z ≐ zero :=
  zero_mul_l (zero_mul_l ((congrSg h).eqTrans sg_zero) Y) Z

theorem dp_step (d N : PTm n) :
    Γ ⊢[PRAAx] (inst2 DPB d (succ N) ≐ inst2 DPB d N + inst2 IPB d N) ⋏
      (inst2 DNB d (succ N) ≐ inst2 DNB d N + inst2 INB d N) := by
  rw [inst2_DP, inst2_DP, inst2_IP, inst2_DN, inst2_DN, inst2_IN]
  refine .orE (zero_or_succ d) ?_ ?_
  · have h : ((d ≐ zero) :: Γ) ⊢[PRAAx] d ≐ zero := Prf.hyp0
    exact .andI ((sg_zero_case h _ _).eqTrans ((congrAdd (sg_zero_case h _ _) (sg_zero_case h _ _)).eqTrans
      (add_zero _)).eqSymm) ((sg_zero_case h _ _).eqTrans ((congrAdd (sg_zero_case h _ _) (sg_zero_case h _ _)).eqTrans
      (add_zero _)).eqSymm)
  · exact .andI (sq_step _ Prf.hyp0) (sq_step _ Prf.hyp0)

/-- `⌊N/(N+1)⌋ = 0`. -/
theorem quo_lt_self (N : PTm n) : Γ ⊢[PRAAx] quo N (succ N) ≐ zero :=
  quo_eq (congrSucc (pred_succ _).eqSymm) (r := N) (by ipra_ring) (monus_self _ |>.eqTrans (.eqRefl _))

/-- `D(N + 1) = D(N) + ∑_{d ≤ N+1} inc(d, N)`. -/
theorem D_step (N : PTm n) :
    Γ ⊢[PRAAx] (ap2 (sumF DPB) (succ (succ N)) (succ N) ≐
        ap2 (sumF DPB) (succ N) N + ap2 (sumF IPB) (succ (succ N)) N) ⋏
      (ap2 (sumF DNB) (succ (succ N)) (succ N) ≐
        ap2 (sumF DNB) (succ N) N + ap2 (sumF INB) (succ (succ N)) N) := by
  have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  have cP : Γ ⊢[PRAAx] ap2 (sumF DPB) (succ (succ N)) (succ N) ≐ ap2 (sumF (addBody DPB IPB)) (succ (succ N)) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, hs]; exact Prf.andE₁ (dp_step _ _)
  have cN : Γ ⊢[PRAAx] ap2 (sumF DNB) (succ (succ N)) (succ N) ≐ ap2 (sumF (addBody DNB INB)) (succ (succ N)) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, hs]; exact Prf.andE₂ (dp_step _ _)
  have q0 := quo_lt_self (Γ := Γ) N
  have tP : Γ ⊢[PRAAx] inst2 DPB (succ N) N ≐ zero := by
    rw [inst2_DP]; exact (congrMul (.eqRefl _) (congrMul q0 q0)).eqTrans (by ipra_ring)
  have tN : Γ ⊢[PRAAx] inst2 DNB (succ N) N ≐ zero := by
    rw [inst2_DN]; exact (congrMul (.eqRefl _) (congrMul q0 q0)).eqTrans (by ipra_ring)
  have a₁ := natEq cP; have a₂ := natEq cN
  have c₁ := natEq (sum_succ' (Γ := Γ) DPB (succ N) N); have c₂ := natEq (sum_succ' (Γ := Γ) DNB (succ N) N)
  have z₁ := natEq tP; have z₂ := natEq tN
  refine .andI ?_ ?_
  · ipra_lc a₁ + natEq (sum_add (Γ := Γ) DPB IPB (succ (succ N)) N) + c₁ + z₁
  · ipra_lc a₂ + natEq (sum_add (Γ := Γ) DNB INB (succ (succ N)) N) + c₂ + z₂

/-! ## The increment as a Möbius sum -/

/-- `inc(d, N) + [d ∣ M] μ(d) = 2 [d ∣ M] μ(d) M/d` for `M = N + 1` and `d ≤ M`. -/
theorem inc_pt {d N : PTm n} (h : Γ ⊢[PRAAx] lt d (succ (succ N))) :
    Γ ⊢[PRAAx] (inst2 IPB d N + inst2 PB d (succ N) ≐ two * inst2 MobiusInversion.QP d (succ N)) ⋏
      (inst2 INB d N + inst2 NB d (succ N) ≐ two * inst2 MobiusInversion.QN d (succ N)) := by
  rw [inst2_IP, inst2_IN, inst2_PB, inst2_NB, MobiusInversion.inst2_QP, MobiusInversion.inst2_QN]
  refine .orE (zero_or_succ d) ?_ ?_
  · have h0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] d ≐ zero := Prf.hyp0
    have z := natEq ((congrSg h0).eqTrans sg_zero)
    refine .andI ?_ ?_ <;> (apply deriveNat; ipra_simps)
    · linear_combination (𝔞 (eqb (sq (succ d) d) zero) * 𝔞 (eqb (rem (om (succ d) d) two) zero) *
        (𝔞 (eqb (rem (succ N) d) zero) * (2 * 𝔞 (quo N d) + 1)) +
        𝔞 (eqb (rem (succ N) d) zero) * 𝔞 (eqb (sq (succ (succ N)) d) zero) *
          𝔞 (eqb (rem (om (succ (succ N)) d) two) zero) * (1 - 2 * 𝔞 (quo (succ N) d))) * z
    · linear_combination (𝔞 (eqb (sq (succ d) d) zero) * 𝔞 (eqb (rem (om (succ d) d) two) one) *
        (𝔞 (eqb (rem (succ N) d) zero) * (2 * 𝔞 (quo N d) + 1)) +
        𝔞 (eqb (rem (succ N) d) zero) * 𝔞 (eqb (sq (succ (succ N)) d) zero) *
          𝔞 (eqb (rem (om (succ (succ N)) d) two) one) * (1 - 2 * 𝔞 (quo (succ N) d))) * z
  · let C : List (Fm PTm n) := (d ≐ succ (pred d)) :: Γ
    have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    have hdM : C ⊢[PRAAx] le (succ d) (succ (succ N)) := h.wk
    have hdd : C ⊢[PRAAx] le (succ d) (succ d) := le_refl _
    have b₁ := mu_bound hd hdM
    have q := natEq (quo_succ (N := N) hd)
    have e := natEq (eqb_sq (Γ := C) (rem (succ N) d) zero)
    have m₁ := natEq (Prf.andE₁ b₁); have m₂ := natEq (Prf.andE₂ b₁)
    refine .andI ?_ ?_ <;> (apply deriveNat; ipra_simps)
    · linear_combination 𝔞 (sg d) * 𝔞 (eqb (rem (succ N) d) zero) * (1 - 2 * 𝔞 (quo (succ N) d)) * m₁ -
        2 * 𝔞 (sg d) * 𝔞 (eqb (rem (succ N) d) zero) * 𝔞 (eqb (sq (succ d) d) zero) *
          𝔞 (eqb (rem (om (succ d) d) two) zero) * q -
        2 * 𝔞 (sg d) * 𝔞 (eqb (sq (succ d) d) zero) * 𝔞 (eqb (rem (om (succ d) d) two) zero) * e
    · linear_combination 𝔞 (sg d) * 𝔞 (eqb (rem (succ N) d) zero) * (1 - 2 * 𝔞 (quo (succ N) d)) * m₂ -
        2 * 𝔞 (sg d) * 𝔞 (eqb (rem (succ N) d) zero) * 𝔞 (eqb (sq (succ d) d) zero) *
          𝔞 (eqb (rem (om (succ d) d) two) one) * q -
        2 * 𝔞 (sg d) * 𝔞 (eqb (sq (succ d) d) zero) * 𝔞 (eqb (rem (om (succ d) d) two) one) * e

/-- `PB` read at `N + 1`. -/
def PBs : PTm 2 := Syn.subst ![var 0, succ (var 1)] PB
def NBs : PTm 2 := Syn.subst ![var 0, succ (var 1)] NB

theorem inst2_PBs (d N : PTm n) : inst2 PBs d N = inst2 PB d (succ N) := by
  simp only [inst2, PBs, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
theorem inst2_NBs (d N : PTm n) : inst2 NBs d N = inst2 NB d (succ N) := by
  simp only [inst2, NBs, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

/-- `∑_{d ≤ M} inc(d) + ∑_{d ∣ M} μ(d) = 2 ∑_{d ∣ M} μ(d) M/d` for `M = N + 1`. -/
theorem inc_sum (N : PTm n) :
    Γ ⊢[PRAAx] (ap2 (sumF IPB) (succ (succ N)) N + ap2 (sumF PB) (succ (succ N)) (succ N) ≐
        two * ap2 (sumF MobiusInversion.QP) (succ (succ N)) (succ N)) ⋏
      (ap2 (sumF INB) (succ (succ N)) N + ap2 (sumF NB) (succ (succ N)) (succ N) ≐
        two * ap2 (sumF MobiusInversion.QN) (succ (succ N)) (succ N)) := by
  have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  have hss : Syn.shift (succ (succ N)) = succ (succ (Syn.shift N)) := by simp [Syn.shift]
  have h2 : Syn.shift (two : PTm n) = two := by simp [Syn.shift]
  have pP : Γ ⊢[PRAAx] ap2 (sumF PBs) (succ (succ N)) N ≐ ap2 (sumF PB) (succ (succ N)) (succ N) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_PBs, hs]; exact .eqRefl _
  have pN : Γ ⊢[PRAAx] ap2 (sumF NBs) (succ (succ N)) N ≐ ap2 (sumF NB) (succ (succ N)) (succ N) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_NBs, hs]; exact .eqRefl _
  have sP : Γ ⊢[PRAAx] ap2 (sumF (addBody IPB PBs)) (succ (succ N)) N ≐
      two * ap2 (sumF MobiusInversion.QP) (succ (succ N)) (succ N) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, inst2_PBs, hs, h2]
    have hl : (lt (var 0) (Syn.shift (succ (succ N))) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (var 0) (succ (succ (Syn.shift N))) := by rw [← hss]; exact Prf.hyp0
    exact Prf.andE₁ (inc_pt hl)
  have sN : Γ ⊢[PRAAx] ap2 (sumF (addBody INB NBs)) (succ (succ N)) N ≐
      two * ap2 (sumF MobiusInversion.QN) (succ (succ N)) (succ N) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, inst2_NBs, hs, h2]
    have hl : (lt (var 0) (Syn.shift (succ (succ N))) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (var 0) (succ (succ (Syn.shift N))) := by rw [← hss]; exact Prf.hyp0
    exact Prf.andE₂ (inc_pt hl)
  have b₁ := natEq pP; have b₂ := natEq pN; have c₁ := natEq sP; have c₂ := natEq sN
  refine .andI ?_ ?_
  · ipra_lc -natEq (sum_add (Γ := Γ) IPB PBs (succ (succ N)) N) - b₁ + c₁
  · ipra_lc -natEq (sum_add (Γ := Γ) INB NBs (succ (succ N)) N) - b₂ + c₂

/-- `∑_{d ∣ M} μ⁺(d) = ∑_{d ∣ M} μ⁻(d) + [M = 1]` for `M ≥ 1`. -/
theorem pb_cancel {M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ ⊢[PRAAx] ap2 (sumF PB) (succ M) M ≐ ap2 (sumF NB) (succ M) M + eqb M one := by
  refine .orE (lt_or_le one M) ?_ ?_
  · have h2 : (lt one M :: Γ) ⊢[PRAAx] le two M := Prf.hyp0
    have ne : (lt one M :: Γ) ⊢[PRAAx] eqb M one ≐ zero :=
      eqb_of_ne (.impI (not_succ_le_self one _ (le_congr (.eqRefl _) Prf.hyp0 h2.wk)))
    exact (mobius_cancel h2).eqTrans ((add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) ne.eqSymm))
  · let C : List (Fm PTm n) := le M one :: Γ
    have e1 : C ⊢[PRAAx] M ≐ one :=
      le_antisymm Prf.hyp0 (LeanProofs.IPRA.DiophantineNumberTheory.Coprime.one_le_of_pos hM.wk)
    have m1 := mobius_one (Γ := C)
    have aP : C ⊢[PRAAx] ap2 (sumF PB) (succ M) M ≐ ap2 (sumF PB) (succ one) one := congrAp2 (sumF PB) (congrSucc e1) e1
    have aN : C ⊢[PRAAx] ap2 (sumF NB) (succ M) M ≐ ap2 (sumF NB) (succ one) one := congrAp2 (sumF NB) (congrSucc e1) e1
    exact aP.eqTrans ((Prf.andE₁ m1).eqTrans ((zero_add _).eqSymm.eqTrans
      (congrAdd (aN.eqTrans (Prf.andE₂ m1)).eqSymm (eqb_of_eq e1).eqSymm)))

/-! ## The induction -/

open LeanProofs.IPRA.AnalyticNumberTheory.CoprimePairs (PhiB inst2_Phi gB3 coprime_pairs)

/-- The induction step of `D⁺(N) + sg N = D⁻(N) + 2 ∑_{b ≤ N} φ(b)`. -/
theorem sp_step {N : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (sumF DPB) (succ N) N + sg N ≐ ap2 (sumF DNB) (succ N) N + two * ap2 (sumF PhiB) (succ N) zero) :
    Γ ⊢[PRAAx] ap2 (sumF DPB) (succ (succ N)) (succ N) + sg (succ N) ≐
      ap2 (sumF DNB) (succ (succ N)) (succ N) + two * ap2 (sumF PhiB) (succ (succ N)) zero := by
  have hM : Γ ⊢[PRAAx] succ N ≐ succ (pred (succ N)) := congrSucc (pred_succ _).eqSymm
  have ds := D_step (Γ := Γ) N
  have is := inc_sum (Γ := Γ) N
  have ph := sum_succ' (Γ := Γ) PhiB (succ N) zero
  rw [inst2_Phi] at ph
  ipra_lc natEq (Prf.andE₁ ds) - natEq (Prf.andE₂ ds) + natEq ih + natEq (Prf.andE₁ is) - natEq (Prf.andE₂ is) -
    natEq (pb_cancel hM) + 2 * natEq (MobiusInversion.phi_mobius hM) - natEq (eqb_sg (Γ := Γ) N) - 2 * natEq ph +
    natEq (sg_succ (Γ := Γ) N)

/-- Variable: `0 = N`. -/
private abbrev spF : Fm PTm 1 :=
  ap2 (sumF DPB) (succ (var 0)) (var 0) + sg (var 0) ≐
    ap2 (sumF DNB) (succ (var 0)) (var 0) + two * ap2 (sumF PhiB) (succ (var 0)) zero

private theorem sp_base : Γ ⊢[PRAAx] ap2 (sumF DPB) (succ zero) (zero : PTm n) + sg zero ≐
    ap2 (sumF DNB) (succ zero) zero + two * ap2 (sumF PhiB) (succ zero) zero := by
  have a := natEq (sum_succ' (Γ := Γ) DPB zero (zero : PTm n))
  have b := natEq (sum_succ' (Γ := Γ) DNB zero (zero : PTm n))
  have c := sum_succ' (Γ := Γ) PhiB zero (zero : PTm n)
  rw [inst2_Phi] at c
  have c' := natEq c
  have z₁ := natEq (sum_zero (Γ := Γ) DPB (zero : PTm n)); have z₂ := natEq (sum_zero (Γ := Γ) DNB (zero : PTm n))
  have z₃ := natEq (sum_zero (Γ := Γ) PhiB (zero : PTm n))
  have t₁ := natEq ((show inst2 DPB zero (zero : PTm n) = _ from inst2_DP _ _) ▸ sg_zero_case (Γ := Γ) (.eqRefl zero) _ _)
  have t₂ := natEq ((show inst2 DNB zero (zero : PTm n) = _ from inst2_DN _ _) ▸ sg_zero_case (Γ := Γ) (.eqRefl zero) _ _)
  have p0 := natEq (sum_zero (Γ := Γ) totBody (zero : PTm n))
  have s0 := natEq (sg_zero (Γ := Γ) (n := n))
  apply deriveNat; ipra_simps
  linear_combination a - b + z₁ - z₂ + t₁ - t₂ + s0 - 2 * c' - 2 * z₃ - 2 * p0

private theorem sp₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] spF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.inst_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, PTm.subst_monus]
    exact sp_base
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.repl_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, PTm.subst_monus]
    exact sp_step Prf.hyp0

/-- `thm:summatory-phi`: `2 ∑_{n ≤ N} φ(n) − 1 = ∑_{d ≤ N} μ(d) ⌊N/d⌋²` for `N ≥ 1`, as
`∑_d μ⁺(d) ⌊N/d⌋² + 1 = ∑_d μ⁻(d) ⌊N/d⌋² + 2 ∑_{n ≤ N} φ(n)`; and both sides count the coprime
pairs in `[1, N]²`: `∑_d μ⁺(d) ⌊N/d⌋² = ∑_d μ⁻(d) ⌊N/d⌋² + C_N`. -/
theorem summatory_phi {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] (ap2 (sumF DPB) (succ N) N + one ≐ ap2 (sumF DNB) (succ N) N + two * ap2 (sumF PhiB) (succ N) zero) ⋏
      (ap2 (sumF DPB) (succ N) N ≐ ap2 (sumF DNB) (succ N) N + SquareLayers.Sq gB3 (succ N) zero) := by
  have i := inst (Γ := Γ) sp₀ ![N]
  simp at i
  have s1 := (congrSg hN).eqTrans (sg_succ _)
  have a := natEq i; have b := natEq s1
  refine .andI ?_ ?_
  · ipra_lc a - b
  · ipra_lc a - b - natEq (coprime_pairs hN)

end LeanProofs.IPRA.AnalyticNumberTheory.SummatoryPhi
