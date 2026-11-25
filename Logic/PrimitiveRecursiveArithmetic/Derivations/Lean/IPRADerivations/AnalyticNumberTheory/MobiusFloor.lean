import IPRADerivations.AnalyticNumberTheory.MobiusSummatory
import IPRADerivations.AnalyticNumberTheory.SumPhi
import IPRADerivations.AnalyticNumberTheory.HyperbolaSwap
import IPRADerivations.Core.CommonLemmas

/-!
# The Möbius floor identity `∑_{d ≤ x} μ(d) ⌊x/d⌋ = [x ≥ 1]`

Packets: `analytic-number-theory/mobius_ipra`, `arithmetic.tex` ("`1 = ∑_{d ≤ N} μ(d) ⌊N/d⌋`"), and
`diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex` (the hyperbola identities).

It is the summed Möbius inversion `MobiusSummatory.mobius_summatory` at the unit `ε(n) = [n = 1]` of the
convolution: `(ε * 𝟏)(k) = 1` for `k ≥ 1`, so the inner summatory function is `B(m) = m`, and
`∑_{n ≤ x} ε(n) = [x ≥ 1]`.

* the unit `ε`, `(ε * 𝟏)(k) = 1` and `∑_{k < m} (ε * 𝟏)(k + 1) = m` are `SymmetryInstances.epsB`, `conv_eps`,
  `eps_bs`;
* `FPB`, `FNB`: the bodies `[d ≥ 1] μ^±(d) ⌊x/d⌋`; `rowP`, `rowN`, `sumP`, `sumN`: the two sides of the summed
  inversion in this form;
* `sum_eps`: `∑_{n ≤ x} [n ≥ 1] ε(n) = [x ≥ 1]` for every `x` (`SymmetryInstances.sum_sg_eps` for `x ≥ 1`);
* `mobius_floor`: `∑_{d ≤ x} μ⁺(d) ⌊x/d⌋ = [x ≥ 1] + ∑_{d ≤ x} μ⁻(d) ⌊x/d⌋`, the Möbius function being the pair
  `μ = μ⁺ − μ⁻` of natural-number bodies;
* `MP`, `MN`: the two parts `M^±(m) = ∑_{k ≤ m} μ^±(k)` of the Mertens function, and `mertens_floor`
  (packet `analytic-number-theory/mertens-ipra`, `identities.tex`, `thm:floor-recurrence`, first identity):
  `∑_{a ≤ x} M⁺(⌊x/a⌋) = [x ≥ 1] + ∑_{a ≤ x} M⁻(⌊x/a⌋)`, that is `∑_{a=1}^{N} M(⌊N/a⌋) = 1` for `N ≥ 1`.
  It is `mobius_floor` read through the exchange `HyperbolaSwap.hyp_swap` of the two summations.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.MobiusFloor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (muP muN congrSg zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances (epsB eps_bs sum_sg_eps)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (one_le_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv cv_at)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (cvF inst2_cvF sg_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (RB RB_at Bs bS inst2_bS)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetrySum (aPB aNB inst2_aP inst2_aN)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusSummatory (bF gS inst2_gS mobius_summatory)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_ones)
open LeanProofs.IPRA.AnalyticNumberTheory.HyperbolaSwap (hyp_swap)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The unit of the convolution -/

theorem inst2_oneB (d y : PTm n) : inst2 (one : PTm 2) d y = one := by simp [inst2]

/-! ## The two sides -/

/-- `[d ≥ 1] μ⁺(d) ⌊x/d⌋`, over `0 = d`, `1 = x`. -/
abbrev FPB : PTm 2 := (sg (var 0) * muP (succ (var 0)) (var 0)) * quo (var 1) (var 0)

/-- `[d ≥ 1] μ⁻(d) ⌊x/d⌋`. -/
abbrev FNB : PTm 2 := (sg (var 0) * muN (succ (var 0)) (var 0)) * quo (var 1) (var 0)

theorem inst2_FPB (d x : PTm n) : inst2 FPB d x = (sg d * muP (succ d) d) * quo x d := by simp [inst2]

theorem inst2_FNB (d x : PTm n) : inst2 FNB d x = (sg d * muN (succ d) d) * quo x d := by simp [inst2]

theorem rowP (d x y : PTm n) : Γ ⊢[PRAAx] inst2 (RB aPB (bF epsB)) d (pairT x y) ≐ inst2 FPB d x := by
  have h := RB_at (Γ := Γ) aPB (bF epsB) d x y
  rw [inst2_aP] at h
  rw [inst2_FPB]
  exact h.eqTrans (congrMul (.eqRefl _) (eps_bs _ _))

theorem rowN (d x y : PTm n) : Γ ⊢[PRAAx] inst2 (RB aNB (bF epsB)) d (pairT x y) ≐ inst2 FNB d x := by
  have h := RB_at (Γ := Γ) aNB (bF epsB) d x y
  rw [inst2_aN] at h
  rw [inst2_FNB]
  exact h.eqTrans (congrMul (.eqRefl _) (eps_bs _ _))

theorem sumP (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB aPB (bF epsB))) (succ x) (pairT x y) ≐ ap2 (sumF FPB) (succ x) x :=
  sum_congr_bounded _ _ _ _ _ (.allI (.impI (by rw [shift_pairT]; exact rowP _ _ _)))

theorem sumN (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB aNB (bF epsB))) (succ x) (pairT x y) ≐ ap2 (sumF FNB) (succ x) x :=
  sum_congr_bounded _ _ _ _ _ (.allI (.impI (by rw [shift_pairT]; exact rowN _ _ _)))

/-! ## The sum of the unit -/

/-- `∑_{n ≤ x} [n ≥ 1] ε(n) = [x ≥ 1]`. -/
theorem sum_eps (x y : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (gS epsB)) (succ x) y ≐ sg x := by
  refine .orE (zero_or_succ x) ?_ ?_
  · have x0 : ((x ≐ zero) :: Γ) ⊢[PRAAx] x ≐ zero := Prf.hyp0
    have low : ((x ≐ zero) :: Γ) ⊢[PRAAx] ap2 (sumF (gS epsB)) (succ zero) y ≐ zero := by
      have s0 := sum_succ' (Γ := (x ≐ zero) :: Γ) (gS epsB) zero y
      rw [inst2_gS] at s0
      exact s0.eqTrans ((congrAdd (sum_zero _ _) (zero_mul_l sg_zero _)).eqTrans (zero_add zero))
    exact (congrAp2 _ (congrSucc x0) (.eqRefl _)).eqTrans (low.eqTrans ((congrSg x0).eqTrans sg_zero).eqSymm)
  · have xp : ((x ≐ succ (pred x)) :: Γ) ⊢[PRAAx] x ≐ succ (pred x) := Prf.hyp0
    exact (sum_sg_eps y (one_le_pos xp)).eqTrans (sg_pos xp).eqSymm

/-! ## The identity -/

/-- `∑_{d ≤ x} μ⁺(d) ⌊x/d⌋ = [x ≥ 1] + ∑_{d ≤ x} μ⁻(d) ⌊x/d⌋`. -/
theorem mobius_floor (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF FPB) (succ x) x ≐ sg x + ap2 (sumF FNB) (succ x) x :=
  (sumP x zero).eqSymm.eqTrans ((mobius_summatory epsB x zero).eqTrans
    (congrAdd (sum_eps x zero) (sumN x zero)))

/-! ## The floor recurrence of the Mertens function -/

theorem B_one (m y : PTm n) : Γ ⊢[PRAAx] Bs (one : PTm 2) m y ≐ m := by
  refine (sum_congr_bounded (bS (one : PTm 2)) (one : PTm 2) y y m (.allI (.impI ?_))).eqTrans (sum_ones m y)
  rw [inst2_bS, inst2_oneB, inst2_oneB]
  exact .eqRefl _

theorem rowP1 (d x y : PTm n) : Γ ⊢[PRAAx] inst2 (RB aPB one) d (pairT x y) ≐ inst2 FPB d x := by
  have h := RB_at (Γ := Γ) aPB (one : PTm 2) d x y
  rw [inst2_aP] at h
  rw [inst2_FPB]
  exact h.eqTrans (congrMul (.eqRefl _) (B_one _ _))

theorem rowN1 (d x y : PTm n) : Γ ⊢[PRAAx] inst2 (RB aNB one) d (pairT x y) ≐ inst2 FNB d x := by
  have h := RB_at (Γ := Γ) aNB (one : PTm 2) d x y
  rw [inst2_aN] at h
  rw [inst2_FNB]
  exact h.eqTrans (congrMul (.eqRefl _) (B_one _ _))

theorem sumP1 (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB aPB one)) (succ x) (pairT x y) ≐ ap2 (sumF FPB) (succ x) x :=
  sum_congr_bounded _ _ _ _ _ (.allI (.impI (by rw [shift_pairT]; exact rowP1 _ _ _)))

theorem sumN1 (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB aNB one)) (succ x) (pairT x y) ≐ ap2 (sumF FNB) (succ x) x :=
  sum_congr_bounded _ _ _ _ _ (.allI (.impI (by rw [shift_pairT]; exact rowN1 _ _ _)))

/-- `M⁺(m) = ∑_{k ≤ m} μ⁺(k)` and `M⁻(m) = ∑_{k ≤ m} μ⁻(k)`: the two parts of the Mertens function. -/
abbrev MP (m : PTm n) : PTm n := Bs aPB m zero
abbrev MN (m : PTm n) : PTm n := Bs aNB m zero

/-- `[a ≥ 1] M⁺(⌊x/a⌋)`, over `0 = a`, `1 = x`. -/
abbrev GPB : PTm 2 := sg (var 0) * ap2 (sumF (bS aPB)) (quo (var 1) (var 0)) zero

/-- `[a ≥ 1] M⁻(⌊x/a⌋)`. -/
abbrev GNB : PTm 2 := sg (var 0) * ap2 (sumF (bS aNB)) (quo (var 1) (var 0)) zero

theorem inst2_GPB (a x : PTm n) : inst2 GPB a x = sg a * MP (quo x a) := by simp [inst2]

theorem inst2_GNB (a x : PTm n) : inst2 GNB a x = sg a * MN (quo x a) := by simp [inst2]

alias mul_one1 := Common.mul_one_right

theorem colP (a x : PTm n) : Γ ⊢[PRAAx] inst2 (RB (one : PTm 2) aPB) a (pairT x zero) ≐ inst2 GPB a x := by
  have h := RB_at (Γ := Γ) (one : PTm 2) aPB a x zero
  rw [inst2_oneB] at h
  rw [inst2_GPB]
  exact h.eqTrans (congrMul (mul_one1 _) (.eqRefl _))

theorem colN (a x : PTm n) : Γ ⊢[PRAAx] inst2 (RB (one : PTm 2) aNB) a (pairT x zero) ≐ inst2 GNB a x := by
  have h := RB_at (Γ := Γ) (one : PTm 2) aNB a x zero
  rw [inst2_oneB] at h
  rw [inst2_GNB]
  exact h.eqTrans (congrMul (mul_one1 _) (.eqRefl _))

theorem csumP (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB (one : PTm 2) aPB)) (succ x) (pairT x zero) ≐ ap2 (sumF GPB) (succ x) x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  have sz : Syn.shift (pairT x (zero : PTm n)) = pairT (Syn.shift x) zero := by simp [Syn.shift]
  rw [sz]
  exact colP _ _

theorem csumN (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB (one : PTm 2) aNB)) (succ x) (pairT x zero) ≐ ap2 (sumF GNB) (succ x) x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  have sz : Syn.shift (pairT x (zero : PTm n)) = pairT (Syn.shift x) zero := by simp [Syn.shift]
  rw [sz]
  exact colN _ _

/-- `thm:floor-recurrence`: `∑_{a ≤ x} M⁺(⌊x/a⌋) = [x ≥ 1] + ∑_{a ≤ x} M⁻(⌊x/a⌋)`. -/
theorem mertens_floor (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF GPB) (succ x) x ≐ sg x + ap2 (sumF GNB) (succ x) x :=
  (csumP x).eqSymm.eqTrans ((hyp_swap (one : PTm 2) aPB x zero).eqTrans ((sumP1 x zero).eqTrans
    ((mobius_floor x).eqTrans (congrAdd (.eqRefl _)
      ((sumN1 x zero).eqSymm.eqTrans ((hyp_swap aNB (one : PTm 2) x zero).eqTrans (csumN x)))))))

end LeanProofs.IPRA.AnalyticNumberTheory.MobiusFloor
