import IPRADerivations.AnalyticNumberTheory.MobiusFloor

/-!
# Weighted floor sums of the Mertens function and the summatory totient

Packet: `analytic-number-theory/mertens-ipra`, `identities.tex`: Lemma `lem:weightedsum` and the first identity of
Theorem `thm:totient-chebyshev`.

The Mertens function is the pair `M = M⁺ − M⁻` of `MobiusFloor.MP`, `MobiusFloor.MN`; every identity is stated
with the negative part moved to the other side.

* `weighted_floor` (`lem:weightedsum`): for every weight `w` and every body `b`,
  `∑_{a ≤ x} w(a) B(⌊x/a⌋) = ∑_{m ≤ x} (w * b)(m)` with `B(m) = ∑_{k ≤ m} b(k)`; at `b = μ^±` the inner function is
  `M^±` and the right side is `∑_{m ≤ x} ∑_{d ∣ m} μ^±(d) w(m/d)`;
* `floor_term`, `floor_summatory`: at `b = 𝟏` the inner function is `B(m) = m`, so
  `∑_{n ≤ x} (w * 𝟏)(n) = ∑_{d ≤ x} w(d) ⌊x/d⌋` for every weight `w`; with `w(d) = d^r` this is the first identity
  of `el:summatory` in `number_theory_ipra_2026-11-22` (`∑_{n ≤ N} σ_r(n) = ∑_{d ≤ N} d^r ⌊N/d⌋`, with
  `σ_r = (d ↦ d^r) * 𝟏`);
* `phiB`, `conv_phi`: `(φ * 𝟏)(k) = k` for `k ≥ 1`, from `SumPhi.sum_phi_at`;
* `B_phi`: `∑_{k ≤ m} (φ * 𝟏)(k) = ∑_{k ≤ m} k`, so the summatory function of `φ * 𝟏` is that of the identity
  weight `idB`;
* `totient_floor`: `∑_{a ≤ x} a M⁺(⌊x/a⌋) = ∑_{m ≤ x} φ(m) + ∑_{a ≤ x} a M⁻(⌊x/a⌋)`, that is
  `∑_{a=1}^{N} a M(⌊N/a⌋) = ∑_{m=1}^{N} φ(m)`. It is the summed inversion `MobiusSummatory.mobius_summatory` at
  `g = φ`, read through the exchange `HyperbolaSwap.hyp_swap`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.MertensTotient

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (dpB inst2_dp sum_phi_at)
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv cv_at)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (RB RB_at Bs bS inst2_bS conv_summatory)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusSummatory (bF gS inst2_gS mobius_summatory)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusFloor (MP MN inst2_oneB B_one)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Weighted floor sums -/

/-- `lem:weightedsum`: `∑_{a ≤ x} w(a) B(⌊x/a⌋) = ∑_{m ≤ x} (w * b)(m)`, `B(m) = ∑_{1 ≤ k ≤ m} b(k)`. -/
theorem weighted_floor (w b : PTm 2) (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB w b)) (succ x) (pairT x y) ≐ ap2 (sumF (cvF w b)) (succ x) y :=
  (conv_summatory w b x y).eqSymm

/-- The term of the floor sum: `[d ≥ 1] w(d) ⌊x/d⌋`. -/
theorem floor_term (w : PTm 2) (d x y : PTm n) :
    Γ ⊢[PRAAx] inst2 (RB w one) d (pairT x y) ≐ (sg d * inst2 w d y) * quo x d :=
  (RB_at w one d x y).eqTrans (congrMul (.eqRefl _) (B_one _ _))

/-- `∑_{n ≤ x} (w * 𝟏)(n) = ∑_{d ≤ x} [d ≥ 1] w(d) ⌊x/d⌋`, the right side with the terms `floor_term`. -/
theorem floor_summatory (w : PTm 2) (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (cvF w one)) (succ x) y ≐ ap2 (sumF (RB w one)) (succ x) (pairT x y) :=
  conv_summatory w one x y

/-! ## The totient as a body -/

/-- `φ(d)`, over `0 = d`. -/
abbrev phiB : PTm 2 := ap2 (sumF totBody) (var 0) (var 0)

theorem inst2_phi (d y : PTm n) : inst2 phiB d y = phi d := by simp [inst2, subst_ap2]

theorem phi_zero : Γ ⊢[PRAAx] phi (zero : PTm n) ≐ zero := sum_zero _ _

theorem sg_phi (d : PTm n) : Γ ⊢[PRAAx] sg d * phi d ≐ phi d := by
  refine .orE (zero_or_succ d) ?_ ?_
  · have h0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] d ≐ zero := Prf.hyp0
    have pz : ((d ≐ zero) :: Γ) ⊢[PRAAx] phi d ≐ zero := (congrAp2 _ h0 h0).eqTrans phi_zero
    exact ((congrMul (.eqRefl _) pz).eqTrans (mul_zero _)).eqTrans pz.eqSymm
  · have hp : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    exact (congrMul (sg_pos hp) (.eqRefl _)).eqTrans (one_mul _)

theorem sg_self (a : PTm n) : Γ ⊢[PRAAx] sg a * a ≐ a := by
  refine .orE (zero_or_succ a) ?_ ?_
  · have h0 : ((a ≐ zero) :: Γ) ⊢[PRAAx] a ≐ zero := Prf.hyp0
    exact ((congrMul (.eqRefl _) h0).eqTrans (mul_zero _)).eqTrans h0.eqSymm
  · have hp : ((a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] a ≐ succ (pred a) := Prf.hyp0
    exact (congrMul (sg_pos hp) (.eqRefl _)).eqTrans (one_mul _)

theorem term_alg {S E P : PTm n} (h : Γ ⊢[PRAAx] S * P ≐ P) : Γ ⊢[PRAAx] (S * E) * (P * one) ≐ E * P := by
  ipra_lc 𝔞 E * natEq h

/-- `(φ * 𝟏)(k) = k` for `k ≥ 1`. -/
theorem conv_phi {k : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (y : PTm n) :
    Γ ⊢[PRAAx] conv phiB one k y ≐ k := by
  refine (sum_congr_bounded (cvB phiB one) dpB (pairT k y) k (succ k) (.allI (.impI ?_))).eqTrans (sum_phi_at hk)
  rw [shift_pairT, inst2_dp]
  refine (cv_at phiB one _ _ _).eqTrans ?_
  rw [inst2_phi, inst2_oneB]
  exact term_alg (sg_phi _)

/-- The identity weight `w(a) = a`. -/
abbrev idB : PTm 2 := var 0

theorem inst2_id (a y : PTm n) : inst2 idB a y = a := by simp [inst2]

/-- `∑_{k < m} (φ * 𝟏)(k + 1) = ∑_{k < m} (k + 1)`. -/
theorem B_phi (m y : PTm n) : Γ ⊢[PRAAx] Bs (bF phiB) m y ≐ Bs idB m y := by
  refine sum_congr_bounded (bS (bF phiB)) (bS idB) y y m (.allI (.impI ?_))
  rw [inst2_bS, inst2_bS, inst2_cvF, inst2_id]
  exact conv_phi (congrSucc (pred_succ _).eqSymm) _

/-! ## The rows -/

theorem rowPhi (a : PTm 2) (d x y : PTm n) :
    Γ ⊢[PRAAx] inst2 (RB a (bF phiB)) d (pairT x y) ≐ inst2 (RB a idB) d (pairT x y) :=
  (RB_at a (bF phiB) d x y).eqTrans ((congrMul (.eqRefl _) (B_phi _ _)).eqTrans (RB_at a idB d x y).eqSymm)

theorem sumPhiRow (a : PTm 2) (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB a (bF phiB))) (succ x) (pairT x y) ≐ ap2 (sumF (RB a idB)) (succ x) (pairT x y) :=
  sum_congr_bounded _ _ _ _ _ (.allI (.impI (by rw [shift_pairT]; exact rowPhi _ _ _ _)))

/-- `a M⁺(⌊x/a⌋)`, over `0 = a`, `1 = x`. -/
abbrev TPB : PTm 2 := var 0 * ap2 (sumF (bS aPB)) (quo (var 1) (var 0)) zero

/-- `a M⁻(⌊x/a⌋)`. -/
abbrev TNB : PTm 2 := var 0 * ap2 (sumF (bS aNB)) (quo (var 1) (var 0)) zero

theorem inst2_TPB (a x : PTm n) : inst2 TPB a x = a * MP (quo x a) := by simp [inst2]

theorem inst2_TNB (a x : PTm n) : inst2 TNB a x = a * MN (quo x a) := by simp [inst2]

theorem colT (b : PTm 2) (a x : PTm n) :
    Γ ⊢[PRAAx] inst2 (RB idB b) a (pairT x zero) ≐ a * Bs b (quo x a) zero := by
  have h := RB_at (Γ := Γ) idB b a x zero
  rw [inst2_id] at h
  exact h.eqTrans (congrMul (sg_self _) (.eqRefl _))

theorem csumTP (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB idB aPB)) (succ x) (pairT x zero) ≐ ap2 (sumF TPB) (succ x) x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  have sz : Syn.shift (pairT x (zero : PTm n)) = pairT (Syn.shift x) zero := by simp [Syn.shift]
  rw [sz, inst2_TPB]
  exact colT aPB _ _

theorem csumTN (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB idB aNB)) (succ x) (pairT x zero) ≐ ap2 (sumF TNB) (succ x) x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  have sz : Syn.shift (pairT x (zero : PTm n)) = pairT (Syn.shift x) zero := by simp [Syn.shift]
  rw [sz, inst2_TNB]
  exact colT aNB _ _

/-- `∑_{m ≤ x} [m ≥ 1] φ(m) = ∑_{m ≤ x} φ(m)`. -/
theorem sumG (x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (gS phiB)) (succ x) zero ≐ ap2 (sumF phiB) (succ x) x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_gS, inst2_phi, inst2_phi]
  exact sg_phi _

/-! ## The summatory totient -/

/-- `thm:totient-chebyshev`, first identity:
`∑_{a ≤ x} a M⁺(⌊x/a⌋) = ∑_{m ≤ x} φ(m) + ∑_{a ≤ x} a M⁻(⌊x/a⌋)`. -/
theorem totient_floor (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF TPB) (succ x) x ≐ ap2 (sumF phiB) (succ x) x + ap2 (sumF TNB) (succ x) x :=
  (csumTP x).eqSymm.eqTrans ((hyp_swap idB aPB x zero).eqTrans ((sumPhiRow aPB x zero).eqSymm.eqTrans
    ((mobius_summatory phiB x zero).eqTrans (congrAdd (sumG x)
      ((sumPhiRow aNB x zero).eqTrans ((hyp_swap aNB idB x zero).eqTrans (csumTN x)))))))

end LeanProofs.IPRA.AnalyticNumberTheory.MertensTotient

export_ipra AnalyticNumberTheory.MertensTotient (floor_summatory floor_term)
