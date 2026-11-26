import IPRADerivations.AnalyticNumberTheory.WeightedVariation
import IPRADerivations.Core.Header

/-!
# Selberg's weighted inequality (`pnt_ipra_constructive_2026-11-14`, `sb:weighted-sum`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, Lemma `sb:weighted-sum`:
"`|R(x)|(log x)² ≤ 2 Σ_{n≤x} log n |R(x/n)| + 2^{17} x log x`." From `sb:first-weighted-bound`
(`WeightedBound.first_weighted`) the coefficient `a(n) = Λ(n) log n + (Λ * Λ)(n)` is replaced by `2 log n` through the
finite Abel identity, the symmetry estimate `|Δ_n| = |A(n) − 2P₁(n)| ≤ 4096n` at every `n ≤ x`, and the variation
bound for `g_n = |R(x/n)|` (`WeightedVariation.variation`). Scaled by `F = L!` with `u = F λ_K`:

* `sg_drop`, `az_y`, `A1_eq`, `aw_split`: the partial sums of `a(n)` in closed form;
* `a2_lo`, `a2_hi`: `2F Σ_{k≤n} L_w(k) ≤ 2F Σ_{k≤n} u_k ≤ 2F Σ_{k≤n} L_w(k) + 2F²`;
* `dA_le`: `|Σ_{k≤n} a(k) − 2F Σ_{k≤n} u_k| ≤ 2206 F² n` for `n ≤ x` (`SymmetryBound`, `ChebyshevAbel.lam_bridge`);
* `parts_diff`: `Σ a(n) g_n ≤ Σ 2F u_n g_n + 2206 F² Σ n|g_n − g_{n+1}|` (`AbelParts.abel_parts`, `g_{x+1} = 0`);
* `weighted_sum`: `|ψ(x) − Fx| u_x² ≤ 2F Σ_{n≤x} u_n |ψ(⌊x/n⌋) − F⌊x/n⌋| + 19222 F² x u_x + 11070 F³ x`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanProofs.IPRA.AnalyticNumberTheory.WeightedAbel

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi LamB pos_of_lt_zero lt_zero_of_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lam Lw)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd absd_le le_absd_l le_absd_r absd_scale adB inst2_adB absd_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.AbelParts (agB upB dnB inst2_agB inst2_upB inst2_dnB inst2_g1 abel_parts)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedBound (psiB qB lamB0 first_weighted)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedSplit (lamW uw luB uw_at hRB_at inst2_add inst2_mul sz)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedVariation (gZ inst2_gZ gB nabsB inst2_nabs g_at quo_self_succ absdC
  variation)
open LeanProofs.IPRA.AnalyticNumberTheory.SummatoryCompose (hRB inst2_hRB)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevAbel (auB lwB lam_bridge pw_exp_le)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryBound (gL Aw Ls symmetry_upper symmetry_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetrySum (GxB inst2_GxB)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryPointwise (quo_mul_le le_Q4 Q4_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances (conv_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusSummatory (gS inst2_gS)
open LeanProofs.IPRA.AnalyticNumberTheory.ErrorEquation (inst2_gL)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightBridge (lw_le_u u_le_lw sum_le_add_const)
open LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum (Q4)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (cvF inst2_cvF)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic (shift_fact')
open LeanProofs.IPRA.Probability.Lotus (cmB sum_const_mul)
open LeanProofs.IPRA.Probability.Independence (cm_pt)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Coefficients and their partial sums -/

/-- `[k ≥ 1] a(k, y)` over `0 = k`, `1 = (x, y)`. -/
def aZ (a : PTm 2) : PTm 2 := sg (var 0) * Syn.subst ![var 0, sndT (var 1)] a

theorem inst2_aZ (a : PTm 2) (k z : PTm n) : inst2 (aZ a) k z = sg k * inst2 a k (sndT z) := by
  have h : Syn.subst ![k, z] (Syn.subst ![var 0, sndT (var 1)] a) = inst2 a k (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  simp only [inst2, aZ, PTm.subst_mul, h]; simp [sg]

theorem hRB_eq (h a : PTm 2) (N z : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (hRB h a)) N z ≐ ap2 (sumF (agB (aZ a) (gZ h))) N z := .eqRefl _

/-- `Σ_{k≤N} [k ≥ 1] a(k)` with the parameter `(x, y)`, as a sum over `y`. -/
theorem az_y (a : PTm 2) (N x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (aZ a)) (succ N) (pairT x y) ≐ ap2 (sumF (gS a)) (succ N) y := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_pairT, inst2_aZ, inst2_gS]
  exact congrMul (.eqRefl _) (congrInst2 a (.eqRefl _) (snd_pair _ _))

theorem sg_drop (b : PTm 2) (h0 : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (y : PTm m), Δ ⊢[PRAAx] inst2 b zero y ≐ zero)
    (N y : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (gS b)) N y ≐ ap2 (sumF b) N y := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_gS]
  refine .orE (zero_or_succ (var 0)) ?_ ?_
  · have z : ((var 0 ≐ zero) :: lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
        inst2 b (var 0) (Syn.shift y) ≐ zero := (congrInst2 b Prf.hyp0 (.eqRefl _)).eqTrans (h0 _)
    exact (zero_mul_l ((congrSg Prf.hyp0).eqTrans sg_zero) _).eqTrans z.eqSymm
  · exact (congrMul ((congrSg Prf.hyp0).eqTrans (sg_succ _)) (.eqRefl _)).eqTrans (one_mul _)

/-- `a₁ = Λ * Λ + Λ u`. -/
abbrev a1 : PTm 2 := cvF lamW lamW + luB
/-- `a₂ = 2F u`. -/
abbrev a2 : PTm 2 := two * (sndT (var 1) * uw)

theorem a1_zero {m : ℕ} {Δ : List (Fm PTm m)} (y : PTm m) : Δ ⊢[PRAAx] inst2 a1 zero y ≐ zero := by
  rw [inst2_add, inst2_cvF, inst2_mul]
  exact (congrAdd (conv_zero _ _ _) (zero_mul_l (lamB0 y) _)).eqTrans (add_zero _)

/-- `Σ_{k≤N} a₁(k) = Σ (Λ * Λ) + Σ Λ u`. -/
theorem A1_eq (N x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (aZ a1)) (succ N) (pairT x y) ≐
      ap2 (sumF (cvF lamW lamW)) (succ N) y + ap2 (sumF (auB (LamB wt))) (succ N) y := by
  refine (az_y a1 N x y).eqTrans ((sg_drop a1 a1_zero _ _).eqTrans ?_)
  have s := sum_add2 (Γ := Γ) (cvF lamW lamW) luB a1 (K := succ N) (x := y) (x' := y) (z := y)
    (.allI (.impI (by rw [inst2_add]; exact .eqRefl _)))
  exact s.eqTrans (congrAdd (.eqRefl _) (.eqRefl _))

/-- `A_w(N) = Σ Λ L_w + Σ (Λ * Λ)`. -/
theorem aw_split (N K L : PTm n) :
    Γ ⊢[PRAAx] Aw N K L ≐ ap2 (sumF lwB) (succ N) (pairT K (fact L)) +
      ap2 (sumF (cvF lamW lamW)) (succ N) (pairT K (fact L)) :=
  sum_add2 (Γ := Γ) lwB (cvF lamW lamW) (GxB wt) (K := succ N) (x := pairT K (fact L))
    (x' := pairT K (fact L)) (z := pairT K (fact L)) (.allI (.impI (by
      rw [inst2_GxB, ChebyshevAbel.inst2_lwB, inst2_cvF]
      ipra_ring)))

/-! ## `2F Σ u_k` against `2F Σ L_w(k)` -/

theorem inst2_a2 (k y : PTm n) : inst2 a2 k y = two * (sndT y * inst2 uw k y) := by simp [inst2]

theorem lw_conv {k K L : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (hK : Γ ⊢[PRAAx] le one K)
    (hkL : Γ ⊢[PRAAx] le (K * k) L) :
    Γ ⊢[PRAAx] le (Lw wt k (pairT K (fact L))) (U k K (fact L)) ⋏
      le (U k K (fact L)) (Lw wt k (pairT K (fact L)) + k * quo (fact L) K) := by
  have hL' := le_congr (congrMul (.eqRefl K) hk) (.eqRefl _) hkL
  have eL : Γ ⊢[PRAAx] Lw wt (succ (pred k)) (pairT K (fact L)) ≐ Lw wt k (pairT K (fact L)) :=
    congrAp2 _ (congrSucc hk.eqSymm) (congrPairT hk.eqSymm (.eqRefl _))
  have eU : Γ ⊢[PRAAx] U (succ (pred k)) K (fact L) ≐ U k K (fact L) :=
    congrMonus (congrAp2 _ (congrMul (.eqRefl _) hk.eqSymm) (.eqRefl _)) (.eqRefl _)
  refine .andI (le_congr eL eU (lw_le_u hK hL')) (le_congr eU (congrAdd eL (congrMul hk.eqSymm (.eqRefl _)))
    (u_le_lw hK hL'))

theorem a2_pt_lo {k K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hkL : Γ ⊢[PRAAx] le (K * k) L) :
    Γ ⊢[PRAAx] le (inst2 (cmB (gS gL)) k (pairT (two * fact L) (pairT K (fact L))))
      (inst2 (gS a2) k (pairT K (fact L))) := by
  refine le_congr (cm_pt _ _ _ _).eqSymm (.eqRefl _) ?_
  rw [inst2_gS, inst2_gS, inst2_gL, inst2_a2]
  refine .orE (zero_or_succ k) ?_ ?_
  · have z := (congrSg (Γ := (k ≐ zero) :: Γ) Prf.hyp0).eqTrans sg_zero
    exact le_congr ((congrMul (.eqRefl _) (zero_mul_l z _)).eqTrans (mul_zero _)).eqSymm (.eqRefl _) (zero_le _)
  · let D := (k ≐ succ (pred k)) :: Γ
    have hk : D ⊢[PRAAx] k ≐ succ (pred k) := Prf.hyp0
    have l1 := Prf.andE₁ (lw_conv hk hK.wk hkL.wk)
    have e1 := natEq (uw_at (Γ := D) k K (fact L))
    have e2 := natEq (snd_pair (Γ := D) K (fact L))
    have s := natEq ((congrSg hk).eqTrans (sg_succ (pred k)))
    have p := le_scale (two * fact L) l1
    ipra_le sl p with (2 * 𝔞 (sndT (pairT K (fact L))) * 𝔞 (inst2 uw k (pairT K (fact L))) -
      2 * 𝔞 (fact L) * 𝔞 (Lw wt k (pairT K (fact L)))) * s + 2 * 𝔞 (sndT (pairT K (fact L))) * e1 +
      2 * 𝔞 (U k K (fact L)) * e2

theorem a2_pt_hi {k N K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hkN : Γ ⊢[PRAAx] le k N)
    (hNL : Γ ⊢[PRAAx] le (K * N) L) :
    Γ ⊢[PRAAx] le (inst2 (gS a2) k (pairT K (fact L)))
      (inst2 (cmB (gS gL)) k (pairT (two * fact L) (pairT K (fact L))) + two * (fact L * (N * quo (fact L) K))) := by
  refine le_congr (.eqRefl _) (congrAdd (cm_pt _ _ _ _) (.eqRefl _)).eqSymm ?_
  rw [inst2_gS, inst2_gS, inst2_gL, inst2_a2]
  refine .orE (zero_or_succ k) ?_ ?_
  · have z := (congrSg (Γ := (k ≐ zero) :: Γ) Prf.hyp0).eqTrans sg_zero
    exact le_congr (zero_mul_l z _).eqSymm (.eqRefl _) (zero_le _)
  · let D := (k ≐ succ (pred k)) :: Γ
    have hk : D ⊢[PRAAx] k ≐ succ (pred k) := Prf.hyp0
    have ul := Prf.andE₂ (lw_conv hk hK.wk (le_trans (le_scale K hkN.wk) hNL.wk))
    have mq := mul_le_mul_right (quo (fact L) K) (hkN.wk (ψ := k ≐ succ (pred k)))
    have e1 := natEq (uw_at (Γ := D) k K (fact L))
    have e2 := natEq (snd_pair (Γ := D) K (fact L))
    have s := natEq ((congrSg hk).eqTrans (sg_succ (pred k)))
    have p1 := le_scale (two * fact L) ul
    have p2 := le_scale (two * fact L) mq
    ipra_le sl p1 + sl p2 with (2 * 𝔞 (fact L) * 𝔞 (Lw wt k (pairT K (fact L))) -
      2 * 𝔞 (sndT (pairT K (fact L))) * 𝔞 (inst2 uw k (pairT K (fact L)))) * s -
      2 * 𝔞 (sndT (pairT K (fact L))) * e1 - 2 * 𝔞 (U k K (fact L)) * e2

theorem shiftKL {K L N : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hNL : Γ ⊢[PRAAx] le (K * N) L) :
    (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) ⋏ le (Syn.shift K * Syn.shift N) (Syn.shift L) :=
  .andI (by simpa [Fm.shift, Syn.shift] using hK.shift) (by simpa [Fm.shift, Syn.shift] using hNL.shift)

/-- `2F Σ_{k≤N} L_w(k) ≤ Σ_{k≤N} 2F u_k`. -/
theorem a2_lo {N K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hNL : Γ ⊢[PRAAx] le (K * N) L) :
    Γ ⊢[PRAAx] le (two * (fact L * Ls N K L)) (ap2 (sumF (gS a2)) (succ N) (pairT K (fact L))) := by
  have sh := shiftKL hK hNL
  have p := sum_le_params (Γ := Γ) (cmB (gS gL)) (gS a2) (pairT (two * fact L) (pairT K (fact L)))
    (pairT K (fact L)) (succ N) (.allI (.impI (by
      simp only [ConvSummatory.shift_succ_x, shift_pairT, shift_fact']
      rw [show Syn.shift (two * fact L : PTm n) = two * fact (Syn.shift L) by simp [Syn.shift]]
      have hv : (lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
        (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
      exact a2_pt_lo (Prf.andE₁ sh).wk (le_trans (le_scale _ hv) (Prf.andE₂ sh).wk))))
  have c := natEq (sum_const_mul (Γ := Γ) (gS gL) (succ N) (two * fact L) (pairT K (fact L)))
  ipra_le sl p with c

/-- `Σ_{k≤N} 2F u_k ≤ 2F Σ_{k≤N} L_w(k) + (N+1) 2F N ⌊F/K⌋`. -/
theorem a2_hi {N K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hNL : Γ ⊢[PRAAx] le (K * N) L) :
    Γ ⊢[PRAAx] le (ap2 (sumF (gS a2)) (succ N) (pairT K (fact L)))
      (two * (fact L * Ls N K L) + succ N * (two * (fact L * (N * quo (fact L) K)))) := by
  have sh := shiftKL hK hNL
  have p := sum_le_add_const (Γ := Γ) (gS a2) (cmB (gS gL)) (x := pairT K (fact L))
    (y := pairT (two * fact L) (pairT K (fact L))) (c := two * (fact L * (N * quo (fact L) K))) (N := succ N)
    (.allI (.impI (by
      simp only [ConvSummatory.shift_succ_x, shift_pairT, shift_fact']
      rw [show Syn.shift (two * fact L : PTm n) = two * fact (Syn.shift L) by simp [Syn.shift],
        show Syn.shift (two * (fact L * (N * quo (fact L) K)) : PTm n) =
          two * (fact (Syn.shift L) * (Syn.shift N * quo (fact (Syn.shift L)) (Syn.shift K))) by simp [Syn.shift]]
      have hv : (lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
        (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
      exact a2_pt_hi (Prf.andE₁ sh).wk hv (Prf.andE₂ sh).wk)))
  have c := natEq (sum_const_mul (Γ := Γ) (gS gL) (succ N) (two * fact L) (pairT K (fact L)))
  ipra_le sl p with -c

/-! ## `|Σ a₁ − Σ a₂| ≤ 2206 F² n` -/

theorem AZ_zero (a : PTm 2) (z : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (aZ a)) (succ zero) z ≐ zero := by
  refine (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) (.eqRefl _)).eqTrans ((zero_add _).eqTrans ?_))
  rw [inst2_aZ]; exact zero_mul_l sg_zero _

/-- `|Σ_{k≤N} a₁(k) − Σ_{k≤N} 2F u_k| ≤ 2206 F² N` for `N ≤ x`. -/
theorem dA_le {N x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hx4 : Γ ⊢[PRAAx] le (Q4 x) K)
    (hL : Γ ⊢[PRAAx] le (K * Q4 x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
    (hNx : Γ ⊢[PRAAx] le N x) :
    Γ ⊢[PRAAx] le (absd (ap2 (sumF (aZ a1)) (succ N) (pairT x (pairT K (fact L))))
        (ap2 (sumF (aZ a2)) (succ N) (pairT x (pairT K (fact L)))))
      (num 2206 * (fact L * fact L * N)) := by
  refine .orE (zero_or_succ N) ?_ ?_
  · let D := (N ≐ zero) :: Γ
    have hN : D ⊢[PRAAx] N ≐ zero := Prf.hyp0
    have z1 := (congrAp2 (sumF (aZ a1)) (congrSucc hN) (.eqRefl (pairT x (pairT K (fact L))))).eqTrans
      (AZ_zero a1 _)
    have z2 := (congrAp2 (sumF (aZ a2)) (congrSucc hN) (.eqRefl (pairT x (pairT K (fact L))))).eqTrans
      (AZ_zero a2 _)
    refine le_congr (WeightedVariation.absdC z1 z2).eqSymm (.eqRefl _) ?_
    exact absd_le (by ipra_le 𝔞 (num 2206 * (fact L * fact L * N))) (by ipra_le 𝔞 (num 2206 * (fact L * fact L * N)))
  · let D := (N ≐ succ (pred N)) :: Γ
    have hn : D ⊢[PRAAx] le one N := lt_zero_of_pos Prf.hyp0
    have hNx' := hNx.wk (ψ := N ≐ succ (pred N))
    have hN4 := le_trans (Q4_mono hNx') hx4.wk
    have hLN := le_trans (le_scale K (Q4_mono hNx')) hL.wk
    have hPN := le_trans (le_scale K (pw_exp_le (le_scale two (le_scale two hNx')))) hP.wk
    have hKN := le_trans (le_scale K (le_Q4 N)) hLN
    have e1 := natEq (A1_eq (Γ := D) N x (pairT K (fact L)))
    have e2 := natEq (aw_split (Γ := D) N K L)
    have lb := lam_bridge hK.wk hN4 hPN hKN
    have b1 := Prf.andE₁ lb; have b2 := Prf.andE₂ lb
    have su := symmetry_upper hn hK.wk hN4 hLN
    have slo := symmetry_lower hn hK.wk hN4 hLN
    have e3 := natEq (az_y (Γ := D) a2 N x (pairT K (fact L)))
    have l2 := a2_lo hK.wk hKN
    have u2 := a2_hi hK.wk hKN
    have hsq : D ⊢[PRAAx] le (succ N * N) (Q4 N) := by
      ipra_le 𝔞 N * 𝔞 N * 𝔞 N * 𝔞 N + 4 * (𝔞 N * 𝔞 N * 𝔞 N) + 5 * (𝔞 N * 𝔞 N) + 3 * 𝔞 N + 1
    have c := mul_le_mul_right (quo (fact L) K) (le_trans hsq hN4)
    have r := quo_mul_le (Γ := D) (x := fact L) (pos_of_lt_zero hK.wk)
    have nq := le_scale (two * fact L) (le_trans c (le_congr (mul_comm _ _) (.eqRefl _) r))
    exact absd_le
      (by ipra_le sl b2 + sl su + sl l2 + 6 * (𝔞 (fact L) * 𝔞 (fact L)) * sl hn + 2 * (𝔞 (fact L) * 𝔞 (fact L)) with
            e3 - e1 + e2)
      (by ipra_le sl u2 + sl nq + sl slo + sl b1 + 6 * (𝔞 (fact L) * 𝔞 (fact L)) * sl hn +
            4 * (𝔞 (fact L) * 𝔞 (fact L)) with e1 - e3 - e2)

/-! ## Summation by parts -/

/-- `n (g_n ∸ g_{n+1})`. -/
abbrev ndB : PTm 2 := var 0 * monus gB (Syn.subst ![succ (var 0), var 1] gB)
/-- `n (g_{n+1} ∸ g_n)`. -/
abbrev nuB : PTm 2 := var 0 * monus (Syn.subst ![succ (var 0), var 1] gB) gB

theorem inst2_nd (k z : PTm n) : inst2 ndB k z = k * monus (inst2 gB k z) (inst2 gB (succ k) z) := by
  simp only [ndB, inst2, PTm.subst_mul, PTm.subst_monus, Syn.subst_var]
  rw [inst2_g1]; simp [inst2]

theorem inst2_nu (k z : PTm n) : inst2 nuB k z = k * monus (inst2 gB (succ k) z) (inst2 gB k z) := by
  simp only [nuB, inst2, PTm.subst_mul, PTm.subst_monus, Syn.subst_var]
  rw [inst2_g1]; simp [inst2]

theorem g_end {x K L : PTm n} : Γ ⊢[PRAAx] inst2 gB (succ x) (pairT x (pairT K (fact L))) ≐ zero := by
  refine (g_at (succ x)).eqTrans ?_
  have q := quo_self_succ (Γ := Γ) x
  have p0 := WeightedBound.psi_zero (Δ := Γ) (pairT K (fact L))
  rw [WeightedBound.inst2_psiB] at p0
  have p : Γ ⊢[PRAAx] WeightedVariation.Pv (succ x) x K L ≐ zero :=
    (congrAp2 _ (congrSucc q) (.eqRefl _)).eqTrans p0
  have r : Γ ⊢[PRAAx] WeightedVariation.Qv (succ x) x L ≐ zero := (congrMul (.eqRefl _) q).eqTrans (mul_zero _)
  have zz : Γ ⊢[PRAAx] absd (zero : PTm n) zero ≐ zero :=
    (congrAdd (zero_monus _) (zero_monus _)).eqTrans (add_zero _)
  exact (absdC p r).eqTrans zz

section Parts
variable {x K L : PTm n} (hx : Γ ⊢[PRAAx] le one x) (hK : Γ ⊢[PRAAx] le one K) (hx4 : Γ ⊢[PRAAx] le (Q4 x) K)
  (hL : Γ ⊢[PRAAx] le (K * Q4 x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
include hK hx4 hL hP

theorem shifted :
    (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) ⋏ (le (Q4 (Syn.shift x)) (Syn.shift K) ⋏
      (le (Syn.shift K * Q4 (Syn.shift x)) (Syn.shift L) ⋏
        le (Syn.shift K * pw two (two * (two * Syn.shift x))) (Syn.shift L))) := by
  have b : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have c : (Γ.map Fm.shift) ⊢[PRAAx] le (Q4 (Syn.shift x)) (Syn.shift K) := by
    simpa [Fm.shift, Syn.shift] using hx4.shift
  have d : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * Q4 (Syn.shift x)) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hL.shift
  have e : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * pw two (two * (two * Syn.shift x))) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hP.shift
  exact .andI b (.andI c (.andI d e))

theorem d_pt (D1 D2 : PTm 2) (wB : PTm 2)
    (h1 : ∀ (k z : PTm (n + 1)), inst2 D1 k z = ap2 (sumF (aZ a1)) (succ k) z * inst2 wB k z)
    (h2 : ∀ (k z : PTm (n + 1)), inst2 D2 k z = ap2 (sumF (aZ a2)) (succ k) z * inst2 wB k z) :
    Γ ⊢[PRAAx] le (ap2 (sumF (adB D1 D2)) (succ x) (pairT x (pairT K (fact L))))
      (ap2 (sumF (cmB (var 0 * wB))) (succ x) (pairT (num 2206 * (fact L * fact L)) (pairT x (pairT K (fact L))))) := by
  have sh := shifted hK hx4 hL hP
  refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
  simp only [ConvSummatory.shift_succ_x, shift_pairT, shift_fact']
  rw [show Syn.shift (num 2206 * (fact L * fact L) : PTm n) = num 2206 * (fact (Syn.shift L) * fact (Syn.shift L)) by
    simp [Syn.shift], inst2_adB, h1, h2]
  refine le_congr (.eqRefl _) (cm_pt _ _ _ _).eqSymm ?_
  rw [inst2_mul, show inst2 (var 0 : PTm 2) (var 0) (pairT (Syn.shift x) (pairT (Syn.shift K) (fact (Syn.shift L)))) =
    (var 0 : PTm (n + 1)) by simp [inst2]]
  have hv : (lt (var 0) (succ (Syn.shift x)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift x) :=
    (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have dA := dA_le (Prf.andE₁ sh).wk (Prf.andE₁ (Prf.andE₂ sh)).wk (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ sh))).wk
    (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ sh))).wk hv
  have sc := absd_scale (Γ := (lt (var 0) (succ (Syn.shift x)) :: Γ.map Fm.shift))
    (inst2 wB (var 0) (pairT (Syn.shift x) (pairT (Syn.shift K) (fact (Syn.shift L)))))
    (ap2 (sumF (aZ a1)) (succ (var 0)) (pairT (Syn.shift x) (pairT (Syn.shift K) (fact (Syn.shift L)))))
    (ap2 (sumF (aZ a2)) (succ (var 0)) (pairT (Syn.shift x) (pairT (Syn.shift K) (fact (Syn.shift L)))))
  have sc' := le_congr (absdC (mul_comm _ _) (mul_comm _ _)).eqSymm (.eqRefl _) sc
  have p := le_scale (inst2 wB (var 0) (pairT (Syn.shift x) (pairT (Syn.shift K) (fact (Syn.shift L))))) dA
  ipra_le sl sc' + sl p

theorem split :
    Γ ⊢[PRAAx] ap2 (sumF nabsB) (succ x) (pairT x (pairT K (fact L))) ≐
      ap2 (sumF ndB) (succ x) (pairT x (pairT K (fact L))) + ap2 (sumF nuB) (succ x) (pairT x (pairT K (fact L))) :=
  sum_add2 (Γ := Γ) ndB nuB nabsB (K := succ x) (x := pairT x (pairT K (fact L))) (x' := pairT x (pairT K (fact L)))
    (z := pairT x (pairT K (fact L))) (.allI (.impI (by
      rw [inst2_nabs, inst2_nd, inst2_nu]
      ipra_ring)))

include hx in
/-- `Σ a₁(n) g_n ≤ Σ 2F u_n g_n + 2206 F² · 5x(u_x + F)`. -/
theorem parts_diff :
    Γ ⊢[PRAAx] le (sz (hRB (adB psiB qB) a1) x K L)
      (sz (hRB (adB psiB qB) a2) x K L + num 2206 * (fact L * fact L) * (num 5 * x * (U x K (fact L) + fact L))) := by
  have e1 := natEq (hRB_eq (Γ := Γ) (adB psiB qB) a1 (succ x) (pairT x (pairT K (fact L))))
  have e2 := natEq (hRB_eq (Γ := Γ) (adB psiB qB) a2 (succ x) (pairT x (pairT K (fact L))))
  have ab1 := natEq (abel_parts (Γ := Γ) (aZ a1) gB x (pairT x (pairT K (fact L))))
  have ab2 := natEq (abel_parts (Γ := Γ) (aZ a2) gB x (pairT x (pairT K (fact L))))
  have ge := natEq (g_end (Γ := Γ) (x := x) (K := K) (L := L))
  have a := le_absd_l (Γ := Γ) (ap2 (sumF (dnB (aZ a1) gB)) (succ x) (pairT x (pairT K (fact L))))
    (ap2 (sumF (dnB (aZ a2) gB)) (succ x) (pairT x (pairT K (fact L))))
  have b := le_absd_r (Γ := Γ) (ap2 (sumF (upB (aZ a1) gB)) (succ x) (pairT x (pairT K (fact L))))
    (ap2 (sumF (upB (aZ a2) gB)) (succ x) (pairT x (pairT K (fact L))))
  have dd := le_trans (absd_sum _ _ _ _) (d_pt hK hx4 hL hP (dnB (aZ a1) gB) (dnB (aZ a2) gB)
    (monus gB (Syn.subst ![succ (var 0), var 1] gB)) (fun k z => by rw [inst2_dnB]; simp only [inst2, PTm.subst_monus]; rw [inst2_g1]; rfl)
    (fun k z => by rw [inst2_dnB]; simp only [inst2, PTm.subst_monus]; rw [inst2_g1]; rfl))
  have du := le_trans (absd_sum _ _ _ _) (d_pt hK hx4 hL hP (upB (aZ a1) gB) (upB (aZ a2) gB)
    (monus (Syn.subst ![succ (var 0), var 1] gB) gB) (fun k z => by rw [inst2_upB]; simp only [inst2, PTm.subst_monus]; rw [inst2_g1]; rfl)
    (fun k z => by rw [inst2_upB]; simp only [inst2, PTm.subst_monus]; rw [inst2_g1]; rfl))
  have cd := natEq (sum_const_mul (Γ := Γ) ndB (succ x) (num 2206 * (fact L * fact L)) (pairT x (pairT K (fact L))))
  have cu := natEq (sum_const_mul (Γ := Γ) nuB (succ x) (num 2206 * (fact L * fact L)) (pairT x (pairT K (fact L))))
  have sp := natEq (split hK hx4 hL hP)
  have vv := le_scale (num 2206 * (fact L * fact L)) (variation hx hK hx4 hL hP)
  ipra_le sl a + sl b + sl dd + sl du + sl vv with e2 + ab2 +
    𝔞 (ap2 (sumF (aZ a2)) (succ x) (pairT x (pairT K (fact L)))) * ge - e1 - ab1 -
    𝔞 (ap2 (sumF (aZ a1)) (succ x) (pairT x (pairT K (fact L)))) * ge - cd - cu +
    2206 * 𝔞 (fact L) * 𝔞 (fact L) * sp

include hx in
/-- `sb:weighted-sum`, scaled:
`|ψ(x) − Fx| u_x² ≤ 2F Σ_{n≤x} u_n |ψ(⌊x/n⌋) − F⌊x/n⌋| + 19222 F² x u_x + 11070 F³ x`. -/
theorem weighted_sum :
    Γ ⊢[PRAAx] le (absd (inst2 psiB x (pairT K (fact L)) * U x K (fact L) * U x K (fact L))
        (inst2 qB x (pairT K (fact L)) * U x K (fact L) * U x K (fact L)))
      (sz (hRB (adB psiB qB) a2) x K L + num 19222 * (fact L * fact L * (x * U x K (fact L))) +
        num 11070 * (fact L * fact L * fact L * x)) := by
  have fw := first_weighted hx hK hx4 hL hP
  have sp1 := natEq (sum_add2 (Γ := Γ) (hRB (adB psiB qB) (cvF lamW lamW)) (hRB (adB psiB qB) luB)
    (hRB (adB psiB qB) a1) (K := succ x) (x := pairT x (pairT K (fact L))) (x' := pairT x (pairT K (fact L)))
    (z := pairT x (pairT K (fact L))) (.allI (.impI (by
      rw [inst2_hRB, inst2_hRB, inst2_hRB, inst2_add]
      ipra_ring))))
  have pd := parts_diff hx hK hx4 hL hP
  ipra_le sl fw + sl pd with sp1

end Parts

end LeanProofs.IPRA.AnalyticNumberTheory.WeightedAbel
