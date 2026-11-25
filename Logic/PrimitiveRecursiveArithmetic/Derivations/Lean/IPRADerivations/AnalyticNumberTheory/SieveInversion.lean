import IPRADerivations.AnalyticNumberTheory.SymmetryInstances
import IPRADerivations.AnalyticNumberTheory.DivisorSwapP
import IPRADerivations.Probability.Independence
import IPRADerivations.Core.LinearCombination

/-!
# Möbius inversion over multiples (the sieve inversion)

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, `eq:sieve-inversion`:
"Finite Möbius inversion recovers the weights from `y`: `λ_d = d Σ_{r ∈ D, d ∣ r} μ(r/d) y_r`. To check the formula,
substitute it into the defining sum for `y_s`. The coefficient of `y_r` becomes `Σ_{s ∣ d ∣ r} μ(r/d)`, which equals
one when `r = s` and zero otherwise."

With `u_d = λ_d / d` and the signed pair `μ = μ⁺ − μ⁻`, the check is, for every natural body `y(r, p)` and
`1 ≤ s ≤ Z`,

  `Σ_{d ≤ Z, s ∣ d} Σ_{r ≤ Z, d ∣ r} μ⁺(r/d) y_r = y_s + Σ_{d ≤ Z, s ∣ d} Σ_{r ≤ Z, d ∣ r} μ⁻(r/d) y_r`  (`dual_inversion`).

* `ind_conv`: `(δ_s * 𝟏)(k) = [s ∣ k]` for `k, s ≥ 1` (`Core/Fubini.sum_delta`);
* `coef`: the coefficient of `y_r`, `Σ_{d ∣ r} [s ∣ d] μ⁺(r/d) = [r = s] + Σ_{d ∣ r} [s ∣ d] μ⁻(r/d)` for `r, s ≥ 1`:
  the divisor sum is the convolution `[s ∣ ·] * μ^±`, commuted (`DivisorSwapP.conv_comm`) to `μ^± * (δ_s * 𝟏)`, and
  `MobiusSummatory.pt_n` inverts it;
* `cut`: for `1 ≤ r ≤ Z` the range `d ≤ Z` of the coefficient may be cut at `d ≤ r`;
* `colK`, `col_eq`: the column `r` of the double sum is `[r ≥ 1] y_r` times the coefficient;
* `dual_inversion`: the double sum, exchanged by `Core/Fubini.fubini`; the term `[r = s]` selects `y_s`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveInversion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg zero_mul_l congrEqb' one_inst)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion (eqb_rem_big)
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv cv_at)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (cvF inst2_cvF sg_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwapP (conv_comm)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusSummatory (gS inst2_gS pt_n)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetrySum (aPB aNB)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances (dvdB inst2_dvdB)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eqb_comm')
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' pos_of_eq_mul)
open LeanProofs.IPRA.Probability.Independence (col_pt sum_scale dsum)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## `[s ∣ k]` as a convolution -/

/-- `δ_s(e) = [e = s]` over `0 = e`, `1 = s`. -/
abbrev dlt : PTm 2 := eqb (var 0) (var 1)

theorem inst2_dlt (e s : PTm n) : inst2 dlt e s = eqb e s := by simp [inst2]

/-- `[s ∣ d]` over `0 = d`, `1 = s`. -/
abbrev hS : PTm 2 := eqb (rem (var 0) (var 1)) zero

theorem inst2_hS (d s : PTm n) : inst2 hS d s = eqb (rem d s) zero := by simp [inst2]

theorem dl_alg {S R R' E F : PTm n} (h1 : Γ ⊢[PRAAx] F ≐ E) (h2 : Γ ⊢[PRAAx] R' ≐ R) :
    Γ ⊢[PRAAx] (S * R) * (E * one) ≐ F * (S * R') := by
  ipra_lc -𝔞 S * 𝔞 R * natEq h1 - 𝔞 F * 𝔞 S * natEq h2

/-- The summand of `(δ_s * 𝟏)(k)` at `e` is the summand `[s = e] [e ≥ 1][e ∣ k]` of a delta sum. -/
theorem dl_pt (e k s : PTm n) :
    Γ ⊢[PRAAx] inst2 (cvB dlt one) e (pairT k s) ≐ inst2 (dB dvdB) e (pairT s k) := by
  refine (cv_at dlt one e k s).eqTrans ?_
  rw [inst2_dlt, one_inst, inst2_dB, inst2_dvdB]
  exact dl_alg ((congrEqb' (fst_pair _ _) (.eqRefl _)).eqTrans (eqb_comm' _ _))
    (congrEqb' (congrAp2 remF (snd_pair _ _) (.eqRefl _)) (.eqRefl _))

/-- A delta summand vanishes when the selected index `s` is above the range. -/
theorem dB_zero {e k s : PTm n} (he : Γ ⊢[PRAAx] lt e (succ k)) (hks : Γ ⊢[PRAAx] lt k s) :
    Γ ⊢[PRAAx] inst2 (dB dvdB) e (pairT s k) ≐ zero := by
  rw [inst2_dB]
  have hne : Γ ⊢[PRAAx] neg (s ≐ e) := by
    refine .impI ?_
    have h1 : ((s ≐ e) :: Γ) ⊢[PRAAx] le (succ k) e := le_congr (.eqRefl _) Prf.hyp0 (hks.wk (ψ := s ≐ e))
    exact lt_irrefl e _ (le_trans (he.wk (ψ := s ≐ e)) h1)
  exact zero_mul_l ((congrEqb' (fst_pair _ _) (.eqRefl _)).eqTrans (eqb_of_ne hne)) _

/-- `(δ_s * 𝟏)(k) = [s ∣ k]` for `k, s ≥ 1`. -/
theorem ind_conv {k s : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) :
    Γ ⊢[PRAAx] conv dlt one k s ≐ eqb (rem k s) zero := by
  have cg : Γ ⊢[PRAAx] conv dlt one k s ≐ ap2 (sumF (dB dvdB)) (succ k) (pairT s k) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact dl_pt _ _ _
  refine cg.eqTrans ?_
  refine .orE (lt_or_le s (succ k)) ?_ ?_
  · have sd := sum_delta (Γ := lt s (succ k) :: Γ) dvdB (N := succ k) (c := s) (x := k) Prf.hyp0
    rw [inst2_dvdB] at sd
    exact sd.eqTrans ((congrMul (sg_pos (hs.wk (ψ := lt s (succ k)))) (.eqRefl _)).eqTrans (one_mul _))
  · -- `k < s`: both sides vanish
    have hlt : (le (succ k) s :: Γ) ⊢[PRAAx] lt k s := Prf.hyp0
    refine Prf.eqTrans ?_ (eqb_rem_big (hk.wk (ψ := le (succ k) s)) hlt).eqSymm
    have hs' : Syn.shift (succ k) = succ (Syn.shift k) := by simp [Syn.shift]
    have hlt' : ((le (succ k) s :: Γ).map Fm.shift) ⊢[PRAAx] lt (Syn.shift k) (Syn.shift s) := by
      simpa [Fm.shift, Syn.shift] using hlt.shift
    refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [hs']
    exact dB_zero Prf.hyp0 hlt'.wk

/-! ## The coefficient of `y_r` -/

/-- In a convolution `a * [s ∣ ·]` at `r ≥ 1`, the indicator may be replaced by `δ_s * 𝟏`. -/
theorem cong_pt (a : PTm 2) {d r s : PTm n} (hr : Γ ⊢[PRAAx] r ≐ succ (pred r))
    (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) :
    Γ ⊢[PRAAx] inst2 (cvB a hS) d (pairT r s) ≐ inst2 (cvB a (cvF dlt one)) d (pairT r s) := by
  refine (cv_at a hS d r s).eqTrans (Prf.eqTrans ?_ (cv_at a (cvF dlt one) d r s).eqSymm)
  rw [inst2_hS, inst2_cvF]
  refine .orE (zero_or_succ d) ?_ ?_
  · have s0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    exact (zero_mul_l (zero_mul_l s0 _) _).eqTrans (zero_mul_l (zero_mul_l s0 _) _).eqSymm
  · refine .orE (eq_or_ne (rem r d) zero) ?_ ?_
    · let C : List (Fm PTm n) := (rem r d ≐ zero) :: (d ≐ succ (pred d)) :: Γ
      have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp1
      have eN := eq_of_dvd' hd (Prf.hyp0 : C ⊢[PRAAx] dvd d r)
      have hq := pos_of_eq_mul hr.wk.wk eN
      exact congrMul (.eqRefl _) (congrMul (.eqRefl _) (ind_conv hq hs.wk.wk).eqSymm)
    · have z : (neg (rem r d ≐ zero) :: (d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] sg d * eqb (rem r d) zero ≐ zero :=
        (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (by ipra_ring)
      exact (zero_mul_l z _).eqTrans (zero_mul_l z _).eqSymm

/-- `Σ_{d ∣ r} [s ∣ d] μ⁺(r/d) = [r = s] + Σ_{d ∣ r} [s ∣ d] μ⁻(r/d)` for `r, s ≥ 1`. -/
theorem coef {r s : PTm n} (hr : Γ ⊢[PRAAx] r ≐ succ (pred r)) (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) :
    Γ ⊢[PRAAx] conv hS aPB r s ≐ eqb r s + conv hS aNB r s := by
  have cP : Γ ⊢[PRAAx] conv aPB hS r s ≐ conv aPB (cvF dlt one) r s := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT]
    exact cong_pt aPB (shift_pos hr).wk (shift_pos hs).wk
  have cN : Γ ⊢[PRAAx] conv aNB hS r s ≐ conv aNB (cvF dlt one) r s := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT]
    exact cong_pt aNB (shift_pos hr).wk (shift_pos hs).wk
  have p : Γ ⊢[PRAAx] conv aPB (cvF dlt one) r s ≐ sg r * eqb r s + conv aNB (cvF dlt one) r s := by
    have p := pt_n (Γ := Γ) dlt r s
    rw [inst2_cvF, inst2_cvF, inst2_gS, inst2_dlt] at p
    exact p
  have p' : Γ ⊢[PRAAx] conv aPB (cvF dlt one) r s ≐ eqb r s + conv aNB (cvF dlt one) r s :=
    p.eqTrans (congrAdd ((congrMul (sg_pos hr) (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _))
  exact (conv_comm hS aPB hr).eqTrans (cP.eqTrans (p'.eqTrans
    (congrAdd (.eqRefl _) (cN.eqSymm.eqTrans (conv_comm hS aNB hr).eqSymm))))

/-- For `1 ≤ r ≤ Z` the divisors `d` of `r` lie below `r + 1`: the range `d ≤ Z` may be cut. -/
theorem cut (a : PTm 2) {r Z s : PTm n} (hr : Γ ⊢[PRAAx] r ≐ succ (pred r)) (hrZ : Γ ⊢[PRAAx] lt r (succ Z)) :
    Γ ⊢[PRAAx] ap2 (sumF (cvB hS a)) (succ Z) (pairT r s) ≐ conv hS a r s := by
  have hr' := shift_pos hr
  refine sum_ext (cvB hS a) (fun Δ d hsub hl => ?_) hrZ
  rw [shift_pairT]
  refine (cv_at hS a d _ _).eqTrans ?_
  exact zero_mul_l ((congrMul (.eqRefl _) (eqb_rem_big (hr'.weaken hsub) hl)).eqTrans (mul_zero _)) _

/-! ## The double sum -/

section Inversion

variable (y : PTm 2)

/-- `[d ≥ 1][d ∣ r][s ∣ d] a(r/d) · [r ≥ 1] y(r, p)` over `(d, r, ⟨s, p⟩)`. -/
def wB (a : PTm 2) : PTm 3 :=
  Syn.subst ![var 0, pairT (var 1) (fstT (var 2))] (cvB hS a) * (sg (var 1) * Syn.subst ![var 1, sndT (var 2)] y)

theorem inst3_wB (a : PTm 2) (d r x : PTm n) :
    inst3 (wB y a) d r x = inst2 (cvB hS a) d (pairT r (fstT x)) * (sg r * inst2 y r (sndT x)) := by
  have h1 : Syn.subst ![d, r, x] (Syn.subst ![var 0, pairT (var 1) (fstT (var 2))] (cvB hS a)) =
      inst2 (cvB hS a) d (pairT r (fstT x)) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  have h2 : Syn.subst ![d, r, x] (Syn.subst ![var 1, sndT (var 2)] y) = inst2 y r (sndT x) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst3, wB, PTm.subst_mul, h1, h2]
  simp

theorem wB_at (a : PTm 2) (d r s p : PTm n) :
    Γ ⊢[PRAAx] inst3 (wB y a) d r (pairT s p) ≐ inst2 (cvB hS a) d (pairT r s) * (sg r * inst2 y r p) := by
  rw [inst3_wB]
  exact congrMul (congrInst2 _ (.eqRefl _) (congrPairT (.eqRefl _) (fst_pair s p)))
    (congrMul (.eqRefl _) (congrInst2 y (.eqRefl _) (snd_pair s p)))

/-- The column `r`: `Σ_{d ≤ Z} w(d, r) = [r ≥ 1] y_r · Σ_{d ≤ Z} [d ∣ r][s ∣ d] a(r/d)`. -/
theorem colK (a : PTm 2) (r Z s p : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB (wB y a)) r (pairT (succ Z) (pairT s p)) ≐
      (sg r * inst2 y r p) * ap2 (sumF (cvB hS a)) (succ Z) (pairT r s) := by
  rw [inst2_pB]
  have e1 : Γ ⊢[PRAAx] ap2 (sumF (colB (wB y a))) (fstT (pairT (succ Z) (pairT s p)))
      (pairT r (sndT (pairT (succ Z) (pairT s p)))) ≐ ap2 (sumF (colB (wB y a))) (succ Z) (pairT r (pairT s p)) :=
    congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))
  refine e1.eqTrans (sum_scale (colB (wB y a)) (cvB hS a) (succ Z) (sg r * inst2 y r p) (pairT r s)
    (pairT r (pairT s p)) (.allI (.impI ?_)))
  have hK : Syn.shift (sg r * inst2 y r p) = sg (Syn.shift r) * inst2 y (Syn.shift r) (Syn.shift p) := by
    simp [Syn.shift]
  simp only [shift_pairT]
  rw [hK]
  exact (col_pt (wB y a) _ _ _).eqTrans ((wB_at y a _ _ _ _).eqTrans (mul_comm _ _))

/-- The column algebra over opaque terms. -/
theorem col_alg {P N K K' SP SN CP CN E F : PTm n} (kP : Γ ⊢[PRAAx] P ≐ K * SP) (kN : Γ ⊢[PRAAx] N ≐ K * SN)
    (cP : Γ ⊢[PRAAx] SP ≐ CP) (cN : Γ ⊢[PRAAx] SN ≐ CN) (cf : Γ ⊢[PRAAx] CP ≐ E + CN)
    (eF : Γ ⊢[PRAAx] F ≐ E) (eK : Γ ⊢[PRAAx] K' ≐ K) : Γ ⊢[PRAAx] P ≐ F * K' + N := by
  ipra_lc natEq kP - natEq kN + 𝔞 K * natEq cP - 𝔞 K * natEq cN + 𝔞 K * natEq cf - 𝔞 K' * natEq eF - 𝔞 E * natEq eK

/-- The column `r ≤ Z` of the `μ⁺` sum is `[r = s][r ≥ 1] y_r` plus the column of the `μ⁻` sum. -/
theorem col_eq {r Z s p : PTm n} (hrZ : Γ ⊢[PRAAx] lt r (succ Z)) (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) :
    Γ ⊢[PRAAx] inst2 (pB (wB y aPB)) r (pairT (succ Z) (pairT s p)) ≐
      inst2 (dB (gS y)) r (pairT s p) + inst2 (pB (wB y aNB)) r (pairT (succ Z) (pairT s p)) := by
  have kP := colK (Γ := Γ) y aPB r Z s p
  have kN := colK (Γ := Γ) y aNB r Z s p
  rw [inst2_dB, inst2_gS]
  have eD : Γ ⊢[PRAAx] eqb (fstT (pairT s p)) r ≐ eqb r s :=
    (congrEqb' (fst_pair _ _) (.eqRefl _)).eqTrans (eqb_comm' _ _)
  have eY : Γ ⊢[PRAAx] inst2 y r (sndT (pairT s p)) ≐ inst2 y r p := congrInst2 y (.eqRefl _) (snd_pair _ _)
  refine .orE (zero_or_succ r) ?_ ?_
  · have s0 : ((r ≐ zero) :: Γ) ⊢[PRAAx] sg r ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    have hP := (kP.wk (ψ := r ≐ zero)).eqTrans (zero_mul_l (zero_mul_l s0 _) _)
    have hN := (kN.wk (ψ := r ≐ zero)).eqTrans (zero_mul_l (zero_mul_l s0 _) _)
    have hD : ((r ≐ zero) :: Γ) ⊢[PRAAx]
        eqb (fstT (pairT s p)) r * (sg r * inst2 y r (sndT (pairT s p))) ≐ zero :=
      (congrMul (.eqRefl _) (zero_mul_l s0 _)).eqTrans (mul_zero _)
    exact hP.eqTrans ((congrAdd hD hN).eqTrans (add_zero zero)).eqSymm
  · have hr : ((r ≐ succ (pred r)) :: Γ) ⊢[PRAAx] r ≐ succ (pred r) := Prf.hyp0
    have hs' := hs.wk (ψ := r ≐ succ (pred r))
    exact col_alg (kP.wk (ψ := r ≐ succ (pred r))) (kN.wk (ψ := r ≐ succ (pred r)))
      (cut aPB hr (hrZ.wk (ψ := r ≐ succ (pred r)))) (cut aNB hr (hrZ.wk (ψ := r ≐ succ (pred r))))
      (coef hr hs') (eD.wk (ψ := r ≐ succ (pred r))) (congrMul (.eqRefl _) (eY.wk (ψ := r ≐ succ (pred r))))

/-- `eq:sieve-inversion`, the check: for `1 ≤ s ≤ Z`,
`Σ_{d ≤ Z, s ∣ d} Σ_{r ≤ Z, d ∣ r} μ⁺(r/d) y_r = y_s + Σ_{d ≤ Z, s ∣ d} Σ_{r ≤ Z, d ∣ r} μ⁻(r/d) y_r`. -/
theorem dual_inversion {Z s p : PTm n} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) (hsZ : Γ ⊢[PRAAx] lt s (succ Z)) :
    Γ ⊢[PRAAx] dsum (wB y aPB) (succ Z) (succ Z) (pairT s p) ≐
      inst2 y s p + dsum (wB y aNB) (succ Z) (succ Z) (pairT s p) := by
  have fP := fubini (Γ := Γ) (wB y aPB) (succ Z) (succ Z) (pairT s p)
  have fN := fubini (Γ := Γ) (wB y aNB) (succ Z) (succ Z) (pairT s p)
  have hs' := shift_pos hs
  have hsh : Syn.shift (succ Z) = succ (Syn.shift Z) := by simp [Syn.shift]
  have sm : Γ ⊢[PRAAx] ap2 (sumF (pB (wB y aPB))) (succ Z) (pairT (succ Z) (pairT s p)) ≐
      ap2 (sumF (dB (gS y))) (succ Z) (pairT s p) +
        ap2 (sumF (pB (wB y aNB))) (succ Z) (pairT (succ Z) (pairT s p)) := by
    refine sum_add2 (dB (gS y)) (pB (wB y aNB)) (pB (wB y aPB)) (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [hsh]
    exact col_eq y Prf.hyp0 hs'.wk
  have sd := sum_delta (Γ := Γ) (gS y) (N := succ Z) (c := s) (x := p) hsZ
  rw [inst2_gS] at sd
  have sd' : Γ ⊢[PRAAx] ap2 (sumF (dB (gS y))) (succ Z) (pairT s p) ≐ inst2 y s p :=
    sd.eqTrans ((congrMul (sg_pos hs) (.eqRefl _)).eqTrans (one_mul _))
  exact fP.eqTrans (sm.eqTrans (congrAdd sd' fN.eqSymm))

end Inversion

end LeanProofs.IPRA.AnalyticNumberTheory.SieveInversion
