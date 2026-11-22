import IPRADerivations.AnalyticNumberTheory.WeightedReorder
import IPRADerivations.AnalyticNumberTheory.FactorialError

/-!
# The weighted identity for one monotone function (`pnt_ipra_constructive_2026-11-14`, `sb:weighted-sum`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:weighted-sum`:
"Multiply the defining equation for `E_R(x)` by `log x`, split `log x = log n + log(x/n)` in its sum, and use the
same equation at `x/n`." The identity is linear in `R`, so it is proved for each monotone `f` with `f(0) = 0`
separately (`f = ψ` and `f = F · id` in the application). With the harmonic logarithm `u`,
`E_f(m) = f(m) u_m + Σ_{j≤m} Λ(j) f(⌊m/j⌋)` and

* `T_B = Σ_{d≤x} Λ(d) u_d f(⌊x/d⌋)`, `T_C = Σ_{d≤x} Λ(d) E_f(⌊x/d⌋)`, `T_D = Σ_{n≤x} (Λ * Λ)(n) f(⌊x/n⌋)`:

  `f(x) u_x² + T_B + T_C ≤ E_f(x) u_x + T_D ≤ f(x) u_x² + T_B + T_C + Σ_{d≤x} Λ(d) f(⌊x/d⌋)(Δ_{⌊x/d⌋} + ⌊F/K⌋)`

  (`fid_lo`, `fid_hi`), `Δ_m = F(H_{K(m+1)} − H_{Km})`. The exact part is `WeightedReorder.reorder`; the inexact part is
  the split of the logarithm, `0 ≤ u_x − u_d − u_{⌊x/d⌋} ≤ Δ_{⌊x/d⌋} + ⌊F/K⌋` (`usplit_lo`, `usplit_hi`, from
  `HarmonicChebyshev.superadd` and `HarmonicMertens.subadd`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.WeightedSplit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono wt superadd)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale subadd)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (pos_of_lt_zero lt_zero_of_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.SelbergLeibniz (lamF)
open LeanProofs.IPRA.AnalyticNumberTheory.SummatoryCompose (Mono hRB inst2_hRB)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedReorder (S1B inst2_S1 reorder)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryBound (quo_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (cvF)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic (shift_fact')
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg)
open LeanProofs.IPRA.Probability.Lotus (cmB sum_const_mul)
open LeanProofs.IPRA.Probability.Independence (cm_pt)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Signum (sg sg_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Splitting the logarithm -/

theorem kle {K a : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) : Γ ⊢[PRAAx] le K (K * a) := by
  have w := natEq ha
  exact le_of_eq_add (d := K * pred a) (by apply deriveNat; ipra_simps; linear_combination 𝔞 K * w)

theorem eSU {K a : PTm n} (F : PTm n) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) :
    Γ ⊢[PRAAx] S (K * a) F ≐ S K F + U a K F :=
  eq_add_of_le (S_mono F (kle ha))

/-- `u_d + u_{⌊x/d⌋} ≤ u_x` for `1 ≤ d ≤ x`, `Kx ≤ L`. -/
theorem usplit_lo {d x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (hdx : Γ ⊢[PRAAx] le d x) (hKx : Γ ⊢[PRAAx] le (K * x) L) :
    Γ ⊢[PRAAx] le (U d K (fact L) + U (quo x d) K (fact L)) (U x K (fact L)) := by
  have hm := quo_pos hd hdx
  have hx := pos_of_lt_zero (le_trans (lt_zero_of_pos hd) hdx)
  have dm := div_mod_at (Γ := Γ) (x := x) hd
  have hdm : Γ ⊢[PRAAx] le (d * quo x d) x := le_of_eq_add (d := rem x d) (Prf.andE₁ dm)
  have sa := superadd (pos_of_lt_zero hK) hd hm (le_trans (le_scale K hdm) hKx)
  have mo := S_mono (fact L) (le_scale K hdm)
  have e1 := natEq (eSU (K := K) (fact L) hd); have e2 := natEq (eSU (K := K) (fact L) hm)
  have e3 := natEq (eSU (K := K) (fact L) hx)
  ipra_le sl sa + sl mo with e1 + e2 - e3

/-- `u_x ≤ u_d + u_{⌊x/d⌋} + Δ_{⌊x/d⌋} + ⌊F/K⌋` for `1 ≤ d ≤ x`, `K · 2x ≤ L`. -/
theorem usplit_hi {d x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (hdx : Γ ⊢[PRAAx] le d x) (hL : Γ ⊢[PRAAx] le (K * (two * x)) L) :
    Γ ⊢[PRAAx] le (U x K (fact L))
      (U d K (fact L) + U (quo x d) K (fact L) +
        (monus (S (K * succ (quo x d)) (fact L)) (S (K * quo x d) (fact L)) + quo (fact L) K)) := by
  have hm := quo_pos hd hdx
  have hx := pos_of_lt_zero (le_trans (lt_zero_of_pos hd) hdx)
  have dm := div_mod_at (Γ := Γ) (x := x) hd
  have e0 := natEq (Prf.andE₁ dm)
  have hr := Prf.andE₂ dm
  have hxd : Γ ⊢[PRAAx] le x (d * succ (quo x d)) := by ipra_le sl hr + 1 with e0
  have hdm : Γ ⊢[PRAAx] le (d * quo x d) x := le_of_eq_add (d := rem x d) (Prf.andE₁ dm)
  have h2 : Γ ⊢[PRAAx] le (d * succ (quo x d)) (two * x) := by ipra_le sl hdm + sl hdx
  have hsm : Γ ⊢[PRAAx] succ (quo x d) ≐ succ (pred (succ (quo x d))) := congrSucc (pred_succ _).eqSymm
  have sb := subadd (pos_of_lt_zero hK) hd hsm (le_trans (le_scale K h2) hL)
  have mo := S_mono (fact L) (le_scale K hxd)
  have eD := natEq (eq_add_of_le (S_mono (fact L) (le_scale K (le_succ_self (Γ := Γ) (quo x d)))))
  have e1 := natEq (eSU (K := K) (fact L) hd); have e2 := natEq (eSU (K := K) (fact L) hm)
  have e3 := natEq (eSU (K := K) (fact L) hx)
  ipra_le sl mo + sl sb with -e1 - eD - e2 + e3

/-! ## Bodies -/

/-- `Λ_w(d)`. -/
abbrev lamW : PTm 2 := lamF wt
/-- `u_k` with parameter `(K, F)`. -/
abbrev uw : PTm 2 := monus (S (fstT (var 1) * var 0) (sndT (var 1))) (S (fstT (var 1)) (sndT (var 1)))
/-- `Λ_w(d) u_d`. -/
abbrev luB : PTm 2 := lamW * uw
/-- `f(m) u_m`. -/
abbrev fuB (f : PTm 2) : PTm 2 := f * uw
/-- `E_f(m) = f(m) u_m + Σ_{j≤m} Λ(j) f(⌊m/j⌋)`. -/
abbrev EfB (f : PTm 2) : PTm 2 := f * uw + S1B f lamW
/-- `Δ_m + ⌊F/K⌋`. -/
abbrev dqB : PTm 2 := monus (S (fstT (var 1) * succ (var 0)) (sndT (var 1))) (S (fstT (var 1) * var 0) (sndT (var 1))) +
  quo (sndT (var 1)) (fstT (var 1))

theorem uw_at (k K F : PTm n) : Γ ⊢[PRAAx] inst2 uw k (pairT K F) ≐ U k K F := by
  rw [show inst2 uw k (pairT K F) = monus (S (fstT (pairT K F) * k) (sndT (pairT K F)))
    (S (fstT (pairT K F)) (sndT (pairT K F))) by simp [inst2]]
  exact congrMonus (congrAp2 (sumF hB) (congrMul (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))
    (congrAp2 (sumF hB) (fst_pair _ _) (snd_pair _ _))

theorem dq_at (k K F : PTm n) : Γ ⊢[PRAAx] inst2 dqB k (pairT K F) ≐
    monus (S (K * succ k) F) (S (K * k) F) + quo F K := by
  rw [show inst2 dqB k (pairT K F) = monus (S (fstT (pairT K F) * succ k) (sndT (pairT K F)))
    (S (fstT (pairT K F) * k) (sndT (pairT K F))) + quo (sndT (pairT K F)) (fstT (pairT K F)) by simp [inst2]]
  exact congrAdd (congrMonus (congrAp2 (sumF hB) (congrMul (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))
    (congrAp2 (sumF hB) (congrMul (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)))
    (congrAp2 quoF (snd_pair _ _) (fst_pair _ _))

theorem hRB_at (h a : PTm 2) (d X y : PTm n) :
    Γ ⊢[PRAAx] inst2 (hRB h a) d (pairT X y) ≐ (sg d * inst2 a d y) * inst2 h (quo X d) y := by
  rw [inst2_hRB]
  exact congrMul (congrMul (.eqRefl _) (congrInst2 a (.eqRefl _) (snd_pair _ _)))
    (congrInst2 h (congrAp2 quoF (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))

theorem inst2_mul (f g : PTm 2) (k y : PTm n) : inst2 (f * g) k y = inst2 f k y * inst2 g k y := by simp [inst2]
theorem inst2_add (f g : PTm 2) (k y : PTm n) : inst2 (f + g) k y = inst2 f k y + inst2 g k y := by simp [inst2]

/-! ## The pointwise split -/

theorem pure_lo {s l fm ud um ux : PTm n} (h : Γ ⊢[PRAAx] le (ud + um) ux) :
    Γ ⊢[PRAAx] le ((s * (l * ud)) * fm + (s * l) * (fm * um)) (ux * ((s * l) * fm)) := by
  have p := le_scale ((s * l) * fm) h
  ipra_le sl p

theorem pure_hi {s l fm ud um ux dq : PTm n} (h : Γ ⊢[PRAAx] le ux (ud + um + dq)) :
    Γ ⊢[PRAAx] le (ux * ((s * l) * fm)) ((s * (l * ud)) * fm + (s * l) * (fm * um) + (s * l) * (fm * dq)) := by
  have p := le_scale ((s * l) * fm) h
  ipra_le sl p

theorem pure_zero {s l fm ud um ux : PTm n} (hs : Γ ⊢[PRAAx] s ≐ zero) :
    Γ ⊢[PRAAx] le ((s * (l * ud)) * fm + (s * l) * (fm * um)) (ux * ((s * l) * fm)) := by
  have z := natEq hs
  ipra_le 0 with (𝔞 ux * 𝔞 l * 𝔞 fm - 𝔞 l * 𝔞 ud * 𝔞 fm - 𝔞 l * 𝔞 fm * 𝔞 um) * z

theorem pure_zero' {s l fm ud um ux dq : PTm n} (hs : Γ ⊢[PRAAx] s ≐ zero) :
    Γ ⊢[PRAAx] le (ux * ((s * l) * fm)) ((s * (l * ud)) * fm + (s * l) * (fm * um) + (s * l) * (fm * dq)) := by
  have z := natEq hs
  ipra_le 0 with (𝔞 l * 𝔞 ud * 𝔞 fm + 𝔞 l * 𝔞 fm * 𝔞 um + 𝔞 l * 𝔞 fm * 𝔞 dq - 𝔞 ux * 𝔞 l * 𝔞 fm) * z

section Point
variable (f : PTm 2) {d x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hdx : Γ ⊢[PRAAx] le d x)
include hK hdx

theorem eL (y : PTm n) (hy : y = pairT K (fact L)) :
    Γ ⊢[PRAAx] inst2 (hRB f luB + hRB (fuB f) lamW) d (pairT x y) ≐
      (sg d * (inst2 lamW d y * U d K (fact L))) * inst2 f (quo x d) y +
        (sg d * inst2 lamW d y) * (inst2 f (quo x d) y * U (quo x d) K (fact L)) := by
  subst hy
  rw [inst2_add]
  have a := hRB_at (Γ := Γ) f luB d x (pairT K (fact L))
  have b := hRB_at (Γ := Γ) (fuB f) lamW d x (pairT K (fact L))
  rw [inst2_mul] at a b
  exact congrAdd (a.eqTrans (congrMul (congrMul (.eqRefl _) (congrMul (.eqRefl _) (uw_at _ _ _))) (.eqRefl _)))
    (b.eqTrans (congrMul (.eqRefl _) (congrMul (.eqRefl _) (uw_at _ _ _))))

/-- Pointwise lower split. -/
theorem lo_pt (hKx : Γ ⊢[PRAAx] le (K * x) L) :
    Γ ⊢[PRAAx] le (inst2 (hRB f luB + hRB (fuB f) lamW) d (pairT x (pairT K (fact L))))
      (inst2 (cmB (hRB f lamW)) d (pairT (U x K (fact L)) (pairT x (pairT K (fact L))))) := by
  refine le_congr (eL f hK hdx _ rfl).eqSymm ((cm_pt _ _ _ _).eqTrans
    (congrMul (.eqRefl _) (hRB_at f lamW d x _))).eqSymm ?_
  refine .orE (zero_or_succ d) ?_ ?_
  · exact pure_zero ((congrSg Prf.hyp0).eqTrans sg_zero)
  · exact pure_lo (usplit_lo hK.wk Prf.hyp0 hdx.wk hKx.wk)

/-- `Λ(d) f(⌊x/d⌋)(Δ + ⌊F/K⌋)`. -/
abbrev errB : PTm 2 := hRB (f * dqB) lamW

/-- Pointwise upper split. -/
theorem hi_pt (hL : Γ ⊢[PRAAx] le (K * (two * x)) L) :
    Γ ⊢[PRAAx] le (inst2 (cmB (hRB f lamW)) d (pairT (U x K (fact L)) (pairT x (pairT K (fact L)))))
      (inst2 (hRB f luB + hRB (fuB f) lamW + errB f) d (pairT x (pairT K (fact L)))) := by
  have ee : Γ ⊢[PRAAx] inst2 (errB f) d (pairT x (pairT K (fact L))) ≐
      (sg d * inst2 lamW d (pairT K (fact L))) * (inst2 f (quo x d) (pairT K (fact L)) *
        (monus (S (K * succ (quo x d)) (fact L)) (S (K * quo x d) (fact L)) + quo (fact L) K)) := by
    have a := hRB_at (Γ := Γ) (f * dqB) lamW d x (pairT K (fact L))
    rw [inst2_mul] at a
    exact a.eqTrans (congrMul (.eqRefl _) (congrMul (.eqRefl _) (dq_at _ _ _)))
  rw [inst2_add]
  refine le_congr ((cm_pt _ _ _ _).eqTrans (congrMul (.eqRefl _) (hRB_at f lamW d x _))).eqSymm
    (congrAdd (eL f hK hdx _ rfl) ee).eqSymm ?_
  refine .orE (zero_or_succ d) ?_ ?_
  · exact pure_zero' ((congrSg Prf.hyp0).eqTrans sg_zero)
  · exact pure_hi (usplit_hi hK.wk Prf.hyp0 hdx.wk hL.wk)

end Point

/-! ## The summed split and the identity -/

section Sum
variable (f : PTm 2) (hm : Mono f) (h0 : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (y : PTm m), Δ ⊢[PRAAx] inst2 f zero y ≐ zero)
  {x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K * (two * x)) L)

/-- `Σ_{d≤x} g(d)` with `Z = (x, (K, L!))`. -/
abbrev sz (g : PTm 2) (x K L : PTm n) : PTm n := ap2 (sumF g) (succ x) (pairT x (pairT K (fact L)))

include hL in
theorem hKx2 : Γ ⊢[PRAAx] le (K * x) L := by
  have h : Γ ⊢[PRAAx] le (K * x) (K * (two * x)) := le_scale K (by ipra_le 𝔞 x)
  exact le_trans h hL

theorem shiftK {K : PTm n} (h : Γ ⊢[PRAAx] le one K) : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by
  simpa [Fm.shift, Syn.shift] using h.shift

include hK hL in
/-- `T_B + T_{C,1} ≤ u_x Σ_{d≤x} Λ(d) f(⌊x/d⌋)`. -/
theorem lo_sum :
    Γ ⊢[PRAAx] le (sz (hRB f luB) x K L + sz (hRB (fuB f) lamW) x K L) (U x K (fact L) * sz (hRB f lamW) x K L) := by
  have hKx := hKx2 hL
  have hKx' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * Syn.shift x) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hKx.shift
  have e1 := natEq (sum_add2 (Γ := Γ) (hRB f luB) (hRB (fuB f) lamW) (hRB f luB + hRB (fuB f) lamW)
    (K := succ x) (x := pairT x (pairT K (fact L))) (x' := pairT x (pairT K (fact L)))
    (z := pairT x (pairT K (fact L))) (.allI (.impI (by rw [inst2_add]; exact .eqRefl _))))
  have p := sum_le_params (Γ := Γ) (hRB f luB + hRB (fuB f) lamW) (cmB (hRB f lamW)) (pairT x (pairT K (fact L)))
    (pairT (U x K (fact L)) (pairT x (pairT K (fact L)))) (succ x) (.allI (.impI (by
      simp only [ConvSummatory.shift_succ_x, shift_pairT, shift_fact']
      rw [show Syn.shift (U x K (fact L)) = U (Syn.shift x) (Syn.shift K) (fact (Syn.shift L)) by simp [Syn.shift]]
      have hv : (lt (var 0) (succ (Syn.shift x)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift x) :=
        (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
      exact lo_pt (d := var 0) (x := Syn.shift x) (K := Syn.shift K) (L := Syn.shift L) f (shiftK hK).wk hv hKx'.wk)))
  have c := natEq (sum_const_mul (Γ := Γ) (hRB f lamW) (succ x) (U x K (fact L)) (pairT x (pairT K (fact L))))
  ipra_le sl p with e1 - c

include hK hL in
/-- `u_x Σ_{d≤x} Λ(d) f(⌊x/d⌋) ≤ T_B + T_{C,1} + Σ_{d≤x} Λ(d) f(⌊x/d⌋)(Δ + ⌊F/K⌋)`. -/
theorem hi_sum :
    Γ ⊢[PRAAx] le (U x K (fact L) * sz (hRB f lamW) x K L)
      (sz (hRB f luB) x K L + sz (hRB (fuB f) lamW) x K L + sz (errB f) x K L) := by
  have hL' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * (two * Syn.shift x)) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hL.shift
  have e1 := natEq (sum_add2 (Γ := Γ) (hRB f luB + hRB (fuB f) lamW) (errB f) (hRB f luB + hRB (fuB f) lamW + errB f)
    (K := succ x) (x := pairT x (pairT K (fact L))) (x' := pairT x (pairT K (fact L)))
    (z := pairT x (pairT K (fact L))) (.allI (.impI (by rw [inst2_add]; exact .eqRefl _))))
  have e2 := natEq (sum_add2 (Γ := Γ) (hRB f luB) (hRB (fuB f) lamW) (hRB f luB + hRB (fuB f) lamW)
    (K := succ x) (x := pairT x (pairT K (fact L))) (x' := pairT x (pairT K (fact L)))
    (z := pairT x (pairT K (fact L))) (.allI (.impI (by rw [inst2_add]; exact .eqRefl _))))
  have p := sum_le_params (Γ := Γ) (cmB (hRB f lamW)) (hRB f luB + hRB (fuB f) lamW + errB f)
    (pairT (U x K (fact L)) (pairT x (pairT K (fact L)))) (pairT x (pairT K (fact L))) (succ x) (.allI (.impI (by
      simp only [ConvSummatory.shift_succ_x, shift_pairT, shift_fact']
      rw [show Syn.shift (U x K (fact L)) = U (Syn.shift x) (Syn.shift K) (fact (Syn.shift L)) by simp [Syn.shift]]
      have hv : (lt (var 0) (succ (Syn.shift x)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift x) :=
        (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
      exact hi_pt (d := var 0) (x := Syn.shift x) (K := Syn.shift K) (L := Syn.shift L) f (shiftK hK).wk hv hL'.wk)))
  have c := natEq (sum_const_mul (Γ := Γ) (hRB f lamW) (succ x) (U x K (fact L)) (pairT x (pairT K (fact L))))
  ipra_le sl p with -c + e1 + e2

omit hm h0 in
theorem inst2_EfB (k y : PTm n) :
    inst2 (EfB f) k y = inst2 f k y * inst2 uw k y + inst2 (S1B f lamW) k y := by simp [inst2]

include hm h0 in
/-- `T_C = T_{C,1} + T_D`. -/
theorem tc_split (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (hRB (EfB f) lamW)) (succ x) (pairT x y) ≐
      ap2 (sumF (hRB (fuB f) lamW)) (succ x) (pairT x y) + ap2 (sumF (hRB f (cvF lamW lamW))) (succ x) (pairT x y) := by
  have s := sum_add2 (Γ := Γ) (hRB (fuB f) lamW) (hRB (S1B f lamW) lamW) (hRB (EfB f) lamW) (K := succ x)
    (x := pairT x y) (x' := pairT x y) (z := pairT x y) (.allI (.impI (by
      rw [inst2_hRB, inst2_hRB, inst2_hRB, inst2_EfB, inst2_mul]
      apply deriveNat; ipra_simps; ring)))
  exact s.eqTrans (congrAdd (.eqRefl _) (reorder f lamW hm h0 lamW x y))

include hm h0 hK hL

/-- `f(x) u_x² + T_B + T_C ≤ E_f(x) u_x + T_D`. -/
theorem fid_lo :
    Γ ⊢[PRAAx] le (inst2 f x (pairT K (fact L)) * U x K (fact L) * U x K (fact L) + sz (hRB f luB) x K L +
        sz (hRB (EfB f) lamW) x K L)
      ((inst2 f x (pairT K (fact L)) * U x K (fact L) + sz (hRB f lamW) x K L) * U x K (fact L) +
        sz (hRB f (cvF lamW lamW)) x K L) := by
  have lo := lo_sum f hK hL
  have tc := natEq (tc_split (Γ := Γ) f hm h0 x (pairT K (fact L)))
  ipra_le sl lo with tc

/-- `E_f(x) u_x + T_D ≤ f(x) u_x² + T_B + T_C + Σ_{d≤x} Λ(d) f(⌊x/d⌋)(Δ + ⌊F/K⌋)`. -/
theorem fid_hi :
    Γ ⊢[PRAAx] le ((inst2 f x (pairT K (fact L)) * U x K (fact L) + sz (hRB f lamW) x K L) * U x K (fact L) +
        sz (hRB f (cvF lamW lamW)) x K L)
      (inst2 f x (pairT K (fact L)) * U x K (fact L) * U x K (fact L) + sz (hRB f luB) x K L +
        sz (hRB (EfB f) lamW) x K L + sz (errB f) x K L) := by
  have hi := hi_sum f hK hL
  have tc := natEq (tc_split (Γ := Γ) f hm h0 x (pairT K (fact L)))
  ipra_le sl hi with tc

end Sum

end LeanProofs.IPRA.AnalyticNumberTheory.WeightedSplit
