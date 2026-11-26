import IPRADerivations.AnalyticNumberTheory.RateAbel
import IPRADerivations.Geometry.HypercubeSplit
import IPRADerivations.AnalyticNumberTheory.SummatoryPhi
import IPRADerivations.AnalyticNumberTheory.TotientCorollaries
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Shell arithmetic for the weighted series (`riemann_ipra_equivalences_2026-11-20`, `thm:rate`, (1) ⇒ (2))

Packet: `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`, `series.tex`, proof of Theorem `thm:rate`:
"For (1) to (3), use the supplied witness `c` at index `2r`, giving `|M(i)|^{4r} ≤ c i^{2r+1}`. For any `i < B^{j+1}`
this implies `|M(i)| ≤ (c+1)2^{r(j+1)+⌈(j+1)/2⌉}`. Raise to `4r` to verify the inequality in integers."

* `lg_one`, `lg_step` (`⌊log₂(N+1)⌋ ≤ ⌊log₂ N⌋ + 1`), `jj_step` (`j(N+1) ≤ j(N) + 1`);
* `shell_bound`: `N < B^{j(N)+1} = 2^{2r(j(N)+1)}`;
* `m_bound`: from `|M(N)|^{4r} ≤ c N^{2r+1}`, `2^{⌊j/2⌋}|M(N)| ≤ (c+1) 2^{(r+1) + (r+1)j}` with `j = j(N)` — the packet's
  estimate with its half-integer exponent cleared by the factor `2^{⌊j/2⌋}`: after raising to `4r`, the exponents
  compare as `4r⌊j/2⌋ + 2r(2r+1)(j+1) ≤ 4r(r+1)(j+1)`, i.e. `2⌊j/2⌋ ≤ j + 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.RateShell

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RateAbel
open LeanProofs.IPRA.AnalyticNumberTheory.StepParams (ell clog_bracket)
open LeanProofs.IPRA.Geometry.HypercubeSplit (exp_le_of_pw_le)
open LeanProofs.IPRA.AnalyticNumberTheory.SummatoryPhi (quo_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.TotientCorollaries (eqb_le_one)
open LeanProofs.IPRA.DiophantineNumberTheory.Dirichlet (quo_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp pw_le_cancel)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockChain (one_le_pw')
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd absd_le le_absd_l le_absd_r)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerTransfer (k4)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The floor logarithm along `N` -/

theorem lg_one : Γ ⊢[PRAAx] lg (one : PTm n) ≐ zero := by
  have b := Prf.andE₁ (lg_bracket (Γ := Γ) (x := (one : PTm n)) (le_refl _))
  refine .orE (lt_or_le zero (lg (one : PTm n))) ?_ ?_
  · let C : List (Fm PTm n) := lt zero (lg one) :: Γ
    have p := pw_le_exp (Γ := C) two_pos (Prf.hyp0 : C ⊢[PRAAx] le one (lg one))
    have e := natEq (pw_one (Γ := C) two)
    have c : C ⊢[PRAAx] lt (one : PTm n) one := by ipra_le sl p + sl b.wk with e
    exact lt_irrefl one _ c
  · exact (monus_zero _).eqSymm.eqTrans Prf.hyp0

theorem lg_step {N : PTm n} (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le (lg (succ N)) (succ (lg N)) := by
  have b1 := Prf.andE₂ (lg_bracket hN)
  have b2 := Prf.andE₁ (lg_bracket (Γ := Γ) (x := succ N) (by ipra_le sl hN + 1))
  exact exp_le_of_pw_le (le_trans b2 b1)

theorem jj_step {r N : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le (jj r (succ N)) (succ (jj r N)) := by
  have q := quo_mono (two_r_pos hr) (lg_step hN)
  have f := natEq (LeanProofs.IPRA.AnalyticNumberTheory.SummatoryPhi.quo_succ (N := lg N) (two_r_pos hr))
  have eb := eqb_le_one (Γ := Γ) (rem (succ (lg N)) (two * r)) zero
  ipra_le sl q + sl eb with -f

/-- `N < 2^{2r(j(N)+1)}`. -/
theorem shell_bound {r N : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] lt N (pw two (two * r * succ (jj r N))) := by
  have b := Prf.andE₂ (lg_bracket hN)
  have d := div_mod_at (Γ := Γ) (x := lg N) (y := two * r) (c := pred (two * r)) (two_r_pos hr)
  have e1 := natEq (Prf.andE₁ d)
  have r1 := Prf.andE₂ d
  have hl : Γ ⊢[PRAAx] le (succ (lg N)) (two * r * succ (jj r N)) := by ipra_le sl r1 with -e1
  exact le_trans b (pw_le_exp two_pos hl)

/-! ## One value of the prefix inside its shell -/

/-- The packet's `|M(i)| ≤ (c+1)2^{r(j+1)+⌈(j+1)/2⌉}`, cleared: `2^{⌊j/2⌋}|M(N)| ≤ (c+1) 2^{(r+1) + (r+1)j}`. -/
theorem m_bound {r c N X : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hN : Γ ⊢[PRAAx] le one N)
    (hc : Γ ⊢[PRAAx] le (pw X (k4 r)) (c * pw N (succ (two * r)))) :
    Γ ⊢[PRAAx] le (pw two (quo (jj r N) two) * X) (succ c * pw two (succ r + succ r * jj r N)) := by
  have hk : Γ ⊢[PRAAx] k4 r ≐ succ (pred (k4 r)) := pos_of_one_le (by ipra_le sl hr + 𝔞 r + 𝔞 r + 𝔞 r)
  refine pw_le_cancel (k := pred (k4 r)) ?_
  refine le_congr (congrPw (.eqRefl _) hk) (congrPw (.eqRefl _) hk) ?_
  -- left side: `2^{h·4r} X^{4r} ≤ c 2^{h·4r + 2r(j+1)(2r+1)}`
  have eL : Γ ⊢[PRAAx] pw (pw two (quo (jj r N) two) * X) (k4 r) ≐
      pw two (quo (jj r N) two * k4 r) * pw X (k4 r) :=
    (pw_mul_base _ _ _).eqTrans (congrMul (pw_mul _ _ _) (.eqRefl _))
  have sb := le_trans (le_succ_self N) (shell_bound hr hN)
  have nb : Γ ⊢[PRAAx] le (pw N (succ (two * r)))
      (pw two (two * r * succ (jj r N) * succ (two * r))) :=
    le_congr (.eqRefl _) (pw_mul _ _ _) (pw_le_pw _ sb)
  have l1 := le_mul_mono (le_refl (pw two (quo (jj r N) two * k4 r))) hc
  have l2 := le_mul_mono (le_refl (pw two (quo (jj r N) two * k4 r) * c)) nb
  have eA : Γ ⊢[PRAAx] pw two (quo (jj r N) two * k4 r) * c * pw two (two * r * succ (jj r N) * succ (two * r)) ≐
      c * pw two (quo (jj r N) two * k4 r + two * r * succ (jj r N) * succ (two * r)) :=
    (by ipra_ring : Γ ⊢[PRAAx] _ ≐ c * (pw two (quo (jj r N) two * k4 r) *
      pw two (two * r * succ (jj r N) * succ (two * r)))).eqTrans (congrMul (.eqRefl c) (pw_add two _ _).eqSymm)
  -- right side: `(c+1)^{4r} 2^{(r+1)(j+1)·4r}`
  have eR : Γ ⊢[PRAAx] pw (succ c * pw two (succ r + succ r * jj r N)) (k4 r) ≐
      pw (succ c) (k4 r) * pw two ((succ r + succ r * jj r N) * k4 r) :=
    (pw_mul_base _ _ _).eqTrans (congrMul (.eqRefl _) (pw_mul _ _ _))
  have cb : Γ ⊢[PRAAx] le c (pw (succ c) (k4 r)) :=
    le_trans (le_succ_self c) (le_congr (.eqRefl _) (congrPw (.eqRefl _) hk.eqSymm) (le_self_pw c (pred (k4 r))))
  -- the exponents: `4r⌊j/2⌋ + 2r(2r+1)(j+1) ≤ 4r(r+1)(j+1)`
  have dj := div_mod_at (Γ := Γ) (x := jj r N) (y := two) (c := one) (.eqRefl _)
  have ej := natEq ((congrMul (.eqRefl r) (Prf.andE₁ dj)).eqTrans (by ipra_ring) :
    Γ ⊢[PRAAx] r * jj r N ≐ two * (r * quo (jj r N) two) + r * rem (jj r N) two)
  have ex : Γ ⊢[PRAAx] le (quo (jj r N) two * k4 r + two * r * succ (jj r N) * succ (two * r))
      ((succ r + succ r * jj r N) * k4 r) := by
    ipra_le 𝔞 r + 𝔞 r + 𝔞 (r * rem (jj r N) two) + 𝔞 (r * rem (jj r N) two) with ej + ej
  have pe := pw_le_exp two_pos ex
  have r1 := le_mul_mono cb pe
  exact le_congr eL.eqSymm eR.eqSymm (le_trans (le_trans l1 (le_congr (mul_assoc _ _ _) (.eqRefl _) l2))
    (le_congr eA.eqSymm (.eqRefl _) r1))

/-! ## Splitting `j + 1` into halves -/

theorem half_succ {j : PTm n} :
    Γ ⊢[PRAAx] ((rem j two ≐ zero) ⋏ (quo (succ j) two ≐ quo j two) ⋏ (rem (succ j) two ≐ one)) ⋎
      ((rem j two ≐ one) ⋏ (quo (succ j) two ≐ succ (quo j two)) ⋏ (rem (succ j) two ≐ zero)) := by
  have d := div_mod_at (Γ := Γ) (x := j) (y := two) (c := one) (.eqRefl _)
  have e := Prf.andE₁ d
  have rl := Prf.andE₂ d
  refine .orE (lt_or_le (rem j two) one) ?_ ?_
  · let C : List (Fm PTm n) := lt (rem j two) one :: Γ
    have r0 : C ⊢[PRAAx] rem j two ≐ zero := (monus_zero _).eqSymm.eqTrans ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)
    have f := natEq (Γ := C) e.wk
    have z := natEq (Γ := C) r0
    have hz : C ⊢[PRAAx] succ j ≐ two * quo j two + one := by apply deriveNat; ipra_simps; linear_combination f + z
    refine .orI₁ (.andI r0 (.andI ?_ ?_))
    · exact LeanProofs.IPRA.AnalyticNumberTheory.Totient.quo_eq two_pos hz (by ipra_le 0)
    · exact LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative.rem_eq' two_pos hz (by ipra_le 0)
  · let C : List (Fm PTm n) := le one (rem j two) :: Γ
    have h1 : C ⊢[PRAAx] le one (rem j two) := Prf.hyp0
    have rl' : C ⊢[PRAAx] lt (rem j two) two := rl.wk
    have r1 : C ⊢[PRAAx] rem j two ≐ one := by
      have a : C ⊢[PRAAx] le (rem j two) one := by ipra_le sl rl'
      exact le_antisymm a h1
    have f := natEq (Γ := C) e.wk
    have z := natEq (Γ := C) r1
    have hz : C ⊢[PRAAx] succ j ≐ two * succ (quo j two) + zero := by
      ipra_lc f + z
    refine .orI₂ (.andI r1 (.andI ?_ ?_))
    · exact LeanProofs.IPRA.AnalyticNumberTheory.Totient.quo_eq two_pos hz (by ipra_le 1)
    · exact LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative.rem_eq' two_pos hz (by ipra_le 1)

/-! ## The weighted error `E = W − M` across one step -/

variable (aP aN : PTm 2)

/-- `|E(N)| = |(M⁺ + W⁻) − (M⁻ + W⁺)|`. -/
abbrev Eab (r y N : PTm n) : PTm n := absd (Mv aP y N + Wv aN r y N) (Mv aN y N + Wv aP r y N)
/-- `|M(N)|`. -/
abbrev Mab (y N : PTm n) : PTm n := absd (Mv aP y N) (Mv aN y N)

/-- `E(N+1) = ρ_N E(N) + (ρ_N − 1) M(N)`, so `|E(N+1)| ≤ ρ_N |E(N)| + (ρ_N − 1)|M(N)|`. -/
theorem e_step (r y N : PTm n) :
    Γ ⊢[PRAAx] le (Eab aP aN r y (succ N)) (rho r N * Eab aP aN r y N + pred (rho r N) * Mab aP aN y N) := by
  have mP := natEq (M_succ (Γ := Γ) aP y N)
  have mN := natEq (M_succ (Γ := Γ) aN y N)
  have wP := natEq (W_succ (Γ := Γ) aP r y N)
  have wN := natEq (W_succ (Γ := Γ) aN r y N)
  have hρ : Γ ⊢[PRAAx] rho r N ≐ succ (pred (rho r N)) := pos_of_one_le (rho_pos r N)
  have qq : ∀ (X : PTm n), Γ ⊢[PRAAx] rho r N * X ≐ pred (rho r N) * X + X := fun X =>
    (congrMul hρ (.eqRefl X)).eqTrans (by ipra_ring)
  have qP := natEq (qq (Mv aP y N))
  have qN := natEq (qq (Mv aN y N))
  have l1 := le_mul_mono (le_refl (rho r N))
    (le_absd_l (Γ := Γ) (Mv aP y N + Wv aN r y N) (Mv aN y N + Wv aP r y N))
  have l2 := le_mul_mono (le_refl (rho r N))
    (le_absd_r (Γ := Γ) (Mv aP y N + Wv aN r y N) (Mv aN y N + Wv aP r y N))
  have l3 := le_mul_mono (le_refl (pred (rho r N))) (le_absd_r (Γ := Γ) (Mv aP y N) (Mv aN y N))
  have l4 := le_mul_mono (le_refl (pred (rho r N))) (le_absd_l (Γ := Γ) (Mv aP y N) (Mv aN y N))
  refine absd_le ?_ ?_
  · ipra_le sl l1 + sl l3 with mN + wP - mP - wN + qP - qN
  · ipra_le sl l2 + sl l4 with mP + wN - mN - wP + qN - qP

/-! ## The invariant -/

/-- `8`. -/
abbrev eight : PTm n := two * (two * two)
/-- `A = (c+1) 2^r`. -/
abbrev Ac (r c : PTm n) : PTm n := succ c * pw two r
/-- `2^{⌊j(N)/2⌋}`. -/
abbrev Hh (r N : PTm n) : PTm n := pw two (quo (jj r N) two)

/-- `2^{⌊j/2⌋}|E(N)| + 8 A u_N ≤ A u_N (8·2^{⌊j/2⌋} + 2(j mod 2))`. -/
abbrev Inv (r c y N : PTm n) : Fm PTm n :=
  le (Hh r N * Eab aP aN r y N + eight * (Ac r c * uu r N))
    (Ac r c * uu r N * (eight * Hh r N + two * rem (jj r N) two))

/-- The input bound at `N`, cleared into the invariant's units: `2^{⌊j/2⌋}|M(N)| ≤ 2 A u_N`. -/
theorem m_bound' {r c y N : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hN : Γ ⊢[PRAAx] le one N)
    (hc : Γ ⊢[PRAAx] le (pw (Mab aP aN y N) (k4 r)) (c * pw N (succ (two * r)))) :
    Γ ⊢[PRAAx] le (Hh r N * Mab aP aN y N) (two * (Ac r c * uu r N)) := by
  have b := m_bound hr hN hc
  have e : Γ ⊢[PRAAx] succ c * pw two (succ r + succ r * jj r N) ≐ two * (Ac r c * uu r N) :=
    (congrMul (.eqRefl _) ((pw_add two _ _).eqTrans (congrMul (pw_succ two r) (.eqRefl _)))).eqTrans
      (by ipra_ring)
  exact le_congr (.eqRefl _) e b

/-- One step of the invariant, for `N ≥ 1`. -/
theorem inv_step {r c y N : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hN : Γ ⊢[PRAAx] le one N)
    (ih : Γ ⊢[PRAAx] Inv aP aN r c y N)
    (hc : Γ ⊢[PRAAx] le (pw (Mab aP aN y N) (k4 r)) (c * pw N (succ (two * r)))) :
    Γ ⊢[PRAAx] Inv aP aN r c y (succ N) := by
  have es := e_step (Γ := Γ) aP aN r y N
  have mb := m_bound' aP aN hr hN hc
  have jm := jj_mono hr hN
  have js := jj_step hr hN
  have hρ : Γ ⊢[PRAAx] rho r N ≐ succ (pred (rho r N)) := pos_of_one_le (rho_pos r N)
  have g4p : Γ ⊢[PRAAx] rho r N * (Ac r c * uu r N) ≐ pred (rho r N) * (Ac r c * uu r N) + Ac r c * uu r N :=
    (congrMul hρ (.eqRefl (Ac r c * uu r N))).eqTrans (by ipra_ring)
  refine .orE (lt_or_le (jj r N) (jj r (succ N))) ?_ ?_
  · -- a shell crossing: `j(N+1) = j(N) + 1`, `ρ_N = 2^{r+1}`, `u_{N+1} = ρ_N u_N`
    let C : List (Fm PTm n) := lt (jj r N) (jj r (succ N)) :: Γ
    have hJ : C ⊢[PRAAx] jj r (succ N) ≐ succ (jj r N) := le_antisymm js.wk Prf.hyp0
    have eU : C ⊢[PRAAx] uu r (succ N) ≐ rho r N * uu r N := uu_succ hr.wk hN.wk
    have f1 := le_mul_mono (le_refl (Hh r N)) (es.wk : C ⊢[PRAAx] _)
    have f2 := le_mul_mono (le_refl (rho r N)) (ih.wk : C ⊢[PRAAx] _)
    have f3 := le_mul_mono (le_refl (pred (rho r N))) (mb.wk : C ⊢[PRAAx] _)
    have hs := half_succ (Γ := C) (j := jj r N)
    refine .orE hs ?_ ?_
    · -- `j` even: `⌊(j+1)/2⌋ = ⌊j/2⌋`, `(j+1) mod 2 = 1`
      let D : List (Fm PTm n) := ((rem (jj r N) two ≐ zero) ⋏ (quo (succ (jj r N)) two ≐ quo (jj r N) two) ⋏
        (rem (succ (jj r N)) two ≐ one)) :: C
      have p0 : D ⊢[PRAAx] rem (jj r N) two ≐ zero := Prf.andE₁ Prf.hyp0
      have q0 : D ⊢[PRAAx] quo (succ (jj r N)) two ≐ quo (jj r N) two := Prf.andE₁ (Prf.andE₂ Prf.hyp0)
      have p1 : D ⊢[PRAAx] rem (succ (jj r N)) two ≐ one := Prf.andE₂ (Prf.andE₂ Prf.hyp0)
      have eH : D ⊢[PRAAx] Hh r N ≐ Hh r (succ N) :=
        (congrPw (.eqRefl _) ((congrAp2 quoF hJ.wk (.eqRefl _)).eqTrans q0)).eqSymm
      have eP : D ⊢[PRAAx] one ≐ rem (jj r (succ N)) two := ((congrAp2 remF hJ.wk (.eqRefl _)).eqTrans p1).eqSymm
      have f2' : D ⊢[PRAAx] le (rho r N * (Hh r N * Eab aP aN r y N + eight * (Ac r c * uu r N)))
          (rho r N * (Ac r c * uu r N * (eight * Hh r N + two * zero))) :=
        le_congr (.eqRefl _) (congrMul (.eqRefl _) (congrMul (.eqRefl _) (congrAdd (.eqRefl _)
          (congrMul (.eqRefl _) p0)))) f2.wk
      have core : D ⊢[PRAAx] le (Hh r N * Eab aP aN r y (succ N) + eight * (Ac r c * (rho r N * uu r N)))
          (Ac r c * (rho r N * uu r N) * (eight * Hh r N + two * one)) := by
        have f1' := f1.wk (ψ := ((rem (jj r N) two ≐ zero) ⋏ (quo (succ (jj r N)) two ≐ quo (jj r N) two) ⋏
          (rem (succ (jj r N)) two ≐ one)))
        have f3' := f3.wk (ψ := ((rem (jj r N) two ≐ zero) ⋏ (quo (succ (jj r N)) two ≐ quo (jj r N) two) ⋏
          (rem (succ (jj r N)) two ≐ one)))
        have g4 := natEq (Γ := D) (g4p.wk.wk)
        ipra_le sl f1' + sl f2' + sl f3' + 𝔞 (Ac r c * uu r N) + 𝔞 (Ac r c * uu r N) with g4 + g4
      exact le_congr (congrAdd (congrMul eH (.eqRefl _)) (congrMul (.eqRefl _) (congrMul (.eqRefl _) eU.wk.eqSymm)))
        (congrMul (congrMul (.eqRefl _) eU.wk.eqSymm) (congrAdd (congrMul (.eqRefl _) eH) (congrMul (.eqRefl _) eP)))
        core
    · -- `j` odd: `⌊(j+1)/2⌋ = ⌊j/2⌋ + 1`, `(j+1) mod 2 = 0`
      let D : List (Fm PTm n) := ((rem (jj r N) two ≐ one) ⋏ (quo (succ (jj r N)) two ≐ succ (quo (jj r N) two)) ⋏
        (rem (succ (jj r N)) two ≐ zero)) :: C
      have p0 : D ⊢[PRAAx] rem (jj r N) two ≐ one := Prf.andE₁ Prf.hyp0
      have q0 : D ⊢[PRAAx] quo (succ (jj r N)) two ≐ succ (quo (jj r N) two) := Prf.andE₁ (Prf.andE₂ Prf.hyp0)
      have p1 : D ⊢[PRAAx] rem (succ (jj r N)) two ≐ zero := Prf.andE₂ (Prf.andE₂ Prf.hyp0)
      have eH : D ⊢[PRAAx] Hh r N * two ≐ Hh r (succ N) :=
        ((congrPw (.eqRefl _) ((congrAp2 quoF hJ.wk (.eqRefl _)).eqTrans q0)).eqTrans (pw_succ two _)).eqSymm
      have eP : D ⊢[PRAAx] zero ≐ rem (jj r (succ N)) two := ((congrAp2 remF hJ.wk (.eqRefl _)).eqTrans p1).eqSymm
      have f2' : D ⊢[PRAAx] le (rho r N * (Hh r N * Eab aP aN r y N + eight * (Ac r c * uu r N)))
          (rho r N * (Ac r c * uu r N * (eight * Hh r N + two * one))) :=
        le_congr (.eqRefl _) (congrMul (.eqRefl _) (congrMul (.eqRefl _) (congrAdd (.eqRefl _)
          (congrMul (.eqRefl _) p0)))) f2.wk
      have core : D ⊢[PRAAx] le (Hh r N * two * Eab aP aN r y (succ N) + eight * (Ac r c * (rho r N * uu r N)))
          (Ac r c * (rho r N * uu r N) * (eight * (Hh r N * two) + two * zero)) := by
        have f1' := f1.wk (ψ := ((rem (jj r N) two ≐ one) ⋏ (quo (succ (jj r N)) two ≐ succ (quo (jj r N) two)) ⋏
          (rem (succ (jj r N)) two ≐ zero)))
        have f3' := f3.wk (ψ := ((rem (jj r N) two ≐ one) ⋏ (quo (succ (jj r N)) two ≐ succ (quo (jj r N) two)) ⋏
          (rem (succ (jj r N)) two ≐ zero)))
        have g4 := natEq (Γ := D) (g4p.wk.wk)
        ipra_le sl f1' + sl f1' + sl f2' + sl f2' + sl f3' + sl f3' + 𝔞 (Ac r c * uu r N) + 𝔞 (Ac r c * uu r N) +
          𝔞 (Ac r c * uu r N) + 𝔞 (Ac r c * uu r N) with g4 + g4 + g4 + g4
      exact le_congr (congrAdd (congrMul eH (.eqRefl _)) (congrMul (.eqRefl _) (congrMul (.eqRefl _) eU.wk.eqSymm)))
        (congrMul (congrMul (.eqRefl _) eU.wk.eqSymm) (congrAdd (congrMul (.eqRefl _) eH) (congrMul (.eqRefl _) eP)))
        core
  · -- inside a shell: `j(N+1) = j(N)`, `ρ_N = 1`
    let C : List (Fm PTm n) := le (jj r (succ N)) (jj r N) :: Γ
    have hJ : C ⊢[PRAAx] jj r (succ N) ≐ jj r N := le_antisymm Prf.hyp0 jm.wk
    have m0 : C ⊢[PRAAx] monus (jj r (succ N)) (jj r N) ≐ zero := (congrMonus hJ (.eqRefl _)).eqTrans (monus_self _)
    have r1 : C ⊢[PRAAx] rho r N ≐ one :=
      (congrPw (.eqRefl _) ((congrMul (.eqRefl _) m0).eqTrans (mul_zero _))).eqTrans (pw_zero two)
    have r0 : C ⊢[PRAAx] pred (rho r N) ≐ zero := (congrPred r1).eqTrans (pred_succ _)
    have eE : C ⊢[PRAAx] le (Eab aP aN r y (succ N)) (Eab aP aN r y N) := by
      refine le_congr (.eqRefl _) ?_ es.wk
      refine (congrAdd ((congrMul r1 (.eqRefl _)).eqTrans (one_mul _)) ((congrMul r0 (.eqRefl _)).eqTrans
        (zero_mul _))).eqTrans (add_zero _)
    have eU : C ⊢[PRAAx] uu r N ≐ uu r (succ N) := (congrPw (.eqRefl _) (congrMul (.eqRefl _)
      (congrAp2 quoF (.eqRefl _) (.eqRefl _)))).eqTrans (congrPw (.eqRefl _) (congrMul (.eqRefl _) hJ.eqSymm))
    have eH : C ⊢[PRAAx] Hh r N ≐ Hh r (succ N) := congrPw (.eqRefl _) (congrAp2 quoF hJ.eqSymm (.eqRefl _))
    have eR : C ⊢[PRAAx] rem (jj r N) two ≐ rem (jj r (succ N)) two := congrAp2 remF hJ.eqSymm (.eqRefl _)
    have m := le_mul_mono (le_refl (Hh r N)) eE
    have core : C ⊢[PRAAx] le (Hh r N * Eab aP aN r y (succ N) + eight * (Ac r c * uu r N))
        (Ac r c * uu r N * (eight * Hh r N + two * rem (jj r N) two)) := by
      have ih' := ih.wk (ψ := le (jj r (succ N)) (jj r N))
      ipra_le sl m + sl ih'
    exact le_congr (congrAdd (congrMul eH (.eqRefl _)) (congrMul (.eqRefl _) (congrMul (.eqRefl _) eU)))
      (congrMul (congrMul (.eqRefl _) eU) (congrAdd (congrMul (.eqRefl _) eH) (congrMul (.eqRefl _) eR))) core

/-! ## The start of the induction -/

/-- `E(1) = 0`. -/
theorem e_one (r y : PTm n) : Γ ⊢[PRAAx] le (Eab aP aN r y one) zero := by
  have mP := natEq (M_succ (Γ := Γ) aP y zero)
  have mN := natEq (M_succ (Γ := Γ) aN y zero)
  have wP := natEq (W_succ (Γ := Γ) aP r y zero)
  have wN := natEq (W_succ (Γ := Γ) aN r y zero)
  have m0P := natEq (sum_zero (Γ := Γ) (shiftBody aP) y)
  have m0N := natEq (sum_zero (Γ := Γ) (shiftBody aN) y)
  have z1 := natEq ((congrMul (.eqRefl (rho r zero)) (W_zero (Γ := Γ) aP r y)).eqTrans (mul_zero _))
  have z2 := natEq ((congrMul (.eqRefl (rho r zero)) (W_zero (Γ := Γ) aN r y)).eqTrans (mul_zero _))
  refine absd_le ?_ ?_
  · ipra_le 0 with mN + wP - mP - wN + m0N - m0P + z1 - z2
  · ipra_le 0 with mP + wN - mN - wP + m0P - m0N + z2 - z1

theorem jj_one {r : PTm n} (hr : Γ ⊢[PRAAx] le one r) : Γ ⊢[PRAAx] jj r one ≐ zero :=
  (congrAp2 quoF lg_one (.eqRefl _)).eqTrans
    (LeanProofs.IPRA.Combinatorics.LegendreDigits.quo_small (two_r_pos hr) (by ipra_le sl hr + 𝔞 r))

/-- The invariant at `N = 1`. -/
theorem inv_one {r c : PTm n} (hr : Γ ⊢[PRAAx] le one r) (y : PTm n) : Γ ⊢[PRAAx] Inv aP aN r c y one := by
  have j1 := jj_one (Γ := Γ) hr
  have eq0 : Γ ⊢[PRAAx] quo (jj r one) two ≐ zero :=
    (congrAp2 quoF j1 (.eqRefl _)).eqTrans (LeanProofs.IPRA.Combinatorics.LegendreDigits.quo_small two_pos (by ipra_le 1))
  have eH : Γ ⊢[PRAAx] one ≐ Hh r one := ((congrPw (.eqRefl _) eq0).eqTrans (pw_zero two)).eqSymm
  have eR : Γ ⊢[PRAAx] zero ≐ rem (jj r one) two :=
    ((congrAp2 remF j1 (.eqRefl _)).eqTrans
      (LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc.rem_small (by ipra_le 1))).eqSymm
  have e1 := e_one (Γ := Γ) aP aN r y
  have core : Γ ⊢[PRAAx] le (one * Eab aP aN r y one + eight * (Ac r c * uu r one))
      (Ac r c * uu r one * (eight * one + two * zero)) := by ipra_le sl e1
  exact le_congr (congrAdd (congrMul eH (.eqRefl _)) (.eqRefl _))
    (congrMul (.eqRefl _) (congrAdd (congrMul (.eqRefl _) eH) (congrMul (.eqRefl _) eR))) core

/-! ## The invariant for every `N ≥ 1` -/

/-- The input `|M(N)|^{4r} ≤ c N^{2r+1}` for every `N`. -/
abbrev InM (r c y : PTm n) : Fm PTm n :=
  Fm.all (le (pw (Mab aP aN (Syn.shift y) (var 0)) (k4 (Syn.shift r))) (Syn.shift c * pw (var 0) (succ (two * Syn.shift r))))

theorem inM_at {r c y : PTm n} (hc : Γ ⊢[PRAAx] InM aP aN r c y) (N : PTm n) :
    Γ ⊢[PRAAx] le (pw (Mab aP aN y N) (k4 r)) (c * pw N (succ (two * r))) := by
  have b := Prf.allE N hc
  simp only [InM, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_pairT,
    LeanProofs.IPRA.PTm.subst_pred, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at b
  exact b

/-- `Inv(m+1)` for every `m`. -/
theorem inv_all {r c y : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hc : Γ ⊢[PRAAx] InM aP aN r c y) (m : PTm n) :
    Γ ⊢[PRAAx] Inv aP aN r c y (succ m) := by
  have hall : Γ ⊢[PRAAx] Fm.all (Inv aP aN (Syn.shift r) (Syn.shift c) (Syn.shift y) (succ (var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [Inv, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_pairT,
        LeanProofs.IPRA.PTm.subst_pred, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift]
      exact inv_one aP aN hr y
    · simp only [Inv, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_pairT,
        LeanProofs.IPRA.PTm.subst_pred, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift]
      let φ : Fm PTm (n + 1) := Inv aP aN (Syn.shift r) (Syn.shift c) (Syn.shift y) (succ (var 0))
      let Δ : List (Fm PTm (n + 1)) := φ :: Γ.map Fm.shift
      have hr' : Δ ⊢[PRAAx] le one (Syn.shift r) := by
        have b : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift r) := by simpa [Fm.shift, Syn.shift] using hr.shift
        exact b.wk
      have hc' : Δ ⊢[PRAAx] InM aP aN (Syn.shift r) (Syn.shift c) (Syn.shift y) := by
        have b : (Γ.map Fm.shift) ⊢[PRAAx] InM aP aN (Syn.shift r) (Syn.shift c) (Syn.shift y) := by
          have h := hc.shift
          simp only [InM, Fm.shift, Fm.subst_all, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul,
            PTm.subst_monus, LeanProofs.IPRA.PTm.subst_pred, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
            Syn.subst_var, Syn.up_zero, subst_up_shift_pal,
            LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorGrowth.subst_sh] at h
          exact h
        exact b.wk
      exact inv_step aP aN hr' (by ipra_le 𝔞 (var 0)) Prf.hyp0 (inM_at aP aN hc' (succ (var 0)))
  have a := Prf.allE m hall
  simp only [Inv, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_pairT,
    LeanProofs.IPRA.PTm.subst_pred, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at a
  exact a

/-! ## The weighted sums are bounded -/

/-- `K = c + r + 4`. -/
abbrev Kc (r c : PTm n) : PTm n := succ (succ (succ (succ (c + r))))

/-- `|W(m+1)| ≤ 2^{c+r+4} u_{m+1}`. -/
theorem w_bound {r c y : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hc : Γ ⊢[PRAAx] InM aP aN r c y) (m : PTm n) :
    Γ ⊢[PRAAx] le (absd (Wv aP r y (succ m)) (Wv aN r y (succ m))) (pw two (Kc r c) * uu r (succ m)) := by
  have iv := inv_all aP aN hr hc m
  have hN : Γ ⊢[PRAAx] le one (succ m) := by ipra_le 𝔞 m
  have mb := m_bound' aP aN hr hN (inM_at aP aN hc (succ m))
  have hH : Γ ⊢[PRAAx] le one (Hh r (succ m)) := one_le_pw' (by ipra_le 1) _
  have hp : Γ ⊢[PRAAx] Hh r (succ m) ≐ succ (pred (Hh r (succ m))) := pos_of_one_le hH
  have rm : Γ ⊢[PRAAx] le (rem (jj r (succ m)) two) one := by
    have d := Prf.andE₂ (div_mod_at (Γ := Γ) (x := jj r (succ m)) (y := two) (c := one) (.eqRefl _))
    ipra_le sl d
  have rmA := le_mul_mono rm (le_refl (Ac r c * uu r (succ m)))
  -- `|E| ≤ 8 A u`
  have hE : Γ ⊢[PRAAx] le (Hh r (succ m) * Eab aP aN r y (succ m)) (Hh r (succ m) * (eight * (Ac r c * uu r (succ m)))) := by
    ipra_le sl iv + sl rmA + sl rmA + 𝔞 (Ac r c * uu r (succ m)) + 𝔞 (Ac r c * uu r (succ m)) + 𝔞 (Ac r c * uu r (succ m)) +
      𝔞 (Ac r c * uu r (succ m)) + 𝔞 (Ac r c * uu r (succ m)) + 𝔞 (Ac r c * uu r (succ m))
  have hE' : Γ ⊢[PRAAx] le (Eab aP aN r y (succ m)) (eight * (Ac r c * uu r (succ m))) :=
    mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) hE)
  -- `|M| ≤ 2 A u`
  have hM0 := le_mul_mono hH (le_refl (Mab aP aN y (succ m)))
  have hM : Γ ⊢[PRAAx] le (Mab aP aN y (succ m)) (two * (Ac r c * uu r (succ m))) := by
    ipra_le sl hM0 + sl mb
  -- `|W| ≤ |E| + |M|`
  have l1 := le_absd_l (Γ := Γ) (Mv aP y (succ m) + Wv aN r y (succ m)) (Mv aN y (succ m) + Wv aP r y (succ m))
  have l2 := le_absd_r (Γ := Γ) (Mv aP y (succ m) + Wv aN r y (succ m)) (Mv aN y (succ m) + Wv aP r y (succ m))
  have l3 := le_absd_l (Γ := Γ) (Mv aP y (succ m)) (Mv aN y (succ m))
  have l4 := le_absd_r (Γ := Γ) (Mv aP y (succ m)) (Mv aN y (succ m))
  -- `10 A ≤ 2^{c+r+4}`
  have cb := LeanProofs.IPRA.Topology.CollisionScales.lt_pw_two (Γ := Γ) c
  have cb' := le_mul_mono cb (le_refl (pw two r * uu r (succ m)))
  have eK : Γ ⊢[PRAAx] pw two (Kc r c) * uu r (succ m) ≐
      two * (two * (two * (two * (pw two c * (pw two r * uu r (succ m)))))) := by
    refine (congrMul ((pw_succ two _).eqTrans (congrMul ((pw_succ two _).eqTrans (congrMul ((pw_succ two _).eqTrans
      (congrMul ((pw_succ two _).eqTrans (congrMul (pw_add two c r) (.eqRefl _))) (.eqRefl _))) (.eqRefl _)))
      (.eqRefl _))) (.eqRefl _)).eqTrans ?_
    ipra_ring
  have f := natEq eK
  refine absd_le ?_ ?_
  · ipra_le sl l2 + sl l3 + sl hE' + sl hM + sl cb' + sl cb' + sl cb' + sl cb' + sl cb' + sl cb' + sl cb' + sl cb' +
      sl cb' + sl cb' + 𝔞 (pw two c * (pw two r * uu r (succ m))) + 𝔞 (pw two c * (pw two r * uu r (succ m))) +
      𝔞 (pw two c * (pw two r * uu r (succ m))) + 𝔞 (pw two c * (pw two r * uu r (succ m))) +
      𝔞 (pw two c * (pw two r * uu r (succ m))) + 𝔞 (pw two c * (pw two r * uu r (succ m))) with f
  · ipra_le sl l1 + sl l4 + sl hE' + sl hM + sl cb' + sl cb' + sl cb' + sl cb' + sl cb' + sl cb' + sl cb' + sl cb' +
      sl cb' + sl cb' + 𝔞 (pw two c * (pw two r * uu r (succ m))) + 𝔞 (pw two c * (pw two r * uu r (succ m))) +
      𝔞 (pw two c * (pw two r * uu r (succ m))) + 𝔞 (pw two c * (pw two r * uu r (succ m))) +
      𝔞 (pw two c * (pw two r * uu r (succ m))) + 𝔞 (pw two c * (pw two r * uu r (succ m))) with f

/-- `thm:rate` (1) ⇒ (2), core: `|M(i)|^{4r} ≤ c i^{2r+1}` for every `i` gives `|W(i)| ≤ 2^{c+r+4} u_i` for every `i`,
i.e. `|S_r(i)| ≤ 2^{c+r+4}`. -/
theorem w_all {r c y : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hc : Γ ⊢[PRAAx] InM aP aN r c y) :
    Γ ⊢[PRAAx] WBound aP aN r y (Kc r c) := by
  refine .allI ?_
  rw [show Syn.shift (Kc r c) = Kc (Syn.shift r) (Syn.shift c) by simp [Syn.shift]]
  have hr' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift r) := by simpa [Fm.shift, Syn.shift] using hr.shift
  have hc' : (Γ.map Fm.shift) ⊢[PRAAx] InM aP aN (Syn.shift r) (Syn.shift c) (Syn.shift y) := by
    have h := hc.shift
    simp only [InM, Fm.shift, Fm.subst_all, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul,
      PTm.subst_monus, LeanProofs.IPRA.PTm.subst_pred, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
      Syn.subst_var, Syn.up_zero, subst_up_shift_pal,
      LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorGrowth.subst_sh] at h
    exact h
  refine .orE (lt_or_le zero (var 0)) ?_ ?_
  · let C : List (Fm PTm (n + 1)) := lt zero (var 0) :: Γ.map Fm.shift
    have hp : C ⊢[PRAAx] (var 0 : PTm (n + 1)) ≐ succ (pred (var 0)) := pos_of_one_le Prf.hyp0
    have w := w_bound (Γ := C) aP aN hr'.wk hc'.wk (pred (var 0))
    have e : C ⊢[PRAAx] succ (pred (var 0)) ≐ (var 0 : PTm (n + 1)) := hp.eqSymm
    have cWP : C ⊢[PRAAx] Wv aP (Syn.shift r) (Syn.shift y) (succ (pred (var 0))) ≐ Wv aP (Syn.shift r) (Syn.shift y) (var 0) :=
      congrAp2 _ e (.eqRefl _)
    have cWN : C ⊢[PRAAx] Wv aN (Syn.shift r) (Syn.shift y) (succ (pred (var 0))) ≐ Wv aN (Syn.shift r) (Syn.shift y) (var 0) :=
      congrAp2 _ e (.eqRefl _)
    have cu : C ⊢[PRAAx] uu (Syn.shift r) (succ (pred (var 0))) ≐ uu (Syn.shift r) (var 0) :=
      congrPw (.eqRefl _) (congrMul (.eqRefl _) (congrAp2 quoF (congrPred (congrAp2 _ (congrSucc (congrSucc e))
        (congrSucc e))) (.eqRefl _)))
    exact le_congr (congrAdd (congrMonus cWP cWN) (congrMonus cWN cWP)) (congrMul (.eqRefl _) cu) w
  · let C : List (Fm PTm (n + 1)) := le (var 0) zero :: Γ.map Fm.shift
    have hz : C ⊢[PRAAx] (var 0 : PTm (n + 1)) ≐ zero := (monus_zero _).eqSymm.eqTrans Prf.hyp0
    have z1 := natEq ((congrAp2 _ hz (.eqRefl _)).eqTrans (W_zero aP _ _) :
      C ⊢[PRAAx] Wv aP (Syn.shift r) (Syn.shift y) (var 0) ≐ zero)
    have z2 := natEq ((congrAp2 _ hz (.eqRefl _)).eqTrans (W_zero aN _ _) :
      C ⊢[PRAAx] Wv aN (Syn.shift r) (Syn.shift y) (var 0) ≐ zero)
    refine absd_le ?_ ?_
    · ipra_le 𝔞 (pw two (Kc (Syn.shift r) (Syn.shift c)) * uu (Syn.shift r) (var 0)) with z2 - z1
    · ipra_le 𝔞 (pw two (Kc (Syn.shift r) (Syn.shift c)) * uu (Syn.shift r) (var 0)) with z1 - z2

end LeanProofs.IPRA.AnalyticNumberTheory.RateShell
