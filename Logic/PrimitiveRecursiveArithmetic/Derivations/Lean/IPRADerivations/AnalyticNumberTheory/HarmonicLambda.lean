import IPRADerivations.AnalyticNumberTheory.ChebyshevBounds
import IPRADerivations.AnalyticNumberTheory.BinomialThree
import IPRADerivations.Core.LinearCombination

/-!
# The harmonic Mangoldt sum, integer form

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:harmonic-lambda`:
`log N − 2 log 2 ≤ ∑_{n≤N} Λ(n)/n ≤ log N + 4 log 2`. With the common denominator `N!`, write
`S_w(N) = ∑_{d≤N} Λ_w(d) · (N!/d) = N! · ∑_{d≤N} Λ_w(d)/d`. For every weight `w`:

* `harmonic_sandwich`: `N! · L_w(N!) ≤ N · S_w(N) ≤ N! · (L_w(N!) + Ψ_w(N))`, i.e.
  `L_w(N!)/N ≤ ∑ Λ_w(d)/d ≤ (L_w(N!) + Ψ_w(N))/N`, from `d⌊N/d⌋ ≤ N < d(⌊N/d⌋ + 1)` and the exact
  factorial identity `L_w(N!) = ∑ Λ_w(d)⌊N/d⌋` (`factorial_lambda`);
* `fact_le_pow`, `pow_le_three_fact`: `N! ≤ N^N ≤ 3^N N!`, i.e. `N log N − N log 3 ≤ log N! ≤ N log N`
  (from `binomial_three`, stronger than the packet's `2 log 2`).

With `w = log` and `ψ(N) ≤ 4N log 2` (`ChebyshevBounds.lcmu_upper` with `thm:psi-lcm`) these give the
displayed bounds; the passage to real logarithms is not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLambda

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (lamB Lam Lw)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (FLB FL_at lam_zero factorial_lambda sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (LamB Psi inst2_LamB)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd')
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## `N! ≤ N^N ≤ 3^N N!` -/

theorem fact_le_pow (N : PTm n) : Γ ⊢[PRAAx] le (fact N) (pw N N) := by
  have h := BinomialThree.fact_le_falling (Γ := Γ) zero N
  exact le_congr (congrAp2 factF (zero_add _) (.eqRefl _))
    ((congrMul (fact_zero zero) (congrAp2 powF (.eqRefl _) (zero_add _))).eqTrans (one_mul _)) h

theorem pow_le_three_fact (N : PTm n) : Γ ⊢[PRAAx] le (pw N N) (pw (succ two) N * fact N) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (pw (var 0) (var 0)) (pw (succ two) (var 0) * fact (var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero,
        ConciseIPRA.PTm.subst_succ]
      exact le_congr (pw_zero _).eqSymm ((congrMul (pw_zero _) (fact_zero zero)).eqTrans (one_mul _)).eqSymm (le_refl _)
    · simp only [subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero,
        ConciseIPRA.PTm.subst_succ]
      let D : List (Fm PTm (n + 1)) := le (pw (var 0) (var 0)) (pw (succ two) (var 0) * fact (var 0)) :: Γ.map Fm.shift
      have ih : D ⊢[PRAAx] le (pw (var 0) (var 0)) (pw (succ two) (var 0) * fact (var 0)) := Prf.hyp0
      have b3 : D ⊢[PRAAx] le (pw (succ (var 0)) (var 0)) (succ two * pw (var 0) (var 0)) :=
        BinomialThree.binomial_three (var 0)
      have s1 := mul_le_mul_right (succ (var 0)) b3
      have s2 := mul_le_mul_right (succ (var 0)) (le_mul_mono (le_refl (succ two)) ih)
      have eL : D ⊢[PRAAx] pw (succ (var 0)) (succ (var 0)) ≐ pw (succ (var 0)) (var 0) * succ (var 0) := pw_succ _ _
      refine le_congr eL.eqSymm ?_ (le_trans s1 s2)
      ipra_lc -natEq ((congrMul (pw_succ (Γ := D) (succ two) (var 0)) (fact_succ (var 0) zero)))
  have i := Prf.allE N hall
  simp only [subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at i
  exact i

/-! ## The sandwich -/

section Sandwich

variable (w : PTm 2)

/-- `Λ_w(d) · (N!/d)`, over `0 = d`, `1 = ⟨N, y⟩`. -/
abbrev AB : PTm 2 := ap2 (sumF (lamB w)) (succ (var 0)) (pairT (var 0) (sndT (var 1))) * quo (fact (fstT (var 1))) (var 0)
/-- `Λ_w(d) · (⌊N/d⌋ + 1)`. -/
abbrev WB : PTm 2 := ap2 (sumF (lamB w)) (succ (var 0)) (pairT (var 0) (sndT (var 1))) * (quo (fstT (var 1)) (var 0) + one)
abbrev U1 : PTm 2 := fact (fstT (var 1)) * FLB w
abbrev V1 : PTm 2 := fstT (var 1) * AB w
abbrev U2 : PTm 2 := fact (fstT (var 1)) * WB w

/-- `S_w(N) = ∑_{d ≤ N} Λ_w(d) · (N!/d)`. -/
abbrev Sw (N y : PTm n) : PTm n := ap2 (sumF (AB w)) (succ N) (pairT N y)

theorem lam_at (d N y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (lamB w)) (succ d) (pairT d (sndT (pairT N y))) ≐ Lam w d y :=
  congrAp2 (sumF (lamB w)) (.eqRefl _) (congrPairT (.eqRefl _) (snd_pair _ _))

theorem fct_at (N y : PTm n) : Γ ⊢[PRAAx] fact (fstT (pairT N y)) ≐ fact N := congrAp2 factF (fst_pair _ _) (.eqRefl _)

theorem AB_at (d N y : PTm n) : Γ ⊢[PRAAx] inst2 (AB w) d (pairT N y) ≐ Lam w d y * quo (fact N) d := by
  have e : inst2 (AB w) d (pairT N y) =
      ap2 (sumF (lamB w)) (succ d) (pairT d (sndT (pairT N y))) * quo (fact (fstT (pairT N y))) d := by simp [inst2]
  rw [e]; exact congrMul (lam_at w _ _ _) (congrAp2 quoF (fct_at _ _) (.eqRefl _))

theorem WB_at (d N y : PTm n) : Γ ⊢[PRAAx] inst2 (WB w) d (pairT N y) ≐ Lam w d y * (quo N d + one) := by
  have e : inst2 (WB w) d (pairT N y) =
      ap2 (sumF (lamB w)) (succ d) (pairT d (sndT (pairT N y))) * (quo (fstT (pairT N y)) d + one) := by simp [inst2]
  rw [e]; exact congrMul (lam_at w _ _ _) (congrAdd (congrAp2 quoF (fst_pair _ _) (.eqRefl _)) (.eqRefl _))

theorem U1_at (d N y : PTm n) : Γ ⊢[PRAAx] inst2 (U1 w) d (pairT N y) ≐ fact N * (Lam w d y * quo N d) := by
  have e : inst2 (U1 w) d (pairT N y) = fact (fstT (pairT N y)) * inst2 (FLB w) d (pairT N y) := by simp [inst2]
  rw [e]; exact congrMul (fct_at _ _) (FL_at w _ _ _)

theorem V1_at (d N y : PTm n) : Γ ⊢[PRAAx] inst2 (V1 w) d (pairT N y) ≐ N * (Lam w d y * quo (fact N) d) := by
  have e : inst2 (V1 w) d (pairT N y) = fstT (pairT N y) * inst2 (AB w) d (pairT N y) := by simp [inst2]
  rw [e]; exact congrMul (fst_pair _ _) (AB_at w _ _ _)

theorem U2_at (d N y : PTm n) : Γ ⊢[PRAAx] inst2 (U2 w) d (pairT N y) ≐ fact N * (Lam w d y * (quo N d + one)) := by
  have e : inst2 (U2 w) d (pairT N y) = fact (fstT (pairT N y)) * inst2 (WB w) d (pairT N y) := by simp [inst2]
  rw [e]; exact congrMul (fct_at _ _) (WB_at w _ _ _)

/-- `Λ_w(0) = 0` makes the `d = 0` terms vanish. -/
theorem lam_d0 {d y : PTm n} (h : Γ ⊢[PRAAx] d ≐ zero) : Γ ⊢[PRAAx] Lam w d y ≐ zero :=
  (congrAp2 (sumF (lamB w)) (congrSucc h) (congrPairT h (.eqRefl _))).eqTrans (lam_zero w y)

/-- `N! Λ(d) ⌊N/d⌋ ≤ N Λ(d) (N!/d)` for `d ≤ N`. -/
theorem pt1 {d N y : PTm n} (hd : Γ ⊢[PRAAx] lt d (succ N)) :
    Γ ⊢[PRAAx] le (fact N * (Lam w d y * quo N d)) (N * (Lam w d y * quo (fact N) d)) := by
  refine .orE (zero_or_succ d) ?_ ?_
  · have l := lam_d0 w (y := y) (Prf.hyp0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] d ≐ zero)
    exact le_congr ((congrMul (.eqRefl _) (Mobius.zero_mul_l l _)).eqTrans (mul_zero _)).eqSymm (.eqRefl _) (zero_le _)
  · let C : List (Fm PTm n) := (d ≐ succ (pred d)) :: Γ
    have hp : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    have dl : C ⊢[PRAAx] le (succ (pred d)) N :=
      le_congr hp (.eqRefl _) ((succ_monus_succ _ _).eqSymm.eqTrans hd.wk |> fun h => le_congr (.eqRefl _) (.eqRefl _) h)
    have df := Primes.dvd_fact dl
    have eF := natEq (eq_of_dvd' hp (dvd_congr_left hp.eqSymm df))
    have dv := natEq (GcdFiber.div_eq (j := N) hp)
    exact le_of_eq_add (d := Lam w d y * quo (fact N) d * rem N d)
      (by apply deriveNat; ipra_simps; linear_combination 𝔞 (Lam w d y) * 𝔞 (quo (fact N) d) * dv -
        𝔞 (Lam w d y) * 𝔞 (quo N d) * eF)

/-- `N Λ(d) (N!/d) ≤ N! Λ(d) (⌊N/d⌋ + 1)` for `d ≤ N`. -/
theorem pt2 {d N y : PTm n} (hd : Γ ⊢[PRAAx] lt d (succ N)) :
    Γ ⊢[PRAAx] le (N * (Lam w d y * quo (fact N) d)) (fact N * (Lam w d y * (quo N d + one))) := by
  refine .orE (zero_or_succ d) ?_ ?_
  · have l := lam_d0 w (y := y) (Prf.hyp0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] d ≐ zero)
    exact le_congr ((congrMul (.eqRefl _) (Mobius.zero_mul_l l _)).eqTrans (mul_zero _)).eqSymm (.eqRefl _) (zero_le _)
  · let C : List (Fm PTm n) := (d ≐ succ (pred d)) :: Γ
    have hp : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    have dl : C ⊢[PRAAx] le (succ (pred d)) N :=
      le_congr hp (.eqRefl _) ((succ_monus_succ _ _).eqSymm.eqTrans hd.wk)
    have df := Primes.dvd_fact dl
    have eF := natEq (eq_of_dvd' hp (dvd_congr_left hp.eqSymm df))
    have dv := natEq (GcdFiber.div_eq (j := N) hp)
    have ds := natEq (eq_add_of_le (Multiplicative.rem_lt' hp N))
    exact le_of_eq_add (d := Lam w d y * quo (fact N) d * succ (monus d (succ (rem N d))))
      (by apply deriveNat; ipra_simps; linear_combination 𝔞 (Lam w d y) * (𝔞 (quo N d) + 1) * eF -
        𝔞 (Lam w d y) * 𝔞 (quo (fact N) d) * dv + 𝔞 (Lam w d y) * 𝔞 (quo (fact N) d) * ds)

theorem shift_fact (N : PTm n) : Syn.shift (fact N) = fact (Syn.shift N) := by simp [Syn.shift]

/-- `thm:harmonic-lambda`, integer core: `N! L_w(N!) ≤ N S_w(N) ≤ N! (L_w(N!) + Ψ_w(N))`. -/
theorem harmonic_sandwich (N y : PTm n) :
    Γ ⊢[PRAAx] le (fact N * Lw w (fact N) y) (N * Sw w N y) ⋏
      le (N * Sw w N y) (fact N * (Lw w (fact N) y + Psi w N y)) := by
  have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  have A1 : Γ ⊢[PRAAx] ap2 (sumF (U1 w)) (succ N) (pairT N y) ≐ fact N * Lw w (fact N) y := by
    refine (sum_scale _ _ _ _ _ _ (.allI (.impI ?_))).eqTrans (congrMul (.eqRefl _) (factorial_lambda w N y).eqSymm)
    rw [shift_pairT, shift_fact]
    exact (U1_at w _ _ _).eqTrans (congrMul (.eqRefl _) (FL_at w _ _ _).eqSymm)
  have A2 : Γ ⊢[PRAAx] ap2 (sumF (V1 w)) (succ N) (pairT N y) ≐ N * Sw w N y := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT]
    exact (V1_at w _ _ _).eqTrans (congrMul (.eqRefl _) (AB_at w _ _ _).eqSymm)
  have A3 : Γ ⊢[PRAAx] ap2 (sumF (U2 w)) (succ N) (pairT N y) ≐ fact N * ap2 (sumF (WB w)) (succ N) (pairT N y) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, shift_fact]
    exact (U2_at w _ _ _).eqTrans (congrMul (.eqRefl _) (WB_at w _ _ _).eqSymm)
  have A4 : Γ ⊢[PRAAx] ap2 (sumF (WB w)) (succ N) (pairT N y) ≐ Lw w (fact N) y + Psi w N y := by
    refine (sum_add2 (FLB w) (LamB w) (WB w) (K := succ N) (x := pairT N y) (x' := y) (z := pairT N y)
      (.allI (.impI ?_))).eqTrans (congrAdd (factorial_lambda w N y).eqSymm (.eqRefl _))
    rw [shift_pairT, inst2_LamB]
    refine (WB_at w _ _ _).eqTrans (.eqTrans ?_ (congrAdd (FL_at w _ _ _) (.eqRefl _)).eqSymm)
    ipra_ring
  have L1 := Analysis.PowerSums.sum_le (Γ := Γ) (U1 w) (V1 w) (pairT N y) (succ N) (.allI (.impI (by
    rw [shift_pairT, hs]
    exact le_congr (U1_at w _ _ _).eqSymm (V1_at w _ _ _).eqSymm (pt1 w Prf.hyp0))))
  have L2 := Analysis.PowerSums.sum_le (Γ := Γ) (V1 w) (U2 w) (pairT N y) (succ N) (.allI (.impI (by
    rw [shift_pairT, hs]
    exact le_congr (V1_at w _ _ _).eqSymm (U2_at w _ _ _).eqSymm (pt2 w Prf.hyp0))))
  exact .andI (le_congr A1 A2 L1) (le_congr A2 (A3.eqTrans (congrMul (.eqRefl _) A4)) L2)

end Sandwich

end LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLambda
