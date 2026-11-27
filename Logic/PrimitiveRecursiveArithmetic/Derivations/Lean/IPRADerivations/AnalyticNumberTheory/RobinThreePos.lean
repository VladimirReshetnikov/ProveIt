import IPRADerivations.AnalyticNumberTheory.RobinThree
import IPRADerivations.AnalyticNumberTheory.RobinLogInterval
import IPRADerivations.AnalyticNumberTheory.RobinGammaInterval
import IPRADerivations.AnalyticNumberTheory.RobinExpName

/-!
# `thm:three` as `Pos` certificates (`robin_ipra_research_2026-11-19`, §"Composing the double logarithm", `eq:pos`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`: "For `n ≥ 2` let `ℓ(n)` denote the
binary bit length of `n` and put `r = k + ℓ(n) + 16`. Enclose `log n` at precision `r`, then enclose the logarithms of its
two endpoints at the same precision. … Multiply it by the `[1,3]`-bounded enclosure of `e^γ` at precision `r`, using the
minimum and maximum of all four endpoint products. … `Pos(n, k) :⟺ n ≥ 2 ∧ n L(n, k) > σ(n)` (`eq:pos`)." And Theorem
`thm:three`: "If `n ≥ 5041` has at most three distinct prime factors, then `σ(n) < e^γ n log log n`. … The certificate above
proves `B(5041) > 15/4` by a single integer cross-multiplication. Both logarithms and `e^γ` are increasing or positive on
the relevant domains, so `B(n) ≥ B(5041)`."

The lower end `L(n, k) = (Lp − Lm)/Ld` is a fixed primitive-recursive rational:

* `log n` is `LogI(n/1, r)` (`RobinLogInterval`), with lower end `A₁/B₁`;
* if `A₁ ≥ B₁` (the case `log n ≥ 1`), the double logarithm's lower end is `LogI(A₁/B₁, r)`'s lower end `LLn/LLd`, and
  `L = E_{K_e}(γ_lo) · LLn/LLd`, the lower corner since both factors are nonnegative; otherwise the double logarithm is
  negative, its lower end is `−hi(B₁/A₁)`, and `L = −3 · hi(B₁/A₁)` uses the packet's bound `e^γ ≤ 3` (its intersection with
  `[1, 3]`) for the lower corner;
* `γ_lo = 1/2 + An/Ad` at `t = 2^{r+4} − 1`, `K_γ = 2r + 2` (`RobinGammaInterval`), and `e^γ`'s lower end is
  `E_{K_e}(γ_lo)`, `K_e = 2r + 32` (`RobinExpName`).

`B(n) ≥ B(5041) > 15/4` is derived on these names, uniformly in `n` and `k`, by monotonicity (`lo_mono_le`, `e_mono`) and
nesting (`exp_name`) down to three closed cross-multiplications (`lo5041`, `lo17`, `ev47`):
`lo(5041, K) ≥ lo(5041, 2) ≥ 17/2`, `lo(17/2, 2) ≥ 1067/500`, `γ_lo ≥ 4/7`, `E_5(4/7) ≥ 17707/10000`, and
`(17707/10000)(1067/500) > 15/4`. With `RobinThree.three_core` (`4σ(n) < 15n`) this gives `three_pos`: for primes
`p < q < r` and `n = p^a q^b r^c ≥ 5041`, `Pos(n, k)` for every precision `k`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinThreePos

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Lv L_zero Pv P_succ P_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Nz_zero Nz_succ Lz frac_trans)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval
  (eb eb_eq a_eq loN loD hiN hiD Kp lo_mono_le loD_pos dt st c3)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaInterval (k2 L_one L_two Pv_two An Ad Ad_pos t3 gamma_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinExpName
  (Ev Ed Fv E_zero E_succ F_zero F_succ exp_name e_mono Ed_pos Ed_congr Ev_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinThree (three_core)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Signum (sg sg_zero)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Closed evaluation -/

/-- `a^k` at a numeral exponent, in the ring of differences. -/
theorem pw_lit (a : PTm n) : (k : ℕ) → Groth.ι (Q.mk Γ (pw a (num k))) = Groth.ι (Q.mk Γ a) ^ k
  | 0 => by
    have e := natEq (pw_zero (Γ := Γ) a)
    simp only [LeanProofs.IPRA.Q.mk_one, map_one] at e
    exact e.trans (pow_zero _).symm
  | k + 1 => by
    have e := natEq (pw_succ (Γ := Γ) a (num k))
    simp only [LeanProofs.IPRA.Q.mk_mul, map_mul] at e
    rw [pow_succ, ← pw_lit a k]
    exact e

theorem Nz_two_gen (p s : PTm n) :
    Γ ⊢[PRAAx] Nz k2 p s ≐ num 6 * p * (s * s * (s * s)) + two * (p * p * p) * (s * s) := by
  have n1 : Γ ⊢[PRAAx] Nz (succ zero) p s ≐ two * p * (s * s) := by
    refine (Nz_succ zero p s).eqTrans ?_
    refine withEq (Nz_zero (Γ := Γ) p s) fun e0 => withEq (L_zero (Γ := Γ) (zero : PTm n)) fun e1 =>
      withEq (P_zero (Γ := Γ) p) fun e2 => ?_
    apply deriveNat; ipra_simps; rw [e0, e1, e2]; ring
  refine (Nz_succ (succ zero) p s).eqTrans ?_
  refine withEq n1 fun e0 => withEq (L_one (Γ := Γ) (zero : PTm n)) fun e1 =>
    withEq ((P_succ (Γ := Γ) zero p).eqTrans (congrMul (congrMul (P_zero p) (.eqRefl _)) (.eqRefl _))) fun e2 => ?_
  apply deriveNat; ipra_simps; rw [e0, e1, e2]; ring

/-- The lower end of `LogI` at `K = 2`, symbolically in the reduced argument. -/
theorem lo_k2 (a b : PTm n) :
    Γ ⊢[PRAAx] loN a b k2 ≐ eb a b * num 504 * (num 3 * (st a b * st a b * st a b * st a b * st a b)) +
        (num 6 * dt a b * (st a b * st a b * (st a b * st a b)) + two * (dt a b * dt a b * dt a b) * (st a b * st a b)) *
          num 729 ⋏
      loD a b k2 ≐ num 729 * (num 3 * (st a b * st a b * st a b * st a b * st a b)) := by
  have eNt := natEq (Nz_two_gen (Γ := Γ) (dt a b) (st a b))
  have eN3 := natEq (Nz_two_gen (Γ := Γ) one c3)
  have eL := natEq (L_two (Γ := Γ) (zero : PTm n))
  have eP3 := natEq (Pv_two (Γ := Γ) (c3 : PTm n))
  have ePt := natEq (Pv_two (Γ := Γ) (st a b))
  refine .andI ?_ ?_
  · apply deriveNat; ipra_simps; rw [eNt, eN3, eL, eP3, ePt]; ring
  · apply deriveNat; ipra_simps; rw [eL, eP3, ePt]; ring

/-- `lo(5041, 2) = 1184361528722374280853288/139272992628296954202459 ≈ 8.50389`. -/
theorem lo5041 : Γ ⊢[PRAAx] loN (num 5041) one k2 ≐ num 1184361528722374280853288 ⋏
    loD (num 5041) one k2 ≐ num 139272992628296954202459 := by
  have h1 : Γ ⊢[PRAAx] le one (one : PTm n) := le_refl _
  have h2 : Γ ⊢[PRAAx] le one (num 5041 : PTm n) := by ipra_le 5040
  have p12 := pw_lit (Γ := Γ) (two : PTm n) 12
  have p13 : Groth.ι (Q.mk Γ (pw (two : PTm n) (succ (num 12)))) = Groth.ι (Q.mk Γ (two : PTm n)) ^ 13 :=
    pw_lit (Γ := Γ) (two : PTm n) 13
  have l1 : Γ ⊢[PRAAx] le (one * pw two (num 12)) (num 5041) := by ipra_le 945 with -p12
  have l2 : Γ ⊢[PRAAx] lt (num 5041) (one * pw two (succ (num 12))) := by ipra_le 3150 with p13
  have eE := eb_eq h1 h2 l1 l2
  have EE := natEq eE
  have EP : Groth.ι (Q.mk Γ (pw two (eb (num 5041 : PTm n) one))) = 4096 := by
    have x := natEq (congrAp2 powF eE (.eqRefl (two : PTm n)))
    ipra_simps; rw [x, p12]; norm_num
  have ED : Groth.ι (Q.mk Γ (dt (num 5041 : PTm n) one)) = 945 := by
    have ad := natEq (a_eq (Γ := Γ) h1 h2)
    ipra_simps; rw [EP] at ad; linear_combination -ad
  have v := lo_k2 (Γ := Γ) (num 5041 : PTm n) one
  refine .andI ((Prf.andE₁ v).eqTrans ?_) ((Prf.andE₂ v).eqTrans ?_)
  · apply deriveNat; ipra_simps; rw [EE, EP, ED]; norm_num
  · apply deriveNat; ipra_simps; rw [EP]; norm_num

/-- `lo(17/2, 2) = 182706948864/85589104491 ≈ 2.13470`. -/
theorem lo17 : Γ ⊢[PRAAx] loN (num 17) two k2 ≐ num 182706948864 ⋏ loD (num 17) two k2 ≐ num 85589104491 := by
  have h1 : Γ ⊢[PRAAx] le one (two : PTm n) := by ipra_le 1
  have h2 : Γ ⊢[PRAAx] le two (num 17 : PTm n) := by ipra_le 15
  have p3 := pw_lit (Γ := Γ) (two : PTm n) 3
  have p4 : Groth.ι (Q.mk Γ (pw (two : PTm n) (succ (num 3)))) = Groth.ι (Q.mk Γ (two : PTm n)) ^ 4 :=
    pw_lit (Γ := Γ) (two : PTm n) 4
  have l1 : Γ ⊢[PRAAx] le (two * pw two (num 3)) (num 17) := by ipra_le 1 with -2 * p3
  have l2 : Γ ⊢[PRAAx] lt (num 17) (two * pw two (succ (num 3))) := by ipra_le 14 with 2 * p4
  have eE := eb_eq h1 h2 l1 l2
  have EE := natEq eE
  have EP : Groth.ι (Q.mk Γ (pw two (eb (num 17 : PTm n) two))) = 8 := by
    have x := natEq (congrAp2 powF eE (.eqRefl (two : PTm n)))
    ipra_simps; rw [x, p3]; norm_num
  have ED : Groth.ι (Q.mk Γ (dt (num 17 : PTm n) two)) = 1 := by
    have ad := natEq (a_eq (Γ := Γ) h1 h2)
    ipra_simps; rw [EP] at ad; linear_combination -ad
  have v := lo_k2 (Γ := Γ) (num 17 : PTm n) two
  refine .andI ((Prf.andE₁ v).eqTrans ?_) ((Prf.andE₂ v).eqTrans ?_)
  · apply deriveNat; ipra_simps; rw [EE, EP, ED]; norm_num
  · apply deriveNat; ipra_simps; rw [EP]; norm_num

/-- `E_5(4/7) = 3571304/2016840 ≈ 1.77074`. -/
theorem ev47 : Γ ⊢[PRAAx] Ev (num 5) (num 4) (num 7) ≐ num 3571304 ⋏ Ed (num 5) (num 7) ≐ num 2016840 := by
  have e0 : Γ ⊢[PRAAx] Ev (num 0) (num 4) (num 7) ≐ one := E_zero _ _
  have e1 : Γ ⊢[PRAAx] Ev (num 1) (num 4) (num 7) ≐
      succ (num 0) * num 7 * Ev (num 0) (num 4) (num 7) + pw (num 4) (num 1) := E_succ _ _ _
  have e2 : Γ ⊢[PRAAx] Ev (num 2) (num 4) (num 7) ≐
      succ (num 1) * num 7 * Ev (num 1) (num 4) (num 7) + pw (num 4) (num 2) := E_succ _ _ _
  have e3 : Γ ⊢[PRAAx] Ev (num 3) (num 4) (num 7) ≐
      succ (num 2) * num 7 * Ev (num 2) (num 4) (num 7) + pw (num 4) (num 3) := E_succ _ _ _
  have e4 : Γ ⊢[PRAAx] Ev (num 4) (num 4) (num 7) ≐
      succ (num 3) * num 7 * Ev (num 3) (num 4) (num 7) + pw (num 4) (num 4) := E_succ _ _ _
  have e5 : Γ ⊢[PRAAx] Ev (num 5) (num 4) (num 7) ≐
      succ (num 4) * num 7 * Ev (num 4) (num 4) (num 7) + pw (num 4) (num 5) := E_succ _ _ _
  have f0 : Γ ⊢[PRAAx] Fv (num 0 : PTm n) ≐ one := F_zero
  have f1 : Γ ⊢[PRAAx] Fv (num 1 : PTm n) ≐ succ (num 0) * Fv (num 0) := F_succ _
  have f2 : Γ ⊢[PRAAx] Fv (num 2 : PTm n) ≐ succ (num 1) * Fv (num 1) := F_succ _
  have f3 : Γ ⊢[PRAAx] Fv (num 3 : PTm n) ≐ succ (num 2) * Fv (num 2) := F_succ _
  have f4 : Γ ⊢[PRAAx] Fv (num 4 : PTm n) ≐ succ (num 3) * Fv (num 3) := F_succ _
  have f5 : Γ ⊢[PRAAx] Fv (num 5 : PTm n) ≐ succ (num 4) * Fv (num 4) := F_succ _
  have g0 := natEq e0
  have g1 := natEq e1
  have g2 := natEq e2
  have g3 := natEq e3
  have g4 := natEq e4
  have g5 := natEq e5
  have h0 := natEq f0
  have h1 := natEq f1
  have h2 := natEq f2
  have h3 := natEq f3
  have h4 := natEq f4
  have h5 := natEq f5
  have q1 := pw_lit (Γ := Γ) (num 4 : PTm n) 1
  have q2 := pw_lit (Γ := Γ) (num 4 : PTm n) 2
  have q3 := pw_lit (Γ := Γ) (num 4 : PTm n) 3
  have q4 := pw_lit (Γ := Γ) (num 4 : PTm n) 4
  have q5 := pw_lit (Γ := Γ) (num 4 : PTm n) 5
  have r5 := pw_lit (Γ := Γ) (num 7 : PTm n) 5
  refine .andI ?_ ?_
  · apply deriveNat; ipra_simps; rw [g5, g4, g3, g2, g1, g0, q5, q4, q3, q2, q1]; norm_num
  · apply deriveNat; ipra_simps; rw [h5, h4, h3, h2, h1, h0, r5]; norm_num

/-! ## Generic arithmetic steps (over opaque terms) -/

alias one_le_of_pos := Common.one_le_of_pos

theorem swap_r {a b c : PTm n} (h : Γ ⊢[PRAAx] le a (b * c)) : Γ ⊢[PRAAx] le a (c * b) := by ipra_le sl h

theorem scale1 {x y A B : PTm n} (hx : Γ ⊢[PRAAx] x ≐ num 1184361528722374280853288)
    (hy : Γ ⊢[PRAAx] y ≐ num 139272992628296954202459) (hm : Γ ⊢[PRAAx] le (x * B) (A * y)) :
    Γ ⊢[PRAAx] le (num 17 * B) (two * A) := by
  have ex := natEq hx
  have ey := natEq hy
  have hp : Γ ⊢[PRAAx] y ≐ succ (pred y) := pos_of_one_le (by ipra_le 139272992628296954202458 with ey)
  have c : Γ ⊢[PRAAx] le (y * (num 17 * B)) (y * (two * A)) := by
    ipra_le 2 * sl hm + 1082182763700340264773 * 𝔞 B with 2 * 𝔞 B * ex - 17 * 𝔞 B * ey
  exact mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) c)

theorem scale2 {x y A B : PTm n} (hx : Γ ⊢[PRAAx] x ≐ num 182706948864) (hy : Γ ⊢[PRAAx] y ≐ num 85589104491)
    (hm : Γ ⊢[PRAAx] le (x * B) (A * y)) : Γ ⊢[PRAAx] le (num 1067 * B) (num 500 * A) := by
  have ex := natEq hx
  have ey := natEq hy
  have hp : Γ ⊢[PRAAx] y ≐ succ (pred y) := pos_of_one_le (by ipra_le 85589104490 with ey)
  have c : Γ ⊢[PRAAx] le (y * (num 1067 * B)) (y * (num 500 * A)) := by
    ipra_le 500 * sl hm + 29899940103 * 𝔞 B with 500 * 𝔞 B * ex - 1067 * 𝔞 B * ey
  exact mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) c)

theorem scale3 {x y A B : PTm n} (hx : Γ ⊢[PRAAx] x ≐ num 3571304) (hy : Γ ⊢[PRAAx] y ≐ num 2016840)
    (hm : Γ ⊢[PRAAx] le (x * B) (A * y)) : Γ ⊢[PRAAx] le (num 17707 * B) (num 10000 * A) := by
  have ex := natEq hx
  have ey := natEq hy
  have hp : Γ ⊢[PRAAx] y ≐ succ (pred y) := pos_of_one_le (by ipra_le 2016839 with ey)
  have c : Γ ⊢[PRAAx] le (y * (num 17707 * B)) (y * (num 10000 * A)) := by
    ipra_le 10000 * sl hm + 854120 * 𝔞 B with 10000 * 𝔞 B * ex - 17707 * 𝔞 B * ey
  exact mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) c)

/-- `(17707/10000)(1067/500) > 15/4`. -/
theorem final_comb {X1 Y1 X2 Y2 : PTm n} (he : Γ ⊢[PRAAx] le (num 17707 * X1) (num 10000 * Y1))
    (hl : Γ ⊢[PRAAx] le (num 1067 * X2) (num 500 * Y2)) :
    Γ ⊢[PRAAx] le (num 15 * (X1 * X2)) (num 4 * (Y1 * Y2)) := by
  have m := le_mul_mono he hl
  have c : Γ ⊢[PRAAx] le (num 5000000 * (num 15 * (X1 * X2))) (num 5000000 * (num 4 * (Y1 * Y2))) := by
    ipra_le 4 * sl m + 573476 * 𝔞 (X1 * X2)
  exact mul_le_cancel (d' := num 4999999) c

theorem le_of_17 {A B : PTm n} (h : Γ ⊢[PRAAx] le (num 17 * B) (two * A)) : Γ ⊢[PRAAx] le B A := by
  have c : Γ ⊢[PRAAx] le (two * B) (two * A) := by ipra_le sl h + 15 * 𝔞 B
  exact mul_le_cancel (d' := one) c

theorem gx {A D : PTm n} (h : Γ ⊢[PRAAx] le D (num 14 * A)) : Γ ⊢[PRAAx] le (num 4 * (two * D)) ((D + two * A) * num 7) := by
  ipra_le sl h

/-- `2^{r+4} − 1 ≥ 3`. -/
theorem tg_ge (r : PTm n) : Γ ⊢[PRAAx] le t3 (pred (pw two (num 4 + r))) := by
  have e1 := natEq (pw_add (Γ := Γ) two (num 4) r)
  have e2 := pw_lit (Γ := Γ) (two : PTm n) 4
  have pp := natEq (pw_pos' (Γ := Γ) two_pos' r)
  have e3 := natEq (pw_pos' (Γ := Γ) two_pos' (num 4 + r))
  ipra_le 16 * 𝔞 (pred (pw two r)) + 12 with -e3 + e1 + 𝔞 (pw two r) * e2 + 16 * pp

/-- `σ·Ld < n·Lp` from `4σ < 15n`, `15·Ld ≤ 4·Lp` and `Ld ≥ 1`. -/
theorem pos_comb {s N X Y : PTm n} (h3 : Γ ⊢[PRAAx] lt (two * two * s) (succ two * succ (succ (succ (succ one))) * N))
    (hL : Γ ⊢[PRAAx] le (num 15 * X) (num 4 * Y)) (hX : Γ ⊢[PRAAx] le one X) :
    Γ ⊢[PRAAx] lt (s * X + N * zero) (N * Y) := by
  refine .orE (lt_or_le (s * X + N * zero) (N * Y)) Prf.hyp0 ?_
  let C : List (Fm PTm n) := le (N * Y) (s * X + N * zero) :: Γ
  have c : C ⊢[PRAAx] le (N * Y) (s * X + N * zero) := Prf.hyp0
  have m1 := le_mul_mono (h3.wk : C ⊢[PRAAx] le (succ (two * two * s)) _) (le_refl X)
  have m2 := le_mul_mono (le_refl N) (hL.wk : C ⊢[PRAAx] _)
  have hX' : C ⊢[PRAAx] le one X := hX.wk
  exact lt_irrefl zero _ (by ipra_le 4 * sl c + sl m1 + sl m2 + sl hX')

/-- With `c = 0`, the case split selects the first branch. -/
theorem branch {c : PTm n} (hc : Γ ⊢[PRAAx] c ≐ zero) (X Y Z W : PTm n) :
    Γ ⊢[PRAAx] monus one (sg c) * X ≐ X ⋏ (sg c * Y ≐ zero ⋏ monus one (sg c) * Z + sg c * W ≐ Z) := by
  have s0 : Γ ⊢[PRAAx] sg c ≐ zero := (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hc)).eqTrans sg_zero
  have m1 : Γ ⊢[PRAAx] monus one (sg c) ≐ one := (congrMonus (.eqRefl _) s0).eqTrans (monus_zero _)
  have e0 := natEq s0
  have e1 := natEq m1
  refine .andI ?_ (.andI ?_ ?_)
  · apply deriveNat; ipra_simps; rw [e1]; ring
  · apply deriveNat; ipra_simps; rw [e0]; ring
  · apply deriveNat; ipra_simps; rw [e0, e1]; ring

/-! ## The interval program `L(n, k)` and `Pos(n, k)` -/

/-- `r = k + ℓ(n) + 16`, with the bit length `ℓ(n) = e(n) + 1`. -/
abbrev rr (N k : PTm n) : PTm n := k + succ (eb N one) + num 16
abbrev K1 (N k : PTm n) : PTm n := Kp N one (rr N k)
/-- `log n ≥ A₁/B₁`. -/
abbrev A1 (N k : PTm n) : PTm n := loN N one (K1 N k)
abbrev B1 (N k : PTm n) : PTm n := loD N one (K1 N k)
abbrev K2 (N k : PTm n) : PTm n := Kp (A1 N k) (B1 N k) (rr N k)
/-- `log log n ≥ LLn/LLd` when `A₁ ≥ B₁`. -/
abbrev LLn (N k : PTm n) : PTm n := loN (A1 N k) (B1 N k) (K2 N k)
abbrev LLd (N k : PTm n) : PTm n := loD (A1 N k) (B1 N k) (K2 N k)
abbrev K2' (N k : PTm n) : PTm n := Kp (B1 N k) (A1 N k) (rr N k)
/-- `log log n ≥ −LHn/LHd` when `A₁ < B₁`. -/
abbrev LHn (N k : PTm n) : PTm n := hiN (B1 N k) (A1 N k) (K2' N k)
abbrev LHd (N k : PTm n) : PTm n := hiD (B1 N k) (A1 N k) (K2' N k)
/-- `γ ≥ gN/gD` at `t = 2^{r+4} − 1`, `K_γ = 2r + 2`. -/
abbrev tg (N k : PTm n) : PTm n := pred (pw two (num 4 + rr N k))
abbrev Kg (N k : PTm n) : PTm n := succ (succ (two * rr N k))
abbrev gN (N k : PTm n) : PTm n := Ad (tg N k) (Kg N k) + two * An (tg N k) (Kg N k)
abbrev gD (N k : PTm n) : PTm n := two * Ad (tg N k) (Kg N k)
/-- `e^γ ≥ EN/ED = E_{K_e}(gN/gD)`, `K_e = 2r + 32`. -/
abbrev Ke (N k : PTm n) : PTm n := num 32 + two * rr N k
abbrev EN (N k : PTm n) : PTm n := Ev (Ke N k) (gN N k) (gD N k)
abbrev ED (N k : PTm n) : PTm n := Ed (Ke N k) (gD N k)
/-- The case test: `1` iff `A₁ < B₁`. -/
abbrev cnd (N k : PTm n) : PTm n := sg (monus (B1 N k) (A1 N k))
/-- `L(n, k) = (Lp − Lm)/Ld`. -/
abbrev Lp (N k : PTm n) : PTm n := monus one (cnd N k) * (EN N k * LLn N k)
abbrev Lm (N k : PTm n) : PTm n := cnd N k * (c3 * LHn N k)
abbrev Ld (N k : PTm n) : PTm n := monus one (cnd N k) * (ED N k * LLd N k) + cnd N k * LHd N k

/-- `eq:pos`: `Pos(n, k) :⟺ n ≥ 2 ∧ n L(n, k) > σ(n)`, cleared: `σ(n)·Ld + n·Lm < n·Lp`. -/
def Pos (N k : PTm n) : Fm PTm n := le two N ⋏ lt (sig N * Ld N k + N * Lm N k) (N * Lp N k)

/-! ## `B(n) > 15/4` for `n ≥ 5041`, and `thm:three` -/

/-- For `n ≥ 5041` with `4σ(n) < 15n`: `Pos(n, k)` for every `k`. -/
theorem pos_of {N : PTm n} (hN : Γ ⊢[PRAAx] le (num 5041) N)
    (h3 : Γ ⊢[PRAAx] lt (two * two * sig N) (succ two * succ (succ (succ (succ one))) * N)) (k : PTm n) :
    Γ ⊢[PRAAx] Pos N k := by
  have h1 : Γ ⊢[PRAAx] le one (one : PTm n) := le_refl _
  have h5041 : Γ ⊢[PRAAx] le one (num 5041 : PTm n) := by ipra_le 5040
  have hN1 : Γ ⊢[PRAAx] le one N := by ipra_le sl hN + 5040
  -- `log n ≥ lo(5041, 2) ≥ 17/2`
  have hK1 : Γ ⊢[PRAAx] le k2 (K1 N k) := by ipra_le 𝔞 (rr N k) + 𝔞 (eb N one) + 2
  have m1 := lo_mono_le (a := num 5041) (b := one) (a' := N) (b' := one) h1 h5041 h1 hN1 (by ipra_le sl hN) hK1
  have v1 := lo5041 (Γ := Γ)
  have c1 := scale1 (Prf.andE₁ v1) (Prf.andE₂ v1) m1
  have hB1 : Γ ⊢[PRAAx] le one (B1 N k) := one_le_of_pos (loD_pos h1 hN1 (K1 N k))
  have hAB : Γ ⊢[PRAAx] le (B1 N k) (A1 N k) := le_of_17 c1
  -- `log log n ≥ lo(17/2, 2) ≥ 1067/500`
  have h2 : Γ ⊢[PRAAx] le one (two : PTm n) := by ipra_le 1
  have h17 : Γ ⊢[PRAAx] le two (num 17 : PTm n) := by ipra_le 15
  have hK2 : Γ ⊢[PRAAx] le k2 (K2 N k) := by ipra_le 𝔞 (rr N k) + 𝔞 (eb (A1 N k) (B1 N k)) + 2
  have m2 := lo_mono_le (a := num 17) (b := two) (a' := A1 N k) (b' := B1 N k) h2 h17 hB1 hAB (swap_r c1) hK2
  have v2 := lo17 (Γ := Γ)
  have c2 := scale2 (Prf.andE₁ v2) (Prf.andE₂ v2) m2
  -- `γ ≥ 4/7`
  have ht := tg_ge (Γ := Γ) (rr N k)
  have et := (eq_add_of_le ht).eqSymm
  have g := gamma_lower (Γ := Γ) (monus (tg N k) t3) (two * rr N k)
  have g' : Γ ⊢[PRAAx] le (Ad (tg N k) (Kg N k)) (num 14 * An (tg N k) (Kg N k)) :=
    le_congr (congrAp2 _ et (.eqRefl _)) (congrMul (.eqRefl _) (congrAp2 _ et (.eqRefl _))) g
  have hx := gx g'
  -- `e^γ ≥ E_{K_e}(4/7) ≥ E_5(4/7) ≥ 17707/10000`
  have hq7 : Γ ⊢[PRAAx] (num 7 : PTm n) ≐ succ (pred (num 7)) := pos_of_one_le (by ipra_le 6)
  have h47 : Γ ⊢[PRAAx] le (num 4 : PTm n) (num 7) := by ipra_le 3
  have hKe : Γ ⊢[PRAAx] le (num 5) (Ke N k) := by ipra_le 27 + 2 * 𝔞 (rr N k)
  have eKe := (eq_add_of_le hKe).eqSymm
  have nest := Prf.andE₁ (Prf.andE₁ (exp_name (Γ := Γ) hq7 h47 (num 5) (monus (Ke N k) (num 5))))
  have nest' := le_congr (congrMul (.eqRefl _) (Ed_congr _ eKe)) (congrMul (Ev_congr _ _ eKe) (.eqRefl _)) nest
  have em := e_mono (p := num 4) (q := num 7) (p' := gN N k) (q' := gD N k) hx (Ke N k)
  have t1 := frac_trans (Ed_pos hq7 (Ke N k)) nest' em
  have v3 := ev47 (Γ := Γ)
  have c3' := scale3 (Prf.andE₁ v3) (Prf.andE₂ v3) t1
  -- `L(n, k) ≥ 15/4`
  have fc := final_comb c3' c2
  have hgD : Γ ⊢[PRAAx] gD N k ≐ succ (pred (gD N k)) := pos_mul two_pos' (Ad_pos _ _)
  have hX : Γ ⊢[PRAAx] le one (ED N k * LLd N k) :=
    one_le_of_pos (pos_mul (Ed_pos hgD (Ke N k)) (loD_pos hB1 hAB (K2 N k)))
  have pc := pos_comb h3 fc hX
  have br := branch hAB (EN N k * LLn N k) (c3 * LHn N k) (ED N k * LLd N k) (LHd N k)
  refine .andI (by ipra_le sl hN + 5039) ?_
  exact lt_congr (congrAdd (congrMul (.eqRefl _) (Prf.andE₂ (Prf.andE₂ br)).eqSymm)
      (congrMul (.eqRefl _) (Prf.andE₁ (Prf.andE₂ br)).eqSymm))
    (congrMul (.eqRefl _) (Prf.andE₁ br).eqSymm) pc

/-- `thm:three` in the certificate form `eq:pos`: for primes `p < q < r` and exponents `a, b, c`, if
`n = p^a q^b r^c ≥ 5041` then `Pos(n, k)` holds at every precision `k`. -/
theorem three_pos {p q r : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hq : Γ ⊢[PRAAx] prime q) (hr : Γ ⊢[PRAAx] prime r)
    (hpq : Γ ⊢[PRAAx] lt p q) (hqr : Γ ⊢[PRAAx] lt q r) (a b c : PTm n)
    (hN : Γ ⊢[PRAAx] le (num 5041) (pw p a * pw q b * pw r c)) (k : PTm n) :
    Γ ⊢[PRAAx] Pos (pw p a * pw q b * pw r c) k :=
  pos_of hN (three_core hp hq hr hpq hqr a b c) k

end LeanProofs.IPRA.AnalyticNumberTheory.RobinThreePos
