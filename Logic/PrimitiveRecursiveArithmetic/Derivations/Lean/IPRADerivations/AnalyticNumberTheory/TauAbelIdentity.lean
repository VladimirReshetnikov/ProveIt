import IPRADerivations.AnalyticNumberTheory.DivisorSwapP
import IPRADerivations.AnalyticNumberTheory.TauLogAbel
import IPRADerivations.AnalyticNumberTheory.ConvSummatory

/-!
# The divisor count and the Abel identity for `T(y)` (`pnt_ipra_constructive_2026-11-14`, `sb:divisor-approx`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:divisor-approx`:
"`D(y) = Σ_{n≤y} τ(n)`" and "for `T(y) = Σ_{n≤y} τ(n) log n`, finite partial summation gives
`T(y) = D(y) log y − ∫_1^y D(t)/t dt`". With `τ = 𝟏 * 𝟏` (`DirichletLeibniz.conv one one`), the harmonic logarithm
`u_n = F λ_K(n)` and the Abel sum `A(N) = Σ_{n<N} D(n)(x_{n+1} − x_n)` of `TauLogAbel` (`x_n = S(Kn)`):

* `tau_sum`: `Σ_{n≤N} τ(n) = D(N) = S(N, N)` (`ConvSummatory.conv_summatory` with `a = b = 𝟏`);
* `tau_succ`: `D(N + 1) = D(N) + τ(N + 1)`;
* `abel_tau`: `Σ_{n≤N} τ(n) u_n + A(N) = D(N) u_N` — the finite partial summation, by one QF induction.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.TauAbelIdentity

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U U_paired U_zero U_increment_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.TauLogAbel (As A_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv cv_at)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (bS inst2_bS RB RB_at conv_summatory)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_ones)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## `Σ τ = D` -/

theorem bS_one : bS (one : PTm 2) = one := by simp [bS]

theorem inst2_one' (k y : PTm n) : inst2 (one : PTm 2) k y = one := by simp [inst2]

/-- `Σ_{n≤N} τ(n) = D(N) = Σ_{i<N} ⌊N/(i+1)⌋`. -/
theorem tau_sum (N y : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (cvF one one)) (succ N) y ≐ S N N := by
  have cs := conv_summatory (Γ := Γ) one one N y
  have rg : Γ ⊢[PRAAx] succ N ≐ one + N := by ipra_ring
  have sp := sum_split (Γ := Γ) (RB one one) one N (pairT N y)
  have h0 : Γ ⊢[PRAAx] ap2 (sumF (RB one one)) one (pairT N y) ≐ zero := by
    refine (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) (RB_at _ _ _ _ _)).eqTrans ?_)
    exact (congrAdd (.eqRefl _) (zero_mul_l (zero_mul_l sg_zero _) _)).eqTrans (add_zero _)
  have tl : Γ ⊢[PRAAx] ap2 (sumF (offB (RB one one))) N (pairT one (pairT N y)) ≐ S N N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_offB, inst2_h, shift_pairT, shift_pairT]
    have e1 : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
        fstT (pairT (Syn.shift (one : PTm n)) (pairT (Syn.shift N) (Syn.shift y))) + var 0 ≐ succ (var 0) :=
      (congrAdd (fst_pair _ _) (.eqRefl _)).eqTrans (by
        rw [show Syn.shift (one : PTm n) = one by simp [Syn.shift]]; ipra_ring)
    refine (congrInst2 _ e1 (snd_pair _ _)).eqTrans ((RB_at _ _ _ _ _).eqTrans ?_)
    rw [inst2_one']
    simp only [ConvSummatory.Bs, bS_one]
    refine (congrMul ((congrMul (sg_succ _) (.eqRefl _)).eqTrans (by ipra_ring))
      (sum_ones _ _)).eqTrans (one_mul _)
  have e1 := natEq cs; have e2 := natEq (congrAp2 (Γ := Γ) (sumF (RB one one)) rg (.eqRefl (pairT N y)))
  ipra_lc e1 + e2 + natEq sp + natEq h0 + natEq tl

/-- `D(N + 1) = D(N) + τ(N + 1)`. -/
theorem tau_succ (N y : PTm n) : Γ ⊢[PRAAx] S (succ N) (succ N) ≐ S N N + conv one one (succ N) y := by
  have s := sum_succ' (Γ := Γ) (cvF one one) (succ N) y
  rw [inst2_cvF] at s
  ipra_lc -natEq (tau_sum (succ N) y) + natEq s + natEq (tau_sum N y)

/-! ## The Abel identity -/

/-- `τ(n) u_n` with parameter `z = (K, F)`. -/
abbrev tuB : PTm 2 := ap2 (sumF (cvB one one)) (succ (var 0)) (pairT (var 0) (var 1)) *
  monus (S (fstT (var 1) * var 0) (sndT (var 1))) (S (fstT (var 1)) (sndT (var 1)))

theorem inst2_tuB (k z : PTm n) : inst2 tuB k z =
    conv one one k z * monus (S (fstT z * k) (sndT z)) (S (fstT z) (sndT z)) := by simp [inst2]

theorem tuB_at (k K F : PTm n) :
    Γ ⊢[PRAAx] inst2 tuB k (pairT K F) ≐ conv one one k (pairT K F) * U k K F := by
  rw [inst2_tuB]
  exact congrMul (.eqRefl _) (U_paired k K F)

/-- The invariant `Σ_{n≤N} τ(n) u_n + A(N) = D(N) u_N`. -/
abbrev Ab (N K F : PTm n) : Fm PTm n :=
  ap2 (sumF tuB) (succ N) (pairT K F) + As N K F ≐ S N N * U N K F

theorem ab_zero (K F : PTm n) : Γ ⊢[PRAAx] Ab zero K F := by
  have t0 := (tuB_at (Γ := Γ) zero K F).eqTrans
    ((congrMul (.eqRefl _) (U_zero K F)).eqTrans (mul_zero _))
  ipra_lc natEq (sum_succ' (Γ := Γ) tuB zero (pairT K F)) + natEq (sum_zero (Γ := Γ) tuB (pairT K F)) + natEq t0 +
    natEq (sum_zero (Γ := Γ) TauLogAbel.AB (pairT K F)) - 𝔞 (U zero K F) * natEq (sum_zero (Γ := Γ) hB (zero : PTm n))

theorem ab_step {N K F : PTm n} (ih : Γ ⊢[PRAAx] Ab N K F) : Γ ⊢[PRAAx] Ab (succ N) K F := by
  have d := natEq (tau_succ (Γ := Γ) N (pairT K F))
  have key := U_increment_mul (Γ := Γ) N K F (S N N)
    ((congrAp2 (sumF hB) Prf.hyp0 Prf.hyp0).eqTrans (sum_zero _ _))
  ipra_lc natEq (sum_succ' (Γ := Γ) tuB (succ N) (pairT K F)) + natEq (tuB_at (Γ := Γ) (succ N) K F) +
    natEq (A_succ (Γ := Γ) N K F) + natEq ih - 𝔞 (U (succ N) K F) * d + natEq key

/-- Variables `0 = N`, `1 = K`, `2 = F`. -/
private abbrev abF : Fm PTm 3 := Ab (var 0) (var 1) (var 2)

private theorem ab₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] abF := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact ab_zero _ _
  · exact ab_step Prf.hyp0

/-- The finite partial summation: `Σ_{n≤N} τ(n) u_n + A(N) = D(N) u_N`. -/
theorem abel_tau (N K F : PTm n) : Γ ⊢[PRAAx] Ab N K F := by
  have i := inst (Γ := Γ) ab₀ (![N, K, F] : Fin 3 → PTm n)
  simpa using i

end LeanProofs.IPRA.AnalyticNumberTheory.TauAbelIdentity
