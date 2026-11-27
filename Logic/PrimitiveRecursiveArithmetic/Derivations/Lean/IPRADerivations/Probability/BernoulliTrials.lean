import IPRADerivations.Probability.WeakLaw
import IPRADerivations.Foundations.BoundedReflection

/-!
# The binomial law as Bernoulli trials

Packet: `probability/expected_value_ipra_2026-11-16`, Proposition `prop:binomial`. For a rational
success probability `p = a/(a + c)`, the Bernoulli law on `{0, 1}` has weights `w(0) = c`, `w(1) = a`
(parameter `⟨a, c⟩`) and success indicator `X(i) = [i = 1]`. `Bin(r, p)` is the law of the number of
successes `S_r` in `r` independent trials, i.e. of the sample sum under the `r`-fold product law of
`Probability/ProductPower` (`T = ∑_t P_r`, `A = ∑_t P_r S_r`, `B = ∑_t P_r S_r²`):

* `bern_total`, `bern_success`: `∑_{i<2} w_i = c + a`, `∑_{i<2} w_i X_i = a`;
* `binomial_mean` (`prop:binomial`): `(c + a) A = r a T` and `T = (c + a)^r`, i.e. `E[S_r] = r p`;
* `binomial_variance`: `(c + a)² T B + r a² T² = (c + a)² A² + r (c + a) a T²`, i.e.
  `Var(S_r) = r p (1 − p)` (Monte Carlo law for the indicator `X`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.BernoulliTrials

open_ipra
open LeanProofs.IPRA.Probability.ProductPower (Tt At Bt total_pow)
open LeanProofs.IPRA.Probability.WeakLaw (monte_carlo)
open LeanProofs.IPRA.Probability.Expectation (inst2_mul')

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Bernoulli weights `w(i, ⟨a, c⟩) = [i = 0] c + [i = 1] a`. -/
abbrev bw : PTm 2 := eqb (var 0) zero * sndT (var 1) + eqb (var 0) one * fstT (var 1)
/-- The success indicator `[i = 1]`. -/
abbrev bX : PTm 2 := eqb (var 0) one

theorem inst2_bw (i x : PTm n) : inst2 bw i x = eqb i zero * sndT x + eqb i one * fstT x := by simp [inst2]
theorem inst2_bX (i x : PTm n) : inst2 bX i x = eqb i one := by simp [inst2]

theorem eqb_00 : Γ ⊢[PRAAx] eqb (zero : PTm n) zero ≐ one := eqb_of_eq (.eqRefl _)
theorem eqb_11 : Γ ⊢[PRAAx] eqb (one : PTm n) one ≐ one := eqb_of_eq (.eqRefl _)
theorem eqb_01 : Γ ⊢[PRAAx] eqb (zero : PTm n) one ≐ zero := eqb_zero_of_lt (le_refl _)
theorem eqb_10 : Γ ⊢[PRAAx] eqb (one : PTm n) zero ≐ zero := eqb_zero_of_gt (le_refl _)

/-- `∑_{i<2} f(i) = f(0) + f(1)`. -/
theorem sum_two (f : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF f) two x ≐ inst2 f zero x + inst2 f one x :=
  (sum_succ' _ _ _).eqTrans (congrAdd ((sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) (.eqRefl _)).eqTrans
    (zero_add _))) (.eqRefl _))

theorem bern_total (a c : PTm n) : Γ ⊢[PRAAx] ap2 (sumF bw) two (pairT a c) ≐ c + a := by
  refine (sum_two _ _).eqTrans ?_
  rw [inst2_bw, inst2_bw]
  refine (congrAdd (congrAdd (congrMul eqb_00 (snd_pair _ _)) (congrMul eqb_01 (.eqRefl _)))
    (congrAdd (congrMul eqb_10 (.eqRefl _)) (congrMul eqb_11 (fst_pair _ _)))).eqTrans ?_
  ipra_ring

theorem bern_success (a c : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (bw * bX)) two (pairT a c) ≐ a := by
  refine (sum_two _ _).eqTrans ?_
  rw [inst2_mul', inst2_mul', inst2_bw, inst2_bw, inst2_bX, inst2_bX]
  refine (congrAdd (congrMul (congrAdd (congrMul eqb_00 (.eqRefl _)) (congrMul eqb_01 (.eqRefl _))) eqb_01)
    (congrMul (congrAdd (congrMul eqb_10 (.eqRefl _)) (congrMul eqb_11 (fst_pair _ _))) eqb_11)).eqTrans ?_
  ipra_ring

theorem bX_idem (x : PTm n) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift two) ⟶
      (inst2 bX (var 0) (Syn.shift x) * inst2 bX (var 0) (Syn.shift x) ≐ inst2 bX (var 0) (Syn.shift x))) := by
  refine .allI (.impI ?_)
  rw [inst2_bX]
  exact Common.mul_self_eq_of_zero_or_one (Common.eqb_zero_or_one _ _)

alias two_pos := Common.two_pos

/-- `prop:binomial`: `E[S_r] = r p` for `S_r ∼ Bin(r, a/(a + c))`: `(c + a) A = r a T`, `T = (c + a)^r`. -/
theorem binomial_mean (a c r : PTm n) :
    Γ ⊢[PRAAx] ((c + a) * At bw bX r two (pairT a c) ≐ r * a * Tt bw r two (pairT a c)) ⋏
      (Tt bw r two (pairT a c) ≐ pw (c + a) r) := by
  have m := Prf.andE₁ (monte_carlo (Γ := Γ) bw bX (x := pairT a c) two_pos (bX_idem _) r)
  have W := bern_total (Γ := Γ) a c; have S := bern_success (Γ := Γ) a c
  refine .andI ((congrMul W.eqSymm (.eqRefl _)).eqTrans (m.eqTrans (congrMul (congrMul (.eqRefl _) S) (.eqRefl _)))) ?_
  exact (total_pow bw two_pos r).eqTrans (congrAp2 powF (.eqRefl _) W)

/-- `Var(S_r) = r p (1 − p)`: `(c + a)² T B + r a² T² = (c + a)² A² + r (c + a) a T²`. -/
theorem binomial_variance (a c r : PTm n) :
    Γ ⊢[PRAAx] (c + a) * (c + a) * (Tt bw r two (pairT a c) * Bt bw bX r two (pairT a c)) +
        r * (a * a) * (Tt bw r two (pairT a c) * Tt bw r two (pairT a c)) ≐
      (c + a) * (c + a) * (At bw bX r two (pairT a c) * At bw bX r two (pairT a c)) +
        r * (c + a) * a * (Tt bw r two (pairT a c) * Tt bw r two (pairT a c)) := by
  have m := Prf.andE₂ (monte_carlo (Γ := Γ) bw bX (x := pairT a c) two_pos (bX_idem _) r)
  have W := bern_total (Γ := Γ) a c; have S := bern_success (Γ := Γ) a c
  refine .eqTrans ?_ (m.eqTrans (congrAdd (congrMul (congrMul W W) (.eqRefl _))
    (congrMul (congrMul (congrMul (.eqRefl _) W) S) (.eqRefl _))))
  exact (congrAdd (congrMul (congrMul W W) (.eqRefl _)) (congrMul (congrMul (.eqRefl _) (congrMul S S)) (.eqRefl _))).eqSymm
