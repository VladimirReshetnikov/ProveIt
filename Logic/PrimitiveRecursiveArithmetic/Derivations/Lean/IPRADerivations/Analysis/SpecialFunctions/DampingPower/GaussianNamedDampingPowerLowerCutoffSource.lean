import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerLowerPointwise
import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerCompact
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.Tails.GaussianEulerLowerTailRowBound

/-!
# Native lower cutoff source for named damping

The same actual affine name and the same power-root endpoint geometry
supply the modulus and endpoint observations used for the lower tail.
The damping parameters remain fixed primitive-recursive names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerLowerCutoffSource

open_ipra
open GaussianNamedDampingPowerCompact (evaluatorF fixedData lipschitz sampled_modulus)
open GaussianNamedDampingPowerLowerPointwise (original_pointwise_bound)
open GaussianGammaIntegralCutoffs (etaDen top eta_den_positive top_positive)
open GaussianGammaCompactCutoffGeometry (lowerWidth)
open GaussianEulerLowerTailRootGrid (rootNumerator rootDenominator timeNumerator timeDenominator)
open GaussianEulerLowerTailLocalComparison (rightTime)
open GaussianEulerLowerTailPartition (totalWidth root_right_guard)
open GaussianCompactRiemannName (sampledModulus sampled_modulus_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (F G : PR 2) (z Rz B A x y C₀ C R₀ R : PTm n) : Fm PTm n :=
  GaussianEulerNamedLowerTail.source z Rz B A ⋏
    (GaussianNamedPositiveLogarithm.source F x C₀ C ⋏ GaussianNamedPositiveLogarithm.source G y R₀ R)

ipra_subst source

theorem compact_source (F G : PR 2) (z Rz B A x y C₀ C R₀ R p q : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B A x y C₀ C R₀ R) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    GaussianNamedDampingPowerCompact.source F G z Rz B x y C₀ C R₀ R one (lowerWidth p q A) (etaDen q A Rz) (top q A Rz) :=
  .andI (GaussianGammaCompactCutoffSplit.lower_source z Rz B p q A
    (GaussianEulerNamedLowerTail.split_source z Rz B p q A hs.andE₁ hpq)) hs.andE₂

private theorem pow_time_domain (i N p q A Rz : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hpq : Γ ⊢[PRAAx] le p q) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain
      (pw (rootNumerator (succ i) N p q) A) (pw (rootDenominator N q A Rz) A) (etaDen q A Rz) (top q A Rz) := by
  let a := rootNumerator (succ i) N p q
  let b := rootDenominator N q A Rz
  let E := etaDen q A Rz
  let T := top q A Rz
  have bounds := root_right_guard i N p q A Rz hN hpq hi
  have ha := GaussianPolynomialPerturbation.power_positive (Γ := Γ) a A bounds.andE₁
  have hb := GaussianPolynomialPerturbation.power_positive (Γ := Γ) b A (le_trans bounds.andE₁ bounds.andE₂)
  have up := pw_le_pw A bounds.andE₂
  have low₀ : Γ ⊢[PRAAx] le (pw N A) (pw a A) := pw_le_pw A (le_add_right N _)
  have low : Γ ⊢[PRAAx] le (pw b A) (E*pw a A) :=
    le_congr ((mul_comm (pw N A) E).eqTrans (GaussianEulerLowerTailRootGrid.time_denominator N q A Rz).eqSymm)
      (mul_comm (pw a A) E) (mul_le_mul_right E low₀)
  have grow : Γ ⊢[PRAAx] le (pw b A) (T*pw b A) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (pw b A) (top_positive q A Rz))
  exact .andI (.andI ha hb) (.andI low (le_trans up grow))

private theorem at_pair (F G : PR 2) (s z B x y a b : PTm n) :
    Γ ⊢[PRAAx] ap3 (evaluatorF F G) s (pairT a b) (fixedData z B x y) ≐
      ap2 (GaussianNamedDampingPowerIntegrand.nameF F G) s (GaussianNamedDampingPowerIntegrand.data F G z B x y a b) := by
  let t := pairT a b
  let e {m : ℕ} := @GaussianNamedDampingPowerIntegrand.data m F G
  let body : PTm 6 := e (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
  have transport : Γ ⊢[PRAAx] e z B x y (fstT t) (sndT t) ≐ e z B x y a b := by
    have eq := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) body (σ := ![z,B,x,y,fstT t,sndT t]) (σ' := ![z,B,x,y,a,b]) (fun i => by
      fin_cases i
      exact .eqRefl _
      exact .eqRefl _
      exact .eqRefl _
      exact .eqRefl _
      exact fst_pair a b
      exact snd_pair a b)
    have left : Syn.subst ![z,B,x,y,fstT t,sndT t] body = e z B x y (fstT t) (sndT t) := by
      simp only [body,e,GaussianNamedDampingPowerIntegrand.subst_data,Syn.subst_var]
      rfl
    have right : Syn.subst ![z,B,x,y,a,b] body = e z B x y a b := by
      simp only [body,e,GaussianNamedDampingPowerIntegrand.subst_data,Syn.subst_var]
      rfl
    rw [left,right] at eq
    exact eq
  exact (GaussianNamedDampingPowerCompact.evaluator_at F G s t z B x y).eqTrans (congrAp2 _ (.eqRefl _) transport)

theorem right_bound (F G : PR 2) (i s N p q k z Rz B x y C₀ C R₀ R : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B (succ k) x y C₀ C R₀ R)
    (hN : Γ ⊢[PRAAx] le one N) (hpq : Γ ⊢[PRAAx] le p q) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    bounded (ap3 (evaluatorF F G) s (rightTime i N p q (succ k) Rz) (fixedData z B x y))
      (pw (rootDenominator N q (succ k) Rz) k*unit s+pw (rootNumerator (succ i) N p q) k)
      (pw (rootNumerator (succ i) N p q) k*unit s) := by
  let A := succ k
  let a := rootNumerator (succ i) N p q
  let b := rootDenominator N q A Rz
  let E := etaDen q A Rz
  let T := top q A Rz
  have bounds := root_right_guard i N p q A Rz hN hpq hi
  have low : Γ ⊢[PRAAx] GaussianEulerLowerPowerOrder.source z Rz B A a b :=
    .andI hs.andE₁.andE₂ (.andI (.andI bounds.andE₁ (le_trans bounds.andE₁ bounds.andE₂)) bounds.andE₂)
  have chart : Γ ⊢[PRAAx] GaussianNamedDampingPowerChart.source F G x y C₀ C R₀ R E T (pw a A) (pw b A) :=
    .andI hs.andE₂.andE₁ (.andI hs.andE₂.andE₂ (.andI (eta_den_positive q A Rz) (pow_time_domain i N p q A Rz hN hpq hi)))
  have e := pred_succ (Γ := Γ) k
  exact bound_congr (at_pair F G s z B x y (pw a A) (pw b A)).eqSymm
    (congrAdd (congrMul (congrAp2 powF e (.eqRefl b)) (.eqRefl _)) (congrAp2 powF e (.eqRefl a)))
    (congrMul (congrAp2 powF e (.eqRefl a)) (.eqRefl _))
    (original_pointwise_bound F G s z Rz B A a b x y C₀ C R₀ R E T low chart)

theorem rescaled_modulus (F G : PR 2) (N p q k z Rz B x y C₀ C R₀ R : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B (succ k) x y C₀ C R₀ R)
    (hN : Γ ⊢[PRAAx] le one N) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    sampledModulus (evaluatorF F G) (timeNumerator zero N p q (succ k)) (totalWidth N p q (succ k))
      (timeDenominator N q (succ k) Rz) (lipschitz Rz C R (etaDen q (succ k) Rz) (top q (succ k) Rz)) (fixedData z B x y) := by
  let A := succ k
  let E := etaDen q A Rz
  let W := lowerWidth p q A
  let T := top q A Rz
  let L := lipschitz Rz C R E T
  let K := pw N A
  have hK : Γ ⊢[PRAAx] le one K := GaussianPolynomialPerturbation.power_positive N A hN
  have mod := GaussianCompactIntervalRescaling.rescaled_modulus (evaluatorF F G) K one W E L (fixedData z B x y) hK
    (sampled_modulus F G z Rz B x y C₀ C R₀ R one W E T (compact_source F G z Rz B A x y C₀ C R₀ R p q hs hpq))
  have width := GaussianEulerLowerTailRootGrid.time_width (Γ := Γ) N p q A
  have ha : Γ ⊢[PRAAx] K*one ≐ timeNumerator zero N p q A :=
    (by ipra_ring : Γ ⊢[PRAAx] K*one ≐ K).eqTrans (GaussianEulerLowerTailRootGrid.time_first N p q A).eqSymm
  have hW : Γ ⊢[PRAAx] K*W ≐ totalWidth N p q A := (mul_comm _ _).eqTrans width.eqSymm
  have hE : Γ ⊢[PRAAx] K*E ≐ timeDenominator N q A Rz :=
    (mul_comm _ _).eqTrans (GaussianEulerLowerTailRootGrid.time_denominator N q A Rz).eqSymm
  exact sampled_modulus_congr ha hW hE (.eqRefl _) (.eqRefl _) mod

theorem actual_named_lower_cutoff_right_observations_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 15
      (source F G (var 6) (var 7) (var 8) (succ (var 5)) (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) ⟶
        le one (var 2) ⟶ le (var 3) (var 4) ⟶ lt (var 0) (var 2) ⟶
        bounded (ap3 (evaluatorF F G) (var 1) (rightTime (var 0) (var 2) (var 3) (var 4) (succ (var 5)) (var 7))
          (fixedData (var 6) (var 8) (var 9) (var 10)))
          (pw (rootDenominator (var 2) (var 4) (succ (var 5)) (var 7)) (var 5)*unit (var 1)+
            pw (rootNumerator (succ (var 0)) (var 2) (var 3) (var 4)) (var 5))
          (pw (rootNumerator (succ (var 0)) (var 2) (var 3) (var 4)) (var 5)*unit (var 1))) :=
  closeUniv 15 (.impI (.impI (.impI (.impI (right_bound F G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerLowerCutoffSource
