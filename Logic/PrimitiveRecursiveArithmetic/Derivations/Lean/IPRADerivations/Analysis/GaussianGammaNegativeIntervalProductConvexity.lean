import IPRADerivations.Analysis.GaussianGammaNegativeIntervalProductSign
import IPRADerivations.Analysis.GaussianGammaEulerRationalHeadConvexity
import IPRADerivations.Analysis.GaussianEulerDecayFactorBounds

/-!
# Weighted log-concavity of the original signed shift product

In the coordinate a/b in (0,1), the original signed product has positive
factors a/b and j-a/b. Each factor preserves the same weighted center.
Weighted AM–GM and quantifier-free induction give the powered inequality
for the finite product, with the original rational encoding restored at
the end.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalProductConvexity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open GaussianCompactRiemannName (fraction_congr)
open GaussianDominantPairAlgebra (radius_power)
open GaussianEulerDampedTimeRate (fraction_product)
open GaussianEulerDecayFactorBounds (fraction_is_radius_point)
open GaussianFactorBudget (power_positive)
open GaussianGammaEulerRationalHeadConvexity (barycenter weight)
open GaussianGammaNegativeIntervalProductSign (magnitude magnitudeBody signedProduct fraction_readback)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalReciprocal (power powerF)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianStirlingMultiplicativeBoundsLog (fractions_order)
open RationalArgmin (rationalLE rationalLE_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private def numerator (j a b : PTm n) : PTm n := magnitude a b j*a
private def denominator (j b : PTm n) : PTm n := pw b j*b

theorem center_guard (a b c r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hc : Γ ⊢[PRAAx] le one c)
    (hab : Γ ⊢[PRAAx] lt a b) (hcb : Γ ⊢[PRAAx] lt c b) :
    Γ ⊢[PRAAx] le one (barycenter a c r s) ⋏ lt (barycenter a c r s) (weight r s*b) := by
  refine .andI ?_ ?_
  · unfold barycenter
    ipra_le 𝔞 (succ r)*sl ha+𝔞 s*sl hc+𝔞 r+𝔞 s
  · change Γ ⊢[PRAAx] le (succ (barycenter a c r s)) (weight r s*b)
    unfold barycenter weight
    ipra_le 𝔞 (succ r)*sl hab+𝔞 s*sl hcb+𝔞 r+𝔞 s

theorem factor_affine (a b c r s j : PTm n) (hab : Γ ⊢[PRAAx] le a b) (hcb : Γ ⊢[PRAAx] le c b) :
    Γ ⊢[PRAAx] succ r*monus (b*succ j) a+s*monus (b*succ j) c ≐
      monus ((weight r s*b)*succ j) (barycenter a c r s) := by
  have h₁ : Γ ⊢[PRAAx] le a (b*succ j) := by ipra_le sl hab+𝔞 b*𝔞 j
  have h₂ : Γ ⊢[PRAAx] le c (b*succ j) := by ipra_le sl hcb+𝔞 b*𝔞 j
  have h₃ : Γ ⊢[PRAAx] le (barycenter a c r s) ((weight r s*b)*succ j) := by
    unfold barycenter weight
    ipra_le 𝔞 (succ r)*sl h₁+𝔞 s*sl h₂
  have e₁ := natEq (eq_add_of_le h₁)
  have e₂ := natEq (eq_add_of_le h₂)
  have e₃ := natEq (eq_add_of_le h₃)
  unfold barycenter weight at e₃ ⊢
  apply deriveNat
  ipra_simps
  linear_combination e₃-(𝔞 r+1)*e₁-𝔞 s*e₂

private theorem numerator_zero (a b : PTm n) : Γ ⊢[PRAAx] numerator zero a b ≐ a :=
  (congrMul (prod_zero magnitudeBody (pairT a b)) (.eqRefl a)).eqTrans (one_mul a)

private theorem numerator_step (j a b : PTm n) :
    Γ ⊢[PRAAx] numerator (succ j) a b ≐ numerator j a b*monus (b*succ j) a := by
  have factor : Γ ⊢[PRAAx] inst2 magnitudeBody j (pairT a b) ≐ monus (b*succ j) a := by
    simpa [inst2, magnitudeBody] using
      congrMonus (congrMul (snd_pair (Γ := Γ) a b) (.eqRefl (succ j))) (fst_pair a b)
  have fold : Γ ⊢[PRAAx] magnitude a b (succ j) ≐ magnitude a b j*monus (b*succ j) a :=
    (prod_succ magnitudeBody j (pairT a b)).eqTrans (congrMul (.eqRefl _) factor)
  exact (congrMul fold (.eqRefl a)).eqTrans (by unfold numerator; ipra_ring)

private def numeratorOrder (j a b c r s : PTm n) : Fm PTm n :=
  le (pw (pw (weight r s) (weight r s)) (succ j) * (pw (numerator j a b) (succ r) * pw (numerator j c b) s))
    (pw (numerator j (barycenter a c r s) (weight r s*b)) (weight r s))

@[simp] private theorem subst_numeratorOrder {m : ℕ} (σ : Fin n → PTm m) (j a b c r s : PTm n) :
    (numeratorOrder j a b c r s).subst σ = numeratorOrder (Syn.subst σ j) (Syn.subst σ a)
      (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ r) (Syn.subst σ s) := by
  simp [numeratorOrder, numerator, weight, barycenter]

private theorem numerator_order_zero (a b c r s : PTm n) : Γ ⊢[PRAAx] numeratorOrder zero a b c r s := by
  let w := weight r s
  exact le_congr
    (congrMul (pw_one (pw w w)).eqSymm
      (congrMul (congrAp2 powF (.eqRefl _) (numerator_zero a b).eqSymm)
        (congrAp2 powF (.eqRefl _) (numerator_zero c b).eqSymm)))
    (congrAp2 powF (.eqRefl _) (numerator_zero (barycenter a c r s) (w*b)).eqSymm)
    (WeightedAMGM.amgm r s a c)

private theorem numerator_power_step (j a b k : PTm n) :
    Γ ⊢[PRAAx] pw (numerator (succ j) a b) k ≐ pw (numerator j a b) k*pw (monus (b*succ j) a) k :=
  (congrAp2 powF (.eqRefl k) (numerator_step j a b)).eqTrans (pw_mul_base _ _ _)

private theorem numerator_order_succ (j a b c r s : PTm n) (hab : Γ ⊢[PRAAx] le a b)
    (hcb : Γ ⊢[PRAAx] le c b) (ih : Γ ⊢[PRAAx] numeratorOrder j a b c r s) :
    Γ ⊢[PRAAx] numeratorOrder (succ j) a b c r s := by
  let w := weight r s
  let x := barycenter a c r s
  let d := w*b
  let u := monus (b*succ j) a
  let v := monus (b*succ j) c
  have factor := le_congr (.eqRefl _) (congrAp2 powF (.eqRefl w) (factor_affine a b c r s j hab hcb))
    (WeightedAMGM.amgm (Γ := Γ) r s u v)
  have expand : Γ ⊢[PRAAx]
      pw (pw w w) (succ (succ j)) * (pw (numerator (succ j) a b) (succ r) * pw (numerator (succ j) c b) s) ≐
        (pw (pw w w) (succ j) * (pw (numerator j a b) (succ r) * pw (numerator j c b) s)) *
        (pw w w * (pw u (succ r) * pw v s)) :=
    (congrMul (pw_succ _ _) (congrMul (numerator_power_step j a b (succ r))
      (numerator_power_step j c b s))).eqTrans (by ipra_ring)
  exact le_congr expand.eqSymm (numerator_power_step j x d w).eqSymm (le_mul_mono ih factor)

private theorem numerator_order (j a b c r s : PTm n) (hab : Γ ⊢[PRAAx] le a b)
    (hcb : Γ ⊢[PRAAx] le c b) : Γ ⊢[PRAAx] numeratorOrder j a b c r s := by
  have ab : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift, Syn.shift] using hab.shift
  have cb : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift c) (Syn.shift b) := by simpa [Fm.shift, Syn.shift] using hcb.shift
  have all : Γ ⊢[PRAAx] .all (numeratorOrder (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c)
      (Syn.shift r) (Syn.shift s)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_numeratorOrder, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using
        numerator_order_zero (Γ := Γ) a b c r s
    · simpa only [subst_numeratorOrder, Syn.subst_var, Syn.repl_zero, subst_repl_shift] using
        numerator_order_succ _ _ _ _ _ _ ab.wk cb.wk Prf.hyp0
  simpa only [subst_numeratorOrder, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using all.allE j

private theorem denominator_power_scale (j b w : PTm n) : Γ ⊢[PRAAx]
    pw (denominator j (w*b)) w ≐ pw (pw w w) (succ j)*pw (denominator j b) w := by
  have exchange : Γ ⊢[PRAAx] pw (pw w (succ j)) w ≐ pw (pw w w) (succ j) :=
    (pw_mul w (succ j) w).eqTrans ((congrAp2 powF (mul_comm (succ j) w) (.eqRefl w)).eqTrans
      (pw_mul w w (succ j)).eqSymm)
  have scale : Γ ⊢[PRAAx] denominator j (w*b) ≐ pw w (succ j)*denominator j b := by
    unfold denominator
    exact (congrMul (pw_mul_base _ _ _) (.eqRefl _)).eqTrans
      ((by ipra_ring : Γ ⊢[PRAAx] pw w j*pw b j*(w*b) ≐ (pw w j*w)*(pw b j*b)).eqTrans
        (congrMul (pw_succ _ _).eqSymm (.eqRefl _)))
  exact (congrAp2 powF (.eqRefl w) scale).eqTrans
    ((pw_mul_base _ _ _).eqTrans (congrMul exchange (.eqRefl _)))

private theorem power_fraction (a b k : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    power (fraction a b) k ≐ fraction (pw a k) (pw b k) :=
  (congrAp2 powerF (.eqRefl k) (fraction_is_radius_point a b hb)).eqTrans
    ((radius_power a b k hb).eqTrans (fraction_is_radius_point _ _ (power_positive b k hb)).eqSymm)

theorem powered_order (a b c N r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hc : Γ ⊢[PRAAx] le one c)
    (hab : Γ ⊢[PRAAx] lt a b) (hcb : Γ ⊢[PRAAx] lt c b) : Γ ⊢[PRAAx]
    rationalLE (fstT (qmul (power (signedProduct a b N) (succ r)) (power (signedProduct c b N) s)))
      (fstT (power (signedProduct (barycenter a c r s) (weight r s*b) N) (weight r s))) := by
  let j := succ N
  let w := weight r s
  let x := barycenter a c r s
  let d := w*b
  let A := pw (numerator j a b) (succ r)*pw (numerator j c b) s
  let C := pw (numerator j x d) w
  let B := denominator j b
  let E := pw B (succ r)*pw B s
  let D := pw (denominator j d) w
  let T := pw (pw w w) (succ j)
  have hb := le_trans ha (le_of_lt hab)
  have hx := center_guard a b c r s ha hc hab hcb
  have hd := le_trans hx.andE₁ (le_of_lt hx.andE₂)
  have hB : Γ ⊢[PRAAx] le one B := positive_product _ _ (power_positive b j hb) hb
  have hC : Γ ⊢[PRAAx] le one (denominator j d) := positive_product _ _ (power_positive d j hd) hd
  have he : Γ ⊢[PRAAx] le one E := positive_product _ _ (power_positive B (succ r) hB) (power_positive B s hB)
  have hw : Γ ⊢[PRAAx] w ≐ succ r+s := by unfold w weight; ipra_ring
  have eqD : Γ ⊢[PRAAx] D ≐ T*E :=
    (denominator_power_scale j b w).eqTrans (congrMul (.eqRefl T)
      ((congrAp2 powF hw (.eqRefl B)).eqTrans (pw_add _ _ _)))
  have expand : Γ ⊢[PRAAx] D*A ≐ (T*A)*E :=
    (congrMul eqD (.eqRefl A)).eqTrans (by ipra_ring)
  have clear : Γ ⊢[PRAAx] le (D*A) (C*E) :=
    le_congr expand.eqSymm (.eqRefl _)
      (mul_le_mul_right E (numerator_order j a b c r s (le_of_lt hab) (le_of_lt hcb)))
  have order := fractions_order A E C D he (power_positive _ _ hC) clear
  have left := (congrAp2 powerF (.eqRefl (succ r)) (fraction_readback a b N ha hab)).eqTrans
    (power_fraction (numerator j a b) B (succ r) hB)
  have right := (congrAp2 powerF (.eqRefl s) (fraction_readback c b N hc hcb)).eqTrans
    (power_fraction (numerator j c b) B s hB)
  have middle := (congrAp2 powerF (.eqRefl w) (fraction_readback x d N hx.andE₁ hx.andE₂)).eqTrans
    (power_fraction (numerator j x d) (denominator j d) w hC)
  have product := (qmul_congr left right).eqTrans
    (fraction_product _ _ _ _ (power_positive B (succ r) hB) (power_positive B s hB))
  exact rationalLE_congr (congrFst product).eqSymm (congrFst middle).eqSymm order

theorem actual_signed_negative_interval_product_weighted_order_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((le one (var 0) ⋏ lt (var 0) (var 1)) ⋏ (le one (var 2) ⋏ lt (var 2) (var 1)) ⟶
        rationalLE
          (fstT (qmul (power (signedProduct (var 0) (var 1) (var 3)) (succ (var 4)))
            (power (signedProduct (var 2) (var 1) (var 3)) (var 5))))
          (fstT (power (signedProduct (barycenter (var 0) (var 2) (var 4) (var 5))
            (weight (var 4) (var 5)*var 1) (var 3)) (weight (var 4) (var 5))))) :=
  closeUniv 6 (.impI (powered_order _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalProductConvexity
