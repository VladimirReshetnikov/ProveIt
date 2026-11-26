import IPRADerivations.Analysis.Euler.Integration.GaussianEulerDecayIncrement
import IPRADerivations.Analysis.Integration.GaussianCompactRiemannSplit
import IPRADerivations.Analysis.Polynomials.GaussianRationalCoefficientScaling
import IPRADerivations.Analysis.Euler.GaussianEulerDampedTimeRate
import IPRADerivations.Analysis.Euler.GaussianEulerExponentCompactBounds
import IPRADerivations.Analysis.Gamma.GaussianGammaHalfEulerSquare

/-!
# Exact algebra for the weighted Binet exponential antiderivative

The scaled primitive at the physical time u is
`(2*a*u + 2*b - a) * exp(-a*u/b)`. Its finite first-order difference
is the weighted integrand times the panel width, with one explicit
quadratic correction from the changing linear coefficient.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBinetWeightedExponentialAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner
  (qmul represents qmul_represents ofGaussian_represents ofGaussian_canonical canonical_unique represents_congr positive_product)
open GaussianRationalMetric (bounded qsub qsub_canonical qsub_represents)
open GaussianRationalReciprocal (bounded_negative qone_represents_scaled)
open GaussianRationalSyntheticDivision (qone qsub_congr rescale_to)
open GaussianRootAlgebra (sub equal_refl equal_of_values re_sub im_sub re_mul im_mul re_scale im_scale re_one im_one)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def tagWeight (j N : PTm n) : PTm n := qsub (fraction one two) (fraction j N)
def primitiveCoefficient (a b j N : PTm n) : PTm n := qsub (fraction (two*a*j+two*b*N) N) (fraction a one)
def leftCoefficient (a b : PTm n) : PTm n := qsub (fraction (two*b) one) (fraction a one)
def rightCoefficient (a b : PTm n) : PTm n := fraction (a+two*b) one
def panelScale (a b N : PTm n) : PTm n := fraction (two*a*a) (b*N)
def integrationScale (a b : PTm n) : PTm n := fraction (two*a*a) b
def inverseScale (a b : PTm n) : PTm n := fraction b (two*a*a)
def correction (a b N : PTm n) : PTm n := fraction (two*a*a) (b*N*N)
def cap (a b : PTm n) : PTm n := (two*a+two*b)+a

@[simp] theorem subst_tagWeight {m : ℕ} (σ : Fin n → PTm m) (j N : PTm n) :
    Syn.subst σ (tagWeight j N) = tagWeight (Syn.subst σ j) (Syn.subst σ N) := by simp [tagWeight,one,two]
@[simp] theorem subst_primitiveCoefficient {m : ℕ} (σ : Fin n → PTm m) (a b j N : PTm n) :
    Syn.subst σ (primitiveCoefficient a b j N) =
      primitiveCoefficient (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ j) (Syn.subst σ N) := by simp [primitiveCoefficient,one,two]
@[simp] theorem subst_leftCoefficient {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (leftCoefficient a b) = leftCoefficient (Syn.subst σ a) (Syn.subst σ b) := by simp [leftCoefficient,one,two]
@[simp] theorem subst_rightCoefficient {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (rightCoefficient a b) = rightCoefficient (Syn.subst σ a) (Syn.subst σ b) := by simp [rightCoefficient,one,two]
@[simp] theorem subst_panelScale {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (panelScale a b N) = panelScale (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [panelScale,two]
@[simp] theorem subst_inverseScale {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (inverseScale a b) = inverseScale (Syn.subst σ a) (Syn.subst σ b) := by simp [inverseScale,two]
@[simp] theorem subst_cap {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (cap a b) = cap (Syn.subst σ a) (Syn.subst σ b) := by simp [cap,two]

private theorem rescaled_fraction (a B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] represents (fraction a B) (scale (a*N) oneCode) (B*N) :=
  represents_congr (.eqRefl _) (by
    apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring)
    (.eqRefl _) (rescale_to _ _ B N (B*N) (ofGaussian_represents _ _ hB) (.eqRefl _))

private theorem coefficient_rep (a b j N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] represents (primitiveCoefficient a b j N)
      (sub (scale (two*a*j+two*b*N) oneCode) (scale (a*N) oneCode)) N :=
  qsub_represents _ _ _ _ _ hN (ofGaussian_represents _ _ hN)
    (represents_congr (.eqRefl _) (equal_refl _) (one_mul _) (rescaled_fraction a one N (le_refl one)))

private theorem weight_rep (j N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] represents (tagWeight j N) (sub (scale N oneCode) (scale (two*j) oneCode)) (two*N) := by
  have h := positive_product two N (le_succ_self (Γ := Γ) one) hN
  have l : Γ ⊢[PRAAx] represents (fraction one two) (scale N oneCode) (two*N) := represents_congr (.eqRefl _) (by
    apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring) (.eqRefl _)
    (rescaled_fraction one two N (le_succ_self one))
  have r : Γ ⊢[PRAAx] represents (fraction j N) (scale (two*j) oneCode) (two*N) := represents_congr (.eqRefl _) (by
    apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring) (mul_comm N two)
    (rescaled_fraction j N two hN)
  exact qsub_represents _ _ _ _ _ h l r

theorem local_coefficient (a b j N : PTm n) (hB : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] qsub (qmul (primitiveCoefficient a b (succ j) N) (qsub qone (fraction a (b*N))))
        (primitiveCoefficient a b j N) ≐ qsub (qmul (panelScale a b N) (tagWeight j N)) (correction a b N) := by
  let D := b*N
  let E := N*D
  let T := E*two
  let u := sub (scale (two*a*j+two*b*N) oneCode) (scale (a*N) oneCode)
  let w := sub (scale D oneCode) (scale a oneCode)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hB hN
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hN hD
  have hT : Γ ⊢[PRAAx] le one T := positive_product _ _ hE (le_succ_self one)
  have rf : Γ ⊢[PRAAx] represents (qsub qone (fraction a D)) w D :=
    qsub_represents _ _ _ _ _ hD (qone_represents_scaled D) (ofGaussian_represents _ _ hD)
  have p := qmul_represents _ _ _ _ _ _ hN hD (coefficient_rep a b (succ j) N hN) rf
  have old := rescale_to (primitiveCoefficient a b j N) u N D E (coefficient_rep a b j N hN) (.eqRefl _)
  have lhs := rescale_to _ _ E two T (qsub_represents _ _ _ _ _ hE p old) (.eqRefl _)
  have raw := qmul_represents (panelScale a b N) _ (scale (two*a*a) oneCode) _ D (two*N) hD
    (positive_product _ _ (le_succ_self one) hN) (ofGaussian_represents _ _ hD) (weight_rep j N hN)
  have main := represents_congr (.eqRefl _) (equal_refl _)
    (by dsimp only [D,T,E]; ipra_ring : Γ ⊢[PRAAx] D*(two*N) ≐ T) raw
  have r := represents_congr (.eqRefl _) (equal_refl _)
    (by dsimp only [D,T,E]; ipra_ring : Γ ⊢[PRAAx] (b*N*N)*two ≐ T)
    (rescaled_fraction (two*a*a) (b*N*N) two (positive_product _ _ hD hN))
  have rhs := qsub_represents _ _ _ _ _ hT main r
  apply canonical_unique _ _ _ _ (qsub_canonical _ _) (qsub_canonical _ _) hT (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values <;>
    simp only [u,w,D,re_sub,im_sub,re_mul,im_mul,re_scale,im_scale,re_one,im_one] <;>
    ipra_simps <;> ring

theorem left_read (a b N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] primitiveCoefficient a b zero N ≐ leftCoefficient a b :=
  by
    have frac : Γ ⊢[PRAAx] fraction (two*a*zero+two*b*N) N ≐ fraction (N*(two*b)) (N*one) :=
      GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (by ipra_ring)
    have reduced : Γ ⊢[PRAAx] fraction (N*(two*b)) (N*one) ≐ fraction (two*b) one :=
      GaussianCompactRiemannSplit.fraction_cancel N (two*b) one hN (le_refl one)
    exact qsub_congr (frac.eqTrans reduced) (.eqRefl (fraction a one))

theorem right_read (a b N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] primitiveCoefficient a b N N ≐ rightCoefficient a b := by
  have rhs : Γ ⊢[PRAAx] represents (rightCoefficient a b) (scale ((a+two*b)*N) oneCode) N :=
    represents_congr (.eqRefl _) (equal_refl _) (one_mul N)
    (rescaled_fraction (a+two*b) one N (le_refl one))
  apply canonical_unique _ _ _ _ (qsub_canonical _ _) (ofGaussian_canonical _ _ (le_refl one)) hN (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := coefficient_rep a b N N hN)
  apply equal_of_values <;> simp only [re_sub,im_sub,re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring

theorem coefficient_bound (a b j N : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] bounded (primitiveCoefficient a b j N) (cap a b) one := by
  have top : Γ ⊢[PRAAx] le (two*a*j+two*b*N) ((two*a+two*b)*N) := by ipra_le 2*𝔞(a)*sl hj
  have ha := GaussianEulerExponentCompactBounds.fraction_bound (Γ := Γ) a one a (le_refl one)
    (le_congr (.eqRefl _) (by ipra_ring) (le_refl a))
  apply GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ (le_refl one)
    (GaussianEulerExponentCompactBounds.fraction_bound _ _ _ hN top)
    (bounded_negative _ _ _ (le_refl one) ha)

theorem scale_factorization (a b N : PTm n) (hB : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] qmul (integrationScale a b) (fraction one N) ≐ panelScale a b N :=
  (GaussianEulerDampedTimeRate.fraction_product _ _ _ _ hB hN).eqTrans
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (.eqRefl _))

theorem inverse_product (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qmul (inverseScale a b) (integrationScale a b) ≐ qone :=
  GaussianGammaHalfEulerSquare.inverse_fraction b (two*a*a) hb
    (positive_product _ _ (positive_product _ _ (le_succ_self one) ha) ha)

end LeanProofs.IPRA.Analysis.GaussianBinetWeightedExponentialAlgebra
