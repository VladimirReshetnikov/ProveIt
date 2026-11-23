import IPRADerivations.Analysis.GaussianEulerExponentialSubstitutionIntegrand
import IPRADerivations.Analysis.GaussianEulerCompactAdditivity
import IPRADerivations.Analysis.GaussianPositiveExponentialMajorant

/-!
# Uniform finite compact bounds for the original exponential pullback

The literal coefficient z/B has norm at most R, so the actual exponent
observations lie in R*J+T, where J is the checked compact logarithm
radius. The genuine original finite exponential at its own input query
and cutoff is bounded by 3^(R*J+T), independently of sample precision.
The original unshifted Euler evaluator has its corresponding old bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerExponentialSubstitutionCompactBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerExponentialSubstitutionIntegrand (exponentF exponentData exponentialF data radius logarithmClock evaluatorF fixedData)
open GaussianEulerExponentCompactBounds (source)
open GaussianCompactLogarithmBounds (domain)
open GaussianGammaEulerHeadShift (shifted)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (bounded)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def exponentRadius (R E T : PTm n) : PTm n := R*GaussianCompactLogarithmBounds.radius E T+T
def majorant (R E T : PTm n) : PTm n := pw (num 3) (exponentRadius R E T)
def eulerMajorant (R E T : PTm n) : PTm n := pw (num 3) (GaussianEulerExponentCompactBounds.radius R E T)

@[simp] theorem subst_exponentRadius {m : ℕ} (σ : Fin n → PTm m) (R E T : PTm n) :
    Syn.subst σ (exponentRadius R E T) = exponentRadius (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by simp [exponentRadius]
@[simp] theorem subst_majorant {m : ℕ} (σ : Fin n → PTm m) (R E T : PTm n) :
    Syn.subst σ (majorant R E T) = majorant (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by simp [majorant]
@[simp] theorem subst_eulerMajorant {m : ℕ} (σ : Fin n → PTm m) (R E T : PTm n) :
    Syn.subst σ (eulerMajorant R E T) = eulerMajorant (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by simp [eulerMajorant]

theorem original_exponent_bound (p z R B E T a b : PTm n) (h : Γ ⊢[PRAAx] source z R B E)
    (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    bounded (ap2 exponentF p (exponentData z B a b)) (exponentRadius R E T) one := by
  have product := GaussianRationalReciprocal.bounded_product _ _ R one (GaussianCompactLogarithmBounds.radius E T) one
    (le_refl one) (le_refl one) (GaussianGammaEulerHead.fraction_disk z R B h.andE₁ h.andE₂.andE₂)
    (GaussianCompactLogarithmBounds.sample_bound (logarithmClock p z B a b) a b E T h.andE₂.andE₁ ht)
  have negative := GaussianRationalReciprocal.bounded_negative _ T one (le_refl one)
    (GaussianEulerExponentCompactBounds.fraction_bound a b T ht.andE₁.andE₂ ht.andE₂.andE₂)
  have sum := GaussianRationalReciprocal.bounded_sum _ _ _ (one*one) T one
    (GaussianRationalHorner.positive_product _ _ (le_refl one) (le_refl one)) (le_refl one) product negative
  exact GaussianRationalReciprocal.bound_congr (GaussianEulerExponentialSubstitutionIntegrand.exponent_at p z B a b).eqSymm
    (by unfold exponentRadius; ipra_ring) (by ipra_ring) sum

theorem original_exponential_bound (p z R B E T a b : PTm n) (h : Γ ⊢[PRAAx] source z R B E)
    (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    bounded (ap2 exponentialF p (data z B a b)) (majorant R E T) one := by
  let r := radius z B a b
  let q := GaussianRadiusExponentialName.inputPrecision r p
  let K := GaussianRadiusExponentialName.index r p
  have finite := GaussianPositiveExponentialMajorant.disk_bound _ (exponentRadius R E T) K
    (original_exponent_bound q z R B E T a b h ht)
  exact GaussianRationalReciprocal.bound_congr
    (GaussianRadiusExponentialName.sample_at exponentF r p (exponentData z B a b)).eqSymm (.eqRefl _) (.eqRefl _) finite

/-- Arbitrary raw time codes are decoded by the unchanged original
PR3 program. No equality with pair(fst t,snd t) is assumed. -/
theorem evaluator_raw_at (p t z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    ap3 evaluatorF p t (fixedData z B) ≐ ap2 exponentialF p (data z B (fstT t) (sndT t)) :=
  (GaussianEulerCompactModulus.evaluator_raw_at p t (shifted z B) B).eqTrans
    (congrAp2 exponentialF (.eqRefl p) (GaussianEulerExponentialSubstitutionIntegrand.shifted_data z B (fstT t) (sndT t) hB))

theorem original_evaluator_bound (p t z R B E T : PTm n) (h : Γ ⊢[PRAAx] source z R B E)
    (ht : Γ ⊢[PRAAx] domain (fstT t) (sndT t) E T) : Γ ⊢[PRAAx]
    bounded (ap3 evaluatorF p t (fixedData z B)) (majorant R E T) one :=
  GaussianRationalReciprocal.bound_congr (evaluator_raw_at p t z B h.andE₁).eqSymm (.eqRefl _) (.eqRefl _)
    (original_exponential_bound p z R B E T (fstT t) (sndT t) h ht)

theorem original_inside_bound (p t z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B a C E T)
    (ht : Γ ⊢[PRAAx] GaussianCompactRiemannName.inside a C E t) : Γ ⊢[PRAAx]
    bounded (ap3 evaluatorF p t (fixedData z B)) (majorant R E T) one :=
  original_evaluator_bound p t z R B E T h.andE₁
    (GaussianEulerCompactAdditivity.domain_of_inside t a C E T h.andE₂.andE₁ h.andE₁.andE₂.andE₁ h.andE₂.andE₂ ht)

theorem original_Euler_evaluator_bound (p t z R B E T : PTm n) (h : Γ ⊢[PRAAx] source z R B E)
    (ht : Γ ⊢[PRAAx] domain (fstT t) (sndT t) E T) : Γ ⊢[PRAAx]
    bounded (ap3 GaussianEulerIntegrandName.evaluatorF p t (GaussianEulerIntegrandName.fixedData z B)) (eulerMajorant R E T) one := by
  let X := GaussianEulerIntegrandName.exponentData z B (fstT t) (sndT t)
  let r := GaussianEulerIntegrandName.radius z B (fstT t) (sndT t)
  have finite := GaussianPositiveExponentialMajorant.disk_bound _ (GaussianEulerExponentCompactBounds.radius R E T)
    (GaussianRadiusExponentialName.index r p)
    (GaussianEulerExponentCompactBounds.exponent_bound (GaussianRadiusExponentialName.inputPrecision r p) z R B E T (fstT t) (sndT t) h ht)
  have exactSample := (GaussianEulerCompactModulus.evaluator_raw_at (Γ := Γ) p t z B).eqTrans
    (GaussianRadiusExponentialName.sample_at GaussianEulerIntegrandName.exponentF r p X)
  exact GaussianRationalReciprocal.bound_congr exactSample.eqSymm (.eqRefl _) (.eqRefl _) finite

theorem actual_original_pure_exponential_uniform_compact_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 1) (var 2) (var 3) (var 4) ⋏ domain (var 6) (var 7) (var 4) (var 5)) ⟶
      bounded (ap2 exponentialF (var 0) (data (var 1) (var 3) (var 6) (var 7))) (majorant (var 2) (var 4) (var 5)) one) :=
  closeUniv 8 (.impI (original_exponential_bound _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_pure_exponential_raw_time_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 2) (var 3) (var 4) (var 5) ⋏ domain (fstT (var 1)) (sndT (var 1)) (var 5) (var 6)) ⟶
      bounded (ap3 evaluatorF (var 0) (var 1) (fixedData (var 2) (var 4))) (majorant (var 3) (var 5) (var 6)) one) :=
  closeUniv 7 (.impI (original_evaluator_bound _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerExponentialSubstitutionCompactBound
