import IPRADerivations.Analysis.GaussianEulerSquareTimeGeometry

/-!
# Explicit raw and retimed observation rates for the quadratic Jacobian

The original Jacobian client multiplies the actual Euler observation
at p by the exact rational Jacobian. Its observation errors therefore
carry the factor 2*c*T. The explicit Fast query pays that factor on
each side independently, without changing the raw evaluator or any
finite-cell identity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSquareJacobianRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerSquareTimeGeometry (source lowerDenominator upperEndpoint majorant)
open GaussianCompactLogarithmBounds (domain)
open GaussianRationalQuadratureSquareCells (jacobian timeMap)
open GaussianRationalQuadratureDilation (pullData)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive rate_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

abbrev rawF : PR 3 := GaussianRationalQuadratureSquareJacobian.jacobianF GaussianEulerIntegrandName.evaluatorF
def rawData (z B c d : PTm n) : PTm n := pullData c d (GaussianEulerIntegrandName.fixedData z B)
def rawSample (p z B c d a b : PTm n) : PTm n := ap3 rawF p (pairT a b) (rawData z B c d)
def amplification (T c : PTm n) : PTm n := two*c*T
def lipschitz (R E T c d : PTm n) : PTm n := two*c*majorant R E T c d+
  amplification T c*GaussianEulerCompactModulus.lipschitz R (lowerDenominator d E) (upperEndpoint c T)*(two*c*T)
def rawNumerator (p q R E T c d A D : PTm n) : PTm n :=
  (lipschitz R E T c d*A)*(unit p*unit q)+amplification T c*D*(unit p+unit q)
def query (p T c : PTm n) : PTm n := GaussianFastValueCut.exponent (amplification T c) p

@[simp] theorem subst_rawData {m : ℕ} (σ : Fin n → PTm m) (z B c d : PTm n) :
    Syn.subst σ (rawData z B c d) = rawData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ c) (Syn.subst σ d) := by simp [rawData]
@[simp] theorem subst_rawSample {m : ℕ} (σ : Fin n → PTm m) (p z B c d a b : PTm n) :
    Syn.subst σ (rawSample p z B c d a b) = rawSample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ c) (Syn.subst σ d) (Syn.subst σ a) (Syn.subst σ b) := by simp [rawSample]
@[simp] theorem subst_amplification {m : ℕ} (σ : Fin n → PTm m) (T c : PTm n) :
    Syn.subst σ (amplification T c) = amplification (Syn.subst σ T) (Syn.subst σ c) := by simp [amplification]
@[simp] theorem subst_lipschitz {m : ℕ} (σ : Fin n → PTm m) (R E T c d : PTm n) :
    Syn.subst σ (lipschitz R E T c d) = lipschitz (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ c) (Syn.subst σ d) := by simp [lipschitz]
@[simp] theorem subst_query {m : ℕ} (σ : Fin n → PTm m) (p T c : PTm n) :
    Syn.subst σ (query p T c) = query (Syn.subst σ p) (Syn.subst σ T) (Syn.subst σ c) := by simp [query]

theorem raw_sample_at (p z B c d a b : PTm n) : Γ ⊢[PRAAx]
    rawSample p z B c d a b ≐ qmul (jacobian c d (pairT a b))
      (GaussianEulerIntegrandName.sample p z B (c*a*a) (d*b*b)) := by
  have time : Γ ⊢[PRAAx] timeMap c d (pairT a b) ≐ pairT (c*a*a) (d*b*b) :=
    congrPairT (congrMul (congrMul (.eqRefl _) (fst_pair _ _)) (fst_pair _ _))
      (congrMul (congrMul (.eqRefl _) (snd_pair _ _)) (snd_pair _ _))
  exact (GaussianRationalQuadratureSquareJacobian.jacobian_at GaussianEulerIntegrandName.evaluatorF p (pairT a b) c d
    (GaussianEulerIntegrandName.fixedData z B)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (congrAp3 _ (.eqRefl _) time (.eqRefl _)))

theorem raw_decoded_at (p t z B c d : PTm n) : Γ ⊢[PRAAx]
    ap3 rawF p t (rawData z B c d) ≐ rawSample p z B c d (fstT t) (sndT t) := by
  let u := pairT (fstT t) (sndT t)
  have j : Γ ⊢[PRAAx] jacobian c d u ≐ jacobian c d t :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (congrMul (.eqRefl _) (fst_pair _ _))
      (congrMul (.eqRefl _) (snd_pair _ _))
  have tm : Γ ⊢[PRAAx] timeMap c d u ≐ timeMap c d t :=
    congrPairT (congrMul (congrMul (.eqRefl _) (fst_pair _ _)) (fst_pair _ _))
      (congrMul (congrMul (.eqRefl _) (snd_pair _ _)) (snd_pair _ _))
  have same := (GaussianRationalQuadratureSquareJacobian.jacobian_at (Γ := Γ) GaussianEulerIntegrandName.evaluatorF p u c d
    (GaussianEulerIntegrandName.fixedData z B)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr j (congrAp3 _ (.eqRefl _) tm (.eqRefl _)))
  exact (GaussianRationalQuadratureSquareJacobian.jacobian_at GaussianEulerIntegrandName.evaluatorF p t c d
    (GaussianEulerIntegrandName.fixedData z B)).eqTrans same.eqSymm

theorem raw_observations (p q z R B E T c d a b u v A D : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E c d) (ha : Γ ⊢[PRAAx] domain a b E T) (hu : Γ ⊢[PRAAx] domain u v E T)
    (hD : Γ ⊢[PRAAx] le one D) (near : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction u v) A D) : Γ ⊢[PRAAx]
    distanceBounded (rawSample p z B c d a b) (rawSample q z B c d u v)
      (rawNumerator p q R E T c d A D) (rateDenominator D p q) := by
  let L := GaussianEulerCompactModulus.lipschitz R (lowerDenominator d E) (upperEndpoint c T)
  let J := amplification T c
  let M := majorant R E T c d
  let V := rateDenominator D p q
  have hV := denominator_positive D p q hD
  have ha' := GaussianEulerSquareTimeGeometry.mapped_domain a b E T c d h.andE₂.andE₁ h.andE₂.andE₂ ha
  have hu' := GaussianEulerSquareTimeGeometry.mapped_domain u v E T c d h.andE₂.andE₁ h.andE₂.andE₂ hu
  have mapped := GaussianEulerSquareTimeGeometry.mapped_distance a b u v E T c d A D h.andE₂.andE₂ ha hu hD near
  have rate := GaussianEulerCompactModulus.original_rate z R B (lowerDenominator d E) (upperEndpoint c T)
    (c*a*a) (d*b*b) (c*u*u) (d*v*v) (two*c*T*A) D
    (.andI (GaussianEulerSquareTimeGeometry.mapped_source z R B E c d h) (.andI ha' (.andI hu' (.andI hD mapped))))
  have euler : Γ ⊢[PRAAx] distanceBounded (GaussianEulerIntegrandName.sample p z B (c*a*a) (d*b*b))
      (GaussianEulerIntegrandName.sample q z B (c*u*u) (d*v*v)) (rateNumerator (L*(two*c*T*A)) D p q) V :=
    distance_congr (GaussianEulerIntegrandName.sample_at p z B _ _).eqSymm
      (GaussianEulerIntegrandName.sample_at q z B _ _).eqSymm (.eqRefl _) (.eqRefl _)
      (rate_at _ _ _ _ _ _ p q rate)
  have jac := GaussianEulerSquareTimeGeometry.jacobian_distance a b u v c d A D h.andE₂.andE₂ ha.andE₁.andE₂ hu.andE₁.andE₂ hD near
  have first : Γ ⊢[PRAAx] distanceBounded (jacobian c d (pairT a b)) (jacobian c d (pairT u v))
      ((two*c*A)*(unit p*unit q)) V :=
    distance_radius_mono _ _ _ _ _ _ hD hV (le_of_eq_add (d := zero) (by dsimp only [V,rateDenominator]; ipra_ring)) jac
  have product := GaussianNameArithmetic.product_distance (jacobian c d (pairT a b)) (jacobian c d (pairT u v))
    (GaussianEulerIntegrandName.sample p z B (c*a*a) (d*b*b)) (GaussianEulerIntegrandName.sample q z B (c*u*u) (d*v*v))
    ((two*c*A)*(unit p*unit q)) (rateNumerator (L*(two*c*T*A)) D p q) V M J hV first euler
    (GaussianEulerSquareTimeGeometry.original_mapped_observation_bound p z R B E T c d a b h ha)
    (GaussianEulerSquareTimeGeometry.jacobian_bound u v E T c d h.andE₂.andE₂ hu)
  exact distance_congr (raw_sample_at p z B c d a b).eqSymm (raw_sample_at q z B c d u v).eqSymm
    (by dsimp only [rawNumerator,lipschitz,L,M,J,amplification,rateNumerator]; ipra_ring) (.eqRefl _) product

theorem retimed_observations (p q z R B E T c d a b u v A D : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E c d) (ha : Γ ⊢[PRAAx] domain a b E T) (hu : Γ ⊢[PRAAx] domain u v E T)
    (hD : Γ ⊢[PRAAx] le one D) (near : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction u v) A D) : Γ ⊢[PRAAx]
    distanceBounded (rawSample (query p T c) z B c d a b) (rawSample (query q T c) z B c d u v)
      (rateNumerator (lipschitz R E T c d*A) D p q) (rateDenominator D p q) := by
  let P := unit p
  let Q := unit q
  let X := unit (query p T c)
  let Y := unit (query q T c)
  let J := amplification T c
  have xp : Γ ⊢[PRAAx] le (J*P) X := GaussianFastValueCut.query_budget J p
  have yq : Γ ⊢[PRAAx] le (J*Q) Y := GaussianFastValueCut.query_budget J q
  have actual := raw_observations (query p T c) (query q T c) z R B E T c d a b u v A D h ha hu hD near
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hD) (denominator_positive _ _ _ hD)
    (by dsimp only [rawNumerator,rateNumerator,rateDenominator,P,Q,X,Y,J]
        ipra_le (𝔞 D)^2*𝔞(unit q)*𝔞(unit (query q T c))*sl xp+
          (𝔞 D)^2*𝔞(unit p)*𝔞(unit (query p T c))*sl yq) actual

theorem actual_retimed_quadratic_Jacobian_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 15
    (source (var 2) (var 3) (var 4) (var 5) (var 7) (var 8) ⟶ domain (var 9) (var 10) (var 5) (var 6) ⟶
      domain (var 11) (var 12) (var 5) (var 6) ⟶ le one (var 14) ⟶
      distanceBounded (fraction (var 9) (var 10)) (fraction (var 11) (var 12)) (var 13) (var 14) ⟶
      distanceBounded (rawSample (query (var 0) (var 6) (var 7)) (var 2) (var 4) (var 7) (var 8) (var 9) (var 10))
        (rawSample (query (var 1) (var 6) (var 7)) (var 2) (var 4) (var 7) (var 8) (var 11) (var 12))
        (rateNumerator (lipschitz (var 3) (var 5) (var 6) (var 7) (var 8)*var 13) (var 14) (var 0) (var 1))
        (rateDenominator (var 14) (var 0) (var 1))) :=
  closeUniv 15 (.impI (.impI (.impI (.impI (.impI
    (retimed_observations _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianEulerSquareJacobianRate
