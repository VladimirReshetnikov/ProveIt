import IPRADerivations.Analysis.GaussianEulerLogarithmicCompactName
import IPRADerivations.Analysis.GaussianRationalSlackRemoval

/-!
# Original logarithmic observations across independent compact clients

Changing a numerical radius, compact lower guard or top guard changes
the actual Fast query of the evaluator. Each query pays its own proved
raw observation gain. Comparison through one unchanged original raw
observation and a finite rational gap leaves exactly the two independent
requested errors. No query equality or client-output law is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicClientRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicCompactName (sample query)
open GaussianEulerLogarithmicMultiplier (observationCost)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (z R S B E T F U a b : PTm n) : Fm PTm n :=
  GaussianEulerLogarithmicMultiplier.source z R B E T a b ⋏
    GaussianEulerLogarithmicMultiplier.source z S B F U a b
def cost (j R S E T F U : PTm n) : PTm n := observationCost j R E T+observationCost j S F U
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R S B E T F U a b : PTm n) :
    (source z R S B E T F U a b).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ S)
      (Syn.subst σ B) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ F) (Syn.subst σ U) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [source]
@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (j R S E T F U : PTm n) :
    Syn.subst σ (cost j R S E T F U) = cost (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ S)
      (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ F) (Syn.subst σ U) := by simp [cost]

theorem original_to_raw (p s j z R B E T a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLogarithmicMultiplier.source z R B E T a b) : Γ ⊢[PRAAx]
    distanceBounded (sample p j R E T z B a b) (GaussianEulerLogarithmicMultiplier.sample s j z B a b)
      (unit s+observationCost j R E T*unit p) (unit p*unit s) := by
  let r := query p j R E T
  let P := unit p
  let S := unit s
  let Q := unit r
  let H := observationCost j R E T
  have same : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.input z R B E T a b a b zero one :=
    .andI h.andE₁ (.andI h.andE₂ (.andI h.andE₂ (.andI (le_refl one)
      (GaussianRationalPowerDifference.distance_refl_zero _ one (le_refl one)))))
  have actual := GaussianEulerLogarithmicMultiplier.original_variation r s j z R B E T a b a b zero one same
  have raw : Γ ⊢[PRAAx] distanceBounded (sample p j R E T z B a b)
      (GaussianEulerLogarithmicMultiplier.sample s j z B a b) (H*(Q+S)) (Q*S) :=
    distance_congr (.eqRefl _) (.eqRefl _)
      (by unfold GaussianEulerLogarithmicMultiplier.numerator; dsimp only [H,Q,S]; ipra_ring)
      (by unfold GaussianNamedInverseRate.rateDenominator; dsimp only [Q,S]; ipra_ring) actual
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive r) (unit_positive s)) (positive_product _ _ (unit_positive p) (unit_positive s))
    (by dsimp only [H,P,Q,S,r]
        ipra_le (𝔞(unit s)*𝔞(unit s))*sl (GaussianEulerLogarithmicCompactName.query_budget (Γ := Γ) p j R E T)) raw

theorem original_client_slack (p q s j z R S B E T F U a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R S B E T F U a b) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (sample p j R E T z B a b) (sample q j S F U z B a b))
      (unit p+unit q) (unit p*unit q) (cost j R S E T F U) s := by
  let P := unit p
  let Q := unit q
  let V := unit s
  let D := P*Q*V
  let H := observationCost j R E T
  let K := observationCost j S F U
  have up := unit_positive (Γ := Γ) p
  have uq := unit_positive (Γ := Γ) q
  have uv := unit_positive (Γ := Γ) s
  have dp := positive_product _ _ up uv
  have dq := positive_product _ _ uq uv
  have dd : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ up uq) uv
  have first : Γ ⊢[PRAAx] distanceBounded (sample p j R E T z B a b)
      (GaussianEulerLogarithmicMultiplier.sample s j z B a b) ((V+H*P)*Q) D :=
    distance_radius_mono _ _ _ _ _ _ dp dd (le_of_eq_add (d := zero) (by dsimp only [D,P,Q,V,H]; ipra_ring))
      (original_to_raw p s j z R B E T a b h.andE₁)
  have second : Γ ⊢[PRAAx] distanceBounded (GaussianEulerLogarithmicMultiplier.sample s j z B a b)
      (sample q j S F U z B a b) ((V+K*Q)*P) D :=
    distance_symmetric _ _ _ _ dd
      (distance_radius_mono _ _ _ _ _ _ dq dd (le_of_eq_add (d := zero) (by dsimp only [D,P,Q,V,K]; ipra_ring))
        (original_to_raw q s j z S B F U a b h.andE₂))
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _)
    (by unfold cost; dsimp only [H,K,P,Q,V]; unfold unit; ipra_ring)
    (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ dd first second)

/-- Both actual independently retimed compact clients retain their own
requested observation error, including unrelated radius certificates. -/
theorem original_client_observations (p q j z R S B E T F U a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R S B E T F U a b) : Γ ⊢[PRAAx]
    distanceBounded (sample p j R E T z B a b) (sample q j S F U z B a b)
      (unit p+unit q) (unit p*unit q) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (cost j R S E T F U)
    (positive_product _ _ (unit_positive p) (unit_positive q))
    (original_client_slack p q _ j z R S B E T F U a b h)

theorem wrapped_client_cross (t j z R S B E T F U : PTm n)
    (h : Γ ⊢[PRAAx] source z R S B E T F U (fstT t) (sndT t)) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.crossEquivalent
      (GaussianCompactRiemannName.evaluatorName GaussianEulerLogarithmicCompactName.evaluatorF)
      (GaussianCompactRiemannName.evaluatorName GaussianEulerLogarithmicCompactName.evaluatorF)
      (GaussianCompactRiemannName.nameData t (GaussianEulerLogarithmicCompactName.fixedData j R E T z B))
      (GaussianCompactRiemannName.nameData t (GaussianEulerLogarithmicCompactName.fixedData j S F U z B)) := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift S))
        (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T))
        (Syn.shift (Syn.shift F)) (Syn.shift (Syn.shift U))
        (fstT (Syn.shift (Syn.shift t))) (sndT (Syn.shift (Syn.shift t))) :=
    by simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [GaussianNameEquivalence.crossEquivalent,GaussianCompactRiemannName.subst_nameData,
    GaussianEulerLogarithmicCompactName.subst_fixedData,Syn.shift] using
    distance_congr (GaussianEulerLogarithmicCompactName.wrapped_at (var 1) (Syn.shift (Syn.shift t))
      (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T))
      (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B))).eqSymm
      (GaussianEulerLogarithmicCompactName.wrapped_at (var 0) (Syn.shift (Syn.shift t))
        (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift S)) (Syn.shift (Syn.shift F)) (Syn.shift (Syn.shift U))
        (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B))).eqSymm (.eqRefl _) (.eqRefl _)
      (original_client_observations (var 1) (var 0) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift z))
        (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift S)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift E))
        (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift F)) (Syn.shift (Syn.shift U))
        (fstT (Syn.shift (Syn.shift t))) (sndT (Syn.shift (Syn.shift t))) hs)

theorem actual_logarithmic_independent_client_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    (source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⟶
      distanceBounded (sample (var 0) (var 2) (var 4) (var 7) (var 8) (var 3) (var 6) (var 11) (var 12))
        (sample (var 1) (var 2) (var 5) (var 9) (var 10) (var 3) (var 6) (var 11) (var 12))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 13 (.impI (original_client_observations _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicClientRate
