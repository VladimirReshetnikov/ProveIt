import IPRADerivations.Analysis.Euler.CompactExhaustion.Tails.GaussianEulerCompactLowerTail
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.Tails.GaussianEulerLowerTailFiniteBudget
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.Tails.GaussianEulerLowerCofinalQuadrature
import IPRADerivations.Analysis.Euler.CompactExhaustion.Cutoffs.GaussianEulerCutoffCauchyComparison

/-!
# The actual lower-cutoff Euler name and its sharp tail bound

The original finite quadrature and the transformed cofinal
observations use the same mesh data. Their finite norm and comparison
errors are removed by an explicit rational gap at the original
requested observation. Coincident cutoffs have a zero-width sample.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedLowerTail

open_ipra
open GaussianGammaIntegralCutoffs (height etaDen top)
open GaussianGammaCompactCutoffGeometry (lowerWidth)
open GaussianGammaCompactCutoffSplit (lowerData)
open GaussianEulerCompactAdditivity (nameF)
open GaussianEulerCompactModulus (lipschitz)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianEulerLowerCofinalQuadrature (rootMesh transformed)
open GaussianEulerLowerTailRootGrid (timeNumerator timeDenominator)
open GaussianEulerLowerTailPartition (totalWidth)
open GaussianEulerLowerTailRowBound (stepScale)
open GaussianCompactRiemannName (sampledModulus sampled_modulus_congr quadrature quadrature_congr mesh precision)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalHorner (qzero positive_product)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalSlackRemoval (slack slack_removal_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A : PTm n) : Fm PTm n :=
  GaussianGammaEulerCompactQuadrature.source z R B ⋏ GaussianEulerLowerPowerCoefficients.source z R B A
def point (s z R B p q A : PTm n) : PTm n := ap2 nameF s (lowerData z R B p q A)
def result (s z R B p q A : PTm n) : Fm PTm n :=
  bounded (point s z R B p q A) (A*unit s+unit (height p A R)) (unit (height p A R)*unit s)

ipra_subst source
ipra_subst point
ipra_subst result [height, GaussianGammaIntegralCutoffs.tailCoefficient]

theorem split_source (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] GaussianGammaCompactCutoffSplit.source z R B p q A :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ hpq)

theorem finite_source (z R B N p q k : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] source z R B (succ k)) (hpq : Γ ⊢[PRAAx] lt p q) :
    Γ ⊢[PRAAx] GaussianEulerCompactLowerTail.source z R B N p q k
      (lipschitz R (etaDen q (succ k) R) (top q (succ k) R)) := by
  let A := succ k
  let E := etaDen q A R
  let C := lowerWidth p q A
  let T := top q A R
  let L := lipschitz R E T
  let x := fixedData z B
  let K := pw N A
  have hs := split_source z R B p q A h (le_of_lt hpq)
  have old := GaussianEulerCompactAdditivity.compact_input z R B one C E T
    (GaussianGammaCompactCutoffSplit.lower_source z R B p q A hs)
  have hK : Γ ⊢[PRAAx] le one K := GaussianPolynomialPerturbation.power_positive N A hN
  have hC := GaussianGammaCompactCutoffGeometry.lower_positive p q A h.andE₂.andE₁ hpq
  have width := GaussianEulerLowerTailRootGrid.time_width (Γ := Γ) N p q A
  have hW : Γ ⊢[PRAAx] le one (totalWidth N p q A) :=
    le_congr (.eqRefl _) width.eqSymm (positive_product _ _ hC hK)
  have mod := GaussianCompactIntervalRescaling.rescaled_modulus evaluatorF K one C E L x hK old.andE₂.andE₂.andE₂
  have ha : Γ ⊢[PRAAx] K*one ≐ timeNumerator zero N p q A :=
    (by ipra_ring : Γ ⊢[PRAAx] K*one ≐ K).eqTrans (GaussianEulerLowerTailRootGrid.time_first N p q A).eqSymm
  have hc : Γ ⊢[PRAAx] K*C ≐ totalWidth N p q A := (mul_comm _ _).eqTrans width.eqSymm
  have he : Γ ⊢[PRAAx] K*E ≐ timeDenominator N q A R :=
    (mul_comm _ _).eqTrans (GaussianEulerLowerTailRootGrid.time_denominator N q A R).eqSymm
  exact .andI hN (.andI (le_of_lt hpq) (.andI hW (.andI h.andE₂
    (sampled_modulus_congr ha hc he (.eqRefl _) (.eqRefl _) mod))))

theorem cofinal_bound (t z R B p q k : PTm n)
    (h : Γ ⊢[PRAAx] source z R B (succ k)) (hpq : Γ ⊢[PRAAx] lt p q) :
    Γ ⊢[PRAAx] bounded
      (transformed evaluatorF t (succ k) (lowerWidth p q (succ k)) (etaDen q (succ k) R)
        (lipschitz R (etaDen q (succ k) R) (top q (succ k) R)) (top q (succ k) R) (fixedData z B))
      (GaussianEulerLowerTailFiniteBudget.numerator t p q k R (lipschitz R (etaDen q (succ k) R) (top q (succ k) R)))
      (GaussianEulerLowerTailFiniteBudget.denominator t p k R) := by
  let A := succ k
  let C := lowerWidth p q A
  let E := etaDen q A R
  let T := top q A R
  let L := lipschitz R E T
  let N := rootMesh t L T
  let s := precision t T
  let x := fixedData z B
  let y := GaussianEulerCompactLowerTail.originalQuadrature s z R B N p q k
  let b := transformed evaluatorF t A C E L T x
  have Npos := GaussianEulerLowerCofinalQuadrature.root_mesh_positive (Γ := Γ) t L T
  have raw := GaussianEulerCompactLowerTail.original_finite_lower_tail_bound s z R B N p q k L
    (finite_source z R B N p q k Npos h hpq)
  have hN : Γ ⊢[PRAAx] le (unit t) N := by
    unfold N rootMesh
    exact le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (unit t) (GaussianCompactRiemannName.mesh_positive t L T))
  have hP : Γ ⊢[PRAAx] le (unit t) (unit s) :=
    GaussianExponentialReference.unit_monotone (le_trans (le_add_right t T) (le_add_right _ _))
  have norm := GaussianEulerLowerTailFiniteBudget.original_radius_conversion y s t N p q k R L (le_of_lt hpq) hN hP
    (bound_congr (.eqRefl _) (by
      unfold GaussianEulerLowerTailFiniteBudget.oldNumerator GaussianEulerLowerTailFiniteBudget.scale
        GaussianEulerLowerBlockWeight.numerator stepScale
      ipra_ring) (.eqRefl _) raw)
  have e : Γ ⊢[PRAAx] y ≐ b :=
    let w := GaussianEulerLowerTailRootGrid.time_width (Γ := Γ) N p q A
    quadrature_congr evaluatorF (.eqRefl s) w
      (GaussianEulerLowerTailRootGrid.time_first N p q A) w (GaussianEulerLowerTailRootGrid.time_denominator N q A R) (.eqRefl x)
  exact bound_congr e (.eqRefl _) (.eqRefl _) norm

theorem compared_bound_to_slack (x y A H K s t : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hd : Γ ⊢[PRAAx] distanceBounded x y (two*unit s+unit t) (unit t*unit s))
    (hb : Γ ⊢[PRAAx] bounded y (A*unit t+K*H) (H*unit t)) : Γ ⊢[PRAAx]
    slack x (A*unit s+H) (H*unit s) (K+two) t := by
  have ht := unit_positive (Γ := Γ) t
  have hs := unit_positive (Γ := Γ) s
  have d := positive_product _ _ ht hs
  have b := positive_product _ _ hH ht
  have den := positive_product _ _ (positive_product _ _ hH hs) ht
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ d b) den
    (le_of_eq_add (d := zero) (by unfold unit; ipra_ring))
    (GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ d b hd hb)

theorem original_slack (s t z R B p q k : PTm n)
    (h : Γ ⊢[PRAAx] source z R B (succ k)) (hpq : Γ ⊢[PRAAx] lt p q) :
    Γ ⊢[PRAAx] slack (point s z R B p q (succ k))
      (succ k*unit s+unit (height p (succ k) R)) (unit (height p (succ k) R)*unit s)
      (GaussianEulerLowerTailFiniteBudget.residual (stepScale p q k)
        (lipschitz R (etaDen q (succ k) R) (top q (succ k) R))+two) t := by
  have hs := split_source z R B p q (succ k) h (le_of_lt hpq)
  have hd := GaussianEulerLowerCofinalQuadrature.original_lower_observations t s z R B p q (succ k) hs hpq
  have den := positive_product (Γ := Γ) _ _ (unit_positive t) (unit_positive s)
  exact compared_bound_to_slack _ _ _ _ _ s t (unit_positive _)
    (distance_symmetric _ _ _ _ den hd) (cofinal_bound t z R B p q k h hpq)

theorem strict_successor_bound (s z R B p q k : PTm n)
    (h : Γ ⊢[PRAAx] source z R B (succ k)) (hpq : Γ ⊢[PRAAx] lt p q) :
    Γ ⊢[PRAAx] result s z R B p q (succ k) := by
  let A := succ k
  let H := unit (height p A R)
  let K := GaussianEulerLowerTailFiniteBudget.residual (stepScale p q k) (lipschitz R (etaDen q A R) (top q A R))+two
  let t := GaussianRationalSlackRemoval.precision (point s z R B p q A) (A*unit s+H) (H*unit s) K
  exact slack_removal_at _ _ _ K (positive_product _ _ (unit_positive _) (unit_positive s))
    (original_slack s t z R B p q k h hpq)

theorem strict_bound (s z R B p q A : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A) (hpq : Γ ⊢[PRAAx] lt p q) :
    Γ ⊢[PRAAx] result s z R B p q A := by
  let k := monus A one
  let φ := source (Syn.shift z) (Syn.shift R) (Syn.shift B) (var 0) ⟶
    result (Syn.shift s) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift p) (Syn.shift q) (var 0)
  have e : Γ ⊢[PRAAx] succ k ≐ A :=
    (GaussianCompactRiemannName.positive_as_successor A h.andE₂.andE₁).eqSymm
  have rule : Γ ⊢[PRAAx] source z R B (succ k) ⟶ result s z R B p q (succ k) :=
    .impI (strict_successor_bound s z R B p q k Prf.hyp0 hpq.wk)
  have moved := Prf.eqSubst1 φ e (by simpa [φ] using rule)
  exact .impE (by simpa [φ] using moved) h

theorem point_zero (s z R B p q A : PTm n) (h : Γ ⊢[PRAAx] lowerWidth p q A ≐ zero) :
    Γ ⊢[PRAAx] point s z R B p q A ≐ qzero := by
  let E := etaDen q A R
  let T := top q A R
  have e : Γ ⊢[PRAAx] lowerData z R B p q A ≐ GaussianEulerCompactAdditivity.data z R B one zero E T :=
    GaussianGammaCompactCutoffSplit.euler_data_congr _ _ _ _ _ _ _ _ _ _ _ (.eqRefl _) h (.eqRefl _) (.eqRefl _)
  exact (congrAp2 nameF (.eqRefl s) e).eqTrans
    (GaussianCompactZeroWidth.observation_zero evaluatorF s one E (lipschitz R E T) T (fixedData z B)
      (GaussianGammaIntegralCutoffs.eta_den_positive q A R))

theorem equal_bound (s z R B p q A : PTm n) (hpq : Γ ⊢[PRAAx] p ≐ q) :
    Γ ⊢[PRAAx] result s z R B p q A := by
  have width : Γ ⊢[PRAAx] lowerWidth p q A ≐ lowerWidth p p A := by
    ipra_congr (lowerWidth (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl p, hpq.eqSymm, .eqRefl A]
  have e := point_zero s z R B p q A (width.eqTrans (GaussianGammaCompactCutoffGeometry.same_lower p A))
  exact bound_congr e.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerNamedUpperTail.zero_bound _ _ (positive_product _ _ (unit_positive _) (unit_positive s)))

theorem lower_observation_bound (s z R B p q A : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] result s z R B p q A :=
  .orE (lt_or_eq_of_le hpq) (strict_bound s z R B p q A h.wk Prf.hyp0)
    (equal_bound s z R B p q A Prf.hyp0)

theorem lower_tail_all (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] GaussianEulerCutoffCauchyComparison.lowerTailBound z R B A := by
  let lift (x : PTm n) := Syn.shift (Syn.shift (Syn.shift x))
  have hs : ((Γ.map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx] source (lift z) (lift R) (lift B) (lift A) :=
    by simpa only [lift,Fm.shift,subst_source,Syn.shift] using h.shift.shift.shift
  refine .allI (.allI (.allI (.impI ?_)))
  exact lower_observation_bound (var 2) (lift z) (lift R) (lift B) (var 1) (var 0) (lift A) hs.wk Prf.hyp0

theorem original_lower_tail_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ GaussianEulerCutoffCauchyComparison.lowerTailBound
      (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (lower_tail_all _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerNamedLowerTail
