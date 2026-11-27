import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.GaussianEulerLogarithmicCertificateOverlap
import IPRADerivations.Analysis.Euler.Logarithms.ParameterRates.Compact.GaussianEulerLogarithmicCompactParameterRate
import IPRADerivations.Analysis.Euler.Derivatives.GaussianEulerDerivativeParameterPath

/-!
# A uniform parameter modulus for the actual logarithmic improper names

First choose a moderate compact interval from the desired tolerance and
the original certificate. The exact common endpoint geometry keeps that
interval fixed under the widened argument certificate. The actual compact
Lipschitz estimate and both fixed-cutoff rates then bind the improper names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicContinuity

open_ipra
open GaussianEulerLogarithmicCertificateGeometry (leftIndex rightIndex left_height right_height left_index_late right_index_late same_eta)
open GaussianEulerLogarithmicImproperName (data nameF name_regular)
open GaussianEulerLogarithmicCutoffSplit (fullData)
open GaussianEulerParameterExponentialIncrement (shifted)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianEulerLogarithmicMultiplier (logRadius majorant)
open GaussianEulerLogarithmicParameterIncrement (curvature)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator denominator_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "ordinarySource" => GaussianEulerLowerPowerCoefficients.source
local notation "compactF" => GaussianEulerLogarithmicIntervalName.nameF

def baseIndex (r j R A : PTm n) : PTm n := leftIndex r r j R (two*A) (R+one) (two*A)
def shiftedIndex (r j R A : PTm n) : PTm n := rightIndex r r j R (two*A) (R+one) (two*A)
def intervalDen (r j R A : PTm n) : PTm n := etaDen (baseIndex r j R A) (two*(two*A)) (R+j)
def intervalTop (r j R A : PTm n) : PTm n := top (baseIndex r j R A) (two*(two*A)) (R+j)
def compactGain (j R E T : PTm n) : PTm n := T*(curvature j R E T+majorant (succ j) R E T)
def modulus (r j R A : PTm n) : PTm n :=
  one+num 4*A+logRadius (intervalDen r j R A) (intervalTop r j R A)+
    compactGain j R (intervalDen r j R A) (intervalTop r j R A)*unit r
def source (r j z R B A h D : PTm n) : Fm PTm n :=
  ordinarySource z R B A ⋏ (le one D ⋏ bounded (ofGaussian h D) one (modulus r j R A))

ipra_subst baseIndex
ipra_subst intervalDen [etaDen, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst intervalTop [top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst modulus [compactGain]
ipra_subst source

theorem modulus_positive (r j R A : PTm n) : Γ ⊢[PRAAx] le one (modulus r j R A) := by
  unfold modulus
  exact le_trans (le_trans (le_add_right _ _) (le_add_right _ _)) (le_add_right _ _)

theorem path_source (r j z R B A h D : PTm n) (s : Γ ⊢[PRAAx] source r j z R B A h D) : Γ ⊢[PRAAx]
    GaussianEulerDerivativeParameterPath.source z R B A h D := by
  have width : Γ ⊢[PRAAx] le (num 4*A) (modulus r j R A) :=
    le_trans (le_trans (le_add_left _ _) (le_add_right _ _)) (le_add_right _ _)
  have pos := positive_product _ _ (le_of_eq_add (d := num 3) (by ipra_ring) : Γ ⊢[PRAAx] le one (num 4)) s.andE₁.andE₁
  exact .andI s.andE₁ (.andI s.andE₂.andE₁
    (bounded_radius_mono _ _ _ _ _ (modulus_positive _ _ _ _) pos (le_congr (by ipra_ring) (by ipra_ring) width) s.andE₂.andE₂))

theorem doubled_margin (z R B A : PTm n) (s : Γ ⊢[PRAAx] ordinarySource z R B A) : Γ ⊢[PRAAx]
    ordinarySource z R B (two*A) := by
  have old := zle_toZ s.andE₂.andE₂
  have real : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.realLower z (two*A) B := by
    apply zle_of_toZ (B+two*PolynomialBisection.slack (ZT.ofNat B) (ZT.ofNat A*ComplexLogarithmRemainder.re z))
    simp only [ZT.toZ_ofNat,ZT.toZ_mul] at old ⊢
    dsimp only [PolynomialBisection.slack]
    ipra_simps
    linear_combination 2*old
  exact .andI (positive_product _ _ (le_of_eq_add (d := one) (by ipra_ring)) s.andE₁) (.andI s.andE₂.andE₁ real)

theorem shifted_certificate (r j z R B A h D : PTm n) (s : Γ ⊢[PRAAx] source r j z R B A h D) : Γ ⊢[PRAAx]
    ordinarySource (shifted z B h D) (R+one) (B*D) (two*A) := by
  let p := GaussianEulerDerivativeParameterPath.numerator z B h D one one
  let d := GaussianEulerDerivativeParameterPath.denominator B D one
  have np : Γ ⊢[PRAAx] p ≐ shifted z B h D := by
    simpa [p,shifted,GaussianEulerDerivativeParameterPath.numerator] using Prf.eqCongr
      (ComplexLogarithmRemainder.add (ComplexLogarithmRemainder.scale (var 0) (var 1))
        (ComplexLogarithmRemainder.scale (var 2) (var 3)) : PTm 4)
      (σ := ![D*one,z,B*one,h]) (σ' := ![D,z,B,h]) (fun i => by
        fin_cases i
        · change Γ ⊢[PRAAx] D*one ≐ D
          ipra_ring
        · exact .eqRefl _
        · change Γ ⊢[PRAAx] B*one ≐ B
          ipra_ring
        · exact .eqRefl _)
  have dp : Γ ⊢[PRAAx] d ≐ B*D := by unfold d GaussianEulerDerivativeParameterPath.denominator; ipra_ring
  have actual := GaussianEulerDerivativeParameterPath.path_source z R B A h D one one (path_source r j z R B A h D s)
    (le_refl _) (le_refl _)
  simpa using
    Prf.eqSubst (ordinarySource (var 0) (var 1) (var 2) (var 3) : Fm PTm 4) ![p,R+one,d,two*A]
      ![shifted z B h D,R+one,B*D,two*A] (fun i => by fin_cases i; exact np; exact .eqRefl _; exact dp; exact .eqRefl _)
      (by simpa using actual)

private theorem fixed_at (t r j z R B A k : PTm n) (h : Γ ⊢[PRAAx] ordinarySource z R B A)
    (hk : Γ ⊢[PRAAx] le (GaussianEulerLogarithmicCommonCutoff.cutoff r j A) k) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF t (data j z R B A)) (ap2 compactF t (fullData j z R B A k))
      (two*unit t+two*unit r) (unit r*unit t) := by
  let K := unit (r+num 6)
  have rise : Γ ⊢[PRAAx] le (unit r) K := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have original := rate_at _ _ _ _ two K t t (GaussianEulerLogarithmicFixedCutoff.original_fixed_cutoff_rate r j z R B A k h hk)
  exact distance_radius_mono _ _ _ _ (two*unit t+two*unit r) (unit r*unit t)
    (denominator_positive K t t (unit_positive _)) (positive_product _ _ (unit_positive _) (unit_positive _))
    (by dsimp only [rateNumerator,rateDenominator,K]; ipra_le (2*𝔞(unit t)*𝔞(unit t)*𝔞(unit t))*sl rise) original

theorem original_diagonal (t r j z R B A h D : PTm n) (s : Γ ⊢[PRAAx] source r j z R B A h D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF t (data j (shifted z B h D) (R+one) (B*D) (two*A))) (ap2 nameF t (data j z R B A))
      (GaussianNamedLipschitzRate.diagonalNumerator (num 5) (unit r) (num 8) t)
      (GaussianNamedLipschitzRate.diagonalDenominator (unit r) t) := by
  let Q := unit r
  let U := unit t
  let V := two*A
  let S := R+one
  let k := baseIndex r j R A
  let l := shiftedIndex r j R A
  let E := intervalDen r j R A
  let T := intervalTop r j R A
  let C := width k (two*V) (R+j)
  let Y := modulus r j R A
  let w := shifted z B h D
  let Z := unit r*unit t
  let K := curvature j R E T+majorant (succ j) R E T
  have base : Γ ⊢[PRAAx] ordinarySource z R B V := doubled_margin z R B A s.andE₁
  have shift : Γ ⊢[PRAAx] ordinarySource w S (B*D) V := shifted_certificate r j z R B A h D s
  have hp := base.andE₁
  have lk := left_index_late r r j R V S V hp
  have rl := right_index_late r r j R V S V hp
  have leq := left_height r r j R V S V hp
  have req := right_height r r j R V S V hp
  have topEq : Γ ⊢[PRAAx] top l (two*V) (S+j) ≐ T := congrMul (.eqRefl two) (req.eqTrans leq.eqSymm)
  have etaEq : Γ ⊢[PRAAx] etaDen l (two*V) (S+j) ≐ E := (same_eta r r j R V S V hp hp).eqSymm
  have rightData : Γ ⊢[PRAAx] fullData j w S (B*D) V l ≐ GaussianEulerLogarithmicIntervalName.data j w S (B*D) one C E T :=
    GaussianEulerLogarithmicCutoffSplit.interval_data_congr _ _ _ _ _ _ _ _ one C E T (.eqRefl _)
      (congrMonus (congrMul etaEq topEq) (.eqRefl one)) etaEq topEq
  have interval := GaussianEulerLogarithmicCutoffSplit.full_source j z R B V k base.andE₂.andE₁
  have hJ : Γ ⊢[PRAAx] le (logRadius E T*one) Y :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (le_add_left _ _)) (le_add_right _ _)
  have compactSource : Γ ⊢[PRAAx] GaussianEulerLogarithmicTaylorGrid.source z R B one C E T h D one Y :=
    .andI interval (.andI s.andE₂.andE₁ (.andI (modulus_positive r j R A) (.andI hJ s.andE₂.andE₂)))
  have old := GaussianEulerLogarithmicCompactParameterRate.original_observations t t j z R B one C E T h D one Y compactSource
  have cap : Γ ⊢[PRAAx] le C (E*T) := le_trans (le_add_left _ _) interval.andE₂.andE₂
  have pay : Γ ⊢[PRAAx] le (GaussianEulerLogarithmicCompactParameterRate.gain j R C E T one*Q) (E*Y) := by
    have a := mul_le_mul_right (K*Q) cap
    have b : Γ ⊢[PRAAx] le (T*K*Q) Y := le_add_left _ _
    exact le_trans (le_congr (by unfold GaussianEulerLogarithmicCompactParameterRate.gain; dsimp only [Q,K]; ipra_ring)
      (by ipra_ring) a) (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right E b))
  have hZ : Γ ⊢[PRAAx] le one Z := positive_product _ _ (unit_positive _) (unit_positive _)
  have hEY := positive_product _ _ interval.andE₁.andE₂.andE₁ (modulus_positive r j R A)
  have second := distance_radius_mono _ _ _ _ (U+two*Q) Z
    (denominator_positive (E*Y) t t hEY) hZ
    (by dsimp only [GaussianEulerLogarithmicCompactParameterRate.numerator, GaussianEulerLogarithmicCompactParameterRate.denominator,
          rateNumerator, rateDenominator, GaussianEulerLogarithmicCompactParameterRate.scaleDenominator, U, Q, Z]
        ipra_le (𝔞(unit t)*𝔞(unit t)*𝔞(unit t))*sl pay) old
  have first := distance_congr (.eqRefl _) (congrAp2 compactF (.eqRefl t) rightData) (.eqRefl _) (.eqRefl _)
    (fixed_at t r j w S (B*D) V l shift rl)
  have third := distance_symmetric _ _ _ _ hZ (fixed_at t r j z R B V k base lk)
  have last := GaussianNameEquivalence.cross_at _ _ _ _ t t
    (GaussianEulerLogarithmicCertificateOverlap.original_certificate_overlap j z R R B V A (.andI base s.andE₁))
  have fourth := distance_radius_mono _ _ _ _ (two*Q) Z (positive_product _ _ (unit_positive t) (unit_positive t)) hZ
    (le_congr (.eqRefl _) (by dsimp only [Q,Z]; ipra_ring) (le_refl _)) last
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNamedLipschitzRate.diagonalNumerator U Q; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hZ first (distance_triangle_same _ _ _ _ _ _ hZ second
      (distance_triangle_same _ _ _ _ _ _ hZ third fourth)))

theorem original_parameter_rate (r j z R B A h D : PTm n) (s : Γ ⊢[PRAAx] source r j z R B A h D) : Γ ⊢[PRAAx]
    independentRate nameF nameF (data j (shifted z B h D) (R+one) (B*D) (two*A)) (data j z R B A) (num 5) (unit r) := by
  apply GaussianNamedLipschitzRate.independent_rate nameF nameF _ _ (num 5) (unit r) (num 8) (unit_positive r)
    (name_regular j _ (R+one) (B*D) (two*A) (shifted_certificate r j z R B A h D s)) (name_regular j z R B A s.andE₁)
  refine .allI ?_
  let sh (x : PTm n) := Syn.shift x
  have ss : Γ.map Fm.shift ⊢[PRAAx] source (sh r) (sh j) (sh z) (sh R) (sh B) (sh A) (sh h) (sh D) :=
    by simpa only [Fm.shift,Syn.shift,subst_source,sh] using s.shift
  simpa [GaussianNamedLipschitzRate.diagonalEnvelope,Syn.shift,sh,one,two] using
    original_diagonal (var 0) (sh r) (sh j) (sh z) (sh R) (sh B) (sh A) (sh h) (sh D) ss

theorem actual_original_logarithmic_uniform_parameter_modulus_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      independentRate nameF nameF (data (var 1) (shifted (var 2) (var 4) (var 6) (var 7))
        (var 3+one) (var 4*var 7) (two*var 5)) (data (var 1) (var 2) (var 3) (var 4) (var 5)) (num 5) (unit (var 0))) :=
  closeUniv 8 (.impI (original_parameter_rate _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicContinuity
