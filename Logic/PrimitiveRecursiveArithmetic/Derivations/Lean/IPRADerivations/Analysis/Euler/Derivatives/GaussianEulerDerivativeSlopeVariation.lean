import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicContinuity
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicImproperInputProperness

/-!
# Improper logarithmic slopes on the actual native path

The displacement `i*h/(D*N)` uses the same input modulus as `h/D` for
every `i ≤ N`. The local parameter rate supplies an estimate at this
displacement, and properness identifies its evaluator with the original
improper name at the native path point. The estimate is uniform in `N`.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDerivativeSlopeVariation

open_ipra
open GaussianEulerDerivativeParameterPath (point numerator denominator)
open GaussianEulerLogarithmicImproperName (data nameF name_regular)
open GaussianEulerParameterExponentialIncrement (shifted)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product)
open GaussianRationalMetric (bounded bounded_to_cleared bounded_of_cleared distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator denominator_positive)
open ComplexLogarithmRemainder (scale normSq_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "continuitySource" => GaussianEulerLogarithmicContinuity.source
local notation "modulus" => GaussianEulerLogarithmicContinuity.modulus

def source (r j z R B A h D N i : PTm n) : Fm PTm n :=
  continuitySource r j z R B A h D ⋏ (le one N ⋏ le i N)

def pathData (j z R B A h D N i : PTm n) : PTm n :=
  data j (numerator z B h D N i) (R+one) (denominator B D N) (two*A)

ipra_subst source

ipra_subst pathData

private theorem scaled_displacement (h D N i X Y : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N)
    (hY : Γ ⊢[PRAAx] le one Y) (hh : Γ ⊢[PRAAx] bounded (ofGaussian h D) X Y) : Γ ⊢[PRAAx]
    bounded (ofGaussian (scale i h) (D*N)) X Y := by
  have dn := positive_product _ _ hD hN
  have clear := bounded_to_cleared _ _ D X Y hD hY (ofGaussian_represents h D hD) hh
  apply bounded_of_cleared _ _ (D*N) X Y dn hY (ofGaussian_represents _ _ dn)
  have norm := natEq (normSq_scale (Γ := Γ) i h)
  ipra_le (𝔞 i)^2*sl clear+(𝔞 X)^2*(𝔞 D)^2*sl (sq_le_sq hi) using rw [norm]; ring

private theorem original_diagonal (t r j z R B A h D N i : PTm n)
    (s : Γ ⊢[PRAAx] source r j z R B A h D N i) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF t (pathData j z R B A h D N i)) (ap2 nameF t (data j z R B A))
      (GaussianNamedLipschitzRate.diagonalNumerator (num 5) (unit r) (num 4) t) (unit r*unit t) := by
  let w := shifted z B (scale i h) (D*N)
  let v := numerator z B h D N i
  let V := unit r
  let U := unit t
  let Z := V*U
  have hN := s.andE₂.andE₁
  have hi := s.andE₂.andE₂
  have hB := s.andE₁.andE₁.andE₂.andE₁.andE₁
  have hD := s.andE₁.andE₂.andE₁
  have dn := positive_product _ _ hD hN
  have cs : Γ ⊢[PRAAx] continuitySource r j z R B A (scale i h) (D*N) :=
    .andI s.andE₁.andE₁ (.andI dn
      (scaled_displacement h D N i one (modulus r j R A) hD hN hi
        (GaussianEulerLogarithmicContinuity.modulus_positive r j R A) s.andE₁.andE₂.andE₂))
  have pointCert := GaussianEulerDerivativeParameterPath.path_source z R B A h D N i
    (GaussianEulerLogarithmicContinuity.path_source r j z R B A h D s.andE₁) hN hi
  have shiftCert := GaussianEulerLogarithmicContinuity.shifted_certificate r j z R B A (scale i h) (D*N) cs
  have eq : Γ ⊢[PRAAx] ofGaussian v (denominator B D N) ≐ ofGaussian w (B*(D*N)) :=
    ((GaussianEulerDerivativeParameterPath.point_split z B h D N i hB hD hN).eqTrans
      (GaussianEulerLogarithmicParameterTaylor.encoded_sum z B (scale i h) (D*N) hB dn).eqSymm)
  have proper := GaussianEulerLogarithmicImproperInputProperness.original_observations t t j v w (R+one) (R+one)
    (denominator B D N) (B*(D*N)) (two*A) (two*A) (.andI pointCert (.andI shiftCert eq))
  have changed := rate_at nameF nameF (data j w (R+one) (B*(D*N)) (two*A)) (data j z R B A)
    (num 5) V t t (GaussianEulerLogarithmicContinuity.original_parameter_rate r j z R B A (scale i h) (D*N) cs)
  have hZ : Γ ⊢[PRAAx] le one Z := positive_product _ _ (unit_positive r) (unit_positive t)
  have first := distance_radius_mono _ _ _ _ (two*V) Z (positive_product _ _ (unit_positive t) (unit_positive t)) hZ
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by dsimp only [V,U,Z]; ipra_ring)) proper
  have second := distance_radius_mono _ _ _ _ (num 5*U+two*V) Z (denominator_positive V t t (unit_positive r)) hZ
    (le_of_eq_add (d := ConciseIPRA.PTm.zero)
      (by dsimp only [rateNumerator,rateDenominator,V,U,Z]; ipra_ring)) changed
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [GaussianNamedLipschitzRate.diagonalNumerator,V,U]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hZ first second)

theorem original_parameter_path_rate (r j z R B A h D N i : PTm n)
    (s : Γ ⊢[PRAAx] source r j z R B A h D N i) : Γ ⊢[PRAAx]
    independentRate nameF nameF (pathData j z R B A h D N i) (data j z R B A) (num 5) (unit r) := by
  have pathCert := GaussianEulerDerivativeParameterPath.path_source z R B A h D N i
    (GaussianEulerLogarithmicContinuity.path_source r j z R B A h D s.andE₁) s.andE₂.andE₁ s.andE₂.andE₂
  apply GaussianNamedLipschitzRate.independent_rate nameF nameF _ _ (num 5) (unit r) (num 4)
    (unit_positive r) (name_regular j _ (R+one) _ (two*A) pathCert) (name_regular j z R B A s.andE₁.andE₁)
  refine .allI ?_
  let sh (x : PTm n) := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh r) (sh j) (sh z) (sh R) (sh B) (sh A) (sh h) (sh D) (sh N) (sh i) :=
    by simpa only [Fm.shift,Syn.shift,subst_source,sh] using s.shift
  simpa [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalDenominator,pathData,Syn.shift,sh,one,two] using
    original_diagonal (var 0) (sh r) (sh j) (sh z) (sh R) (sh B) (sh A) (sh h) (sh D) (sh N) (sh i) hs

theorem actual_original_logarithmic_path_slope_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      independentRate nameF nameF (pathData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
        (data (var 1) (var 2) (var 3) (var 4) (var 5)) (num 5) (unit (var 0))) :=
  closeUniv 10 (.impI (original_parameter_path_rate _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerDerivativeSlopeVariation
