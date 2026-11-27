import IPRADerivations.Analysis.Gamma.HalfInteger.GaussianGammaHalfEulerSquare
import IPRADerivations.Analysis.Gamma.HalfInteger.GaussianGammaHalfPiName
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaEulerInverseConvergence
import IPRADerivations.Foundations.CubicBisection

/-!
# Original Gamma at one half squared is π

The unchanged C15 finite inverse converges to the unchanged Gamma value.
A uniform disk for those finite names allows their genuine multiplication
clocks to be composed with C15. The finite square is tied to the exact
Wallis rational and the arctangent quadrature name. A cofinal schedule
then yields the exact equality in the original cross-name sense.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHalfSquareLimit

open_ipra
open GaussianGammaHalfEulerSquare (squareF squareData eulerHalf)
open GaussianGammaReciprocalInverse (gammaF lambdaNumerator lambda_positive)
open GaussianGammaEulerReciprocalInverse (eulerF)
open GaussianGammaEulerInverseConvergence (coefficientNumerator coefficientDenominator)
open GaussianGammaHalfPiName (orderAt orderIndex unit_mono)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_at point_at)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same norm_from_distance_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianNamedMultiplyRate (sampleBound leadingNumerator leadingDenominator)
open ComplexLogarithmRemainder (oneCode)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gammaHalf : PTm n := GaussianGammaReciprocalInverse.gammaData oneCode one two two
def gammaSquareF : PR 2 := squareF gammaF
def gammaSquare : PTm n := squareData gammaF gammaHalf
def gammaBound : PTm n := GaussianNameBounds.U gammaF gammaHalf
def rateConstant : PTm n := coefficientNumerator one two
def eulerBound : PTm n := gammaBound+rateConstant+two
def squareConstant : PTm n := (eulerBound+gammaBound)*rateConstant
def clock (s : PTm n) : PTm n := s+(two+GaussianGammaPerturbationExponent.numerator one+squareConstant)
def cutoff (s : PTm n) : PTm n := orderAt (clock s)

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem gamma_source : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (oneCode : PTm n) one two one two :=
  GaussianGammaDensityDomain.base_gamma_source oneCode one two two GaussianGammaHalfIntegerDomain.half_source

theorem gamma_regular : Γ ⊢[PRAAx] pointCN gammaF (gammaHalf : PTm n) :=
  GaussianGammaReciprocalInverse.gamma_regular _ _ _ _ _ gamma_source

theorem gamma_square_regular : Γ ⊢[PRAAx] pointCN gammaSquareF (gammaSquare : PTm n) :=
  GaussianNameArithmetic.multiply_fast _ _ _ _ gamma_regular gamma_regular

theorem rate_source (s : PTm n) : Γ ⊢[PRAAx] GaussianGammaEulerInverseConvergence.source oneCode one two one two (cutoff s) := by
  let K : PTm n := two+GaussianGammaPerturbationExponent.numerator one+squareConstant
  let t := clock s
  have short : Γ ⊢[PRAAx] le K t := le_congr (.eqRefl _) (add_comm _ _) (le_add_right _ _)
  have ku := le_trans short (AnalyticNumberTheory.ZetaFiniteContract.le_pow_self t)
  have un : Γ ⊢[PRAAx] le (unit t) (cutoff s) := by
    change Γ ⊢[PRAAx] le (unit t) (succ (num 16*unit t))
    ipra_le 15 * 𝔞 (unit t) + 1
  have h := le_trans ku un
  exact .andI gamma_source (.andI
    (le_trans (show Γ ⊢[PRAAx] le (two*one) K by unfold K; ipra_le 𝔞 (GaussianGammaPerturbationExponent.numerator one) + 𝔞 (squareConstant : PTm n)) h)
    (le_trans (show Γ ⊢[PRAAx] le (GaussianGammaPerturbationExponent.numerator one) K by unfold K; ipra_le 2 + 𝔞 (squareConstant : PTm n)) h))

theorem depth_bound (s : PTm n) : Γ ⊢[PRAAx] le ((squareConstant : PTm n)*unit s) (cutoff s) := by
  let K : PTm n := two+GaussianGammaPerturbationExponent.numerator one+squareConstant
  let t := clock s
  have sk : Γ ⊢[PRAAx] le squareConstant K := by unfold K; ipra_le 2 + 𝔞 (GaussianGammaPerturbationExponent.numerator (one : PTm n))
  have clockBudget := Foundations.CubicBisection.width_fuel (Γ := Γ) K s
  have un : Γ ⊢[PRAAx] le (unit t) (cutoff s) := by
    change Γ ⊢[PRAAx] le (unit t) (succ (num 16*unit t))
    ipra_le 15 * 𝔞 (unit t) + 1
  exact le_trans (mul_le_mul_right (unit s) sk) (le_trans clockBudget un)

theorem c15_denominator_ge (N : PTm n) : Γ ⊢[PRAAx] le N (coefficientDenominator one one N) := by
  let L : PTm n := lambdaNumerator one one
  have hL : Γ ⊢[PRAAx] le one L := (lambda_positive (R := one) (a := one) (d := two) (le_refl one) (zero_lt_succ one)).andE₁
  change Γ ⊢[PRAAx] le N (L*L*N)
  ipra_le 𝔞 N * (𝔞 L+1) * sl hL

theorem finite_uniform_bound_at (p N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerInverseConvergence.source oneCode one two one two N) :
    Γ ⊢[PRAAx] bounded (ap2 eulerF p (eulerHalf N)) eulerBound one := by
  let X := ap2 eulerF p (eulerHalf N)
  let Y := ap2 gammaF zero (gammaHalf : PTm n)
  let A : PTm n := rateConstant
  let D := coefficientDenominator one one N
  let U := unit p
  let V : PTm n := unit zero
  have hd := GaussianGammaEulerInverseConvergence.coefficient_denominator_positive _ _ _ _ _ _ h
  have hU := unit_positive (Γ := Γ) p
  have hV : Γ ⊢[PRAAx] le one V := unit_positive _
  have e : Γ ⊢[PRAAx] distanceBounded X Y (rateNumerator A D p zero) (rateDenominator D p zero) :=
    GaussianGammaEulerInverseConvergence.actual_observation_error p zero _ _ _ _ _ _ h
  have cmp : Γ ⊢[PRAAx] le (rateNumerator A D p zero*one) ((A+two)*rateDenominator D p zero) := by
    change Γ ⊢[PRAAx] le ((A*U*V+D*(U+V))*one) ((A+two)*(D*U*V))
    ipra_le 𝔞 A * 𝔞 U * 𝔞 V * sl hd + 𝔞 D * 𝔞 U * sl hV + 𝔞 D * 𝔞 V * sl hU
  have close : Γ ⊢[PRAAx] distanceBounded X Y (A+two) one :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive D p zero hd) (le_refl one) cmp e
  have hy : Γ ⊢[PRAAx] bounded Y gammaBound one :=
    GaussianNameBounds.sample_bound gammaF gammaHalf zero gamma_regular
  exact bound_congr (.eqRefl _) (by unfold eulerBound; ipra_ring) (.eqRefl _)
    (norm_from_distance_same (le_refl one) close hy)

theorem finite_uniform_bound (N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerInverseConvergence.source oneCode one two one two N) :
    Γ ⊢[PRAAx] sampleBound eulerF (eulerHalf N) eulerBound := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianGammaEulerInverseConvergence.source oneCode one two one two (Syn.shift N) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa [sampleBound,Syn.shift,eulerHalf,eulerBound,rateConstant,gammaBound,gammaHalf,
    GaussianGammaEulerReciprocalInverse.eulerData, GaussianGammaEulerReciprocalInverse.eulerHeight,
    GaussianBoundedInverseApartness.height, GaussianBoundedInverseApartness.productError,
    GaussianGammaReciprocalInverse.gammaData, GaussianGammaReciprocalInverse.gammaHeight,
    GaussianGammaEulerInverseConvergence.subst_directData] using finite_uniform_bound_at (var 0) (Syn.shift N) hs

theorem squared_rate (N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerInverseConvergence.source oneCode one two one two N) :
    Γ ⊢[PRAAx] independentRate (squareF eulerF) gammaSquareF (squareData eulerF (eulerHalf N)) gammaSquare
      (leadingNumerator rateConstant (coefficientDenominator one one N) rateConstant (coefficientDenominator one one N) eulerBound gammaBound)
      (leadingDenominator (coefficientDenominator one one N) (coefficientDenominator one one N)) := by
  have cf := GaussianGammaEulerInverseConvergence.actual_rate _ _ _ _ _ _ h
  have rc := GaussianGammaEulerInverseConvergence.actual_names_regular _ _ _ _ _ _ h
  have hp := GaussianGammaEulerInverseConvergence.coefficient_denominator_positive _ _ _ _ _ _ h
  exact GaussianNamedMultiplyRate.independent_rate eulerF eulerF gammaF gammaF _ _ _ _ _ _ _ _ _ _
    hp hp rc.andE₁ rc.andE₁ rc.andE₂ rc.andE₂ (finite_uniform_bound N h)
    (GaussianNameBounds.all_samples_bounded gammaF gammaHalf gamma_regular) cf cf

theorem scheduled_gamma_square (s : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (squareF eulerF) (clock s) (squareData eulerF (eulerHalf (cutoff s))))
      (ap2 gammaSquareF (clock s) gammaSquare) (num 3) (unit s) := by
  let t := clock s
  let N := cutoff s
  let D := coefficientDenominator one one N
  let U := unit s
  let V := unit t
  let K : PTm n := squareConstant
  let P := leadingNumerator rateConstant D rateConstant D eulerBound gammaBound
  let Q := leadingDenominator D D
  let X := ap2 (squareF eulerF) t (squareData eulerF (eulerHalf N))
  let Y := ap2 gammaSquareF t gammaSquare
  have hN := rate_source (Γ := Γ) s
  have hd := GaussianGammaEulerInverseConvergence.coefficient_denominator_positive _ _ _ _ _ _ hN
  have hdepth := le_trans (depth_bound (Γ := Γ) s) (c15_denominator_ge N)
  have hgain := unit_mono (Γ := Γ) s t (le_add_right _ _)
  have hreg : Γ ⊢[PRAAx] distanceBounded X Y (rateNumerator P Q t t) (rateDenominator Q t t) :=
    rate_at _ _ _ _ _ _ _ _ (squared_rate N hN)
  have cmp : Γ ⊢[PRAAx] le (rateNumerator P Q t t*U) (num 3*rateDenominator Q t t) := by
    change Γ ⊢[PRAAx] le
      (((eulerBound*rateConstant*D+gammaBound*rateConstant*D)*V*V+(D*D)*(V+V))*U)
      (num 3*((D*D)*V*V))
    ipra_le 𝔞 D * 𝔞 V * 𝔞 V * sl hdepth + 2 * 𝔞 D * 𝔞 D * 𝔞 V * sl hgain using
      unfold squareConstant
      ipra_simps
      ring
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive Q t t (positive_product _ _ hd hd)) (unit_positive s) cmp hreg

theorem scheduled_pi_comparison (s x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 gammaSquareF (clock s) gammaSquare)
      (ap2 GaussianGammaHalfPiName.nameF (clock s) x) (num 6) (unit s) := by
  let t := clock s
  let N := cutoff s
  let D := unit s
  let T := unit t
  let H := GaussianGammaHalfWallisRate.wallisValue N
  let X := ap2 (squareF eulerF) t (squareData eulerF (eulerHalf N))
  let Y := ap2 gammaSquareF t gammaSquare
  let Z := ap2 GaussianGammaHalfPiName.nameF t x
  have d := unit_positive (Γ := Γ) s
  have tpos := unit_positive (Γ := Γ) t
  have db := unit_mono (Γ := Γ) s t (le_add_right _ _)
  have rg := scheduled_gamma_square (Γ := Γ) s
  have D2 := positive_product (Γ := Γ) _ _ tpos tpos
  have n2 : Γ ⊢[PRAAx] le two N := le_trans (by ipra_le 0 : Γ ⊢[PRAAx] le two (two*one)) (rate_source s).andE₂.andE₁
  have literal : Γ ⊢[PRAAx] distanceBounded X H (T+T) (T*T) :=
    distance_congr (.eqRefl _) (constant_at t H) (.eqRefl _) (.eqRefl _)
      (cross_at _ _ _ _ t t (GaussianGammaHalfEulerSquare.euler_square_value N n2))
  have next : Γ ⊢[PRAAx] distanceBounded X H two D :=
    distance_radius_mono _ _ _ _ _ _ D2 d
      (by ipra_le 2 * 𝔞 T * sl db : Γ ⊢[PRAAx] le ((T+T)*D) (two*(T*T))) literal
  have lastRaw : Γ ⊢[PRAAx] distanceBounded H Z one (two*T) :=
    distance_congr (.eqRefl _) (GaussianGammaHalfPiName.sample_at t x).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianGammaHalfPiName.ordered_grid_error t t (le_refl _))
  have last : Γ ⊢[PRAAx] distanceBounded H Z one D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (zero_lt_succ one) tpos) d
      (by ipra_le sl db + 𝔞 T) lastRaw
  have first : Γ ⊢[PRAAx] distanceBounded Y X (num 3) D :=
    GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ d rg
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ d (distance_triangle_same _ _ _ _ _ _ d first next) last)

theorem gamma_squared_diagonal (s x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 gammaSquareF s gammaSquare) (ap2 GaussianGammaHalfPiName.nameF s x)
      (num 10) (unit s) := by
  let S := unit s
  let t := clock s
  let T := unit t
  let a := ap2 gammaSquareF s gammaSquare
  let b := ap2 gammaSquareF t gammaSquare
  let c := ap2 GaussianGammaHalfPiName.nameF t x
  let d := ap2 GaussianGammaHalfPiName.nameF s x
  have hs : Γ ⊢[PRAAx] le one S := unit_positive s
  have ht : Γ ⊢[PRAAx] le one T := unit_positive t
  have later : Γ ⊢[PRAAx] le S T := unit_mono s t (le_add_right _ _)
  have budget : Γ ⊢[PRAAx] le ((S+T)*S) (two*(S*T)) := by
    ipra_le 𝔞 S * sl later
  have ab : Γ ⊢[PRAAx] distanceBounded a b two S :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hs ht) hs budget
      (point_at gammaSquareF gammaSquare s t gamma_square_regular)
  have cd : Γ ⊢[PRAAx] distanceBounded c d two S := by
    apply GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ hs
    exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hs ht) hs budget
      (point_at GaussianGammaHalfPiName.nameF x s t (GaussianGammaHalfPiName.name_regular x))
  have bc : Γ ⊢[PRAAx] distanceBounded b c (num 6) S := scheduled_pi_comparison s x
  have ac := distance_triangle_same a b c two (num 6) S hs ab bc
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same a c d (two+num 6) two S hs ac cd)

private theorem shift_gammaSquare : Syn.shift (gammaSquare : PTm n) = (gammaSquare : PTm (n+1)) := by
  simp [gammaSquare,squareData,gammaHalf,Syn.shift,
    GaussianGammaReciprocalInverse.gammaData, GaussianGammaReciprocalInverse.gammaHeight,
    GaussianBoundedInverseApartness.height, GaussianBoundedInverseApartness.productError]

theorem original_half_square_is_pi (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent gammaSquareF GaussianGammaHalfPiName.nameF gammaSquare x := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 10)
    gamma_square_regular (GaussianGammaHalfPiName.name_regular x) (.allI ?_)
  change Γ.map Fm.shift ⊢[PRAAx] distanceBounded
    (ap2 gammaSquareF (var 0) (Syn.shift (gammaSquare : PTm n)))
    (ap2 GaussianGammaHalfPiName.nameF (var 0) (Syn.shift x)) (Syn.shift (num 10)) (unit (var 0))
  rw [shift_gammaSquare]
  simpa only [Syn.shift, PTm.subst_num] using
    gamma_squared_diagonal (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x)

theorem original_Gamma_half_square_is_Pi_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (crossEquivalent gammaSquareF GaussianGammaHalfPiName.nameF gammaSquare (var 0)) :=
  closeUniv 1 (original_half_square_is_pi _)

end LeanProofs.IPRA.Analysis.GaussianGammaHalfSquareLimit
