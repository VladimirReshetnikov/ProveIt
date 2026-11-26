import IPRADerivations.Analysis.Euler.Derivatives.GaussianEulerDerivativePrecision
import IPRADerivations.Analysis.Euler.Derivatives.GaussianEulerDerivativeEndpointBinding
import IPRADerivations.Analysis.Euler.Derivatives.GaussianEulerDerivativeCompactSlopeRows
import IPRADerivations.Analysis.Series.GaussianRationalNormalizedTelescope

/-!
# Differentiate the original logarithmic improper name at a native rational input

The radius for the increment is computed from the requested accuracy and the
basepoint certificate before the increment is supplied. Once its native
denominator is known, the two endpoint cutoffs and the finite subdivision
are chosen. The normalized local and observation errors are paid using that
denominator. The finite mean of the slope errors keeps its independent
modulus because the actual reciprocal cancels the whole increment exactly.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicDerivative

open_ipra
open GaussianEulerDerivativeCommonInterval (compactData intervalDen intervalTop intervalWidth endpointQuery endpoint_query_budget)
open GaussianEulerDerivativeParameterPath (increment)
open GaussianEulerDerivativePrecision (workUnit readIndex)
open GaussianEulerLogarithmicImproperName (data nameF name_regular)
open GaussianEulerParameterExponentialIncrement (shifted)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator denominator_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "I" => GaussianEulerLogarithmicImproperName.nameF
local notation "K" => GaussianEulerLogarithmicIntervalName.nameF
local notation "QF" => GaussianNamedDifferenceQuotient.nameF I I
local notation "qData" => GaussianNamedDifferenceQuotient.data I I
local notation "contSource" => GaussianEulerLogarithmicContinuity.source
local notation "count" => GaussianEulerDerivativeSubdivisionBudget.compactCount
local notation "body" => GaussianEulerLogarithmicPathCompactRows.body

def source (p j z R B A h D : PTm n) : Fm PTm n :=
  contSource (p+num 6) (succ j) z R B A h D ⋏ le one (ComplexLogarithmRemainder.normSq h)

def quotientData (j z R B A h D : PTm n) : PTm n :=
  qData (data j (shifted z B h D) (R+one) (B*D) (two*A)) (data j z R B A) h D

ipra_subst source

ipra_subst quotientData

theorem quotient_input (p j z R B A h D : PTm n) (hs : Γ ⊢[PRAAx] source p j z R B A h D) :
    Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.input I I
      (data j (shifted z B h D) (R+one) (B*D) (two*A)) (data j z R B A) h D :=
  .andI (name_regular j _ (R+one) (B*D) (two*A)
    (GaussianEulerLogarithmicContinuity.shifted_certificate (p+num 6) (succ j) z R B A h D hs.andE₁))
    (.andI (name_regular j z R B A hs.andE₁.andE₁) (.andI hs.andE₁.andE₂.andE₁ hs.andE₂))

theorem quotient_regular (p j z R B A h D : PTm n) (hs : Γ ⊢[PRAAx] source p j z R B A h D) :
    Γ ⊢[PRAAx] pointCN QF (quotientData j z R B A h D) :=
  GaussianNamedDifferenceQuotient.name_regular I I _ _ h D (quotient_input p j z R B A h D hs)

private theorem normalized_compact (v p j z R B A h D r N : PTm n)
    (hs : Γ ⊢[PRAAx] source p j z R B A h D)
    (hN : Γ ⊢[PRAAx] le (count p j (R+one) (intervalDen r p j R A) (intervalTop r p j R A) D) N) :
    Γ ⊢[PRAAx] distanceBounded
      (GaussianRationalHorner.qmul (GaussianNamedDifferenceQuotient.inverse h D)
        (qsub (ap2 K (readIndex p N D) (compactData r p j j z R B A h D N N))
          (ap2 K (readIndex p N D) (compactData r p j j z R B A h D N zero))))
      (ap2 I v (data (succ j) z R B A)) (num 10*unit v+workUnit p) (workUnit p*unit v) := by
  let C := intervalWidth r p j R A
  let E := intervalDen r p j R A
  let T := intervalTop r p j R A
  let t := readIndex p N D
  let f := GaussianEulerLogarithmicPathCompactRows.fixedData t j z R B h D N one C E T
  let g := GaussianEulerDerivativeCompactSlopeRows.slopeData t r p j z R B A h D N
  let a := GaussianEulerLogarithmicPathCompactTaylor.numerator t t t j R C E T N
  let L := GaussianEulerLogarithmicPathCompactTaylor.denominator t t t E N
  let b := GaussianEulerDerivativeCompactSlopeRows.numerator t v p (p+num 6)
  let M := GaussianEulerDerivativeCompactSlopeRows.denominator t v p (p+num 6)
  let U := workUnit p
  let V := unit v
  let S := unit t
  let J := GaussianEulerLogarithmicMultiplier.logRadius E T
  let Kc := T*GaussianEulerLogarithmicParameterIncrement.curvature j (R+one) E T
  have path := GaussianEulerLogarithmicContinuity.path_source (p+num 6) (succ j) z R B A h D hs.andE₁
  have hpos := GaussianEulerDerivativeSubdivisionBudget.later_positive p J Kc D N hN
  have log := le_trans (GaussianEulerDerivativeSubdivisionBudget.log_budget p J Kc D) hN
  have geom := GaussianEulerDerivativeCommonInterval.interval_source r p j z R B A h D N zero path hpos (zero_le _)
  have hc : Γ ⊢[PRAAx] le C (E*T) := le_trans (le_add_left _ _) geom.andE₂.andE₂
  have epos : Γ ⊢[PRAAx] le one E := geom.andE₁.andE₂.andE₁
  have hL : Γ ⊢[PRAAx] le one L := GaussianNamedAffineRemainderRate.denominator_positive _ t t t
    (positive_product _ _ epos (positive_product _ _ hpos hpos))
  have hM : Γ ⊢[PRAAx] le one M := GaussianEulerDerivativeCompactSlopeRows.denominator_positive t v p (p+num 6)
  have localRows := GaussianEulerLogarithmicPathCompactRows.original_local_rows t t j z R B A h D one C E T N
    (.andI path (.andI epos (.andI (le_refl one) (.andI geom.andE₂.andE₂ log))))
  have slopeRows := GaussianEulerDerivativeCompactSlopeRows.original_slope_rows t v r p (p+num 6) j z R B A h D N
    (.andI hs.andE₁ hpos)
  have hD := hs.andE₁.andE₂.andE₁
  have sep : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.separated h D := .andI hD hs.andE₂
  have actual := GaussianRationalNormalizedTelescope.normalized_error body body N f g h D
    (GaussianEulerDerivativeCompactSlopeRows.baseSlope v j z R B A) a L b M sep hpos hL hM localRows slopeRows
  have first := GaussianEulerLogarithmicPathCompactRows.body_at (Γ := Γ) N t j z R B h D N one C E T
  have last := GaussianEulerLogarithmicPathCompactRows.body_at (Γ := Γ) zero t j z R B h D N one C E T
  have eq := GaussianRationalSyntheticDivision.qmul_congr (.eqRefl (GaussianNamedDifferenceQuotient.inverse h D))
      (GaussianRationalSyntheticDivision.qsub_congr first last)
  have row := distance_congr eq (.eqRefl _) (.eqRefl _) (.eqRefl _) actual
  have localPay := GaussianEulerDerivativePrecision.local_budget p j R C E T D N hN hc
  have queryPay := GaussianEulerDerivativePrecision.unit_budget p N D hpos hD
  exact distance_radius_mono _ _ _ _ (num 10*V+U) (U*V) (positive_product _ _ hL hM)
    (positive_product _ _ (unit_positive _) (unit_positive _)) (by
      dsimp only [GaussianRationalNormalizedTelescope.numerator, GaussianRationalNormalizedTelescope.denominator]
      have hLocal : Γ ⊢[PRAAx] le ((D*N*a)*U) (two*L) := localPay
      have hQuery : Γ ⊢[PRAAx] le U S := queryPay
      ipra_le (𝔞 M*𝔞 V)*sl hLocal+
        (𝔞 L*(𝔞 U)^2*(𝔞 V)^2)*sl hQuery using
          dsimp only [b,M,GaussianEulerDerivativeCompactSlopeRows.numerator,GaussianEulerDerivativeCompactSlopeRows.denominator,
            GaussianEulerDerivativeCompactSlopeBinding.gain,GaussianEulerDerivativeCompactSlopeBinding.denominator,
            rateNumerator,rateDenominator,U,V,S,workUnit]
          ipra_simps
          ring) row

private theorem tight_endpoint_error (t p j z R B A h D r N : PTm n)
    (hs : Γ ⊢[PRAAx] source p j z R B A h D)
    (hN : Γ ⊢[PRAAx] le one N)
    (tail : Γ ⊢[PRAAx] le (endpointQuery p D) r)
    (read : Γ ⊢[PRAAx] le ((num 4*D)*workUnit p) (unit t)) : Γ ⊢[PRAAx]
    distanceBounded
      (GaussianNamedDifferenceQuotient.raw I I t t (data j (shifted z B h D) (R+one) (B*D) (two*A)) (data j z R B A) h D)
      (GaussianRationalHorner.qmul (GaussianNamedDifferenceQuotient.inverse h D)
        (qsub (ap2 K t (compactData r p j j z R B A h D N N)) (ap2 K t (compactData r p j j z R B A h D N zero))))
      two (workUnit p) := by
  let L := unit (r+num 6)
  let M := rateNumerator two L t t
  let F := rateDenominator L t t
  let U := workUnit p
  let S := unit t
  let left := data j z R B A
  let right := data j (shifted z B h D) (R+one) (B*D) (two*A)
  have hF : Γ ⊢[PRAAx] le one F := denominator_positive L t t (unit_positive _)
  have l := rate_at I K left (compactData r p j j z R B A h D N zero) two L t t
    (GaussianEulerDerivativeEndpointBinding.original_left_rate r p (p+num 6) j z R B A h D N hs.andE₁ hN)
  have k := rate_at I K right (compactData r p j j z R B A h D N N) two L t t
    (GaussianEulerDerivativeEndpointBinding.original_right_rate r p (p+num 6) j z R B A h D N hs.andE₁ hN)
  have diff := GaussianFastValueCut.distance_difference_same _ _ _ _ M M F hF k l
  have sep := (quotient_input p j z R B A h D hs).andE₂.andE₂
  have scaled := GaussianNamedDifferenceQuotient.scale_distance (GaussianNamedDifferenceQuotient.inverse h D)
    _ _ D (M+M) F hF (GaussianNamedDifferenceQuotient.inverse_bound h D sep) diff
  have paid := endpoint_query_budget p D r tail
  exact distance_radius_mono _ _ _ _ two U hF (unit_positive _) (by
    dsimp only [M,F,rateNumerator,rateDenominator,U,L]
    ipra_le (𝔞 S)^2*sl paid+(𝔞(unit (r+num 6))*𝔞 S)*sl read using
      dsimp only [S,workUnit]
      ring) scaled

private theorem tight_quotient_readback (q t p j z R B A h D : PTm n) (hs : Γ ⊢[PRAAx] source p j z R B A h D)
    (read : Γ ⊢[PRAAx] le ((num 4*D)*workUnit p) (unit t)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 QF q (quotientData j z R B A h D))
      (GaussianNamedDifferenceQuotient.raw I I t t (data j (shifted z B h D) (R+one) (B*D) (two*A)) (data j z R B A) h D)
      (unit q+workUnit p) (workUnit p*unit q) := by
  let U := workUnit p
  let S := unit t
  let V := unit q
  have reduced : Γ ⊢[PRAAx] le ((two*D)*U) S :=
    le_trans (le_of_eq_add (d := two*D*U) (by ipra_ring)) read
  exact distance_radius_mono _ _ _ _ (V+U) (U*V) (GaussianNamedDifferenceQuotient.denominator_positive q t t)
    (positive_product _ _ (unit_positive _) (unit_positive q)) (by
      dsimp only [GaussianNamedDifferenceQuotient.numerator,GaussianNamedDifferenceQuotient.denominator,U,S,V]
      ipra_le (𝔞(unit q))^2*𝔞(unit t)*sl reduced)
    (GaussianNamedDifferenceQuotient.independent_readback I I q t t _ _ h D (quotient_input p j z R B A h D hs))

/-- Every observation of the actual difference quotient and every observation
of the next logarithmic order have the independently requested rate. -/
theorem original_observations (q v p j z R B A h D : PTm n) (hs : Γ ⊢[PRAAx] source p j z R B A h D) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 QF q (quotientData j z R B A h D)) (ap2 I v (data (succ j) z R B A))
      (rateNumerator one (unit p) q v) (rateDenominator (unit p) q v) := by
  let r := endpointQuery p D
  let E := intervalDen r p j R A
  let T := intervalTop r p j R A
  let N := count p j (R+one) E T D
  let t := readIndex p N D
  let U := workUnit p
  let Q := unit q
  let V := unit v
  let J := unit p
  let Z := (U*Q)*V
  have hN : Γ ⊢[PRAAx] le one N := GaussianEulerDerivativeSubdivisionBudget.later_positive p (GaussianEulerLogarithmicMultiplier.logRadius E T)
    (T*GaussianEulerLogarithmicParameterIncrement.curvature j (R+one) E T) D N (le_refl N)
  have read := GaussianEulerDerivativePrecision.read_budget p N D hN
  have oneU : Γ ⊢[PRAAx] le one U := unit_positive _
  have oneQ : Γ ⊢[PRAAx] le one Q := unit_positive q
  have oneV : Γ ⊢[PRAAx] le one V := unit_positive v
  have hZ : Γ ⊢[PRAAx] le one Z := positive_product _ _ (positive_product _ _ oneU oneQ) oneV
  have first := distance_radius_mono _ _ _ _ ((Q+U)*V) Z (positive_product _ _ oneU oneQ) hZ
    (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring)) (tight_quotient_readback q t p j z R B A h D hs read)
  have second := distance_radius_mono _ _ _ _ (two*Q*V) Z oneU hZ
    (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring))
    (tight_endpoint_error t p j z R B A h D r N hs hN (le_refl r) read)
  have third := distance_radius_mono _ _ _ _ ((num 10*V+U)*Q) Z (positive_product _ _ oneU oneV) hZ
    (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring)) (normalized_compact v p j z R B A h D r N hs (le_refl N))
  have joined := distance_triangle_same _ _ _ _ _ _ hZ first (distance_triangle_same _ _ _ _ _ _ hZ second third)
  have total := GaussianEulerDerivativePrecision.total_budget (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ _ _ hZ (denominator_positive J q v (unit_positive p)) (by
    dsimp only [rateNumerator,rateDenominator,Z,J,Q,V]
    ipra_le (𝔞(unit q)*𝔞(unit v))^2*sl total) joined

theorem original_derivative_rate (p j z R B A h D : PTm n) (hs : Γ ⊢[PRAAx] source p j z R B A h D) :
    Γ ⊢[PRAAx] independentRate QF I (quotientData j z R B A h D) (data (succ j) z R B A) one (unit p) := by
  let sh (x : PTm n) := Syn.shift (Syn.shift x)
  have ss : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh p) (sh j) (sh z) (sh R) (sh B) (sh A) (sh h) (sh D) :=
    by simpa only [Fm.shift,Syn.shift,subst_source,sh] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa [independentRate,Syn.shift,sh,one] using
    original_observations (var 1) (var 0) (sh p) (sh j) (sh z) (sh R) (sh B) (sh A) (sh h) (sh D) ss

theorem actual_original_improper_logarithmic_derivative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      independentRate QF I (quotientData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (data (succ (var 1)) (var 2) (var 3) (var 4) (var 5)) one (unit (var 0))) :=
  closeUniv 8 (.impI (original_derivative_rate _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicDerivative
