import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderSharpRadiusBridge
import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderSignedParity
import IPRADerivations.Analysis.Stirling.GaussianStirlingExpansionErrorProgram

/-!
# The sharp logarithmic bound discharges the original expansion program

The coefficient bound is a single integer computed at the externally
fixed order. Both parity branches use the original Horner polynomial,
the original normalized Stirling quotient and its existing error code.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSharpLogRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingAllOrderSharpRadius (absoluteCoefficient radiusNumerator radiusDenominator radius_denominator_positive)
open GaussianStirlingAllOrderSharpRadiusBridge (cap_exact zero_point even_degree_budget odd_degree_budget)
open GaussianStirlingAllOrderLogRateTransport (upperPoint lowerPoint)
open GaussianStirlingAllOrderLogRateFromStrict (positive_log_rate negative_log_rate)
open GaussianStirlingAllOrderSignedLower (zeroPoint)
open GaussianStirlingAllOrderSignedParity (even_bracket odd_bracket)
open GaussianStirlingAllOrderTruncationAlgebra (truncation correction)
open GaussianStirlingAllOrderTruncationHorner (truncation_even_horner truncation_odd_horner hornerErrorData)
open GaussianStirlingAllOrderLogTruncation (errorF errorData error_regular)
open GaussianStirlingExpansionFiniteError (logPolynomial)
open GaussianStirlingExpansionConditionalError (logRate)
open GaussianStirlingExpansionExponentialError (logBudget)
open GaussianStirlingExpansionErrorProgram (run returned_approximation_bound)
open GaussianStirlingMultiplicative (quotientF quotientData)
open GaussianStirlingGlobalBounds (remainderData)
open GaussianStirlingNames (source)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open GaussianRationalHorner (qzero)
open GaussianRationalMetric (distanceBounded)
open RationalGaussianEmbedding (embed_canonical negative_congr)
open GaussianGammaCanonicalExponent (constantF)
open GaussianSignedNameExponentialOrder (constant_equal_cross)
open GaussianNameEquivalence (crossEquivalent)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem same_data (f : PR 2) (x y : PTm n) (e : Γ ⊢[PRAAx] x ≐ y)
    (h : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx] crossEquivalent f f x y := by
  refine .allI (.allI ?_)
  let a := Syn.shift (Syn.shift x)
  let b := Syn.shift (Syn.shift y)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have es : Δ ⊢[PRAAx] a ≐ b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using e.shift.shift
  have hs : Δ ⊢[PRAAx] pointCN f a := by simpa [Δ,a,Fm.shift,Syn.shift] using h.shift.shift
  simpa [crossEquivalent,a,b,Δ,Syn.shift] using
    GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (congrAp2 f (.eqRefl _) es) (.eqRefl _) (.eqRefl _)
      (GaussianNameEquivalence.point_at f a (var 1) (var 0) hs)

private theorem data_cross (m d : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (h : Γ ⊢[PRAAx] truncation m A B ≐ logPolynomial d A B) : Γ ⊢[PRAAx]
    crossEquivalent errorF errorF (errorData m A B x) (hornerErrorData d A B x) := by
  apply same_data _ _ _ ?_ (error_regular m A B x hs)
  simpa [errorData,hornerErrorData] using
    Prf.eqCongr (Γ := Γ) (GaussianNamedDifference.data (var 0) (var 1) : PTm 2)
      (σ := ![remainderData A B x,truncation m A B]) (σ' := ![remainderData A B x,logPolynomial d A B])
      (fun i => by fin_cases i; exact .eqRefl _; exact h)

theorem even_cap (m : ℕ) (hm : Even m) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    correction m A B ≐ upperPoint (radiusNumerator m B) (radiusDenominator m A) := by
  have e := GaussianStirlingAllOrderSignedParityAlgebra.even_cap (Γ := Γ) m hm A B
  exact e.eqSymm.eqTrans (cap_exact m A B x hs)

theorem odd_cap (m : ℕ) (hm : Odd m) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    correction m A B ≐ lowerPoint (radiusNumerator m B) (radiusDenominator m A) := by
  let z := correction m A B
  have e := GaussianStirlingAllOrderSignedParityAlgebra.odd_cap (Γ := Γ) m hm A B
  have f := negative_congr (e.eqSymm.eqTrans (cap_exact m A B x hs))
  exact (GaussianDeterminantSignTransport.negative_involution z (embed_canonical _)).eqSymm.eqTrans f

theorem positive_horner_bracket (m d : ℕ) (hm : Even m) (A B x : PTm n)
    (hs : Γ ⊢[PRAAx] source A B) (hPoly : Γ ⊢[PRAAx] truncation m A B ≐ logPolynomial d A B) :
    Γ ⊢[PRAAx] strictOrder constantF errorF qzero (hornerErrorData d A B x) ⋏
      strictOrder errorF constantF (hornerErrorData d A B x)
        (upperPoint (radiusNumerator m B) (radiusDenominator m A)) := by
  have he := data_cross m d A B x hs hPoly
  have ehr := GaussianNameEquivalence.cross_symm _ _ _ _ he
  have zl := constant_equal_cross _ _ (zero_point (Γ := Γ)).eqSymm
  have br := even_bracket m hm A B x hs
  exact .andI (strict_transport _ _ _ _ _ _ _ _ zl he br.andE₁)
    (strict_transport _ _ _ _ _ _ _ _ ehr (constant_equal_cross _ _ (even_cap m hm A B x hs)) br.andE₂)

theorem negative_horner_bracket (m d : ℕ) (hm : Odd m) (A B x : PTm n)
    (hs : Γ ⊢[PRAAx] source A B) (hPoly : Γ ⊢[PRAAx] truncation m A B ≐ logPolynomial d A B) :
    Γ ⊢[PRAAx] strictOrder constantF errorF
      (lowerPoint (radiusNumerator m B) (radiusDenominator m A)) (hornerErrorData d A B x) ⋏
      strictOrder errorF constantF (hornerErrorData d A B x) qzero := by
  have he := data_cross m d A B x hs hPoly
  have ehr := GaussianNameEquivalence.cross_symm _ _ _ _ he
  have zr := constant_equal_cross _ _ (zero_point (Γ := Γ))
  have br := odd_bracket m hm A B x hs
  exact .andI (strict_transport _ _ _ _ _ _ _ _ (constant_equal_cross _ _ (odd_cap m hm A B x hs).eqSymm) he br.andE₁)
    (strict_transport _ _ _ _ _ _ _ _ ehr zr br.andE₂)

theorem log_rate_from_sharp (m d : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (hPoly : Γ ⊢[PRAAx] truncation m A B ≐ logPolynomial d A B)
    (hBudget : Γ ⊢[PRAAx] le (radiusNumerator m B*pw A (succ (num d)))
      ((num (absoluteCoefficient m)*pw B (succ (num d)))*radiusDenominator m A)) :
    Γ ⊢[PRAAx] logRate d A B x (num (absoluteCoefficient m)) := by
  let R := radiusNumerator m B
  let D := radiusDenominator m A
  let C : PTm n := num (absoluteCoefficient m)
  have hD := radius_denominator_positive m A hs.andE₁
  rcases Nat.even_or_odd m with ev | od
  · have br := positive_horner_bracket m d ev A B x hs hPoly
    exact positive_log_rate d A B x R D C hs hD hBudget br.andE₁ br.andE₂
  · have br := negative_horner_bracket m d od A B x hs hPoly
    exact negative_log_rate d A B x R D C hs hD hBudget br.andE₁ br.andE₂

theorem absolute_coefficient_value (m : ℕ) :
    ((absoluteCoefficient m : ℕ) : ℚ)/(BernoulliBounds.bden (2*m+2) : ℚ) =
      |GaussianStirlingExpansionCoefficients.logCoefficient (2*m+1)| := by
  let z := GaussianStirlingAllOrderTruncationCoefficients.coefficientNumerator m
  let D := (BernoulliBounds.bden (2*m+2) : ℚ)
  have hd : 0<D := by dsimp [D]; exact_mod_cast BernoulliBounds.bden_pos (2*m+2)
  have h : (z : ℚ) = GaussianStirlingExpansionCoefficients.logCoefficient (2*m+1)*D :=
    GaussianStirlingAllOrderTruncationCoefficients.coefficient_value m
  change (z.natAbs : ℚ)/D = _
  rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs,h,abs_mul,abs_of_pos hd,mul_div_cancel_right₀ _ hd.ne']

def expansionConstant (d : ℕ) : ℕ := absoluteCoefficient ((d+1)/2)

theorem original_log_rate (d : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (hBA : Γ ⊢[PRAAx] le B A) : Γ ⊢[PRAAx] logRate d A B x (num (expansionConstant d)) := by
  let m := d/2
  have hd : d=2*m ∨ d=2*m+1 := by unfold m; omega
  rcases hd with he | ho
  · rw [he]
    have k : (2*m+1)/2=m := by omega
    simpa only [expansionConstant,k] using
      log_rate_from_sharp m (2*m) A B x hs (truncation_even_horner m A B hs.andE₁) (even_degree_budget m A B hBA)
  · rw [ho]
    have k : (2*m+1+1)/2=m+1 := by omega
    simpa only [expansionConstant,k] using
      log_rate_from_sharp (m+1) (2*m+1) A B x hs (truncation_odd_horner m A B hs.andE₁) (odd_degree_budget m A B hBA)

def output (d : ℕ) (p A B : PTm n) : PTm n := run d p A B (num (expansionConstant d))

theorem original_multiplicative_approximation (d : ℕ) (p A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (hBA : Γ ⊢[PRAAx] le B A) (hSmall : Γ ⊢[PRAAx] le (two*(logBudget d*B)) A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 quotientF p (quotientData A B x)) (fstT (output d p A B))
      (fstT (sndT (output d p A B))) (sndT (sndT (output d p A B))) :=
  returned_approximation_bound d p A B x _ hs hBA hSmall (original_log_rate d A B x hs hBA)

theorem actual_all_order_multiplicative_approximation_closed (d : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 1) (var 2) ⟶ le (var 2) (var 1) ⟶ le (two*(logBudget d*var 2)) (var 1) ⟶
        distanceBounded (ap2 quotientF (var 0) (quotientData (var 1) (var 2) (var 3)))
          (fstT (output d (var 0) (var 1) (var 2)))
          (fstT (sndT (output d (var 0) (var 1) (var 2))))
          (sndT (sndT (output d (var 0) (var 1) (var 2))))) :=
  closeUniv 4 (.impI (.impI (.impI (original_multiplicative_approximation d _ _ _ _
    Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSharpLogRate
