import IPRADerivations.Analysis.Stirling.Expansions.Cubic.GaussianStirlingCubicRate

/-!
# The actual second-order multiplicative Stirling error program

The degree-two coefficient of the logarithmic correction vanishes.
The cubic rate verified on the original remainder supplies the
analytic premise of the fixed-order program at degree two.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingExpansionSecondOrder

open_ipra
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalHorner (horner hornerF horner_succ horner_zero horner_canonical qadd qmul qzero)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr qmul_zero_left qzero_add qzero_canonical)
open GaussianStirlingCubicCell (cube)
open GaussianStirlingCubicRate (cubic_rate_at)
open GaussianStirlingExpansionCoefficients (logCoefficient quoted logTable log_table_length log_table_entry log_table_zero)
open GaussianStirlingExpansionConditionalError (logRate)
open GaussianStirlingExpansionErrorProgram (run returned_approximation_bound)
open GaussianStirlingExpansionExponentialError (logBudget)
open GaussianStirlingExpansionFiniteError (query logPolynomial)
open GaussianStirlingExpansionFirstOrder (first_log_polynomial)
open GaussianStirlingMultiplicative (quotientF quotientData)
open GaussianStirlingMultiplicativeAlgebra (remainderF remainderData)
open GaussianStirlingNames (source)
open GaussianStirlingRationalTelescopers (upperValue)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem second_log_polynomial (a b : PTm n) :
    Γ ⊢[PRAAx] logPolynomial 2 a b ≐ logPolynomial 1 a b := by
  let z := query a b
  let S := logTable (n := n) 1
  let T := logTable (n := n) 2
  have s0 := log_table_entry (Γ := Γ) 1 0 (by decide)
  have t1 := log_table_entry (Γ := Γ) 2 1 (by decide)
  have equalCoeff : Γ ⊢[PRAAx] entry T one ≐ entry S zero := t1.eqTrans s0.eqSymm
  have t0 : Γ ⊢[PRAAx] entry T zero ≐ qzero := by
    simpa [T,logCoefficient,quoted,num] using log_table_entry (Γ := Γ) 2 0 (by decide)
  have empty : Γ ⊢[PRAAx] horner T z one ≐ horner S z zero := by
    have t := (horner_succ T z zero).eqTrans
      ((qadd_congr ((qmul_congr (horner_zero T z) (.eqRefl z)).eqTrans (qmul_zero_left z)) t0).eqTrans
        (qzero_add qzero qzero_canonical))
    exact t.eqTrans (horner_zero S z).eqSymm
  have initial : Γ ⊢[PRAAx] horner T z two ≐ horner S z one :=
    (horner_succ T z one).eqTrans ((qadd_congr (qmul_congr empty (.eqRefl z)) equalCoeff).eqTrans
      (horner_succ S z zero).eqSymm)
  have last : Γ ⊢[PRAAx] horner T z (succ two) ≐ horner S z two :=
    (horner_succ T z two).eqTrans
      ((qadd_congr (qmul_congr initial (.eqRefl z)) ((log_table_zero 2).eqTrans (log_table_zero 1).eqSymm)).eqTrans
        (horner_succ S z one).eqSymm)
  exact (congrAp3 hornerF (log_table_length 2) (.eqRefl T) (.eqRefl z)).eqTrans
    (last.eqTrans (congrAp3 hornerF (log_table_length 1).eqSymm (.eqRefl S) (.eqRefl z)))

private theorem natural_cube (a : PTm n) : Γ ⊢[PRAAx] pw a (num 3) ≐ cube a :=
  (pw_succ a two).eqTrans (congrMul ((pw_succ a one).eqTrans (congrMul (pw_one a) (.eqRefl a))) (.eqRefl a))

theorem second_log_rate_at (p q a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 remainderF p (remainderData a b x)) (ap2 constantF q (logPolynomial 2 a b))
      (rateNumerator (one*pw b (num 3)) (pw a (num 3)) p q) (rateDenominator (pw a (num 3)) p q) := by
  have shape := (second_log_polynomial a b).eqTrans (first_log_polynomial a b hs.andE₁)
  have read := (constant_at q (upperValue a b)).eqTrans (shape.eqSymm.eqTrans (constant_at q (logPolynomial 2 a b)).eqSymm)
  have eb := (one_mul (Γ := Γ) (pw b (num 3))).eqTrans (natural_cube b)
  have ea := natural_cube (Γ := Γ) a
  let p' := GaussianCoefficientNameBounds.unit p
  let q' := GaussianCoefficientNameBounds.unit q
  have eN := congrAdd (congrMul (congrMul eb (.eqRefl p')) (.eqRefl q')) (congrMul ea (.eqRefl (p'+q')))
  have eD := congrMul (congrMul ea (.eqRefl p')) (.eqRefl q')
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) read eN.eqSymm eD.eqSymm
    (cubic_rate_at p q a b x hs)

theorem second_log_rate (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] logRate 2 a b x one := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have positive : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh a) (sh b) := by
    simpa [Fm.shift,Syn.shift,sh] using hs.shift.shift
  simpa [logRate,independentRate,logPolynomial,query,Syn.shift,sh,num,one,two,pw] using
    second_log_rate_at (var 1) (var 0) (sh a) (sh b) (sh x) positive

set_option maxHeartbeats 800000 in
theorem actual_second_Stirling_multiplicative_error_program_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 1) (var 2) ⟶ le (var 2) (var 1) ⟶ le (two*(logBudget 2*var 2)) (var 1) ⟶
        distanceBounded (ap2 quotientF (var 0) (quotientData (var 1) (var 2) (var 3)))
          (fstT (run 2 (var 0) (var 1) (var 2) one))
          (fstT (sndT (run 2 (var 0) (var 1) (var 2) one)))
          (sndT (sndT (run 2 (var 0) (var 1) (var 2) one)))) := by
  refine closeUniv 4 (.impI (.impI (.impI ?_)))
  exact returned_approximation_bound 2 _ _ _ _ one Prf.hyp1.wk Prf.hyp1 Prf.hyp0
    (second_log_rate _ _ _ Prf.hyp1.wk)

end LeanProofs.IPRA.Analysis.GaussianStirlingExpansionSecondOrder
