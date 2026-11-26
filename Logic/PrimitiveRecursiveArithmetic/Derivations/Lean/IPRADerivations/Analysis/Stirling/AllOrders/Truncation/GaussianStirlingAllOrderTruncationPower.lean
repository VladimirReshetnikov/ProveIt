import IPRADerivations.Analysis.Stirling.AllOrders.Truncation.GaussianStirlingAllOrderTruncationAlgebra
import IPRADerivations.Analysis.Stirling.Expansions.GaussianStirlingExpansionFirstOrder

/-!
# The correction terms use the original table and reciprocal powers

The explicit fixed Bernoulli numeral represents the same rational
coefficient quoted in the original logarithmic polynomial. Powers
are computed by the original Gaussian rational power program.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderTruncationPower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open BernoulliBounds (zint toZ_zint bden bden_pos)
open GaussianStirlingAllOrderTruncationCoefficients (literalCoefficient literalPower literalTerm coefficientNumerator coefficient_value)
open GaussianStirlingAllOrderTruncationAlgebra (correction)
open GaussianStirlingAllOrderReciprocalWeightError (power)
open GaussianStirlingExpansionCoefficients (quoted logCoefficient)
open GaussianStirlingExpansionFiniteError (query)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents positive_product canonical_unique
  zero_represents represents_congr qzero qmul)
open GaussianRationalSyntheticDivision (qmul_congr qone)
open RationalGaussianEmbedding (embed embed_multiply embed_from_representation embed_canonical native)
open RationalGaussianRealPart (embed_congr)
open RationalIntegerNormalization (normalize normalize_preserves_value)
open RationalNormalForm (normalize_well_formed)
open GaussianEuclideanDistanceName (fraction)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem signed_quote (q : ℚ) (z : ℤ) (D : ℕ) (hD : 0<D) (hv : (z : ℚ)=q*D) :
    Γ ⊢[PRAAx] embed (normalize (zint z) (num D) : PTm n) ≐ quoted q := by
  let y : PTm n := num D
  have hd : Γ ⊢[PRAAx] le one y := Foundations.NumeralPrimes.num_le (a := 1) hD
  have hq : Γ ⊢[PRAAx] le one (num q.den : PTm n) := Foundations.NumeralPrimes.num_le (a := 1) q.den_pos
  by_cases hz : q=0
  · have z0 : z=0 := by
      have w : (z : ℚ)=0 := by simpa [hz] using hv
      exact_mod_cast w
    rw [hz,z0]
    unfold quoted
    rw [if_pos rfl]
    apply canonical_unique _ _ _ _ (embed_canonical _) (GaussianRationalSyntheticDivision.qzero_canonical) hd
      (hrv := zero_represents y)
    apply represents_congr (.eqRefl _) (hAB := .eqRefl _)
      (h := embed_from_representation _ _ _ (normalize_preserves_value (zint 0) y hd))
    apply GaussianRootAlgebra.equal_of_values <;>
      simp [native,ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,
        GaussianRootAlgebra.re_zero,GaussianRootAlgebra.im_zero,toZ_zint]
  · have qD : (q.den : ℚ) ≠ 0 := by positivity
    have w : (z : ℚ)*q.den = (q.num : ℚ)*D := by
      calc
        (z : ℚ)*q.den = (q.num/(q.den : ℚ))*D*q.den := by
          rw [hv,Rat.num_div_den]
        _ = (q.num : ℚ)*D := by field_simp
    have w' : z*(q.den : ℤ)=q.num*(D : ℤ) := by exact_mod_cast w
    have e : Γ ⊢[PRAAx] normalize (zint z) y ≐ normalize (zint q.num) (num q.den) := by
      apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
        (normalize_well_formed _ _ hd) (normalize_well_formed _ _ hq)
        (normalize_preserves_value _ _ hd) (normalize_preserves_value _ _ hq) hd hq
      apply ZT.derive
      simp only [ZT.toZ_mul,ZT.toZ_ofNat,toZ_zint]
      unfold y
      ipra_simps
      simpa only [Int.cast_mul,Int.cast_natCast] using congrArg (fun i : ℤ => (i : Groth (Q Γ))) w'
    unfold quoted
    rw [if_neg hz]
    exact (embed_congr e).eqTrans
      (canonical_unique _ _ _ _ (embed_canonical _) (ofGaussian_canonical _ _ hq) hq
        (embed_from_representation _ _ _ (normalize_preserves_value (zint q.num) (num q.den) hq))
        (ofGaussian_represents _ _ hq))

theorem literal_coefficient_quoted (m : ℕ) : Γ ⊢[PRAAx]
    embed (literalCoefficient (n := n) m) ≐ quoted (logCoefficient (2*m+1)) :=
  signed_quote _ _ _ (bden_pos (2*m+2)) (coefficient_value m)

private theorem num_succ (k : ℕ) : Γ ⊢[PRAAx] (num (k+1) : PTm n) ≐ succ (num k) := by
  apply deriveNat
  ipra_simps
  push_cast
  ring

private theorem query_one : Γ ⊢[PRAAx] query (one : PTm n) one ≐ qone := by
  apply GaussianGammaFiniteValueProperness.fraction_equal _ _ _ (le_refl one)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,
      GaussianRootAlgebra.im_one]

theorem query_pow (k : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    GaussianRationalReciprocal.power (query A B) (num k) ≐ query (power k A) (power k B) := by
  induction k with
  | zero =>
    have q : Γ ⊢[PRAAx] query (power 0 A) (power 0 B) ≐ query one one :=
      GaussianEulerPositivePowerChartJacobian.fraction_congr (pw_zero B) (pw_zero A)
    exact (GaussianRationalReciprocal.power_zero _).eqTrans (q.eqTrans query_one).eqSymm
  | succ k ih =>
    let j : PTm n := num k
    have e : Γ ⊢[PRAAx] num (k+1) ≐ succ j := num_succ k
    have da : Γ ⊢[PRAAx] power (k+1) A ≐ power k A*A :=
      (congrAp2 powF e (.eqRefl _)).eqTrans (pw_succ A j)
    have db : Γ ⊢[PRAAx] power (k+1) B ≐ power k B*B :=
      (congrAp2 powF e (.eqRefl _)).eqTrans (pw_succ B j)
    have hd : Γ ⊢[PRAAx] le one (power k A) := GaussianFactorBudget.power_positive _ _ hA
    exact (congrAp2 GaussianRationalReciprocal.powerF e (.eqRefl _)).eqTrans
      ((GaussianRationalReciprocal.power_succ _ j).eqTrans
        ((qmul_congr ih (.eqRefl _)).eqTrans
          ((GaussianEulerDampedTimeRate.fraction_product (power k B) (power k A) B A hd hA).eqTrans
            (GaussianEulerPositivePowerChartJacobian.fraction_congr db.eqSymm da.eqSymm))))

theorem correction_at (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    qmul (quoted (logCoefficient (2*m+1))) (GaussianRationalReciprocal.power (query A B) (num (2*m+1))) ≐ correction m A B := by
  let k := 2*m+1
  have hd : Γ ⊢[PRAAx] le one (power k A) := GaussianFactorBudget.power_positive _ _ hA
  have qw := (query_pow k A B hA).eqTrans (GaussianEulerDecayOrder.fraction_embedding (power k B) (power k A) hd).eqSymm
  exact (qmul_congr (literal_coefficient_quoted m).eqSymm qw).eqTrans (embed_multiply _ _).eqSymm

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderTruncationPower
