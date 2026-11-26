import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.GaussianStirlingAllOrderBernoulliEnvelope

/-!
# Exact derivative data for the centered Bernoulli panels

The original cleared Bernoulli sampler provides the two derivative
polynomials. Its first derivative vanishes at both ends, and its
second derivative, after dividing by the degree product, equals the
signed mean minus the preceding centered Bernoulli sample.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingAllOrderBernoulliCoefficients (normalized normalized_derivative coefficient)
open GaussianStirlingAllOrderBernoulliMesh (toZ_value lower_endpoint_value odd_endpoints_zero)
open GaussianStirlingAllOrderCenteredBernoulli
  (factor numerator denominator sample sample_canonical sample_value denominator_positive)
open GaussianStirlingAllOrderBernoulliEnvelope (subst_sample)
open BernoulliCoefficients (bc)
open BernoulliBounds (bden bden_pos bint pv zint toZ_zint)
open GaussianRationalHorner (positive_product)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalArithmetic (add multiply)
open RationalIntegerNormalization (normalize normalize_preserves_value)
open RationalNormalForm (normalize_well_formed)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def degreeProduct (m : ℕ) : ℕ := (2*m+2)*(2*m+1)

theorem factor_succ (m : ℕ) : factor (m+1) = -(degreeProduct m : ℤ)*factor m := by
  unfold factor degreeProduct
  rw [show 2*(m+1)=2*m+2 by omega, Nat.factorial_succ (2*m+1),Nat.factorial_succ (2*m)]
  push_cast
  rw [pow_succ]
  ring

noncomputable def profile (m : ℕ) : Polynomial ℚ :=
  (factor m : ℚ) • (normalized (2*m)-Polynomial.C (bc (2*m) 0))

noncomputable def signedMeanValue (m : ℕ) : ℚ := -(factor m : ℚ)*bc (2*m) 0

theorem first_derivative_identity (m : ℕ) :
    (profile (m+1)).derivative = (factor (m+1) : ℚ) • normalized (2*m+1) := by
  unfold profile
  rw [Polynomial.derivative_smul,Polynomial.derivative_sub,Polynomial.derivative_C,sub_zero,
    show 2*(m+1)=(2*m+1)+1 by omega,normalized_derivative]

theorem second_derivative_identity (m : ℕ) :
    (profile (m+1)).derivative.derivative =
      (degreeProduct m : ℚ) • (Polynomial.C (signedMeanValue m)-profile m) := by
  rw [first_derivative_identity,Polynomial.derivative_smul,normalized_derivative]
  unfold profile signedMeanValue
  rw [factor_succ]
  push_cast
  simp only [Polynomial.smul_eq_C_mul,Polynomial.C_mul,Polynomial.C_neg]
  ring

def derivativeDen (j : ℕ) (M : PTm n) : PTm n := num (bden j)*pw M (num j)

def firstNumerator (m : ℕ) (p M : PTm n) : ZT n :=
  zint (factor (m+1))*pv (bint (2*m+1)) p M

def firstSample (m : ℕ) (p M : PTm n) : PTm n :=
  normalize (firstNumerator m p M) (derivativeDen (2*m+1) M)

def secondScaledNumerator (m : ℕ) (p M : PTm n) : ZT n :=
  zint (-factor m)*pv (bint (2*m)) p M

def secondScaled (m : ℕ) (p M : PTm n) : PTm n :=
  normalize (secondScaledNumerator m p M) (denominator m M)

def secondNumerator (m : ℕ) (p M : PTm n) : ZT n :=
  zint (factor (m+1))*pv (bint (2*m)) p M

def secondSample (m : ℕ) (p M : PTm n) : PTm n :=
  normalize (secondNumerator m p M) (denominator m M)

def meanNumerator (m : ℕ) : ZT n := zint (-factor m*bint (2*m) 0)

def signedMean (m : ℕ) : PTm n := normalize (meanNumerator m) (num (bden (2*m)))

theorem derivative_den_positive (j : ℕ) (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le one (derivativeDen j M) :=
  positive_product _ _ (Foundations.NumeralPrimes.num_le (a := 1) (bden_pos j))
    (GaussianFactorBudget.power_positive _ _ hM)

theorem mean_den_positive (m : ℕ) : Γ ⊢[PRAAx] le one (num (bden (2*m)) : PTm n) :=
  Foundations.NumeralPrimes.num_le (a := 1) (bden_pos (2*m))

theorem mean_value (m : ℕ) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (signedMean m) (meanNumerator m) (num (bden (2*m))) :=
  normalize_preserves_value _ _ (mean_den_positive m)

theorem signedMean_readback (m : ℕ) :
    (-(factor m : ℚ)*(bint (2*m) 0 : ℚ))/(bden (2*m) : ℚ) = signedMeanValue m := by
  rw [BernoulliBounds.bint_eq]
  change -(factor m : ℚ)*(bc (2*m) 0*(bden (2*m) : ℚ))/(bden (2*m) : ℚ) = _
  unfold signedMeanValue
  have h : (bden (2*m) : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (bden_pos (2*m))
  field_simp

theorem first_endpoint (m : ℕ) (M : PTm n) (hm : 0 < m) (hM : Γ ⊢[PRAAx] le one M) :
    (Γ ⊢[PRAAx] firstSample m zero M ≐ fraction zero one) ∧
      (Γ ⊢[PRAAx] firstSample m M M ≐ fraction zero one) := by
  have hD := derivative_den_positive (2*m+1) M hM
  have hz := odd_endpoints_zero (Γ := Γ) (2*m+1) ⟨m,by omega⟩ (by omega) M
  have go (p : PTm n) (h : Γ ⊢[PRAAx] ZT.eq (pv (bint (2*m+1)) p M) (ZT.ofNat zero)) :
      Γ ⊢[PRAAx] firstSample m p M ≐ fraction zero one := by
    apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
      (normalize_well_formed _ _ hD) (normalize_well_formed _ _ (le_refl one))
      (normalize_preserves_value _ _ hD) (fraction_represents _ _ (le_refl one)) hD (le_refl one)
    apply ZT.derive (u := firstNumerator m p M*ZT.ofNat one)
      (v := ZT.ofNat zero*ZT.ofNat (derivativeDen (2*m+1) M))
    simp only [firstNumerator,ZT.toZ_mul,ZT.toZ_eq h,ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero]
    ring
  exact ⟨go zero hz.1,go M hz.2⟩

theorem second_scale (m : ℕ) (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] multiply (fraction (num (degreeProduct m)) one) (secondScaled m p M) ≐ secondSample m p M := by
  let D := denominator m M
  let C : PTm n := num (degreeProduct m)
  have hD := denominator_positive m M hM
  have hE := positive_product _ _ (le_refl one) hD
  have he := RationalRepresentations.represents_multiply _ _ _ _ _ _
    (fraction_represents C one (le_refl one : Γ ⊢[PRAAx] _)) (normalize_preserves_value (secondScaledNumerator m p M) D hD)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalArithmetic.multiply_guard _ _) (normalize_well_formed _ _ hD) he
    (normalize_preserves_value _ _ hD) hE hD
  apply ZT.derive (u := (ZT.ofNat C*secondScaledNumerator m p M)*ZT.ofNat D)
    (v := secondNumerator m p M*ZT.ofNat (one*D))
  dsimp only [C,secondNumerator,secondScaledNumerator]
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,toZ_zint,factor_succ,Int.cast_mul,Int.cast_neg,Int.cast_natCast]
  ipra_simps
  ring

theorem second_complement (m : ℕ) (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] add (sample m p M) (secondScaled m p M) ≐ signedMean m := by
  let D := denominator m M
  let E : PTm n := num (bden (2*m))
  have hD := denominator_positive m M hM
  have hE := mean_den_positive (Γ := Γ) m
  have rep := RationalRepresentations.represents_add _ _ _ _ D D (sample_value m p M hM)
    (normalize_preserves_value (secondScaledNumerator m p M) D hD)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (normalize_well_formed _ _ hE) rep (mean_value m) (positive_product _ _ hD hD) hE
  apply ZT.derive (u := (numerator m p M*ZT.ofNat D+secondScaledNumerator m p M*ZT.ofNat D)*ZT.ofNat E)
    (v := meanNumerator m*ZT.ofNat (D*D))
  have hz := ZT.toZ_eq (lower_endpoint_value (Γ := Γ) (2*m) M)
  dsimp only [D,E,numerator,secondScaledNumerator,meanNumerator,denominator]
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_ofNat,toZ_zint,Int.cast_mul,Int.cast_neg] at hz ⊢
  ipra_simps
  rw [hz]
  ring

theorem actual_second_derivative_complement_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (le one (var 1) ⟶ add (sample m (var 0) (var 1)) (secondScaled m (var 0) (var 1)) ≐ signedMean m) :=
  closeUniv 2 (.impI (second_complement m _ _ Prf.hyp0))

theorem actual_first_derivative_endpoints_closed (m : ℕ) (hm : 0 < m) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (le one (var 0) ⟶ firstSample m zero (var 0) ≐ fraction zero one ⋏ firstSample m (var 0) (var 0) ≐ fraction zero one) :=
  closeUniv 1 (.impI (let h := first_endpoint m (var 0) hm Prf.hyp0; .andI h.1 h.2))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelDerivative
