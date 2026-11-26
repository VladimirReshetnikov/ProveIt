import IPRADerivations.Analysis.Exponential.GaussianNamedConstantExponentialSmallTail
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalHornerPrefixTaylor
import IPRADerivations.Analysis.Gamma.GaussianGammaInputStaticNorm
import IPRADerivations.Analysis.Exponential.GaussianFiniteExponentialCoefficientMajorant
import IPRADerivations.Analysis.Stirling.GaussianStirlingExpansionFiniteError

/-!
# Recompose the original exponential on a shrinking Gaussian disk

A zero constant makes the stored polynomial's value first order in
the input radius. The original named scalar exponential's remainder
and the discarded coefficients of the original exponential buffer then
have the same shrinking factor at every internal truncation degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialExponentialRecomposition

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientL1 (coefficientNorm)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (fraction fraction_order)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope)
open GaussianRadiusExponentialName (sample)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (evaluate qzero positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPolynomialExponential (polynomial polynomial_length polynomial_evaluation polynomial_canonical)
open GaussianRationalPowerExpansion (partialSum prefix_succ prefix_zero)
open GaussianRationalSyntheticDivision (canonicalCoefficients qadd_congr qmul_congr qmul_zero_left qzero_add qzero_canonical qone)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open RationalArgmin (rationalLE)
open RationalSupMetric (numeratorOf denominatorOf)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

abbrev nameF : PR 2 := GaussianRadiusExponentialName.nameF constantF
def data (C w : PTm n) : PTm n := GaussianRadiusExponentialName.data one (evaluate C w)
def value (C N m w : PTm n) : PTm n := partialSum (polynomial C N m) (m*N) w (succ m)
def numerator (m L M H : PTm n) : PTm n := (two*pw L (succ m)+M)*pw H (succ m)
def denominator (m B : PTm n) : PTm n := pw B (succ m)

def input (C N m w H B L : PTm n) : Fm PTm n :=
  (length C ≐ succ N) ⋏ ((entry C N ≐ qzero) ⋏ (le m (m*N) ⋏
    (le one B ⋏ (le H B ⋏ (le (two*(L*H)) B ⋏
      (rationalLE (coefficientNorm C) (fraction L one) ⋏ bounded w H B))))))

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (C w : PTm n) :
    Syn.subst σ (data C w) = data (Syn.subst σ C) (Syn.subst σ w) := by simp [data,one]

@[simp] theorem subst_value {l : ℕ} (σ : Fin n → PTm l) (C N m w : PTm n) :
    Syn.subst σ (value C N m w) = value (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ m) (Syn.subst σ w) := by simp [value]

@[simp] theorem subst_numerator {l : ℕ} (σ : Fin n → PTm l) (m L M H : PTm n) :
    Syn.subst σ (numerator m L M H) = numerator (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ M) (Syn.subst σ H) :=
  by simp [numerator,two]

@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (m B : PTm n) :
    Syn.subst σ (denominator m B) = denominator (Syn.subst σ m) (Syn.subst σ B) := by simp [denominator]

@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (C N m w H B L : PTm n) :
    (input C N m w H B L).subst σ =
      input (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ m) (Syn.subst σ w) (Syn.subst σ H) (Syn.subst σ B) (Syn.subst σ L) :=
  by simp [input,one,two]

private theorem constant_prefix (C N w : PTm n) (h : Γ ⊢[PRAAx] entry C N ≐ qzero) :
    Γ ⊢[PRAAx] partialSum C N w one ≐ qzero := by
  have coefficient : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.coefficient C N zero ≐ qzero :=
    (entry_congr (.eqRefl _) (monus_zero _)).eqTrans h
  have term : Γ ⊢[PRAAx] GaussianOffDominantTerms.term C N w zero ≐ qzero :=
    (qmul_congr coefficient (.eqRefl _)).eqTrans (qmul_zero_left _)
  exact (prefix_succ _ _ _ _ (zero_le _)).eqTrans
    ((qadd_congr (prefix_zero _ _ _) term).eqTrans (qzero_add _ qzero_canonical))

theorem evaluation_bound (C N w H B L : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hZero : Γ ⊢[PRAAx] entry C N ≐ qzero) (hB : Γ ⊢[PRAAx] le one B)
    (hSmall : Γ ⊢[PRAAx] le H B) (hMass : Γ ⊢[PRAAx] rationalLE (coefficientNorm C) (fraction L one))
    (hw : Γ ⊢[PRAAx] bounded w H B) : Γ ⊢[PRAAx] bounded (evaluate C w) (L*H) B := by
  have e := GaussianShrinkingPolynomialTail.finite_coefficient_tail C N zero w L one H B hLen
    (zero_le _) (le_refl _) hB hSmall hMass hw
  have normalized := distance_congr (.eqRefl _) (constant_prefix C N w hZero)
    (congrMul (.eqRefl L) (pw_one H)) ((congrMul (.eqRefl one) (pw_one B)).eqTrans (one_mul B)) e
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ hB).andE₁.impE normalized

private theorem half_disk (C N m w H B L : PTm n) (h : Γ ⊢[PRAAx] input C N m w H B L) :
    Γ ⊢[PRAAx] bounded (evaluate C w) one two := by
  have upper := evaluation_bound C N w H B L h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁
    h.andE₂.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  exact bounded_radius_mono _ _ _ _ _ h.andE₂.andE₂.andE₂.andE₁ RationalAlgebra.two_positive
    (le_congr (mul_comm _ _) (one_mul B).eqSymm h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁) upper

theorem sample_error (C N m w H B L M p : PTm n) (h : Γ ⊢[PRAAx] input C N m w H B L)
    (hExp : Γ ⊢[PRAAx] rationalLE (coefficientNorm (polynomial C N m)) (fraction M one)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data C w)) (value C N m w)
      (numerator m L M H*unit p+two*denominator m B) (denominator m B*unit p) := by
  let d := succ m
  let D := denominator m B
  let A := pw H d
  let U := unit p
  let q := evaluate C w
  let E := polynomial C N m
  have hB := h.andE₂.andE₂.andE₂.andE₁
  have hSmall := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have hMass := h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have hw := h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  have hD : Γ ⊢[PRAAx] le one D := GaussianFactorBudget.power_positive B d hB
  have hu := unit_positive (Γ := Γ) p
  have hDU := positive_product D U hD hu
  have eval := evaluation_bound C N w H B L h.andE₁ h.andE₂.andE₁ hB hSmall hMass hw
  have scalar := GaussianNamedConstantExponentialSmallTail.constant_error q m p (L*H) B hB eval (half_disk C N m w H B L h)
  have drop := GaussianShrinkingPolynomialTail.finite_coefficient_tail E (m*N) m w M one H B
    (polynomial_length C N m) h.andE₂.andE₂.andE₁ (le_refl one) hB hSmall hExp hw
  have drop' := distance_congr (polynomial_evaluation C N m w h.andE₁) (.eqRefl _) (.eqRefl _) (one_mul D) drop
  have lift := distance_radius_mono _ _ _ _ (M*A*U) (D*U) hD hDU
    (le_of_eq_add (d := zero) (by ipra_ring)) drop'
  have total := distance_triangle_same _ _ _ _ _ _ hDU scalar lift
  have factor := LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor.pw_mul_base (Γ := Γ) L H (succ m)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by
    apply deriveNat
    dsimp only [GaussianNamedConstantExponentialSmallTail.errorNumerator,numerator,d,D,A,U,denominator]
    ipra_simps
    rw [natEq factor]
    ipra_simps
    ring) (.eqRefl _) total

theorem rate (C N m w H B L M : PTm n) (h : Γ ⊢[PRAAx] input C N m w H B L)
    (hExp : Γ ⊢[PRAAx] rationalLE (coefficientNorm (polynomial C N m)) (fraction M one)) : Γ ⊢[PRAAx]
    independentRate nameF constantF (data C w) (value C N m w) (numerator m L M H) (denominator m B) := by
  let D := denominator m B
  have hD : Γ ⊢[PRAAx] le one D := GaussianFactorBudget.power_positive B (succ m) h.andE₂.andE₂.andE₂.andE₁
  have disk := bounded_radius_mono _ _ _ _ _ RationalAlgebra.two_positive (le_refl one)
    (le_congr (one_mul one).eqSymm (one_mul two).eqSymm RationalAlgebra.two_positive)
    (half_disk C N m w H B L h)
  have reg := GaussianRadiusExponentialName.name_regular constantF one (evaluate C w)
    (GaussianSignedNameExponentialOrder.constant_input _ _ disk)
  refine GaussianNamedLipschitzRate.independent_rate nameF constantF (data C w) (value C N m w)
    (numerator m L M H) D two hD reg (constant_regular _) (.allI ?_)
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] input (s C) (s N) (s m) (s w) (s H) (s B) (s L) := by
    simpa [Δ,s,Fm.shift,Syn.shift] using h.shift
  have hm : Δ ⊢[PRAAx] rationalLE (coefficientNorm (polynomial (s C) (s N) (s m))) (fraction (s M) one) := by
    simpa [Δ,s,Fm.shift,Syn.shift,one] using hExp.shift
  have e := sample_error (s C) (s N) (s m) (s w) (s H) (s B) (s L) (s M) (var 0) hs hm
  simpa only [diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,GaussianNamedLipschitzRate.diagonalDenominator,
    Δ,s,D,Syn.shift,subst_data,subst_value,subst_numerator,subst_denominator,
    two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    distance_congr (.eqRefl _) (constant_at (var 0) (value (s C) (s N) (s m) (s w))).eqSymm (.eqRefl _) (.eqRefl _) e

theorem uniform_rate (C N m w H B L : PTm n) (h : Γ ⊢[PRAAx] input C N m w H B L)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) : Γ ⊢[PRAAx]
    independentRate nameF constantF (data C w) (value C N m w) (numerator m L (pw (num 3) L) H) (denominator m B) := by
  let ec := polynomial C N m
  have hu := GaussianGammaInputStaticNorm.unit_weighted_norm C N h.andE₁ hCan
  have hk := GaussianGammaInputStaticNorm.unit_weighted_norm (Γ := Γ) ec (m*N)
    (polynomial_length C N m) (polynomial_canonical C N m)
  have src : Γ ⊢[PRAAx] rationalLE (GaussianRationalPolynomialDilation.weightedNorm C N qone)
    (GaussianRationalSyntheticBounds.natCode L) :=
    RationalArgmin.rationalLE_congr hu.eqSymm (.eqRefl _) h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have mass := GaussianFiniteExponentialCoefficientMajorant.polynomial_numerical_majorant C N m qone L h.andE₁ src
  exact rate C N m w H B L (pw (num 3) L) h (RationalArgmin.rationalLE_congr hk (.eqRefl _) mass)

def coefficientBudget (C : PTm n) : PTm n := (numeratorOf (coefficientNorm C)).pos

theorem computed_mass (C : PTm n) : Γ ⊢[PRAAx] rationalLE (coefficientNorm C) (fraction (coefficientBudget C) one) := by
  let c := coefficientNorm C
  let b := coefficientBudget C
  let d := denominatorOf c
  have hd := RationalArgmin.denominator_positive (Γ := Γ) c
  exact RationalArgmin.transitive (GaussianStirlingExpansionFiniteError.norm_upper c)
    (fraction_order b d b one hd (le_refl _)
      (le_congr (.eqRefl _) (mul_comm d b) (mul_le_mul_right b hd)))

theorem computed_rate (C N m w H B : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hZero : Γ ⊢[PRAAx] entry C N ≐ qzero) (hDegree : Γ ⊢[PRAAx] le m (m*N))
    (hB : Γ ⊢[PRAAx] le one B) (hRadius : Γ ⊢[PRAAx] le H B)
    (hSmall : Γ ⊢[PRAAx] le (two*(coefficientBudget C*H)) B)
    (hw : Γ ⊢[PRAAx] bounded w H B) (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) : Γ ⊢[PRAAx]
    independentRate nameF constantF (data C w) (value C N m w)
      (numerator m (coefficientBudget C) (pw (num 3) (coefficientBudget C)) H) (denominator m B) :=
  uniform_rate C N m w H B (coefficientBudget C)
    (.andI hLen (.andI hZero (.andI hDegree (.andI hB (.andI hRadius (.andI hSmall (.andI (computed_mass C) hw)))))))
    hCan

theorem actual_stored_exponential_recomposition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let C := var 0
     let N := var 1
     let m := var 2
     let w := var 3
     let H := var 4
     let B := var 5
     let L := var 6
     input C N m w H B L ⟶ canonicalCoefficients C ⟶
       independentRate nameF constantF (data C w) (value C N m w) (numerator m L (pw (num 3) L) H) (denominator m B)) :=
  closeUniv 7 (.impI (.impI (uniform_rate _ _ _ _ _ _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialExponentialRecomposition
