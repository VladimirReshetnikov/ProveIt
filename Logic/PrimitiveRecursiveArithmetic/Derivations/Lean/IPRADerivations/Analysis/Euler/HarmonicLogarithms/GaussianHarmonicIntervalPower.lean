import IPRADerivations.Analysis.Series.Harmonic.RationalHarmonicIntervalProduct
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalNaturalScale

/-!
# Actual finite harmonic logarithms of numerical rational powers

The same original finite interval at a^j/b^j differs from j times the
original interval at a/b by at most 2j/Q. A genuine quantifier-free
induction accumulates the checked finite product error at every internal
j. No logarithm power law or name-level induction is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianHarmonicIntervalPower

open_ipra
open RationalHarmonicInterval (interval numerator horizon common_value common_canonical)
open GaussianRationalHorner (qzero qadd)
open GaussianRationalNaturalScale (natScale)
open RationalGaussianEmbedding (embed native)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (a b Q j : PTm n) : PTm n := embed (interval (pw a j) (pw b j) Q)
def base (a b Q : PTm n) : PTm n := embed (interval a b Q)
def scaled (a b Q j : PTm n) : PTm n := natScale j (base a b Q)
def law (a b Q j : PTm n) : Fm PTm n := distanceBounded (value a b Q j) (scaled a b Q j) (two*j) Q
ipra_subst value
ipra_subst base
ipra_subst scaled
ipra_subst law

theorem interval_index_congr {a b Q c d : PTm n} (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d) : Γ ⊢[PRAAx]
    embed (interval a b Q) ≐ embed (interval c d Q) := by
  have e : Γ ⊢[PRAAx] interval a b Q ≐ interval c d Q := by
    ipra_congr (interval (var 0) (var 1) (var 2) : PTm 3) with [ha, hb, .eqRefl Q]
  exact RationalGaussianRealPart.embed_congr e

theorem interval_self_zero (a Q : PTm n) : Γ ⊢[PRAAx] embed (interval a a Q) ≐ qzero := by
  let F := Products.fact (horizon a a Q)
  have hF := GammaEulerMesh.factorial_positive (Γ := Γ) (horizon a a Q)
  have r := RationalGaussianEmbedding.embed_from_representation _ _ _ (common_value (Γ := Γ) a a Q (horizon a a Q))
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (native (numerator a a Q (horizon a a Q))) ComplexLogarithmRemainder.zeroCode := by
    apply GaussianRootAlgebra.equal_of_values
    · simp only [native,ComplexLogarithmRemainder.eval_re_code,GaussianRootAlgebra.re_zero]
      simp only [numerator,ZT.toZ]
      ring
    · simp only [native,ComplexLogarithmRemainder.eval_im_code,GaussianRootAlgebra.im_zero,ZT.toZ_ofNat]
      ipra_simps
  exact GaussianRationalHorner.canonical_unique _ _ _ F (RationalGaussianEmbedding.embed_canonical _) GaussianRationalSyntheticDivision.qzero_canonical hF
    (GaussianRationalHorner.represents_congr (.eqRefl _) e (.eqRefl _) r) (GaussianRationalHorner.zero_represents _)

theorem value_zero (a b Q : PTm n) : Γ ⊢[PRAAx] value a b Q zero ≐ qzero :=
  (interval_index_congr (pw_zero a) (pw_zero b)).eqTrans (interval_self_zero one Q)

theorem scaled_succ (a b Q j : PTm n) : Γ ⊢[PRAAx] scaled a b Q (succ j) ≐ qadd (scaled a b Q j) (base a b Q) :=
  (GaussianRationalNaturalScale.natScale_congr (by ipra_ring : Γ ⊢[PRAAx] succ j ≐ j+one) (.eqRefl (base a b Q))).eqTrans
    ((GaussianRationalNaturalScale.natScale_add j one (base a b Q)).eqTrans
      (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _)
        (GaussianRationalNaturalScale.natScale_one_canonical _ (RationalGaussianEmbedding.embed_canonical _))))

theorem step (a b Q j : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hQ : Γ ⊢[PRAAx] le one Q) (ih : Γ ⊢[PRAAx] law a b Q j) : Γ ⊢[PRAAx] law a b Q (succ j) := by
  have row := RationalHarmonicIntervalProduct.finite_product_error (pw a j) (pw b j) a b Q
    (GaussianPolynomialPerturbation.power_positive a j ha) (GaussianPolynomialPerturbation.power_positive b j hb) ha hb hQ
  have first := distance_congr (interval_index_congr (pw_succ a j) (pw_succ b j)).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) row
  have second := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hQ ih
    (GaussianRationalPowerDifference.distance_refl_zero (base a b Q) Q hQ)
  exact distance_congr (.eqRefl _) (scaled_succ a b Q j).eqSymm (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hQ first second)

theorem finite_power (a b Q j : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx] law a b Q j := by
  have all : Γ ⊢[PRAAx] .all (law (Syn.shift a) (Syn.shift b) (Syn.shift Q) (var 0)) := by
    ipra_qfind (by simp [law,distanceBounded,GaussianRationalMetric.bounded,RationalArgmin.rationalLE,Fm.QF,le_QF]) [
        subst_law]
    · exact distance_congr (value_zero a b Q).eqSymm (GaussianRationalNaturalScale.natScale_zero (base a b Q)).eqSymm
        (by ipra_ring) (.eqRefl _) (GaussianRationalPowerDifference.distance_refl_zero (qzero : PTm n) Q hQ)
    · have as : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using ha.shift
      have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hb.shift
      have qs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift Q) := by simpa [Fm.shift,Syn.shift] using hQ.shift
      exact step _ _ _ (var 0) as.wk bs.wk qs.wk Prf.hyp0
  simpa only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem actual_finite_harmonic_power_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 0) ⋏ (le one (var 1) ⋏ le one (var 2))) ⟶ law (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (finite_power _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianHarmonicIntervalPower
