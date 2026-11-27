import IPRADerivations.Analysis.Gamma.EulerProducts.OriginalPrefixes.GaussianGammaOriginalPrefixRegularity

/-!
# Actual finite evaluation of the canonical Gamma coefficient names

The raw observation is the literal finite sum of the SAME canonical
HigherCoefficientName sample at degree e times the original query power.
Its proved modulus and explicit FastValueCut clock give a genuine name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCanonicalPrefixName

open_ipra
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (power)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianRationalL1 (qL1)
open GaussianCoefficientL1 (qL1_congr)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalSyntheticBounds (natCode)
open GaussianGammaInputPrecisionNorm (radiusNumerator radiusDenominator denominator_positive)
open GaussianEuclideanDistanceName (fraction pointCN)
open RationalArgmin (rationalLE)
open RationalArithmetic (multiply)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def termData (p w : PTm n) : PTm n := pairT p w
def term (p w e : PTm n) : PTm n := qmul (GaussianGammaHigherCoefficientName.sample p e) (power w e)
def termBody : PTm 2 := term (fstT (var 1)) (sndT (var 1)) (var 0)
def rawValue (p d w : PTm n) : PTm n := GaussianRationalFiniteSum.sum termBody (succ d) (termData p w)
def rawF : PR 2 := PTm.toPR (rawValue (var 0) (fstT (var 1)) (sndT (var 1)))
def termModulus (R d : PTm n) : PTm n := (two*two)*pw R d
def modulus (R d : PTm n) : PTm n := succ d*termModulus R d
def nameF : PR 2 := GaussianFastValueCut.nameF rawF
def data (d R w : PTm n) : PTm n := GaussianFastValueCut.nameData (modulus R d) (pairT d w)
def clock (p R d : PTm n) : PTm n := GaussianFastValueCut.exponent (modulus R d) p
def sample (p d R w : PTm n) : PTm n := ap2 nameF p (data d R w)
ipra_subst termData
ipra_subst term
ipra_subst rawValue
ipra_subst termModulus
ipra_subst modulus
ipra_subst data
ipra_subst clock
ipra_subst sample

theorem term_congr {p q w v e f : PTm n} (hp : Γ ⊢[PRAAx] p ≐ q) (hw : Γ ⊢[PRAAx] w ≐ v)
    (he : Γ ⊢[PRAAx] e ≐ f) : Γ ⊢[PRAAx] term p w e ≐ term q v f := by
  ipra_congr (term (var 0) (var 1) (var 2) : PTm 3) with [hp, hw, he]
theorem term_at (p w e : PTm n) : Γ ⊢[PRAAx] inst2 termBody e (termData p w) ≐ term p w e := by
  simp only [termBody,inst2,subst_term,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact term_congr (fst_pair _ _) (snd_pair _ _) (.eqRefl _)

theorem power_bound (R d w e : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hw : Γ ⊢[PRAAx] bounded w R one)
    (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx] bounded (power w e) (pw R d) one :=
  GaussianCoefficientNameBounds.bounded_radius_mono_one (GaussianFactorBudget.power_monotone_length R e d hR he)
    (GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _) (GaussianPolynomialPerturbation.one_power e)
      (GaussianRationalReciprocal.bounded_power _ R one e (le_refl one) hw))

theorem term_error (p q R d w e : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hw : Γ ⊢[PRAAx] bounded w R one)
    (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (term p w e) (term q w e)))
      (fraction (termModulus R d*radiusNumerator p q) (radiusDenominator p q)) := by
  have pNorm : Γ ⊢[PRAAx] rationalLE (qL1 (power w e)) (natCode (two*pw R d)) :=
    GaussianRationalL1Algebra.qL1_of_bounded _ _ _ (le_refl one) (power_bound R d w e hR hw he)
  have cNorm := GaussianRationalL1Algebra.qL1_of_bounded _ _ _ (denominator_positive (Γ := Γ) p q)
    (GaussianNameEquivalence.point_at GaussianGammaHigherCoefficientName.nameF (GaussianGammaHigherCoefficientName.data e) p q
      (GaussianGammaHigherCoefficientName.name_regular e))
  have bound := RationalArgmin.transitive (GaussianRationalL1Algebra.qL1_multiply (Γ := Γ) _ _)
    (GaussianFiniteExponentialWeightedNorm.multiply_bounds _ _ _ _ (GaussianRationalL1.qL1_nonnegative _)
      (GaussianRationalSyntheticBounds.natCode_nonnegative _) pNorm cNorm)
  have code : Γ ⊢[PRAAx] qsub (term p w e) (term q w e) ≐ qmul (power w e)
      (qsub (GaussianGammaHigherCoefficientName.sample p e) (GaussianGammaHigherCoefficientName.sample q e)) :=
    (qsub_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)).eqTrans
      (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference _ _ _)
  have scale : Γ ⊢[PRAAx] multiply (natCode (two*pw R d))
      (fraction (two*radiusNumerator p q) (radiusDenominator p q)) ≐
      fraction (termModulus R d*radiusNumerator p q) (radiusDenominator p q) :=
    RationalNonnegativePowers.nat_mul_fraction (denominator_positive p q) (by unfold termModulus; ipra_ring)
  exact RationalArgmin.rationalLE_congr (qL1_congr code).eqSymm scale bound

theorem raw_regularity (p q R d w : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hw : Γ ⊢[PRAAx] bounded w R one) : Γ ⊢[PRAAx]
    distanceBounded (rawValue p d w) (rawValue q d w) (modulus R d*radiusNumerator p q) (radiusDenominator p q) := by
  have rs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hR.shift
  have ws : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift w) (Syn.shift R) one := by simpa [Fm.shift,Syn.shift] using hw.shift
  have terms : Γ ⊢[PRAAx] GaussianFiniteSumL1Variation.termsError termBody termBody (succ d) (termData p w) (termData q w)
      (fraction (termModulus R d*radiusNumerator p q) (radiusDenominator p q)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (succ (Syn.shift d)) :: Γ.map Fm.shift
    have actual := RationalArgmin.rationalLE_congr (qL1_congr (qsub_congr
      (term_at (Γ := Δ) (Syn.shift p) (Syn.shift w) (var 0)) (term_at (Syn.shift q) (Syn.shift w) (var 0)))).eqSymm (.eqRefl _)
      (term_error (Syn.shift p) (Syn.shift q) (Syn.shift R) (Syn.shift d) (Syn.shift w) (var 0) rs.wk ws.wk
        ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0))
    simpa only [Δ,Syn.shift,subst_termData,GaussianEuclideanDistanceName.subst_fraction,subst_termModulus,
      GaussianGammaInputPrecisionNorm.subst_radiusNumerator,GaussianGammaInputPrecisionNorm.subst_radiusDenominator,
      PTm.subst_mul,ConciseIPRA.PTm.subst_succ] using actual
  have scale : Γ ⊢[PRAAx] multiply (natCode (succ d)) (fraction (termModulus R d*radiusNumerator p q) (radiusDenominator p q)) ≐
      fraction (modulus R d*radiusNumerator p q) (radiusDenominator p q) :=
    RationalNonnegativePowers.nat_mul_fraction (denominator_positive p q) (by unfold modulus; ipra_ring)
  exact GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (denominator_positive p q)
    (RationalArgmin.rationalLE_congr (.eqRefl _) scale (GaussianFiniteSumL1Variation.sum_error _ _ _ _ _ _ terms))

theorem raw_value_congr {p q d e w v : PTm n} (hp : Γ ⊢[PRAAx] p ≐ q) (hd : Γ ⊢[PRAAx] d ≐ e)
    (hw : Γ ⊢[PRAAx] w ≐ v) : Γ ⊢[PRAAx] rawValue p d w ≐ rawValue q e v := by
  ipra_congr (rawValue (var 0) (var 1) (var 2) : PTm 3) with [hp, hd, hw]
theorem raw_at (p d w : PTm n) : Γ ⊢[PRAAx] ap2 rawF p (pairT d w) ≐ rawValue p d w := by
  simpa [rawF] using
    (toPR_pair_eq (Γ := Γ) (rawValue (var 0) (var 1) (var 2)) p d w)

theorem raw_regular (R d w : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hw : Γ ⊢[PRAAx] bounded w R one) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular rawF (modulus R d) (pairT d w) := by
  have rs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift R)) := by simpa [Fm.shift,Syn.shift] using hR.shift.shift
  have ws : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] bounded (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift R)) one := by simpa [Fm.shift,Syn.shift] using hw.shift.shift
  refine .allI (.allI ?_)
  have actual := GaussianRationalDistanceOrder.distance_congr
    (raw_at (Γ := (Γ.map Fm.shift).map Fm.shift) (var 1) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift w))).eqSymm
    (raw_at (var 0) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift w))).eqSymm (.eqRefl _) (.eqRefl _)
      (raw_regularity (var 1) (var 0) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift w)) rs ws)
  simpa only [GaussianFastValueCut.regular,Syn.shift,subst_pairT,subst_modulus,
    GaussianGammaInputPrecisionNorm.radiusNumerator,GaussianGammaInputPrecisionNorm.radiusDenominator,unit] using actual

theorem name_regular (d R w : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hw : Γ ⊢[PRAAx] bounded w R one) : Γ ⊢[PRAAx]
    pointCN nameF (data d R w) := GaussianFastValueCut.name_fast rawF (modulus R d) (pairT d w) (raw_regular R d w hR hw)
theorem sample_at (p d R w : PTm n) : Γ ⊢[PRAAx] sample p d R w ≐ rawValue (clock p R d) d w :=
  (GaussianFastValueCut.name_at rawF (modulus R d) (pairT d w) p).eqTrans
    ((GaussianNameArithmetic.recode_congr (raw_at (clock p R d) d w)).eqTrans
      (GaussianNamedSmallPerturbationTransport.recode_fixed _ (GaussianRationalFiniteSum.sum_canonical _ _ _)))

theorem actual_canonical_Gamma_finite_coefficient_evaluation_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ bounded (var 2) (var 1) one ⟶ pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (name_regular _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_canonical_Gamma_finite_coefficient_evaluation_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sample (var 0) (var 1) (var 2) (var 3) ≐ rawValue (clock (var 0) (var 2) (var 1)) (var 1) (var 3)) :=
  closeUniv 4 (sample_at _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaCanonicalPrefixName
