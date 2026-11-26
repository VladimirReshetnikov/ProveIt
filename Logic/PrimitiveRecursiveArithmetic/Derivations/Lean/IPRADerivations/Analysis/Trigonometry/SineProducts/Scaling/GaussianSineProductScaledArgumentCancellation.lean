import IPRADerivations.Analysis.Trigonometry.SineProducts.Scaling.GaussianSineProductScaledArguments
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentSlope
import IPRADerivations.Analysis.Gamma.Names.PositiveAxis.GaussianNamedGammaFirstCrossing
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameConjugation

/-!
# Apartness and cancellation of the encoded scaled π argument

The finite slope of the original arctangent mesh gives a positive
lower bound at every quarter-turn observation. This yields a uniform
reciprocal margin for an encoded nonzero Gaussian numerator and exact
zero samples when the numerator has zero squared norm.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductScaledArgumentCancellation

open_ipra
open ComplexLogarithmRemainder (normSq normSq_scale scale zeroCode)
open GaussianArctangentDivisionAngles (quarterNumerator quarterDenominator)
open GaussianArctangentExponentialPrefix (original_mesh_source total)
open GaussianBoundedConstantProductName (clock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaHalfPiName (meshAt clearing)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameConjugation (pointwiseEqual equal_samples_cross)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameReciprocal (lower apart anchor)
open GaussianRationalHorner (qzero qmul_canonical positive_product canonical_unique
  canonical_congr represents_congr zero_represents)
open GaussianRationalMetric (qnormSq_represents squared_tolerance_represents comparison_of_cleared)
open GaussianRootAlgebra (equal_of_values re_zero im_zero)
open GaussianSineProductScaledArguments (nameF data name_regular sample_at sample_represents)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def apartClock (B m : PTm n) : PTm n := GaussianRootSchedule.binaryLength (B*m)

ipra_subst apartClock

theorem quarter_lower (p : PTm n) : Γ ⊢[PRAAx] le (quarterDenominator p) (quarterNumerator p) := by
  let M := meshAt p
  let L := clearing p
  have source := original_mesh_source (Γ := Γ) p
  have hend : Γ ⊢[PRAAx] le (zero+M) M := le_congr (zero_add M).eqSymm (.eqRefl _) (le_refl _)
  have raw := (GaussianArctangentSlope.finite_slope zero M M L source hend).andE₁
  change Γ ⊢[PRAAx] le (M*fact L+two*M*total zero M L) (two*M*total (zero+M) M L) at raw
  have e₀ : Γ ⊢[PRAAx] total zero M L ≐ zero := sum_zero _ _
  have eM : Γ ⊢[PRAAx] total (zero+M) M L ≐ total M M L := by
    simpa using Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (total (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![zero+M,M,L]) (σ' := ![M,M,L]) (fun i => by
        fin_cases i
        · exact zero_add M
        · exact .eqRefl _
        · exact .eqRefl _)
  have left : Γ ⊢[PRAAx] M*fact L+two*M*total zero M L ≐ M*quarterDenominator p :=
    (congrAdd (.eqRefl _) (congrMul (.eqRefl _) e₀)).eqTrans (by unfold quarterDenominator; dsimp only [L]; ipra_ring)
  have right : Γ ⊢[PRAAx] two*M*total (zero+M) M L ≐ M*quarterNumerator p :=
    (congrMul (.eqRefl _) eM).eqTrans (by unfold quarterNumerator; dsimp only [M,L]; ipra_ring)
  exact RationalValueBounds.positive_cancel source.andE₁ (le_congr left right raw)

theorem scaled_lower_at (z R B m x p D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m)
    (hD : Γ ⊢[PRAAx] le (B*m) D) (hz : Γ ⊢[PRAAx] le one (normSq z)) :
    Γ ⊢[PRAAx] lower (ap2 nameF p (data z R B m x)) D := by
  let j := clock p (two*R)
  let A := two*quarterNumerator j
  let N := quarterDenominator j
  let V := B*m*N
  let q := ap2 nameF p (data z R B m x)
  have hBm := positive_product _ _ hB hm
  have hDp := le_trans hBm hD
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ hBm (GaussianRationalPolynomialExponential.factorial_positive _)
  have hN := quarter_lower (Γ := Γ) j
  have stretch : Γ ⊢[PRAAx] le V (D*A) :=
    le_trans (le_mul_mono hD hN)
      (le_congr (.eqRefl _) (by dsimp only [A]; ipra_ring)
        (le_add_right (D*quarterNumerator j) (D*quarterNumerator j)))
  have squared := le_mul_mono (le_mul_mono stretch stretch) hz
  have rhs : Γ ⊢[PRAAx] ((D*A)*(D*A))*normSq z ≐ normSq (scale A z)*(D*D) :=
    (by ipra_ring : Γ ⊢[PRAAx] ((D*A)*(D*A))*normSq z ≐ ((A*A)*normSq z)*(D*D)).eqTrans
      (congrMul (normSq_scale A z).eqSymm (.eqRefl _))
  have hn := qnormSq_represents q (scale A z) V hV (sample_represents z R B m x p hB hm)
  exact comparison_of_cleared _ _ _ _ _ _ (positive_product _ _ hDp hDp) (positive_product _ _ hV hV)
    (squared_tolerance_represents one D hDp) hn (le_congr (by ipra_ring) rhs squared)

theorem scaled_apart (z R B m x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m)
    (hz : Γ ⊢[PRAAx] le one (normSq z)) :
    Γ ⊢[PRAAx] apart nameF (apartClock B m) (data z R B m x) :=
  scaled_lower_at z R B m x (anchor (apartClock B m)) (unit (apartClock B m)) hB hm
    (GaussianRootSchedule.binary_length_correct (B*m)).andE₁ hz

theorem cancel_scaled_right (f g : PR 2) (u v z R B m x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m)
    (hRadius : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hNonzero : Γ ⊢[PRAAx] le one (normSq z))
    (hf : Γ ⊢[PRAAx] pointCN f u) (hg : Γ ⊢[PRAAx] pointCN g v)
    (he : Γ ⊢[PRAAx] crossEquivalent (multiplyF f nameF) (multiplyF g nameF)
      (multiplyData f nameF u (data z R B m x)) (multiplyData g nameF v (data z R B m x))) :
    Γ ⊢[PRAAx] crossEquivalent f g u v :=
  GaussianNamedGammaFirstCrossing.cancel_right f g nameF u v (data z R B m x) (apartClock B m)
    hf hg (name_regular z R B m x hB hm hRadius) (scaled_apart z R B m x hB hm hNonzero) he

theorem zero_at (z R B m x p : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m)
    (hz : Γ ⊢[PRAAx] normSq z ≐ zero) :
    Γ ⊢[PRAAx] ap2 nameF p (data z R B m x) ≐ qzero := by
  let j := clock p (two*R)
  let a := scale (two*quarterNumerator j) z
  let V := (B*m)*quarterDenominator j
  have size : Γ ⊢[PRAAx] normSq a ≐ zero :=
    (normSq_scale _ _).eqTrans ((congrMul (.eqRefl _) hz).eqTrans (by ipra_ring))
  have values := GaussianProductNorm.norm_zero_values a size
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal a zeroCode :=
    equal_of_values (values.1.trans re_zero.symm) (values.2.trans im_zero.symm)
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ (positive_product _ _ hB hm)
    (GaussianRationalPolynomialExponential.factorial_positive _)
  exact canonical_unique _ _ zeroCode V (canonical_congr (sample_at z R B m x p) (qmul_canonical _ _))
    GaussianRationalSyntheticDivision.qzero_canonical hV
    (represents_congr (.eqRefl _) e (.eqRefl _) (sample_represents z R B m x p hB hm)) (zero_represents V)

theorem zero_cross (z R B m x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m)
    (hz : Γ ⊢[PRAAx] normSq z ≐ zero) :
    Γ ⊢[PRAAx] crossEquivalent nameF constantF (data z R B m x) qzero := by
  have inside : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B) := le_congr hz.eqSymm (.eqRefl _) (zero_le _)
  apply equal_samples_cross _ _ _ _ (name_regular z R B m x hB hm inside) (constant_regular qzero)
  refine .allI ?_
  have hb' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift,one] using hB.shift
  have hm' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift,one] using hm.shift
  have hz' : Γ.map Fm.shift ⊢[PRAAx] normSq (Syn.shift z) ≐ zero := by simpa [Fm.shift,Syn.shift] using hz.shift
  simpa [pointwiseEqual,Syn.shift] using (zero_at (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift m)
    (Syn.shift x) (var 0) hb' hm' hz').eqTrans (constant_at (var 0) qzero).eqSymm

theorem actual_scaled_sine_argument_apart_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 2) ⋏ le one (var 3) ⋏ le one (normSq (var 0))) ⟶
      apart nameF (apartClock (var 2) (var 3)) (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (scaled_apart _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_scaled_sine_argument_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 2) ⋏ le one (var 3) ⋏ normSq (var 0) ≐ zero) ⟶
      crossEquivalent nameF constantF (data (var 0) (var 1) (var 2) (var 3) (var 4)) qzero) :=
  closeUniv 5 (.impI (zero_cross _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianSineProductScaledArgumentCancellation
