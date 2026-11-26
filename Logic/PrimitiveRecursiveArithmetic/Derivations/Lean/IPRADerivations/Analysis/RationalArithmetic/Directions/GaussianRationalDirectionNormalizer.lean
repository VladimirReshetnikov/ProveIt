import IPRADerivations.Analysis.RationalArithmetic.GaussianIntegerCircleProjection
import IPRADerivations.Analysis.Polynomials.RootFinding.RealRoots.RationalSquareRootBounds
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalProductWitness
import IPRADerivations.Foundations.DemandClosure
import IPRADerivations.Combinatorics.FiniteBijection
import IPRADerivations.AnalyticNumberTheory.Totatives

/-!
# An actual rational normalizer and initial unit direction

The original signed Gaussian numerator supplies its actual maximum
coordinate height and strict sign flags. An actual integer square root
constructs the positive scalar normalizer and a rational unit-circle
parameter. All input component denominators remain in the exact raw
representation; no phase, root, unit-output or approximation oracle is used.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalDirectionNormalizer

open_ipra
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im normSq normSq_eval scale)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianIntegerCircleProjection (sign turn re_turn im_turn)
open LeanProofs.IPRA.Analysis.GaussianRationalCircleParametrization (bit)
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Foundations.GapDecision (zabs subst_zabs zabs_sq)
open LeanProofs.IPRA.Foundations.DemandClosure (maximum maximum_left maximum_right)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def negativeBit (a : ZT n) : PTm n := sg (monus a.neg a.pos)
def norm (c : PTm n) : PTm n := normSq (rawGaussian c)
def M (c : PTm n) : PTm n := maximum (zabs (re (rawGaussian c))) (zabs (im (rawGaussian c)))
def Mhat (c : PTm n) : PTm n := succ (pred (M c))
def realFlag (c : PTm n) : PTm n := negativeBit (re (rawGaussian c))
def rotated (c : PTm n) : PTm n := turn (realFlag c) (rawGaussian c)
def imagFlag (c : PTm n) : PTm n := negativeBit (im (rotated c))
def factor (c H : PTm n) : PTm n := Mhat c*H
def W (c H : PTm n) : PTm n := RationalSquareRootBounds.root (norm c) (Mhat c*Mhat c) H
def S (c H : PTm n) : PTm n := succ (W c H)
def X (c H : PTm n) : PTm n := zabs (re (rawGaussian c))*factor c H
def V (c H : PTm n) : PTm n := zabs (im (rotated c))*factor c H
def normalizer (c H : PTm n) : PTm n := fraction (S c H) (factor c H*rawDen c)
def target (c H : PTm n) : PTm n := GaussianRationalHorner.ofGaussian (scale (factor c H) (rawGaussian c)) (S c H)
def initial (c H : PTm n) : PTm n := GaussianIntegerCircleProjection.rotatedPoint (X c H) (V c H) (imagFlag c) (S c H) (realFlag c)
def gap (c H : PTm n) : PTm n := monus (S c H*S c H) (norm c*factor c H*factor c H)
def sixtyFour : PTm n := num 64
def sixtyFive : PTm n := succ sixtyFour

ipra_subst negativeBit [ZT.subst]


ipra_subst norm

@[simp] theorem subst_M {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) :
    Syn.subst σ (M c) = M (Syn.subst σ c) := by
  simp only [M, Foundations.DemandClosure.subst_maximum, subst_zabs,
    ComplexLogarithmRemainder.subst_re, ComplexLogarithmRemainder.subst_im,
    GaussianRationalL1.subst_rawGaussian]

ipra_subst Mhat

ipra_subst realFlag

ipra_subst rotated

ipra_subst imagFlag

ipra_subst factor

ipra_subst W

ipra_subst S

@[simp] theorem subst_X {m : ℕ} (σ : Fin n → PTm m) (c H : PTm n) :
    Syn.subst σ (X c H) = X (Syn.subst σ c) (Syn.subst σ H) := by
  simp only [X, PTm.subst_mul, subst_zabs, ComplexLogarithmRemainder.subst_re,
    GaussianRationalL1.subst_rawGaussian, subst_factor]

@[simp] theorem subst_V {m : ℕ} (σ : Fin n → PTm m) (c H : PTm n) :
    Syn.subst σ (V c H) = V (Syn.subst σ c) (Syn.subst σ H) := by
  simp only [V, PTm.subst_mul, subst_zabs, ComplexLogarithmRemainder.subst_im,
    subst_rotated, subst_factor]

ipra_subst normalizer

ipra_subst target

ipra_subst initial

ipra_subst gap

ipra_subst sixtyFour

ipra_subst sixtyFive

theorem negative_bit_boolean (a : ZT n) : Γ ⊢[PRAAx] bit (negativeBit a) := Combinatorics.FiniteBijection.sg_bit _

/-- The flag is one exactly on the strictly negative side. In particular,
the zero signed value has the positive flag convention. -/
theorem negative_bit_sign (a : ZT n) : ZT.toZ Γ (sign (negativeBit a))*ZT.toZ Γ a = 𝔞(zabs a) := by
  have result : Γ ⊢[PRAAx] ZT.eq (a-ZT.ofNat (two*negativeBit a)*a) (ZT.ofNat (zabs a)) := by
    refine .orE (lt_or_le a.pos a.neg) ?_ ?_
    · have b := natEq (AnalyticNumberTheory.Totatives.sg_lt (Prf.hyp0 : (lt a.pos a.neg)::Γ ⊢[PRAAx] _))
      have ord := le_of_lt (Prf.hyp0 : (lt a.pos a.neg)::Γ ⊢[PRAAx] _)
      have e := natEq (eq_add_of_le ord)
      apply ZT.derive
      simp only [ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat]
      simp only [ZT.toZ]
      unfold zabs Probability.Variance.ad negativeBit
      ipra_simps
      have z := natEq ord
      ipra_simps
      linear_combination -2*(𝔞(a.pos)-𝔞(a.neg))*b+e-z
    · have b := natEq (AnalyticNumberTheory.Totatives.sg_le (Prf.hyp0 : (le a.neg a.pos)::Γ ⊢[PRAAx] _))
      have e := natEq (eq_add_of_le (Prf.hyp0 : (le a.neg a.pos)::Γ ⊢[PRAAx] _))
      apply ZT.derive
      simp only [ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat]
      simp only [ZT.toZ]
      unfold zabs Probability.Variance.ad negativeBit
      ipra_simps
      have z := natEq (Prf.hyp0 : (le a.neg a.pos)::Γ ⊢[PRAAx] _)
      ipra_simps
      linear_combination -2*(𝔞(a.pos)-𝔞(a.neg))*b+e-z
  have e := ZT.toZ_eq result
  simp only [ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat] at e
  simp only [sign,ZT.toZ_sub,ZT.toZ_ofNat]
  ipra_simps
  linear_combination e

theorem negative_bit_restore (a : ZT n) : ZT.toZ Γ (sign (negativeBit a))*𝔞(zabs a) = ZT.toZ Γ a := by
  rw [← negative_bit_sign (Γ := Γ) a,← _root_.mul_assoc,
    GaussianIntegerCircleProjection.sign_square _ (negative_bit_boolean a),_root_.one_mul]

theorem norm_absolute (c : PTm n) : Γ ⊢[PRAAx]
    norm c ≐ zabs (re (rawGaussian c))*zabs (re (rawGaussian c))+zabs (im (rawGaussian c))*zabs (im (rawGaussian c)) := by
  apply deriveNat
  rw [norm,normSq_eval]
  simp only [Q.mk_add,map_add]
  rw [zabs_sq,zabs_sq]
  ring

theorem M_lower (c : PTm n) : Γ ⊢[PRAAx] le (M c*M c) (norm c) := by
  refine .orE (le_total (zabs (re (rawGaussian c))) (zabs (im (rawGaussian c)))) ?_ ?_
  · have eqM : (le (zabs (re (rawGaussian c))) (zabs (im (rawGaussian c))))::Γ ⊢[PRAAx]
        M c ≐ zabs (im (rawGaussian c)) := (eq_add_of_le Prf.hyp0).eqSymm
    exact le_congr (congrMul eqM.eqSymm eqM.eqSymm) (norm_absolute c).wk.eqSymm (le_add_left _ _)
  · have eqM : (le (zabs (im (rawGaussian c))) (zabs (re (rawGaussian c))))::Γ ⊢[PRAAx]
        M c ≐ zabs (re (rawGaussian c)) := (congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _)
    exact le_congr (congrMul eqM.eqSymm eqM.eqSymm) (norm_absolute c).wk.eqSymm (le_add_right _ _)

theorem M_upper (c : PTm n) : Γ ⊢[PRAAx] le (norm c) (two*M c*M c) :=
  le_congr (norm_absolute c).eqSymm (by unfold M; ipra_ring)
    (add_le_add₂ (sq_le_sq (maximum_left _ _)) (sq_le_sq (maximum_right _ _)))

theorem M_positive (c : PTm n) (hc : Γ ⊢[PRAAx] le one (norm c)) : Γ ⊢[PRAAx] le one (M c) := by
  refine .orE (lt_or_le zero (M c)) Prf.hyp0 ?_
  have ez : (le (M c) zero)::Γ ⊢[PRAAx] M c ≐ zero := le_antisymm Prf.hyp0 (zero_le (M c))
  have small : (le (M c) zero)::Γ ⊢[PRAAx] le (norm c) zero :=
    le_congr (.eqRefl _) ((congrMul (congrMul (.eqRefl two) ez) ez).eqTrans (by ipra_ring)) (M_upper c).wk
  exact not_succ_le_self zero _ (le_trans hc.wk small)

theorem Mhat_positive (c : PTm n) : Γ ⊢[PRAAx] le one (Mhat c) := zero_lt_succ _
theorem Mhat_equal (c : PTm n) (hc : Γ ⊢[PRAAx] le one (norm c)) : Γ ⊢[PRAAx] Mhat c ≐ M c :=
  (RationalIntegerNormalization.positive_form (M_positive c hc)).eqSymm

theorem Mhat_lower (c : PTm n) (hc : Γ ⊢[PRAAx] le one (norm c)) : Γ ⊢[PRAAx] le (Mhat c*Mhat c) (norm c) :=
  le_congr (congrMul (Mhat_equal c hc).eqSymm (Mhat_equal c hc).eqSymm) (.eqRefl _) (M_lower c)

theorem factor_positive (c H : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx] le one (factor c H) :=
  positive_product _ _ (Mhat_positive c) hH
theorem S_positive (c H : PTm n) : Γ ⊢[PRAAx] le one (S c H) := zero_lt_succ _

theorem floor_lower (c H : PTm n) : Γ ⊢[PRAAx] le (W c H*W c H) (norm c*factor c H*factor c H) :=
  le_congr (.eqRefl _) (by unfold RationalSquareRootBounds.radicand factor; ipra_ring) (RationalSquareRootBounds.root_lower _ _ _)

theorem floor_upper (c H : PTm n) : Γ ⊢[PRAAx] lt (norm c*factor c H*factor c H) (S c H*S c H) :=
  lt_congr (by unfold RationalSquareRootBounds.radicand factor; ipra_ring) (.eqRefl _) (RationalSquareRootBounds.root_strict _ _ _)

theorem gap_identity (c H : PTm n) : Γ ⊢[PRAAx]
    S c H*S c H ≐ norm c*factor c H*factor c H+gap c H := eq_add_of_le (le_of_lt (floor_upper c H))

theorem floor_height (c H : PTm n) (hc : Γ ⊢[PRAAx] le one (norm c)) : Γ ⊢[PRAAx] le H (W c H) := by
  have first := mul_le_mul_right H (positive_product _ _ (Mhat_positive (Γ := Γ) c) (Mhat_positive c))
  exact le_trans (le_congr (one_mul H) (.eqRefl _) first)
    (RationalSquareRootBounds.root_unit_lower _ _ _ (Mhat_lower c hc))

theorem gap_upper (c H : PTm n) : Γ ⊢[PRAAx] le (gap c H) (two*W c H+one) := by
  have low := natEq (eq_add_of_le (floor_lower (Γ := Γ) c H))
  have high := natEq (gap_identity (Γ := Γ) c H)
  refine le_of_eq_add (d := monus (norm c*factor c H*factor c H) (W c H*W c H)) ?_
  apply deriveNat
  unfold S at high
  ipra_simps
  linear_combination high+low

theorem gap_budget (c H : PTm n) (hc : Γ ⊢[PRAAx] le one (norm c)) : Γ ⊢[PRAAx]
    le (H*gap c H) (GaussianRationalCircleParametrization.four*S c H*S c H) := by
  have Hle := le_trans (floor_height c H hc) (le_succ_self (W c H))
  have gapS : Γ ⊢[PRAAx] le (gap c H) (GaussianRationalCircleParametrization.four*S c H) :=
    le_trans (gap_upper c H) (le_of_eq_add (d := two*W c H+(two+one)) (by
      unfold GaussianRationalCircleParametrization.four S; ipra_ring))
  exact le_congr (.eqRefl _) (by unfold S; ipra_ring) (le_mul_mono Hle gapS)

theorem rotated_real (c : PTm n) : ZT.toZ Γ (re (rotated c)) = 𝔞(zabs (re (rawGaussian c))) := by
  rw [rotated,re_turn]
  exact negative_bit_sign _

theorem rotated_norm (c : PTm n) : Γ ⊢[PRAAx] normSq (rotated c) ≐ norm c :=
  GaussianIntegerCircleProjection.turn_norm _ _ (negative_bit_boolean _)

theorem plane_value (c H : PTm n) : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
    (GaussianIntegerCircleProjection.plane (X c H) (V c H) (imagFlag c)) (scale (factor c H) (rotated c)) := by
  apply GaussianRootAlgebra.equal_of_values
  · rw [GaussianIntegerCircleProjection.re_plane,GaussianRootAlgebra.re_scale,rotated_real]
    unfold X
    ipra_simps
    ring
  · rw [GaussianIntegerCircleProjection.im_plane,GaussianRootAlgebra.im_scale]
    unfold V imagFlag
    simp only [Q.mk_mul,map_mul]
    calc
      _ = 𝔞(factor c H)*(ZT.toZ Γ (sign (negativeBit (im (rotated c))))*𝔞(zabs (im (rotated c)))) := by ring
      _ = _ := by rw [negative_bit_restore]

theorem plane_norm_factor (c H : PTm n) : Γ ⊢[PRAAx]
    X c H*X c H+V c H*V c H ≐ norm c*factor c H*factor c H :=
  (GaussianIntegerCircleProjection.plane_norm _ _ _ (negative_bit_boolean _)).eqSymm.eqTrans
    ((GaussianRootAlgebra.normSq_equal (plane_value c H)).eqTrans
      ((ComplexLogarithmRemainder.normSq_scale _ _).eqTrans
        ((congrMul (.eqRefl _) (rotated_norm c)).eqTrans (by ipra_ring))))

theorem projection_gap (c H : PTm n) : Γ ⊢[PRAAx]
    S c H*S c H ≐ X c H*X c H+V c H*V c H+gap c H :=
  (gap_identity c H).eqTrans (congrAdd (plane_norm_factor c H).eqSymm (.eqRefl _))

theorem target_numerator (c H : PTm n) : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
    (turn (realFlag c) (GaussianIntegerCircleProjection.plane (X c H) (V c H) (imagFlag c)))
    (scale (factor c H) (rawGaussian c)) := by
  apply GaussianRootAlgebra.equal_of_values
  · rw [re_turn,GaussianRootAlgebra.equal_re (plane_value c H),GaussianRootAlgebra.re_scale,rotated,re_turn,GaussianRootAlgebra.re_scale]
    calc
      _ = 𝔞(factor c H)*((ZT.toZ Γ (sign (realFlag c))*ZT.toZ Γ (sign (realFlag c)))*ZT.toZ Γ (re (rawGaussian c))) := by ring
      _ = _ := by rw [GaussianIntegerCircleProjection.sign_square (realFlag c) (negative_bit_boolean (re (rawGaussian c))),_root_.one_mul]
  · rw [im_turn,GaussianRootAlgebra.equal_im (plane_value c H),GaussianRootAlgebra.im_scale,rotated,im_turn,GaussianRootAlgebra.im_scale]
    calc
      _ = 𝔞(factor c H)*((ZT.toZ Γ (sign (realFlag c))*ZT.toZ Γ (sign (realFlag c)))*ZT.toZ Γ (im (rawGaussian c))) := by ring
      _ = _ := by rw [GaussianIntegerCircleProjection.sign_square (realFlag c) (negative_bit_boolean (re (rawGaussian c))),_root_.one_mul]

theorem target_exact (c H : PTm n) : Γ ⊢[PRAAx]
    GaussianIntegerCircleProjection.rotatedTarget (X c H) (V c H) (imagFlag c) (S c H) (realFlag c) ≐ target c H :=
  GaussianRationalHorner.canonical_unique _ _ _ _
    (GaussianRationalHorner.ofGaussian_canonical _ _ (S_positive c H))
    (GaussianRationalHorner.ofGaussian_canonical _ _ (S_positive c H)) (S_positive c H)
    (GaussianRationalHorner.represents_congr (.eqRefl _) (target_numerator c H) (.eqRefl _)
      (GaussianRationalHorner.ofGaussian_represents _ _ (S_positive c H)))
    (GaussianRationalHorner.ofGaussian_represents _ _ (S_positive c H))

theorem initial_canonical (c H : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (initial c H) :=
  GaussianIntegerCircleProjection.rotated_point_canonical _ _ _ _ _ (S_positive c H)

theorem initial_unit (c H : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qnormSq (initial c H) ≐ fraction one one :=
  GaussianIntegerCircleProjection.rotated_point_unit _ _ _ _ _ (negative_bit_boolean _) (negative_bit_boolean _) (S_positive c H)

theorem initial_squared_error (c H : PTm n) (hc : Γ ⊢[PRAAx] le one (norm c)) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianRationalMetric.qnormSq (GaussianRationalMetric.qsub (initial c H) (target c H)))
      (fraction GaussianRationalCircleParametrization.four H) :=
  RationalArgmin.rationalLE_congr
    (GaussianRationalProductWitness.qnormSq_congr
      (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl _) (target_exact c H))) (.eqRefl _)
    (GaussianIntegerCircleProjection.rotated_squared_error _ _ _ _ _ _ _
      (negative_bit_boolean _) (negative_bit_boolean _) (S_positive c H) hH (projection_gap c H) (gap_budget c H hc))

theorem normalizer_denominator_positive (c H : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    le one (factor c H*rawDen c) := positive_product _ _ (factor_positive c H hH) (raw_den_positive c)

theorem normalizer_represents (c H : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (normalizer c H) (ZT.ofNat (S c H)) (factor c H*rawDen c) :=
  fraction_represents _ _ (normalizer_denominator_positive c H hH)

theorem target_represents (c H : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.represents (target c H) (scale (factor c H) (rawGaussian c)) (S c H) :=
  GaussianRationalHorner.ofGaussian_represents _ _ (S_positive c H)

theorem target_bounded (c H : PTm n) : Γ ⊢[PRAAx] GaussianRationalMetric.bounded (target c H) one one :=
  GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ (S_positive c H) (le_refl one) (target_represents c H)
    (le_congr (by ipra_ring) (by ipra_ring) (le_congr
      ((ComplexLogarithmRemainder.normSq_scale _ _).eqTrans (by unfold norm; ipra_ring)).eqSymm
      (.eqRefl _) (le_of_lt (floor_upper c H))))

theorem normalizer_positive (c H : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    neg (RationalArgmin.rationalLE (normalizer c H) (fraction zero one)) := by
  refine .impI ?_
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (normalizer_represents (Γ := Γ) c H hH).wk (fraction_represents (Γ := Γ) zero one (le_refl one)).wk Prf.hyp0
  have small := le_congr (one_mul _) (zero_mul _) raw
  exact not_succ_le_self zero _ (le_trans (S_positive c H).wk small)

theorem normalizer_square_represents (c H : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (RationalSquareRootBounds.square (normalizer c H)) (ZT.ofNat (S c H*S c H))
      ((factor c H*rawDen c)*(factor c H*rawDen c)) := by
  have value := RationalRepresentations.represents_multiply _ _ _ _ _ _
    (normalizer_represents (Γ := Γ) c H hH) (normalizer_represents c H hH)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := value)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps

theorem normalizer_lower (c H : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianRationalMetric.qnormSq c) (RationalSquareRootBounds.square (normalizer c H)) := by
  have hD := raw_den_positive (Γ := Γ) c
  have hp := normalizer_denominator_positive (Γ := Γ) c H hH
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ (positive_product _ _ hD hD) (positive_product _ _ hp hp)
    (GaussianRationalMetric.qnormSq_represents c (rawGaussian c) (rawDen c) hD (raw_represents c))
    (normalizer_square_represents c H hH)
    (le_congr (by unfold norm; ipra_ring) (.eqRefl _) (mul_le_mul_right (rawDen c*rawDen c) (le_of_lt (floor_upper c H))))

theorem sixtyFour_positive : Γ ⊢[PRAAx] le one (sixtyFour : PTm n) :=
  le_of_eq_add (d := num 63) (by unfold sixtyFour; ipra_ring)

theorem H_positive (H : PTm n) (h64 : Γ ⊢[PRAAx] le sixtyFour H) : Γ ⊢[PRAAx] le one H := le_trans sixtyFour_positive h64

theorem normalizer_integer_upper (c H : PTm n) (hc : Γ ⊢[PRAAx] le one (norm c))
    (h64 : Γ ⊢[PRAAx] le sixtyFour H) : Γ ⊢[PRAAx]
    le (sixtyFour*sixtyFour*(S c H*S c H)) (sixtyFive*sixtyFive*norm c*factor c H*factor c H) := by
  have hH := H_positive H h64
  have approx := RationalSquareRootBounds.relative_integer_bound (norm c) (Mhat c*Mhat c) H
    (positive_product _ _ (Mhat_positive c) (Mhat_positive c)) (Mhat_lower c hc)
  have linear : Γ ⊢[PRAAx] le (sixtyFour*succ H) (sixtyFive*H) :=
    le_congr (by ipra_ring) (by unfold sixtyFive; ipra_ring) (add_le_add_right (sixtyFour*H) h64)
  have first : Γ ⊢[PRAAx] le ((H*H)*(sixtyFour*sixtyFour*(S c H*S c H)))
      ((sixtyFour*succ H)*(sixtyFour*succ H)*(norm c*factor c H*factor c H)) :=
    le_congr (by simp only [S,W]; ipra_ring) (by unfold RationalSquareRootBounds.radicand factor; ipra_ring)
      (mul_le_mul_right (sixtyFour*sixtyFour) approx)
  have second : Γ ⊢[PRAAx] le ((sixtyFour*succ H)*(sixtyFour*succ H)*(norm c*factor c H*factor c H))
      ((H*H)*(sixtyFive*sixtyFive*norm c*factor c H*factor c H)) :=
    le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right (norm c*factor c H*factor c H) (sq_le_sq linear))
  exact RationalValueBounds.positive_cancel (positive_product H H hH hH) (le_trans first second)

private theorem multiple_represents (W q A B : PTm n) (hq : Γ ⊢[PRAAx] RationalArithmetic.represents q (ZT.ofNat A) B) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (RationalArithmetic.multiply (fraction W one) q) (ZT.ofNat (W*A)) B := by
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := one_mul _)
    (h := RationalRepresentations.represents_multiply _ _ _ _ _ _ (fraction_represents W one (le_refl one)) hq)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps

theorem normalizer_upper (c H : PTm n) (hc : Γ ⊢[PRAAx] le one (norm c))
    (h64 : Γ ⊢[PRAAx] le sixtyFour H) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (RationalArithmetic.multiply (fraction (sixtyFour*sixtyFour) one) (RationalSquareRootBounds.square (normalizer c H)))
      (RationalArithmetic.multiply (fraction (sixtyFive*sixtyFive) one) (GaussianRationalMetric.qnormSq c)) := by
  have hD := raw_den_positive (Γ := Γ) c
  have hp := normalizer_denominator_positive (Γ := Γ) c H (H_positive H h64)
  apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ (positive_product _ _ hp hp) (positive_product _ _ hD hD)
    (multiple_represents _ _ _ _ (normalizer_square_represents c H (H_positive H h64)))
    (multiple_represents _ _ _ _ (GaussianRationalMetric.qnormSq_represents c (rawGaussian c) (rawDen c) hD (raw_represents c)))
  exact le_congr (by ipra_ring) (by unfold norm; ipra_ring) (mul_le_mul_right (rawDen c*rawDen c) (normalizer_integer_upper c H hc h64))

def certificate (c H : PTm n) : Fm PTm n :=
  neg (RationalArgmin.rationalLE (normalizer c H) (fraction zero one)) ⋏
    (RationalArgmin.rationalLE (GaussianRationalMetric.qnormSq c) (RationalSquareRootBounds.square (normalizer c H)) ⋏
      (RationalArgmin.rationalLE
        (RationalArithmetic.multiply (fraction (sixtyFour*sixtyFour) one) (RationalSquareRootBounds.square (normalizer c H)))
        (RationalArithmetic.multiply (fraction (sixtyFive*sixtyFive) one) (GaussianRationalMetric.qnormSq c)) ⋏
        (GaussianRationalHorner.canonical (initial c H) ⋏
          ((GaussianRationalMetric.qnormSq (initial c H) ≐ fraction one one) ⋏
            RationalArgmin.rationalLE (GaussianRationalMetric.qnormSq (GaussianRationalMetric.qsub (initial c H) (target c H)))
              (fraction GaussianRationalCircleParametrization.four H)))))

ipra_subst certificate

theorem initialization (c H : PTm n) (hc : Γ ⊢[PRAAx] le one (norm c)) (h64 : Γ ⊢[PRAAx] le sixtyFour H) : Γ ⊢[PRAAx]
    certificate c H :=
  .andI (normalizer_positive c H (H_positive H h64)) (.andI (normalizer_lower c H (H_positive H h64))
    (.andI (normalizer_upper c H hc h64) (.andI (initial_canonical c H)
      (.andI (initial_unit c H) (initial_squared_error c H hc (H_positive H h64))))))

def initialF : PR 2 := PTm.toPR (initial (var 0) (var 1))
def normalizerF : PR 2 := PTm.toPR (normalizer (var 0) (var 1))
def targetF : PR 2 := PTm.toPR (target (var 0) (var 1))
def output (c H : PTm n) : PTm n := pairT (normalizer c H)
  (pairT (initial c H) (pairT (target c H) (pairT (factor c H) (S c H))))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (c H : PTm n) : PTm n := ap2 outputF c H

ipra_subst output
ipra_subst run

theorem initial_program (c H : PTm n) : Γ ⊢[PRAAx] ap2 initialF c H ≐ initial c H := by
  simpa [initialF,ap2] using toPR_eq (Γ := Γ) (initial (var 0) (var 1) : PTm 2) ![c,H]
theorem normalizer_program (c H : PTm n) : Γ ⊢[PRAAx] ap2 normalizerF c H ≐ normalizer c H := by
  simpa [normalizerF,ap2] using toPR_eq (Γ := Γ) (normalizer (var 0) (var 1) : PTm 2) ![c,H]
theorem target_program (c H : PTm n) : Γ ⊢[PRAAx] ap2 targetF c H ≐ target c H := by
  simpa [targetF,ap2] using toPR_eq (Γ := Γ) (target (var 0) (var 1) : PTm 2) ![c,H]
theorem program_at (c H : PTm n) : Γ ⊢[PRAAx] run c H ≐ output c H := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![c,H]

theorem returned_normalizer (c H : PTm n) : Γ ⊢[PRAAx] fstT (run c H) ≐ normalizer c H :=
  (program_at c H).fstE
theorem returned_initial (c H : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run c H)) ≐ initial c H :=
  (program_at c H).sndE.fstE
theorem returned_target (c H : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run c H))) ≐ target c H :=
  (program_at c H).sndE.sndE.fstE
theorem returned_factor (c H : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run c H)))) ≐ factor c H :=
  (program_at c H).sndE.sndE.sndE.fstE
theorem returned_S (c H : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run c H)))) ≐ S c H :=
  (program_at c H).sndE.sndE.sndE.sndE

theorem actual_direction_initialization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (norm (var 0)) ⟶ le sixtyFour (var 1) ⟶ certificate (var 0) (var 1)) :=
  closeUniv 2 (.impI (.impI (initialization _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_initial_unit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalHorner.canonical (initial (var 0) (var 1)) ⋏
      GaussianRationalMetric.qnormSq (initial (var 0) (var 1)) ≐ fraction one one) :=
  closeUniv 2 (.andI (initial_canonical _ _) (initial_unit _ _))

theorem actual_target_alignment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶
      (RationalArithmetic.represents (normalizer (var 0) (var 1)) (ZT.ofNat (S (var 0) (var 1))) (factor (var 0) (var 1)*rawDen (var 0)) ⋏
        GaussianRationalHorner.represents (target (var 0) (var 1)) (scale (factor (var 0) (var 1)) (rawGaussian (var 0))) (S (var 0) (var 1)))) :=
  closeUniv 2 (.impI (.andI (normalizer_represents _ _ Prf.hyp0) (target_represents _ _)))

theorem actual_target_bounded_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalMetric.bounded (target (var 0) (var 1)) one one) :=
  closeUniv 2 (target_bounded _ _)

theorem actual_maximum_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (norm (var 0)) ⟶
      (le one (M (var 0)) ⋏ ((Mhat (var 0) ≐ M (var 0)) ⋏
        (le (M (var 0)*M (var 0)) (norm (var 0)) ⋏ le (norm (var 0)) (two*M (var 0)*M (var 0)))))) :=
  closeUniv 1 (.impI (.andI (M_positive _ Prf.hyp0) (.andI (Mhat_equal _ Prf.hyp0) (.andI (M_lower _) (M_upper _)))))

theorem actual_initializer_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((ap2 initialF (var 0) (var 1) ≐ initial (var 0) (var 1)) ⋏
      ((ap2 normalizerF (var 0) (var 1) ≐ normalizer (var 0) (var 1)) ⋏
        ((ap2 targetF (var 0) (var 1) ≐ target (var 0) (var 1)) ⋏
          run (var 0) (var 1) ≐ output (var 0) (var 1)))) :=
  closeUniv 2 (.andI (initial_program _ _) (.andI (normalizer_program _ _) (.andI (target_program _ _) (program_at _ _))))

theorem actual_returned_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((fstT (run (var 0) (var 1)) ≐ normalizer (var 0) (var 1)) ⋏
      ((fstT (sndT (run (var 0) (var 1))) ≐ initial (var 0) (var 1)) ⋏
        ((fstT (sndT (sndT (run (var 0) (var 1)))) ≐ target (var 0) (var 1)) ⋏
          ((fstT (sndT (sndT (sndT (run (var 0) (var 1))))) ≐ factor (var 0) (var 1)) ⋏
            sndT (sndT (sndT (sndT (run (var 0) (var 1))))) ≐ S (var 0) (var 1))))) :=
  closeUniv 2 (.andI (returned_normalizer _ _) (.andI (returned_initial _ _)
    (.andI (returned_target _ _) (.andI (returned_factor _ _) (returned_S _ _)))))

end LeanProofs.IPRA.Analysis.GaussianRationalDirectionNormalizer
