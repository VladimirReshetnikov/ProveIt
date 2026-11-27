import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.PolynomialFactors.RationalConsecutiveFactorProduct
import IPRADerivations.Analysis.RationalArithmetic.GoldenRatio.RationalPhiSection

/-!
# Uniform sharpness of the rational superelliptic section bound

Take the zero polynomial for the source construction's Q. For every
positive r and m greater than r*s, the actual monic product of the first
m linear factors and the actual list (1,0),...,(m,0) give a section with
exactly m original distinct rational points. The feature hyperplane
uses the last coordinate, y.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPhiSharpness

open_ipra
open RationalConsecutiveFactorProduct (consecutive root consecutive_root consecutive_head consecutive_length)
open RationalGaussianEmbedding (embed embed_canonical embed_equal embed_multiply embed_zero scalarZero)
open RationalPolynomialGaussianEmbedding (embed_congr evaluate hornerF)
open RationalArgmin (rationalEq rationalEq_congr)
open RationalPhiSectionNonzero (curveInput)
open RationalCurvePointsGaussianEmbedding (distinct)
open RationalSuperellipticNormDegree (pointPowers)
open GaussianRationalFiberGrouping (abscissa ordinate)
open GaussianRationalHorner (qzero)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_right)
open GaussianRationalSyntheticBounds (natCode_represents)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def pointBody : PTm 2 := pairT (root (var 0)) scalarZero
def points (m : PTm n) : PTm n := sequence pointBody m zero

ipra_subst points

theorem points_length (m : PTm n) : Γ ⊢[PRAAx] length (points m) ≐ m := sequence_length _ _ _

theorem point_lookup (m j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    entry (points m) j ≐ pairT (root j) scalarZero := by
  simpa [points,pointBody,inst2] using sequence_decode (Γ := Γ) pointBody (x := zero) hj

theorem point_abscissa (m j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] abscissa (points m) j ≐ root j :=
  (point_lookup m j hj).fstE

theorem point_ordinate (m j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] ordinate (points m) j ≐ scalarZero :=
  (point_lookup m j hj).sndE

theorem root_injective (i j : PTm n) (h : Γ ⊢[PRAAx] rationalEq (root i) (root j)) : Γ ⊢[PRAAx] i ≐ j := by
  have raw := RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding (root i) (root j)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) (embed_equal _ _ h)
  have same := GaussianRationalHorner.scalar_congr raw.eqSymm (ZT.derive rfl) (.eqRefl one) (natCode_represents (succ j))
  have integers := GaussianDominantPairAlgebra.scalar_representation_cross _ _ _ one one (natCode_represents (succ i)) same
  have succs : Γ ⊢[PRAAx] succ i ≐ succ j := by
    apply deriveNat
    simpa only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_one,map_one,mul_one] using ZT.toZ_eq integers
  exact succ_inj succs

theorem points_distinct (m : PTm n) : Γ ⊢[PRAAx] distinct (points m) := by
  refine .allI (.impI (.allI (.impI (.impI (.impI ?_)))))
  let M := Syn.shift (Syn.shift m)
  let F := (rationalEq (abscissa (points M) (var 0)) (abscissa (points M) (var 1)) ⋏
    rationalEq (ordinate (points M) (var 0)) (ordinate (points M) (var 1)))
  let Δ := F :: lt (var 1) (var 0) :: lt (var 0) (length (points M)) :: lt (var 1) (length (points M)) ::
    (Γ.map Fm.shift).map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 1) M := lt_congr (.eqRefl _) (points_length M) (.hyp (by simp [Δ]))
  have hj : Δ ⊢[PRAAx] lt (var 0) M := lt_congr (.eqRefl _) (points_length M) (.hyp (by simp [Δ]))
  have earlier : Δ ⊢[PRAAx] lt (var 1) (var 0) := Prf.hyp1
  have he := root_injective (var 0) (var 1) (rationalEq_congr (point_abscissa M (var 0) hj)
    (point_abscissa M (var 1) hi) (.andE₁ Prf.hyp0))
  have bot : Δ ⊢[PRAAx] .bot := le_lt_absurd _ (le_congr (.eqRefl _) he (le_refl (var 0))) earlier
  simpa [Δ,F,M,Fm.shift,Syn.shift] using bot

def zeroOrdinates (P : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift P)) ⟶ ordinate (Syn.shift P) (var 0) ≐ scalarZero)

theorem points_on_hyperplane (m : PTm n) : Γ ⊢[PRAAx] zeroOrdinates (points m) := by
  refine .allI (.impI ?_)
  simpa [Syn.shift] using point_ordinate (Syn.shift m) (var 0)
    (lt_congr (.eqRefl _) (points_length (Syn.shift m)) Prf.hyp0)

private theorem zero_power (r : PTm n) (hr : Γ ⊢[PRAAx] le one r) : Γ ⊢[PRAAx]
    embed (RationalScalarPowerGaussianEmbedding.power scalarZero r) ≐ qzero := by
  let p := RationalScalarPowerGaussianEmbedding.power scalarZero (pred r)
  have e := RationalIntegerNormalization.positive_form hr
  exact (embed_congr ((congrAp2 RationalScalarPowerGaussianEmbedding.powerF e (.eqRefl scalarZero)).eqTrans
    (RationalScalarPowerGaussianEmbedding.power_succ scalarZero (pred r)))).eqTrans
    ((embed_multiply p scalarZero).eqTrans ((qmul_congr (.eqRefl _) embed_zero).eqTrans (qmul_zero_right _)))

theorem curve_point_at (m r j : PTm n) (hr : Γ ⊢[PRAAx] le one r) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    rationalEq (RationalScalarPowerGaussianEmbedding.power (ordinate (points m) j) r)
      (evaluate (consecutive m) (abscissa (points m) j)) := by
  have left := (embed_congr (congrAp2 RationalScalarPowerGaussianEmbedding.powerF (.eqRefl r) (point_ordinate m j hj))).eqTrans
    (zero_power r hr)
  have right := (embed_congr (congrAp3 hornerF (.eqRefl _) (.eqRefl _) (point_abscissa m j hj))).eqTrans
    ((embed_equal _ _ (consecutive_root j m hj)).eqTrans embed_zero)
  exact RationalGaussianEmbedding.rational_equal_of_embed _ _ (left.eqTrans right.eqSymm)

theorem points_on_curve (m r : PTm n) (hr : Γ ⊢[PRAAx] le one r) : Γ ⊢[PRAAx]
    pointPowers (consecutive m) r (points m) := by
  have rs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift r) := by simpa [Fm.shift,Syn.shift,one] using hr.shift
  refine .allI (.impI ?_)
  simpa [Syn.shift] using curve_point_at (Syn.shift m) (Syn.shift r) (var 0) rs.wk
    (lt_congr (.eqRefl _) (points_length (Syn.shift m)) Prf.hyp0)

theorem monic_curve_input (m r s : PTm n) (hr : Γ ⊢[PRAAx] le one r) (hm : Γ ⊢[PRAAx] lt (r*s) m) :
    Γ ⊢[PRAAx] curveInput (consecutive m) s r m := by
  refine .andI hr (.andI (consecutive_length m) (.andI (.impI ?_) hm))
  exact .impE GaussianRationalCurveFibers.gaussian_one_nonzero ((consecutive_head m).wk.eqSymm.eqTrans
    ((embed_equal _ _ Prf.hyp0).eqTrans embed_zero))

theorem actual_rational_section_sharpness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ lt (var 1 * var 2) (var 0) ⟶
      curveInput (consecutive (var 0)) (var 2) (var 1) (var 0) ⋏
      (length (points (var 0)) ≐ var 0 ⋏ (distinct (points (var 0)) ⋏
        (pointPowers (consecutive (var 0)) (var 1) (points (var 0)) ⋏ zeroOrdinates (points (var 0)))))) :=
  closeUniv 3 (.impI (.impI (.andI (monic_curve_input (var 0) (var 1) (var 2) Prf.hyp1 Prf.hyp0)
    (.andI (points_length (var 0)) (.andI (points_distinct (var 0))
      (.andI (points_on_curve (var 0) (var 1) Prf.hyp1) (points_on_hyperplane (var 0))))))))

end LeanProofs.IPRA.Analysis.RationalPhiSharpness
