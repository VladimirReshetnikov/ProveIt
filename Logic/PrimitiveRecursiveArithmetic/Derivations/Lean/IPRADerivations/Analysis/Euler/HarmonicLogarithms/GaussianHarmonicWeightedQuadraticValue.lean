import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicWeightedQuadratic
import IPRADerivations.Analysis.Series.Harmonic.RationalHarmonicInterval
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentedUpper
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalNaturalScale
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmProperness

/-!
# The sharp weighted gap on the actual rational harmonic observations

The three real-coded harmonic intervals use one factorial denominator.
Their common lower endpoint cancels with the exact sum of the weights.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianHarmonicWeightedQuadraticValue

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (scale add re oneCode)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianHarmonicWeightedQuadratic (finite_gap finiteGap weightedValue centerValue squareDen gapNumerator meshError)
open GaussianRationalHorner (represents represents_congr positive_product qadd qadd_represents ofGaussian_represents)
open GaussianRationalNaturalScale (natScale natScale_represents)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRootAlgebra (re_scale re_add re_one)
open RationalGaussianEmbedding (embed embed_at embedF native)
open RationalHarmonicInterval (interval common horizon numerator at_common left_horizon)
open RationalRepresentedUpper (from_signed left right)
open RationalValueBounds (upper)
open Products (fact)
open GammaEulerMesh (factorial_positive)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (monus)
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def gapCode (a d B r s : PTm n) : PTm n := fraction (gapNumerator a d r s) (squareDen B r s)
def point (x D Q : PTm n) : PTm n := embed (interval x D Q)

@[simp] theorem subst_gapCode {m : ℕ} (σ : Fin n → PTm m) (a d B r s : PTm n) :
    Syn.subst σ (gapCode a d B r s) = gapCode (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ s) := by
  simp [gapCode]
@[simp] theorem subst_point {m : ℕ} (σ : Fin n → PTm m) (x D Q : PTm n) :
    Syn.subst σ (point x D Q) = point (Syn.subst σ x) (Syn.subst σ D) (Syn.subst σ Q) := by simp [point]

theorem comparison_denominator_positive (B r s : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (squareDen B r s) :=
  positive_product _ _ (positive_product _ _ (positive_product _ _ RationalAlgebra.two_positive (zero_lt_succ _)) hB) hB

theorem point_represents (x D M Q : PTm n) (hx : Γ ⊢[PRAAx] le x M) :
    Γ ⊢[PRAAx] represents (point x D Q) (native (numerator x D Q (horizon M D Q))) (fact (horizon M D Q)) := by
  let L := horizon M D Q
  let c := common x D Q L
  let e := interval x D Q
  have hL : Γ ⊢[PRAAx] le (horizon x D Q) L :=
    le_mul_mono (le_refl Q) (add_le_add_right D hx)
  have read := at_common x D Q L hL
  have ep : Γ ⊢[PRAAx] embed c ≐ embed e := (embed_at c).eqSymm.eqTrans
    ((congrAp1 embedF read).eqTrans (embed_at e))
  exact represents_congr ep (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
    (RationalGaussianEmbedding.embed_from_representation c (numerator x D Q L) (fact L)
      (RationalHarmonicInterval.common_value x D Q L))

theorem raw_upper (a d B D Q r s : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (had : Γ ⊢[PRAAx] le a d) (hdB : Γ ⊢[PRAAx] le d B) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] upper
      (fstT (qadd (gapCode a d B r s)
        (qadd (natScale (succ r) (point (weight r s*a) D Q)) (natScale s (point (weight r s*d) D Q)))))
      (fstT (natScale (weight r s) (point (barycenter a d r s) D Q)))
      (meshError a d r s) (squareDen B r s*Q) := by
  let W := weight r s
  let R := succ r
  let M := W*B
  let X := W*a
  let Y := W*d
  let Z := barycenter a d r s
  let L := horizon M D Q
  let F := fact L
  let P := squareDen B r s
  let H := gapNumerator a d r s
  let E := meshError a d r s
  let α := native (numerator X D Q L)
  let β := native (numerator Y D Q L)
  let γ := native (numerator Z D Q L)
  let A := add (scale R α) (scale s β)
  let T := add (scale F (scale H oneCode)) (scale P A)
  let U := scale W γ
  let f := point X D Q
  let g := point Y D Q
  let k := point Z D Q
  let fg := qadd (natScale R f) (natScale s g)
  let offset := gapCode a d B r s
  have hx : Γ ⊢[PRAAx] le X M := le_mul_mono (le_refl W) (le_trans had hdB)
  have hy : Γ ⊢[PRAAx] le Y M := le_mul_mono (le_refl W) hdB
  have hz : Γ ⊢[PRAAx] le Z M := by
    have h := le_mul_mono (le_refl R) had
    have ew : Γ ⊢[PRAAx] R+s ≐ W := by dsimp [W,R,weight]; ipra_ring
    exact le_trans (le_congr (.eqRefl _) ((by ipra_ring : Γ ⊢[PRAAx] R*d+s*d ≐ (R+s)*d).eqTrans
      (congrMul ew (.eqRefl _))) (add_le_add_right (s*d) h)) hy
  have hF := factorial_positive (Γ := Γ) L
  have hP := comparison_denominator_positive B r s (le_trans ha (le_trans had hdB))
  have hPF := positive_product _ _ hP hF
  have cx := natScale_represents R f α F hF (point_represents X D M Q hx)
  have cy := natScale_represents s g β F hF (point_represents Y D M Q hy)
  have cz := natScale_represents W k γ F hF (point_represents Z D M Q hz)
  have left := qadd_represents _ _ _ _ F hF cx cy
  have off : Γ ⊢[PRAAx] represents offset (scale H oneCode) P := ofGaussian_represents _ _ hP
  have lp := qadd_represents offset fg (scale F (scale H oneCode)) (scale P A) (P*F) hPF
    (rescale_to _ _ _ _ _ off (.eqRefl _)) (rescale_to _ _ _ _ _ left (mul_comm _ _))
  have comp := finite_gap a d B Q L r s ha had hdB hQ (left_horizon M D Q)
  let low := Q*P*weightedValue a d Q L r s+Q*F*H
  let high := Q*P*centerValue a d Q L r s+F*E
  have h : Γ ⊢[PRAAx] le low high := comp
  have ew : Γ ⊢[PRAAx] W ≐ R+s := by dsimp [W,R,weight]; ipra_ring
  apply from_signed _ _ (re T) (re U) (P*F) F E (P*Q) hPF hF lp.andE₁ cz.andE₁
  apply zle_of_toZ (P*F*monus high low)
  have e := natEq (eq_add_of_le h)
  have w := natEq ew
  dsimp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,T,U,A,α,β,γ]
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat,re_scale,re_add,re_one]
  simp only [RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code,numerator]
  simp only [ZT.toZ]
  dsimp only [low,high,weightedValue,centerValue] at e ⊢
  simp only [IPRA.Q.mk_add,IPRA.Q.mk_mul,map_add,map_mul] at e w ⊢
  unfold F X Y Z R W at *
  ipra_simps
  linear_combination -(𝔞 P*𝔞 (fact L))*e +
    𝔞(P)*𝔞(P)*𝔞(Q)*𝔞(fact L)*𝔞(S (Q*D) (fact L))*w

end LeanProofs.IPRA.Analysis.GaussianHarmonicWeightedQuadraticValue
