import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.ExponentNormalization.GaussianBarnesCanonicalCorrectionShift
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalExponentBound
import IPRADerivations.Analysis.Integration.RiemannSums.GaussianRationalRiemannRefinement
import IPRADerivations.Analysis.Polynomials.RootFinding.Characteristic.GaussianCharacteristicEntryNorm
import IPRADerivations.Analysis.Euler.Integration.Incomplete.IntegerValues.GaussianEulerIncompleteFactorialCombination

/-!
# Exact quadratic expansion of the original finite Barnes correction

The actual correction fold equals its quadratic polynomial with the
original harmonic rational coefficient. The finite increment splits
into an exact linear term and a quadratic remainder.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadCorrectionDerivative

open_ipra
open ComplexLogarithmRemainder (add mul scale oneCode)
open GaussianBarnesCanonicalCorrectionShift (total body parameters subst_parameters body_at correction_represents)
open GaussianBarnesCanonicalFactor (correction)
open GaussianGammaCanonicalExponent (harmonicPoint)
open GaussianGammaHarmonicIncrement (reciprocalPoint harmonic_point_increment)
open GaussianRationalFiniteSum (sum_multiply multiplyBody multiply_body_at termsEqual)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at finite_sum_difference)
open GaussianRationalRiemannRefinement (constantBody constant_entry constant_sum)
open GaussianRationalNaturalScale (naturalPoint natScale_as_product)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents positive_product
  qmul qadd qzero qmul_canonical qadd_canonical qmul_represents qadd_represents canonical_unique
  represents represents_congr represents_rescale)
open GaussianRationalMetric (qsub qnegative qsub_canonical qsub_represents distanceBounded bounded)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr qsub_congr qmul_zero_left qzero_add qadd_sub_cancel)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRationalSumAlgebra (qadd_swap_tail)
open GaussianRationalPowerDifference (product_difference)
open GaussianNameArithmetic (sum_difference)
open GaussianRootAlgebra (sub equal equal_of_values equal_refl re_add im_add re_mul im_mul re_sub im_sub re_scale im_scale re_one im_one)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "rsum" => GaussianRationalFiniteSum.sum

def halfSquare (z B : PTm n) : PTm n := qmul (ofGaussian z B) (ofGaussian z (two*B))
def slope (z B N : PTm n) : PTm n := qsub (qmul (ofGaussian z B) (harmonicPoint N)) (naturalPoint N)
def linear (z h B N : PTm n) : PTm n := qmul (ofGaussian h B) (slope z B N)
def remainder (h B N : PTm n) : PTm n := qmul (halfSquare h B) (harmonicPoint N)

@[simp] theorem subst_halfSquare {l : ℕ} (σ : Fin n → PTm l) (z B : PTm n) :
    Syn.subst σ (halfSquare z B) = halfSquare (Syn.subst σ z) (Syn.subst σ B) := by simp [halfSquare,two]
@[simp] theorem subst_slope {l : ℕ} (σ : Fin n → PTm l) (z B N : PTm n) :
    Syn.subst σ (slope z B N) = slope (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [slope]
@[simp] theorem subst_linear {l : ℕ} (σ : Fin n → PTm l) (z h B N : PTm n) :
    Syn.subst σ (linear z h B N) = linear (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) := by simp [linear]
@[simp] theorem subst_remainder {l : ℕ} (σ : Fin n → PTm l) (h B N : PTm n) :
    Syn.subst σ (remainder h B N) = remainder (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) := by simp [remainder]

private def reciprocalBody : PTm 2 := reciprocalPoint (var 0)
private def weightedBody : PTm 2 := differenceBody (multiplyBody reciprocalBody) constantBody

private theorem reciprocal_read (i x : PTm n) : inst2 reciprocalBody i x = reciprocalPoint i := by
  simp [reciprocalBody,inst2]

private theorem reciprocal_sum (N : PTm n) : Γ ⊢[PRAAx] rsum reciprocalBody N zero ≐ harmonicPoint N := by
  have all : Γ ⊢[PRAAx] .all (rsum reciprocalBody (var 0) zero ≐ harmonicPoint (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,GaussianRationalFiniteSum.subst_sum,GaussianGammaCanonicalExponent.subst_harmonicPoint,
        ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero]
      exact (GaussianRationalFiniteSum.sum_zero _ _).eqTrans GaussianGammaEulerHeadQuadratic.harmonic_zero.eqSymm
    · simp only [Fm.subst_eq,GaussianRationalFiniteSum.subst_sum,GaussianGammaCanonicalExponent.subst_harmonicPoint,
        ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.repl_zero]
      have e := GaussianRationalFiniteSum.sum_succ
        (Γ := (rsum reciprocalBody (var 0) zero ≐ harmonicPoint (var 0)) :: Γ.map Fm.shift)
        reciprocalBody (var 0) zero
      rw [reciprocal_read] at e
      exact e.eqTrans ((qadd_congr Prf.hyp0 (.eqRefl _)).eqTrans (harmonic_point_increment _).eqSymm)
  simpa only [Fm.subst_eq,GaussianRationalFiniteSum.subst_sum,GaussianGammaCanonicalExponent.subst_harmonicPoint,
    ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero] using all.allE N

private theorem half_square_represents (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] represents (halfSquare z B) (mul z z) (B*(two*B)) := by
  have hd := positive_product two B (le_succ_self one) hB
  exact qmul_represents _ _ _ _ _ _ hB hd (ofGaussian_represents z B hB) (ofGaussian_represents z (two*B) hd)

private theorem row_formula (z B i : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] correction z B (succ i) ≐ qsub (qmul (halfSquare z B) (reciprocalPoint i)) (ofGaussian z B) := by
  let k := succ i
  let E := two*(B*k)
  let D := B*E
  let A := B*(two*B)
  have hk := zero_lt_succ (Γ := Γ) i
  have hE := positive_product two (B*k) (le_succ_self one) (positive_product B k hB hk)
  have hD := positive_product B E hB hE
  have hA := positive_product B (two*B) hB (positive_product two B (le_succ_self one) hB)
  have pair := qmul_represents (halfSquare z B) (reciprocalPoint i) (mul z z) oneCode A k hA hk
    (half_square_represents z B hB) (ofGaussian_represents oneCode k hk)
  have numerator : Γ ⊢[PRAAx] equal (mul (mul z z) oneCode) (mul z z) := by
    apply equal_of_values <;> simp only [re_mul,im_mul,re_one,im_one] <;> ring
  have q : Γ ⊢[PRAAx] represents (qmul (halfSquare z B) (reciprocalPoint i)) (mul z z) D :=
    represents_congr (.eqRefl _) numerator (by dsimp only [A,D,E]; ipra_ring) pair
  have rhs := qsub_represents _ _ _ _ D hD q (represents_rescale _ _ B E (ofGaussian_represents z B hB))
  exact canonical_unique _ _ _ D (qsub_canonical _ _) (qsub_canonical _ _) hD (correction_represents z B k hB hk) rhs

theorem total_formula (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] total z B N ≐
      qsub (qmul (halfSquare z B) (harmonicPoint N)) (qmul (naturalPoint N) (ofGaussian z B)) := by
  let a := halfSquare z B
  let b := ofGaussian z B
  let x := pairT a zero
  have rows : Γ ⊢[PRAAx] termsEqual body weightedBody N (parameters z B) (pairT x b) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    let s (t : PTm n) := Syn.shift t
    let j : PTm (n+1) := var 0
    let A := halfSquare (s z) (s B)
    let C := ofGaussian (s z) (s B)
    have h' : Δ ⊢[PRAAx] le one (s B) := by simpa [Fm.shift,Syn.shift,s,Δ,one] using hB.shift.wk
    have left := (body_at (Γ := Δ) j (s z) (s B)).eqTrans (row_formula (s z) (s B) j h')
    have right := difference_body_at (Γ := Δ) (multiplyBody reciprocalBody) constantBody j (pairT A zero) C
    have term := multiply_body_at (Γ := Δ) reciprocalBody A j zero
    rw [reciprocal_read] at term
    rw [constant_entry] at right
    simpa only [Syn.shift,subst_parameters,subst_pairT,subst_halfSquare,GaussianRationalHorner.subst_ofGaussian,
      ConciseIPRA.PTm.subst_zero,x,a,b,s,Δ,j,A,C,weightedBody] using
      left.eqTrans ((right.eqTrans (qsub_congr term (.eqRefl _))).eqSymm)
  have r := finite_sum_difference (Γ := Γ) (multiplyBody reciprocalBody) constantBody N x b
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ rows).eqTrans (r.eqTrans
    (qsub_congr ((sum_multiply reciprocalBody a N zero).eqTrans (qmul_congr (.eqRefl _) (reciprocal_sum N)))
      ((constant_sum b N).eqTrans (natScale_as_product N b))))

private theorem half_square_increment (z h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qsub (halfSquare (add z h) B) (halfSquare z B) ≐
      qadd (qmul (ofGaussian z B) (ofGaussian h B)) (halfSquare h B) := by
  let D := B*(two*B)
  let r := add z h
  have hd := positive_product B (two*B) hB (positive_product two B (le_succ_self one) hB)
  have left := qsub_represents _ _ _ _ D hd (half_square_represents r B hB) (half_square_represents z B hB)
  have xy := qmul_represents (ofGaussian z B) (ofGaussian h B) z h B B hB hB
    (ofGaussian_represents z B hB) (ofGaussian_represents h B hB)
  have xy' : Γ ⊢[PRAAx] represents (qmul (ofGaussian z B) (ofGaussian h B)) (scale two (mul z h)) D :=
    represents_congr (.eqRefl _) (equal_refl (scale two (mul z h)))
      (by dsimp only [D]; ipra_ring) (represents_rescale _ _ (B*B) two xy)
  have right := qadd_represents _ _ _ _ D hd xy' (half_square_represents h B hB)
  apply canonical_unique _ _ _ D (qsub_canonical _ _) (qadd_canonical _ _) hd left
  apply represents_congr (.eqRefl _) _ (.eqRefl _) right
  apply equal_of_values <;> simp only [r,re_add,im_add,re_sub,im_sub,re_mul,im_mul,re_scale,im_scale] <;> ipra_simps <;> ring

theorem point_increment (z h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qsub (ofGaussian (add z h) B) (ofGaussian z B) ≐ ofGaussian h B := by
  have old := qsub_represents _ _ _ _ B hB (ofGaussian_represents (add z h) B hB) (ofGaussian_represents z B hB)
  apply canonical_unique _ _ _ B (qsub_canonical _ _) (ofGaussian_canonical _ _ hB) hB _ (ofGaussian_represents h B hB)
  apply represents_congr (.eqRefl _) _ (.eqRefl _) old
  apply equal_of_values <;> simp only [re_sub,im_sub,re_add,im_add] <;> ring

private theorem subtract_difference (a b c d : PTm n) : Γ ⊢[PRAAx]
    qsub (qsub a b) (qsub c d) ≐ qsub (qsub a c) (qsub b d) :=
  GaussianFastValueCut.difference_identity a b c d

private theorem difference_product (a b u : PTm n) : Γ ⊢[PRAAx]
    qsub (qmul a u) (qmul b u) ≐ qmul (qsub a b) u :=
  (product_difference a b u u).eqTrans
    ((qadd_congr (.eqRefl _) ((qmul_congr (.eqRefl _) (GaussianCoefficientNormOrder.qsub_self u)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_zero_right _))).eqTrans
      (GaussianReciprocalHorner.qadd_zero_right _ (qmul_canonical _ _)))

private theorem subtract_after_sum (a b c : PTm n) : Γ ⊢[PRAAx] qsub (qadd a b) c ≐ qadd (qsub a c) b :=
  qadd_swap_tail a b (qnegative c)

theorem exact_expansion (z h B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qsub (total (add z h) B N) (total z B N) ≐
      qadd (linear z h B N) (remainder h B N) := by
  let a := ofGaussian z B
  let b := ofGaussian h B
  let w := ofGaussian (add z h) B
  let M := harmonicPoint N
  let K := naturalPoint N
  let c := halfSquare h B
  have top := (difference_product (Γ := Γ) (halfSquare (add z h) B) (halfSquare z B) M).eqTrans
    ((qmul_congr (half_square_increment z h B hB) (.eqRefl _)).eqTrans
      (GaussianEulerIncompleteFactorialCombination.right_distribute (qmul a b) c M))
  have low := (qsub_congr (qmul_commutative (Γ := Γ) K w) (qmul_commutative K a)).eqTrans
    ((difference_product w a K).eqTrans (qmul_congr (point_increment z h B hB) (.eqRefl _)))
  have linearEq : Γ ⊢[PRAAx] qsub (qmul (qmul a b) M) (qmul b K) ≐ linear z h B N :=
    (qsub_congr ((qmul_congr (qmul_commutative a b) (.eqRefl _)).eqTrans (qmul_associative b a M)) (.eqRefl _)).eqTrans
      (((qsub_congr (qmul_commutative b (qmul a M)) (qmul_commutative b K)).eqTrans
        ((difference_product (qmul a M) K b).eqTrans (qmul_commutative _ _))))
  exact (qsub_congr (total_formula (add z h) B N hB) (total_formula z B N hB)).eqTrans
    ((subtract_difference _ _ _ _).eqTrans ((qsub_congr top low).eqTrans
      ((subtract_after_sum _ _ _).eqTrans (qadd_congr linearEq (.eqRefl _)))))

theorem quadratic_bound (z h B N H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) :
    Γ ⊢[PRAAx] distanceBounded (qsub (total (add z h) B N) (total z B N)) (linear z h B N) (N*H*H) (B*B) := by
  have h2 : Γ ⊢[PRAAx] le B (two*B) := le_congr (one_mul B) (.eqRefl _) (mul_le_mul_right B (le_succ_self one))
  have h2p := le_trans hB h2
  have small : Γ ⊢[PRAAx] bounded (ofGaussian h B) H B :=
    GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hB hB (ofGaussian_represents h B hB)
      (le_congr (.eqRefl _) (mul_comm _ _) (le_mul_mono (le_refl (B*B)) hh))
  have half : Γ ⊢[PRAAx] bounded (ofGaussian h (two*B)) H B :=
    GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ h2p hB (ofGaussian_represents h (two*B) h2p)
      (le_trans (le_mul_mono (le_refl (B*B)) hh)
        (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (H*H)) (le_mul_mono h2 h2))))
  have square := bounded_product _ _ H B H B hB hB small half
  have s := bounded_product _ _ (H*H) (B*B) N one (positive_product B B hB hB) (le_refl one)
    square (GaussianGammaCanonicalExponentBound.harmonic_point_bound N)
  change Γ ⊢[PRAAx] bounded (qsub (qsub (total (add z h) B N) (total z B N)) (linear z h B N)) (N*H*H) (B*B)
  exact bound_congr ((qsub_congr (exact_expansion z h B N hB) (.eqRefl _)).eqTrans
    (qadd_sub_cancel _ _ (qmul_canonical _ _))).eqSymm (by ipra_ring) (by ipra_ring) s

theorem actual_Barnes_finite_correction_expansion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ qsub (total (add (var 0) (var 1)) (var 2) (var 3)) (total (var 0) (var 2) (var 3)) ≐
      qadd (linear (var 0) (var 1) (var 2) (var 3)) (remainder (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (exact_expansion _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadCorrectionDerivative
