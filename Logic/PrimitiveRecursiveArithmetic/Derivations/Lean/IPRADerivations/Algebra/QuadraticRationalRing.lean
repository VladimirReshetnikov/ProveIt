import IPRADerivations.Algebra.QuadraticRationalRadicandEmbedding

/-!
# Original rational quadratic coefficient algebra and root uniqueness

The pair-ring identities hold coefficientwise for an arbitrary original
rational radicand, using its actual SIGNED numerator and positive decoded
denominator. No positivity, nonsquare or supplied ring/output law is
needed for those identities. The positive-radicand sign-zero domain then
derives the source uniqueness of nonnegative square roots.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticRationalRing

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalAlgebra (positive_product)
open QuadraticSignCertificates (encode first second first_value second_value negative_first negative_second)
open QuadraticConeOrder (add_first add_second)
open QuadraticRationalClearing (clear denominator represents sameCoefficients clear_represents denominator_positive)
open QuadraticRationalPairArithmetic (add negative scalar_add_same scalar_code_congr scalar_value_congr)
open QuadraticRationalEqualityOrder (difference cross)
open QuadraticRationalRadicand (multiply isPositive scale_representation equal_pairs_from_representations)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def productNumerator (d A B : PTm n) : PTm n := encode
  (ZT.ofNat (denominatorOf d)*(first A*first B)+numeratorOf d*(second A*second B))
  (ZT.ofNat (denominatorOf d)*(first A*second B+second A*first B))
@[simp] theorem subst_productNumerator {l : ℕ} (σ : Fin n → PTm l) (d A B : PTm n) :
    Syn.subst σ (productNumerator d A B) = productNumerator (Syn.subst σ d) (Syn.subst σ A) (Syn.subst σ B) := by simp [productNumerator]
theorem product_first (d A B : PTm n) : ZT.toZ Γ (first (productNumerator d A B)) =
    𝔞(denominatorOf d)*(ZT.toZ Γ (first A)*ZT.toZ Γ (first B))+
      ZT.toZ Γ (numeratorOf d)*(ZT.toZ Γ (second A)*ZT.toZ Γ (second B)) := by
  simp only [productNumerator,first_value,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
theorem product_second (d A B : PTm n) : ZT.toZ Γ (second (productNumerator d A B)) =
    𝔞(denominatorOf d)*(ZT.toZ Γ (first A)*ZT.toZ Γ (second B)+ZT.toZ Γ (second A)*ZT.toZ Γ (first B)) := by
  simp only [productNumerator,second_value,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
theorem multiply_represents (d x y A D B E : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E)
    (hx : Γ ⊢[PRAAx] represents x A D) (hy : Γ ⊢[PRAAx] represents y B E) : Γ ⊢[PRAAx]
    represents (multiply d x y) (productNumerator d A B) (denominatorOf d*(D*E)) := by
  let q := denominatorOf d
  have ac := LeanProofs.IPRA.Analysis.RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ D E (.andE₁ hx) (.andE₁ hy)
  have be := LeanProofs.IPRA.Analysis.RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ D E (.andE₂ hx) (.andE₂ hy)
  have ae := LeanProofs.IPRA.Analysis.RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ D E (.andE₁ hx) (.andE₂ hy)
  have bc := LeanProofs.IPRA.Analysis.RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ D E (.andE₂ hx) (.andE₁ hy)
  have firstRep := scalar_add_same (Γ := Γ) _ _ (q*(D*E)) _ _
    (positive_product (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive d) (positive_product hD hE))
    (scale_representation _ _ q _ ac)
    (LeanProofs.IPRA.Analysis.RationalRepresentations.represents_multiply d _ (numeratorOf d) _ q (D*E)
      (LeanProofs.IPRA.Analysis.RationalRepresentations.represents_self d) be)
  have secondRep := scale_representation (Γ := Γ) _ _ q _ (scalar_add_same _ _ (D*E) _ _ (positive_product hD hE) ae bc)
  refine .andI (scalar_code_congr _ _ (fst_pair _ _) ?_) (scalar_code_congr _ _ (snd_pair _ _) ?_)
  · exact scalar_value_congr _ _ _ _ (by simp only [productNumerator,first_value,q]) firstRep
  · exact scalar_value_congr _ _ _ _ (by simp only [productNumerator,second_value,q]) secondRep

theorem add_commutative (x y : PTm n) : Γ ⊢[PRAAx] sameCoefficients (add x y) (add y x) := by
  apply equal_pairs_from_representations _ _ _ _ _ _
    (positive_product (denominator_positive x) (denominator_positive y))
    (positive_product (denominator_positive y) (denominator_positive x))
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ (clear_represents x) (clear_represents y))
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ (clear_represents y) (clear_represents x))
  all_goals (simp only [add_first,add_second,QuadraticPositiveScaling.scale_first,QuadraticPositiveScaling.scale_second,Q.mk_mul,map_mul]; ring)
theorem multiply_commutative (d x y : PTm n) : Γ ⊢[PRAAx] sameCoefficients (multiply d x y) (multiply d y x) := by
  apply equal_pairs_from_representations _ _ _ _ _ _
    (positive_product (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive d) (positive_product (denominator_positive x) (denominator_positive y)))
    (positive_product (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive d) (positive_product (denominator_positive y) (denominator_positive x)))
    (multiply_represents _ _ _ _ _ _ _ (denominator_positive x) (denominator_positive y) (clear_represents x) (clear_represents y))
    (multiply_represents _ _ _ _ _ _ _ (denominator_positive y) (denominator_positive x) (clear_represents y) (clear_represents x))
  all_goals (simp only [product_first,product_second,Q.mk_mul,map_mul]; ring)
theorem add_associative (x y z : PTm n) : Γ ⊢[PRAAx] sameCoefficients (add (add x y) z) (add x (add y z)) := by
  have hxy := QuadraticRationalPairArithmetic.add_represents (Γ := Γ) _ _ _ _ _ _ (clear_represents x) (clear_represents y)
  have hyz := QuadraticRationalPairArithmetic.add_represents (Γ := Γ) _ _ _ _ _ _ (clear_represents y) (clear_represents z)
  apply equal_pairs_from_representations _ _ _ _ _ _
    (positive_product (positive_product (denominator_positive x) (denominator_positive y)) (denominator_positive z))
    (positive_product (denominator_positive x) (positive_product (denominator_positive y) (denominator_positive z)))
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ hxy (clear_represents z))
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ (clear_represents x) hyz)
  all_goals (simp only [add_first,add_second,QuadraticPositiveScaling.scale_first,QuadraticPositiveScaling.scale_second,Q.mk_mul,map_mul]; ring)
theorem multiply_associative (d x y z : PTm n) : Γ ⊢[PRAAx] sameCoefficients (multiply d (multiply d x y) z) (multiply d x (multiply d y z)) := by
  have hq := LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive (Γ := Γ) d
  have hxy := multiply_represents (Γ := Γ) d x y _ _ _ _ (denominator_positive x) (denominator_positive y) (clear_represents x) (clear_represents y)
  have hyz := multiply_represents (Γ := Γ) d y z _ _ _ _ (denominator_positive y) (denominator_positive z) (clear_represents y) (clear_represents z)
  have hxyD := positive_product hq (positive_product (denominator_positive x) (denominator_positive y))
  have hyzD := positive_product hq (positive_product (denominator_positive y) (denominator_positive z))
  apply equal_pairs_from_representations _ _ _ _ _ _
    (positive_product hq (positive_product hxyD (denominator_positive z)))
    (positive_product hq (positive_product (denominator_positive x) hyzD))
    (multiply_represents _ _ _ _ _ _ _ hxyD (denominator_positive z) hxy (clear_represents z))
    (multiply_represents _ _ _ _ _ _ _ (denominator_positive x) hyzD (clear_represents x) hyz)
  all_goals (simp only [product_first,product_second,Q.mk_mul,map_mul]; ring)
theorem multiply_add (d x y z : PTm n) : Γ ⊢[PRAAx]
    sameCoefficients (multiply d x (add y z)) (add (multiply d x y) (multiply d x z)) := by
  have hq := LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive (Γ := Γ) d
  have hyz := QuadraticRationalPairArithmetic.add_represents (Γ := Γ) _ _ _ _ _ _ (clear_represents y) (clear_represents z)
  have hxy := multiply_represents (Γ := Γ) d x y _ _ _ _ (denominator_positive x) (denominator_positive y) (clear_represents x) (clear_represents y)
  have hxz := multiply_represents (Γ := Γ) d x z _ _ _ _ (denominator_positive x) (denominator_positive z) (clear_represents x) (clear_represents z)
  apply equal_pairs_from_representations _ _ _ _ _ _
    (positive_product hq (positive_product (denominator_positive x) (positive_product (denominator_positive y) (denominator_positive z))))
    (positive_product (positive_product hq (positive_product (denominator_positive x) (denominator_positive y)))
      (positive_product hq (positive_product (denominator_positive x) (denominator_positive z))))
    (multiply_represents _ _ _ _ _ _ _ (denominator_positive x) (positive_product (denominator_positive y) (denominator_positive z)) (clear_represents x) hyz)
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ hxy hxz)
  all_goals (simp only [product_first,product_second,add_first,add_second,QuadraticPositiveScaling.scale_first,QuadraticPositiveScaling.scale_second,Q.mk_mul,map_mul]; ring)

theorem square_difference_factor (d x y : PTm n) : Γ ⊢[PRAAx]
    sameCoefficients (multiply d (difference x y) (add x y)) (difference (multiply d x x) (multiply d y y)) := by
  have hq := LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive (Γ := Γ) d
  have hx := denominator_positive (Γ := Γ) x
  have hy := denominator_positive (Γ := Γ) y
  have hxy := positive_product hx hy
  have hsx := positive_product hq (positive_product hx hx)
  have hsy := positive_product hq (positive_product hy hy)
  have hdiff := QuadraticRationalEqualityOrder.cross_represents (Γ := Γ) _ _ _ _ _ _ (clear_represents x) (clear_represents y)
  have hsum := QuadraticRationalPairArithmetic.add_represents (Γ := Γ) _ _ _ _ _ _ (clear_represents x) (clear_represents y)
  have hsquarex := multiply_represents (Γ := Γ) d x x _ _ _ _ hx hx (clear_represents x) (clear_represents x)
  have hsquarey := multiply_represents (Γ := Γ) d y y _ _ _ _ hy hy (clear_represents y) (clear_represents y)
  apply equal_pairs_from_representations _ _ _ _ _ _ (positive_product hq (positive_product hxy hxy)) (positive_product hsx hsy)
    (multiply_represents _ _ _ _ _ _ _ hxy hxy hdiff hsum)
    (QuadraticRationalEqualityOrder.cross_represents _ _ _ _ _ _ hsquarex hsquarey)
  all_goals (simp only [product_first,product_second,cross,QuadraticIntegerOrder.difference,add_first,add_second,
    negative_first,negative_second,QuadraticPositiveScaling.scale_first,QuadraticPositiveScaling.scale_second,Q.mk_mul,map_mul]; ring)

def nonnegative (d x : PTm n) : Fm PTm n :=
  QuadraticRationalRadicandOrder.positive d x ⋎ QuadraticRationalRadicandOrder.isZero d x
@[simp] theorem subst_nonnegative {l : ℕ} (σ : Fin n → PTm l) (d x : PTm n) :
    (nonnegative d x).subst σ = nonnegative (Syn.subst σ d) (Syn.subst σ x) := by
  simp [nonnegative,QuadraticRationalRadicandOrder.positive,QuadraticRationalRadicandOrder.isZero,
    QuadraticRationalRadicand.sign,QuadraticRationalRadicand.changeBasis]
theorem same_coefficients_sign (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (h : Γ ⊢[PRAAx] sameCoefficients x y) : Γ ⊢[PRAAx] QuadraticRationalRadicand.sign d x ≐ QuadraticRationalRadicand.sign d y :=
  QuadraticRationalClearing.sign_congr _ _ _ (QuadraticRationalRadicand.integer_radicand_positive d hd)
    (QuadraticRationalRadicandEmbedding.rescale_congr _ _ _ (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive d) h)
theorem positive_value_congr (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (hxy : Γ ⊢[PRAAx] sameCoefficients x y) (h : Γ ⊢[PRAAx] QuadraticRationalRadicandOrder.positive d x) : Γ ⊢[PRAAx]
    QuadraticRationalRadicandOrder.positive d y := (same_coefficients_sign _ _ _ hd hxy).eqSymm.eqTrans h
theorem zero_of_coefficients (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (hxy : Γ ⊢[PRAAx] sameCoefficients x y) (h : Γ ⊢[PRAAx] QuadraticRationalRadicandOrder.isZero d y) : Γ ⊢[PRAAx]
    QuadraticRationalRadicandOrder.isZero d x := (same_coefficients_sign _ _ _ hd hxy).eqTrans h
theorem positive_add_zero (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (hx : Γ ⊢[PRAAx] QuadraticRationalRadicandOrder.positive d x)
    (hy : Γ ⊢[PRAAx] QuadraticRationalRadicandOrder.isZero d y) : Γ ⊢[PRAAx] QuadraticRationalRadicandOrder.positive d (add x y) :=
  (QuadraticRationalClearing.sign_congr _ _ _ (QuadraticRationalRadicand.integer_radicand_positive d hd)
    (QuadraticRationalRadicand.rescale_add _ _ _ (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive d))).eqTrans
      (QuadraticRationalPairArithmetic.positive_add_zero _ _ _ (QuadraticRationalRadicand.integer_radicand_positive d hd) hx hy)
theorem positive_zero_absurd (d x : PTm n) (hp : Γ ⊢[PRAAx] QuadraticRationalRadicandOrder.positive d x)
    (hz : Γ ⊢[PRAAx] QuadraticRationalRadicandOrder.isZero d x) : Γ ⊢[PRAAx] Fm.bot :=
  QuadraticIntegerOrder.one_zero_absurd _ (hp.eqSymm.eqTrans hz)
theorem nonnegative_zero_sum (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (hx : Γ ⊢[PRAAx] nonnegative d x) (hy : Γ ⊢[PRAAx] nonnegative d y)
    (hs : Γ ⊢[PRAAx] QuadraticRationalRadicandOrder.isZero d (add x y)) : Γ ⊢[PRAAx]
    QuadraticRationalRadicandOrder.isZero d x ⋏ QuadraticRationalRadicandOrder.isZero d y := by
  refine .orE hx ?_ ?_
  · refine .orE hy.wk ?_ ?_
    · exact .botE _ (positive_zero_absurd _ _ (QuadraticRationalRadicandOrder.positive_add _ _ _ hd.wk.wk Prf.hyp1 Prf.hyp0) hs.wk.wk)
    · exact .botE _ (positive_zero_absurd _ _ (positive_add_zero _ _ _ hd.wk.wk Prf.hyp1 Prf.hyp0) hs.wk.wk)
  · refine .orE hy.wk ?_ (.andI Prf.hyp1 Prf.hyp0)
    exact .botE _ (positive_zero_absurd _ _ (positive_value_congr _ _ _ hd.wk.wk (add_commutative y x)
      (positive_add_zero _ _ _ hd.wk.wk Prf.hyp0 Prf.hyp1)) hs.wk.wk)
theorem square_root_unique (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (hx : Γ ⊢[PRAAx] nonnegative d x) (hy : Γ ⊢[PRAAx] nonnegative d y)
    (hs : Γ ⊢[PRAAx] QuadraticRationalRadicand.equivalent d (multiply d x x) (multiply d y y)) : Γ ⊢[PRAAx]
    QuadraticRationalRadicand.equivalent d x y := by
  have hp := zero_of_coefficients (Γ := Γ) _ _ _ hd (square_difference_factor d x y) hs
  refine .orE (QuadraticRationalRadicandOrder.zero_product_reflect d (difference x y) (add x y) hd hp) Prf.hyp0 ?_
  have both := nonnegative_zero_sum (Γ := QuadraticRationalRadicandOrder.isZero d (add x y) :: Γ) d x y hd.wk hx.wk hy.wk Prf.hyp0
  exact QuadraticRationalRadicandOrder.zero_add _ _ _ hd.wk (.andE₁ both)
    (QuadraticRationalRadicandOrder.zero_negative _ _ hd.wk (.andE₂ both))
theorem unique_actual_root (d x : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (hx : Γ ⊢[PRAAx] nonnegative d x)
    (hs : Γ ⊢[PRAAx] QuadraticRationalRadicand.equivalent d (multiply d x x) (QuadraticRationalEmbedding.embed d)) : Γ ⊢[PRAAx]
    QuadraticRationalRadicand.equivalent d x QuadraticRationalEmbedding.root :=
  square_root_unique d x QuadraticRationalEmbedding.root hd hx (.orI₁ (QuadraticRationalRadicandEmbedding.root_positive d hd))
    (QuadraticRationalRadicandOrder.equivalent_trans _ _ _ _ hd hs
      (QuadraticRationalRadicandOrder.equivalent_symm _ _ _ hd (QuadraticRationalRadicandEmbedding.root_square d hd)))

def zeroCode : PTm n := QuadraticRationalEmbedding.embed QuadraticRationalEmbedding.zeroScalar
def oneCode : PTm n := QuadraticRationalEmbedding.embed QuadraticRationalEmbedding.oneScalar
@[simp] theorem subst_zeroCode {l : ℕ} (σ : Fin n → PTm l) : Syn.subst σ (zeroCode : PTm n) = (zeroCode : PTm l) := by simp [zeroCode]
@[simp] theorem subst_oneCode {l : ℕ} (σ : Fin n → PTm l) : Syn.subst σ (oneCode : PTm n) = (oneCode : PTm l) := by simp [oneCode]
theorem zero_represents : Γ ⊢[PRAAx] represents (zeroCode : PTm n) QuadraticSignCertificates.zeroCode one :=
  QuadraticRationalEmbedding.embedding_represents _ _ _ (QuadraticRationalPairArithmetic.scalar_represents zero)
theorem one_represents : Γ ⊢[PRAAx] represents (oneCode : PTm n) QuadraticSignCertificates.oneCode one :=
  QuadraticRationalEmbedding.embedding_represents _ _ _ (QuadraticRationalPairArithmetic.scalar_represents one)
theorem add_zero (x : PTm n) : Γ ⊢[PRAAx] sameCoefficients (add x zeroCode) x := by
  apply equal_pairs_from_representations _ _ _ _ _ _ (positive_product (denominator_positive x) (le_refl one)) (denominator_positive x)
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ (clear_represents x) zero_represents) (clear_represents x)
  all_goals (simp only [add_first,add_second,QuadraticPositiveScaling.scale_first,QuadraticPositiveScaling.scale_second,
    QuadraticSignCertificates.zero_first_value,QuadraticSignCertificates.zero_second_value,Q.mk_mul,Q.mk_one,map_mul,map_one]; ring)
theorem add_negative_self (x : PTm n) : Γ ⊢[PRAAx] sameCoefficients (add x (negative x)) zeroCode := by
  apply equal_pairs_from_representations _ _ _ _ _ _ (positive_product (denominator_positive x) (denominator_positive x)) (le_refl one)
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ (clear_represents x)
      (QuadraticRationalPairArithmetic.negative_represents _ _ _ (clear_represents x))) zero_represents
  all_goals (simp only [add_first,add_second,negative_first,negative_second,
    QuadraticPositiveScaling.scale_first,QuadraticPositiveScaling.scale_second,
    QuadraticSignCertificates.zero_first_value,QuadraticSignCertificates.zero_second_value,Q.mk_mul,Q.mk_one,map_mul,map_one]; ring)
theorem multiply_one (d x : PTm n) : Γ ⊢[PRAAx] sameCoefficients (multiply d x oneCode) x := by
  have hq := LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive (Γ := Γ) d
  apply equal_pairs_from_representations _ _ _ _ _ _ (positive_product hq (positive_product (denominator_positive x) (le_refl one))) (denominator_positive x)
    (multiply_represents _ _ _ _ _ _ _ (denominator_positive x) (le_refl one) (clear_represents x) one_represents) (clear_represents x)
  all_goals (simp only [product_first,product_second,QuadraticIntegerOrder.one_first_value,QuadraticIntegerOrder.one_second_value,
    Q.mk_mul,Q.mk_one,map_mul,map_one]; ring)
theorem negative_involution (x : PTm n) : Γ ⊢[PRAAx] sameCoefficients (negative (negative x)) x := by
  apply equal_pairs_from_representations _ _ _ _ _ _ (denominator_positive x) (denominator_positive x)
    (QuadraticRationalPairArithmetic.negative_represents _ _ _ (QuadraticRationalPairArithmetic.negative_represents _ _ _ (clear_represents x))) (clear_represents x)
  all_goals simp only [negative_first,negative_second,neg_neg]

def output (d x y : PTm n) : PTm n :=
  pairT (multiply d (difference x y) (add x y))
    (pairT (difference (multiply d x x) (multiply d y y))
      (pairT QuadraticRationalEmbedding.root (multiply d QuadraticRationalEmbedding.root QuadraticRationalEmbedding.root)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (d x y : PTm n) : PTm n := ap3 outputF d x y
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (d x y : PTm n) :
    Syn.subst σ (output d x y) = output (Syn.subst σ d) (Syn.subst σ x) (Syn.subst σ y) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (d x y : PTm n) :
    Syn.subst σ (run d x y) = run (Syn.subst σ d) (Syn.subst σ x) (Syn.subst σ y) := by simp [run]
theorem program_at (d x y : PTm n) : Γ ⊢[PRAAx] run d x y ≐ output d x y := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![d,x,y]
theorem returned_product (d x y : PTm n) : Γ ⊢[PRAAx] fstT (run d x y) ≐ multiply d (difference x y) (add x y) :=
  (congrFst (program_at _ _ _)).eqTrans (fst_pair _ _)
theorem returned_difference (d x y : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d x y)) ≐ difference (multiply d x x) (multiply d y y) :=
  (congrFst ((congrSnd (program_at _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_root (d x y : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run d x y))) ≐ QuadraticRationalEmbedding.root :=
  (congrFst ((congrSnd ((congrSnd (program_at _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_square (d x y : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run d x y))) ≐ multiply d QuadraticRationalEmbedding.root QuadraticRationalEmbedding.root :=
  (congrSnd ((congrSnd ((congrSnd (program_at _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem coefficients_code_congr {x x' y y' : PTm n} (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y')
    (h : Γ ⊢[PRAAx] sameCoefficients x y) : Γ ⊢[PRAAx] sameCoefficients x' y' :=
  .andI (LeanProofs.IPRA.Analysis.RationalArgmin.rationalEq_congr (congrFst hx) (congrFst hy) (.andE₁ h))
    (LeanProofs.IPRA.Analysis.RationalArgmin.rationalEq_congr (congrSnd hx) (congrSnd hy) (.andE₂ h))
theorem returned_factorization (d x y : PTm n) : Γ ⊢[PRAAx] sameCoefficients (fstT (run d x y)) (fstT (sndT (run d x y))) :=
  coefficients_code_congr (returned_product _ _ _).eqSymm (returned_difference _ _ _).eqSymm (square_difference_factor d x y)

theorem original_rational_pair_ring_addition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sameCoefficients (add (var 0) (var 1)) (add (var 1) (var 0)) ⋏
      sameCoefficients (add (add (var 0) (var 1)) (var 2)) (add (var 0) (add (var 1) (var 2)))) :=
  closeUniv 3 (.andI (add_commutative _ _) (add_associative _ _ _))
theorem original_rational_pair_ring_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sameCoefficients (multiply (var 0) (var 1) (var 2)) (multiply (var 0) (var 2) (var 1)) ⋏
      sameCoefficients (multiply (var 0) (multiply (var 0) (var 1) (var 2)) (var 3)) (multiply (var 0) (var 1) (multiply (var 0) (var 2) (var 3)))) :=
  closeUniv 4 (.andI (multiply_commutative _ _ _) (multiply_associative _ _ _ _))
theorem original_rational_pair_distribution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sameCoefficients (multiply (var 0) (var 1) (add (var 2) (var 3)))
      (add (multiply (var 0) (var 1) (var 2)) (multiply (var 0) (var 1) (var 3)))) := closeUniv 4 (multiply_add _ _ _ _)
theorem original_rational_pair_units_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (sameCoefficients (add (var 1) zeroCode) (var 1) ⋏ (sameCoefficients (add (var 1) (negative (var 1))) zeroCode ⋏
      sameCoefficients (multiply (var 0) (var 1) oneCode) (var 1))) := closeUniv 2 (.andI (add_zero _) (.andI (add_negative_self _) (multiply_one _ _)))
theorem original_rational_pair_square_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sameCoefficients (multiply (var 0) (difference (var 1) (var 2)) (add (var 1) (var 2)))
      (difference (multiply (var 0) (var 1) (var 1)) (multiply (var 0) (var 2) (var 2)))) := closeUniv 3 (square_difference_factor _ _ _)
theorem positive_rational_nonnegative_zero_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (isPositive (var 0) ⟶ nonnegative (var 0) (var 1) ⟶ nonnegative (var 0) (var 2) ⟶
      QuadraticRationalRadicandOrder.isZero (var 0) (add (var 1) (var 2)) ⟶
        (QuadraticRationalRadicandOrder.isZero (var 0) (var 1) ⋏ QuadraticRationalRadicandOrder.isZero (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (nonnegative_zero_sum _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem positive_rational_nonnegative_root_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (isPositive (var 0) ⟶ nonnegative (var 0) (var 1) ⟶ nonnegative (var 0) (var 2) ⟶
      QuadraticRationalRadicand.equivalent (var 0) (multiply (var 0) (var 1) (var 1)) (multiply (var 0) (var 2) (var 2)) ⟶
        QuadraticRationalRadicand.equivalent (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (square_root_unique _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem original_positive_rational_root_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (isPositive (var 0) ⟶ nonnegative (var 0) (var 1) ⟶
      QuadraticRationalRadicand.equivalent (var 0) (multiply (var 0) (var 1) (var 1)) (QuadraticRationalEmbedding.embed (var 0)) ⟶
        QuadraticRationalRadicand.equivalent (var 0) (var 1) QuadraticRationalEmbedding.root) :=
  closeUniv 2 (.impI (.impI (.impI (unique_actual_root _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_rational_pair_factorization_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_rational_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sameCoefficients (fstT (run (var 0) (var 1) (var 2))) (fstT (sndT (run (var 0) (var 1) (var 2))))) := closeUniv 3 (returned_factorization _ _ _)

end LeanProofs.IPRA.Algebra.QuadraticRationalRing
