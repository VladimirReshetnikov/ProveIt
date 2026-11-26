import IPRADerivations.Algebra.QuadraticRationalRing
import IPRADerivations.Algebra.QuadraticRationalZeroProjection

/-!
# One quadratic sign program for nonnegative rational radicands

The radicand is an original rational code with its decoded positive
denominator. The zero branch inspects the first coefficient and the positive
branch uses the change of basis. The product keeps the original radicand
code, including in the zero branch.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticRationalNonnegativeRadicand

open_ipra
open LeanProofs.IPRA.Analysis
open RationalSupMetric (numeratorOf denominatorOf)
open RationalArgmin (rationalEq rationalEq_congr left left_congr)
open QuadraticRationalRadicand (isPositive positiveNumerator multiply)
open QuadraticRationalEmbedding (embed root)
open QuadraticRationalEqualityOrder (difference)
open QuadraticRationalPairArithmetic (add negative)
open QuadraticRationalClearing (sameCoefficients)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def nonnegative (d : PTm n) : Fm PTm n := zle (ZT.ofNat zero) (numeratorOf d)
def radicandZero (d : PTm n) : Fm PTm n := ZT.eq (numeratorOf d) (ZT.ofNat zero)

def sign (d x : PTm n) : PTm n :=
  RationalArithmetic.select (eqb (positiveNumerator d) zero)
    (QuadraticRationalRadicand.sign d x) (QuadraticRationalZeroProjection.sign x)
def positive (d x : PTm n) : Fm PTm n := sign d x ≐ one
def isZero (d x : PTm n) : Fm PTm n := sign d x ≐ zero
def equivalent (d x y : PTm n) : Fm PTm n := isZero d (difference x y)
def less (d x y : PTm n) : Fm PTm n := positive d (difference y x)

ipra_subst sign [QuadraticRationalRadicand.sign, QuadraticRationalRadicand.changeBasis]

theorem radicand_cases (d : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d) : Γ ⊢[PRAAx]
    isPositive d ⋎ radicandZero d := by
  refine .orE (QuadraticIntegerEmbedding.integer_trichotomy (numeratorOf d)) (.orI₁ Prf.hyp0) ?_
  refine .orE Prf.hyp0 ?_ (.orI₂ Prf.hyp0)
  let negative := zle (ZT.ofNat one) (-(numeratorOf d))
  let branch := negative :: (negative ⋎ radicandZero d) :: Γ
  have hNeg : branch ⊢[PRAAx] negative := Prf.hyp0
  have hNonneg : branch ⊢[PRAAx] nonnegative d := hd.wk.wk
  refine false_of_comb (zsl hNonneg + zsl hNeg) ?_ (nn_add (nn_zsl hNonneg) (nn_zsl hNeg)) _
  simp only [zsl_def,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_one,Q.mk_zero,map_one,map_zero]
  ring

theorem positive_branch (d x : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx]
    sign d x ≐ QuadraticRationalRadicand.sign d x := by
  apply RationalArithmetic.select_zero
  apply eqb_of_ne
  refine .impI (not_succ_le_self zero _ ?_)
  exact le_congr (.eqRefl _) Prf.hyp0 (QuadraticRationalRadicand.numerator_positive d hd.wk)

theorem zero_branch (d x : PTm n) (hd : Γ ⊢[PRAAx] radicandZero d) : Γ ⊢[PRAAx]
    sign d x ≐ QuadraticRationalZeroProjection.sign x := by
  apply RationalArithmetic.select_one
  apply eqb_of_eq
  apply QuadraticSignCertificates.positive_part_zero
  exact zle_of_comb 0 (by rw [ZT.toZ_eq hd]; ring) nn_zero

theorem raw_zero_scalar (d : PTm n) (hd : Γ ⊢[PRAAx] radicandZero d) : Γ ⊢[PRAAx]
    rationalEq d (QuadraticRationalPairArithmetic.scalar zero) := by
  have hq := RationalArgmin.denominator_positive (Γ := Γ) d
  apply QuadraticRationalRadicand.equal_from_representations _ _ _ _ _ _ hq (le_refl one)
    (RationalRepresentations.represents_self d) (QuadraticRationalPairArithmetic.scalar_represents zero)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_eq hd,ZT.toZ_ofNat,Q.mk_zero,map_zero]
  ring

private theorem mul_zero_numerator (d a : PTm n) (hd : Γ ⊢[PRAAx] radicandZero d) : Γ ⊢[PRAAx]
    RationalArithmetic.multiply d a ≐ RationalIntegerNormalization.integerCode (ZT.ofNat zero) := by
  apply RationalIntegerNormalization.normalize_integer _ _ _ (RationalArithmetic.product_denominator_positive d a)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_eq hd,ZT.toZ_ofNat,Q.mk_zero,map_zero]
  ring

private theorem zero_scalar_numerator : Γ ⊢[PRAAx]
    radicandZero (QuadraticRationalPairArithmetic.scalar (zero : PTm n)) := by
  ipra_lc -ZT.toZ_eq (QuadraticRationalPairArithmetic.scalar_represents (Γ := Γ) (zero : PTm n))

private theorem add_right_congr (b a a' : PTm n) (h : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx]
    RationalArithmetic.add b a ≐ RationalArithmetic.add b a' := by
  simpa using Prf.eqCongr (RationalArithmetic.add (var 0) (var 1))
    (σ := ![b,a]) (σ' := ![b,a'])
    (fun i => by fin_cases i; exact .eqRefl _; exact h)

theorem raw_zero_product (d x y : PTm n) (hd : Γ ⊢[PRAAx] radicandZero d) : Γ ⊢[PRAAx]
    multiply d x y ≐ QuadraticRationalPairArithmetic.multiply zero x y := by
  let a := RationalArithmetic.multiply (sndT x) (sndT y)
  let b := RationalArithmetic.multiply (fstT x) (fstT y)
  have h := (mul_zero_numerator d a hd).eqTrans (mul_zero_numerator _ a zero_scalar_numerator).eqSymm
  exact congrPairT (add_right_congr b _ _ h) (.eqRefl _)

theorem trichotomy (d x y : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d) : Γ ⊢[PRAAx]
    less d x y ⋎ (less d y x ⋎ equivalent d x y) := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    refine .orE (QuadraticRationalRadicandOrder.trichotomy d x y hp) ?_ ?_
    · exact .orI₁ ((positive_branch d _ hp.wk).eqTrans Prf.hyp0)
    · refine .orE Prf.hyp0 ?_ ?_
      · exact .orI₂ (.orI₁ ((positive_branch d _ hp.wk.wk).eqTrans Prf.hyp0))
      · exact .orI₂ (.orI₂ ((positive_branch d _ hp.wk.wk).eqTrans Prf.hyp0))
  · have hz : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    refine .orE (QuadraticRationalZeroProjection.ordered_trichotomy x y) ?_ ?_
    · exact .orI₁ ((zero_branch d _ hz.wk).eqTrans Prf.hyp0)
    · refine .orE Prf.hyp0 ?_ ?_
      · exact .orI₂ (.orI₁ ((zero_branch d _ hz.wk.wk).eqTrans Prf.hyp0))
      · exact .orI₂ (.orI₂ ((zero_branch d _ hz.wk.wk).eqTrans Prf.hyp0))

theorem root_nonnegative_and_square (d : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d) : Γ ⊢[PRAAx]
    (positive d root ⋎ isZero d root) ⋏ equivalent d (multiply d root root) (embed d) := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    exact .andI (.orI₁ ((positive_branch d root hp).eqTrans (QuadraticRationalRadicandEmbedding.root_positive d hp)))
      ((positive_branch d _ hp).eqTrans (QuadraticRationalRadicandEmbedding.root_square d hp))
  · have hz : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    refine .andI (.orI₂ ((zero_branch d root hz).eqTrans QuadraticRationalZeroProjection.root_isZero))
      ((zero_branch d _ hz).eqTrans ?_)
    have hp := congrFst (raw_zero_product d root root hz)
    have hLeft := QuadraticRationalZeroProjection.equivalent_of_projection _ _
      (rationalEq_congr hp.eqSymm (.eqRefl _)
        (QuadraticRationalZeroProjection.equivalent_reflect _ _ QuadraticRationalZeroProjection.root_square))
    have hRight := QuadraticRationalZeroProjection.equivalent_of_projection
      (embed (QuadraticRationalPairArithmetic.scalar zero)) (embed d)
      (rationalEq_congr (fst_pair _ _).eqSymm (fst_pair _ _).eqSymm (raw_zero_scalar d hz).eqSymm)
    exact QuadraticRationalZeroProjection.equivalent_trans _ _ _ hLeft hRight

theorem coefficients_equivalent (d x y : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (h : Γ ⊢[PRAAx] sameCoefficients x y) : Γ ⊢[PRAAx] equivalent d x y := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · exact (positive_branch d _ Prf.hyp0).eqTrans
      (QuadraticRationalRadicandEmbedding.coefficients_equivalent d x y Prf.hyp0 h.wk)
  · exact (zero_branch d _ Prf.hyp0).eqTrans
      (QuadraticRationalZeroProjection.equivalent_of_projection x y (.andE₁ h.wk))

private theorem zero_sign_congr_code (x y : PTm n) (h : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx]
    QuadraticRationalZeroProjection.sign x ≐ QuadraticRationalZeroProjection.sign y := by
  simpa using Prf.eqCongr (QuadraticRationalZeroProjection.sign (var 0))
    (σ := ![x]) (σ' := ![y]) (fun i => by fin_cases i; exact h)

theorem zero_product_reflect (d x y : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (h : Γ ⊢[PRAAx] isZero d (multiply d x y)) : Γ ⊢[PRAAx] isZero d x ⋎ isZero d y := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    have hm := (positive_branch d (multiply d x y) hp).eqSymm.eqTrans h.wk
    exact .orE (QuadraticRationalRadicandOrder.zero_product_reflect d x y hp hm)
      (.orI₁ ((positive_branch d x hp.wk).eqTrans Prf.hyp0))
      (.orI₂ ((positive_branch d y hp.wk).eqTrans Prf.hyp0))
  · have hz : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    have he := zero_sign_congr_code _ _ (raw_zero_product d x y hz)
    have hm := he.eqSymm.eqTrans ((zero_branch d (multiply d x y) hz).eqSymm.eqTrans h.wk)
    exact .orE (QuadraticRationalZeroProjection.zero_product_reflect x y hm)
      (.orI₁ ((zero_branch d x hz.wk).eqTrans Prf.hyp0))
      (.orI₂ ((zero_branch d y hz.wk).eqTrans Prf.hyp0))

theorem positive_multiply (d x y : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (hx : Γ ⊢[PRAAx] positive d x) (hy : Γ ⊢[PRAAx] positive d y) : Γ ⊢[PRAAx]
    positive d (multiply d x y) := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    exact (positive_branch d _ hp).eqTrans (QuadraticRationalRadicandOrder.positive_multiply d x y hp
      ((positive_branch d x hp).eqSymm.eqTrans hx.wk) ((positive_branch d y hp).eqSymm.eqTrans hy.wk))
  · have hz : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    have he := zero_sign_congr_code _ _ (raw_zero_product d x y hz)
    exact (zero_branch d _ hz).eqTrans (he.eqTrans (QuadraticRationalZeroProjection.positive_multiply x y
      ((zero_branch d x hz).eqSymm.eqTrans hx.wk) ((zero_branch d y hz).eqSymm.eqTrans hy.wk)))

theorem less_trans (d x y z : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (hxy : Γ ⊢[PRAAx] less d x y) (hyz : Γ ⊢[PRAAx] less d y z) : Γ ⊢[PRAAx] less d x z := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    exact (positive_branch d _ hp).eqTrans (QuadraticRationalRadicandOrder.less_trans d x y z hp
      ((positive_branch d _ hp).eqSymm.eqTrans hxy.wk) ((positive_branch d _ hp).eqSymm.eqTrans hyz.wk))
  · have hz : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    exact (zero_branch d _ hz).eqTrans (QuadraticRationalZeroProjection.less_trans x y z
      ((zero_branch d _ hz).eqSymm.eqTrans hxy.wk) ((zero_branch d _ hz).eqSymm.eqTrans hyz.wk))

theorem less_translate (d x y z : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (hxy : Γ ⊢[PRAAx] less d x y) : Γ ⊢[PRAAx] less d (add x z) (add y z) := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    exact (positive_branch d _ hp).eqTrans
      (QuadraticRationalRadicandOrder.less_translate d x y z hp ((positive_branch d _ hp).eqSymm.eqTrans hxy.wk))
  · have hz : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    exact (zero_branch d _ hz).eqTrans
      (QuadraticRationalZeroProjection.less_translate x y z ((zero_branch d _ hz).eqSymm.eqTrans hxy.wk))

def pointNonnegative (d x : PTm n) : Fm PTm n := positive d x ⋎ isZero d x

private theorem zero_root_comparison (d : PTm n) (hz : Γ ⊢[PRAAx] radicandZero d) : Γ ⊢[PRAAx]
    QuadraticRationalZeroProjection.equivalent (embed d) root := by
  have he := QuadraticRationalZeroProjection.equivalent_of_projection
    (embed d) (embed QuadraticRationalEmbedding.zeroScalar)
    (rationalEq_congr (fst_pair _ _).eqSymm (fst_pair _ _).eqSymm (raw_zero_scalar d hz))
  exact QuadraticRationalZeroProjection.equivalent_trans _ _ _ he
    (QuadraticRationalZeroProjection.equivalent_symm _ _ QuadraticRationalZeroProjection.root_equivalent_zero)

theorem unique_actual_root (d x : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (hx : Γ ⊢[PRAAx] pointNonnegative d x) (hs : Γ ⊢[PRAAx] equivalent d (multiply d x x) (embed d)) :
    Γ ⊢[PRAAx] equivalent d x root := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    have hn : (isPositive d :: Γ) ⊢[PRAAx] QuadraticRationalRing.nonnegative d x :=
      .orE hx.wk (.orI₁ ((positive_branch d x hp.wk).eqSymm.eqTrans Prf.hyp0))
        (.orI₂ ((positive_branch d x hp.wk).eqSymm.eqTrans Prf.hyp0))
    exact (positive_branch d _ hp).eqTrans (QuadraticRationalRing.unique_actual_root d x hp hn
      ((positive_branch d _ hp).eqSymm.eqTrans hs.wk))
  · have hz : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    have he : (radicandZero d :: Γ) ⊢[PRAAx]
        QuadraticRationalZeroProjection.equivalent (multiply d x x) (embed d) :=
      (zero_branch d _ hz).eqSymm.eqTrans hs.wk
    have hg := QuadraticRationalZeroProjection.equivalent_trans _ _ _ he (zero_root_comparison d hz)
    have hzero := (QuadraticRationalZeroProjection.sign_congr _ _ hg).eqTrans
      QuadraticRationalZeroProjection.root_isZero
    have hProduct := (zero_sign_congr_code _ _ (raw_zero_product d x x hz)).eqSymm.eqTrans hzero
    have hf : (radicandZero d :: Γ) ⊢[PRAAx] QuadraticRationalZeroProjection.isZero x :=
      .orE (QuadraticRationalZeroProjection.zero_product_reflect x x hProduct) Prf.hyp0 Prf.hyp0
    exact (zero_branch d _ hz).eqTrans (QuadraticRationalZeroProjection.zero_add _ _ hf
      (QuadraticRationalZeroProjection.zero_negative root QuadraticRationalZeroProjection.root_isZero))

theorem equivalent_refl (d x : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d) : Γ ⊢[PRAAx]
    equivalent d x x := coefficients_equivalent d x x hd (.andI (.eqRefl _) (.eqRefl _))

theorem equivalent_symm (d x y : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (h : Γ ⊢[PRAAx] equivalent d x y) : Γ ⊢[PRAAx] equivalent d y x := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    exact (positive_branch d _ hp).eqTrans (QuadraticRationalRadicandOrder.equivalent_symm d x y hp
      ((positive_branch d _ hp).eqSymm.eqTrans h.wk))
  · have hz : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    exact (zero_branch d _ hz).eqTrans (QuadraticRationalZeroProjection.equivalent_symm x y
      ((zero_branch d _ hz).eqSymm.eqTrans h.wk))

theorem equivalent_trans (d x y z : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (hxy : Γ ⊢[PRAAx] equivalent d x y) (hyz : Γ ⊢[PRAAx] equivalent d y z) : Γ ⊢[PRAAx] equivalent d x z := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    exact (positive_branch d _ hp).eqTrans (QuadraticRationalRadicandOrder.equivalent_trans d x y z hp
      ((positive_branch d _ hp).eqSymm.eqTrans hxy.wk) ((positive_branch d _ hp).eqSymm.eqTrans hyz.wk))
  · have hz : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    exact (zero_branch d _ hz).eqTrans (QuadraticRationalZeroProjection.equivalent_trans x y z
      ((zero_branch d _ hz).eqSymm.eqTrans hxy.wk) ((zero_branch d _ hz).eqSymm.eqTrans hyz.wk))

theorem equivalent_add (d x x' y y' : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (hx : Γ ⊢[PRAAx] equivalent d x x') (hy : Γ ⊢[PRAAx] equivalent d y y') : Γ ⊢[PRAAx]
    equivalent d (add x y) (add x' y') := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    exact (positive_branch d _ hp).eqTrans (QuadraticRationalRadicandOrder.equivalent_add d x x' y y' hp
      ((positive_branch d _ hp).eqSymm.eqTrans hx.wk) ((positive_branch d _ hp).eqSymm.eqTrans hy.wk))
  · have hz : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    exact (zero_branch d _ hz).eqTrans (QuadraticRationalZeroProjection.equivalent_add x x' y y'
      ((zero_branch d _ hz).eqSymm.eqTrans hx.wk) ((zero_branch d _ hz).eqSymm.eqTrans hy.wk))

theorem equivalent_negative (d x y : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (h : Γ ⊢[PRAAx] equivalent d x y) : Γ ⊢[PRAAx] equivalent d (negative x) (negative y) := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    exact (positive_branch d _ hp).eqTrans (QuadraticRationalRadicandOrder.equivalent_negative d x y hp
      ((positive_branch d _ hp).eqSymm.eqTrans h.wk))
  · have hz : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    exact (zero_branch d _ hz).eqTrans (QuadraticRationalZeroProjection.equivalent_negative x y
      ((zero_branch d _ hz).eqSymm.eqTrans h.wk))

theorem equivalent_multiply (d x x' y y' : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (hx : Γ ⊢[PRAAx] equivalent d x x') (hy : Γ ⊢[PRAAx] equivalent d y y') : Γ ⊢[PRAAx]
    equivalent d (multiply d x y) (multiply d x' y') := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    exact (positive_branch d _ hp).eqTrans (QuadraticRationalRadicandOrder.equivalent_multiply d x x' y y' hp
      ((positive_branch d _ hp).eqSymm.eqTrans hx.wk) ((positive_branch d _ hp).eqSymm.eqTrans hy.wk))
  · have hz : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    have he := QuadraticRationalZeroProjection.equivalent_multiply x x' y y'
      ((zero_branch d _ hz).eqSymm.eqTrans hx.wk) ((zero_branch d _ hz).eqSymm.eqTrans hy.wk)
    exact (zero_branch d _ hz).eqTrans (QuadraticRationalZeroProjection.equivalent_of_projection _ _
      (rationalEq_congr (congrFst (raw_zero_product d x y hz)).eqSymm
        (congrFst (raw_zero_product d x' y' hz)).eqSymm
        (QuadraticRationalZeroProjection.equivalent_reflect _ _ he)))

theorem less_irrefl (d x : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d) : Γ ⊢[PRAAx] neg (less d x x) := by
  refine .impI (.orE (radicand_cases d hd.wk) ?_ ?_)
  · exact .impE (QuadraticRationalRadicandOrder.less_irrefl d x Prf.hyp0)
      ((positive_branch d _ Prf.hyp0).eqSymm.eqTrans Prf.hyp1)
  · exact .impE (QuadraticRationalZeroProjection.less_irrefl x)
      ((zero_branch d _ Prf.hyp0).eqSymm.eqTrans Prf.hyp1)

theorem embedding_injective_iff (d x y : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d) : Γ ⊢[PRAAx]
    Fm.iff (equivalent d (embed x) (embed y)) (rationalEq x y) := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    have he := QuadraticRationalRadicandEmbedding.embedding_injective_iff d x y hp
    exact .andI (.impI (he.wk.iffMp ((positive_branch d _ hp.wk).eqSymm.eqTrans Prf.hyp0)))
      (.impI ((positive_branch d _ hp.wk).eqTrans (he.wk.iffMpr Prf.hyp0)))
  · have hz : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    have he := QuadraticRationalZeroProjection.equivalent_iff (Γ := radicandZero d :: Γ) (embed x) (embed y)
    refine .andI (.impI ?_) (.impI ?_)
    · exact rationalEq_congr (fst_pair _ _) (fst_pair _ _)
        (he.wk.iffMp ((zero_branch d _ hz.wk).eqSymm.eqTrans Prf.hyp0))
    · exact (zero_branch d _ hz.wk).eqTrans
        (he.wk.iffMpr (rationalEq_congr (fst_pair _ _).eqSymm (fst_pair _ _).eqSymm Prf.hyp0))

theorem embedding_order_iff (d x y : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d) : Γ ⊢[PRAAx]
    Fm.iff (less d (embed x) (embed y)) (lt (left x y) (left y x)) := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    have he := QuadraticRationalRadicandEmbedding.embedding_order_iff d x y hp
    exact .andI (.impI (he.wk.iffMp ((positive_branch d _ hp.wk).eqSymm.eqTrans Prf.hyp0)))
      (.impI ((positive_branch d _ hp.wk).eqTrans (he.wk.iffMpr Prf.hyp0)))
  · have hz : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    let X := embed x
    let Y := embed y
    have he := QuadraticRationalEmbedding.embedding_order_iff one (fstT X) (fstT Y)
      (Γ := radicandZero d :: Γ) (le_refl one)
    have hx : (radicandZero d :: Γ) ⊢[PRAAx] fstT X ≐ x := fst_pair _ _
    have hy : (radicandZero d :: Γ) ⊢[PRAAx] fstT Y ≐ y := fst_pair _ _
    have hl := left_congr hx hy
    have hr := left_congr hy hx
    refine .andI (.impI ?_) (.impI ?_)
    · exact lt_congr hl.wk hr.wk (he.wk.iffMp (QuadraticRationalZeroProjection.less_project X Y
        ((zero_branch d _ hz.wk).eqSymm.eqTrans Prf.hyp0)))
    · exact (zero_branch d _ hz.wk).eqTrans (QuadraticRationalZeroProjection.less_of_project X Y
        (he.wk.iffMpr (lt_congr hl.wk.eqSymm hr.wk.eqSymm Prf.hyp0)))

theorem less_congr (d x x' y y' : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (hx : Γ ⊢[PRAAx] equivalent d x x') (hy : Γ ⊢[PRAAx] equivalent d y y')
    (h : Γ ⊢[PRAAx] less d x y) : Γ ⊢[PRAAx] less d x' y' := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    have he := QuadraticRationalRadicandOrder.less_congr d x x' y y' hp
      ((positive_branch d _ hp).eqSymm.eqTrans hx.wk) ((positive_branch d _ hp).eqSymm.eqTrans hy.wk)
    exact (positive_branch d _ hp).eqTrans (he.iffMp ((positive_branch d _ hp).eqSymm.eqTrans h.wk))
  · have hz : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    exact (zero_branch d _ hz).eqTrans (QuadraticRationalZeroProjection.less_congr x x' y y'
      ((zero_branch d _ hz).eqSymm.eqTrans hx.wk) ((zero_branch d _ hz).eqSymm.eqTrans hy.wk)
      ((zero_branch d _ hz).eqSymm.eqTrans h.wk))

private theorem difference_congr {x x' y y' : PTm n} (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') :
    Γ ⊢[PRAAx] difference x y ≐ difference x' y' := by
  simpa using Prf.eqCongr (difference (var 0) (var 1))
    (σ := ![x,y]) (σ' := ![x',y']) (fun i => by fin_cases i; exact hx; exact hy)

theorem less_multiply_positive (d x y z : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (hz : Γ ⊢[PRAAx] positive d z) (h : Γ ⊢[PRAAx] less d x y) : Γ ⊢[PRAAx]
    less d (multiply d z x) (multiply d z y) := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    exact (positive_branch d _ hp).eqTrans (QuadraticRationalRadicandOrder.less_multiply_positive d x y z hp
      ((positive_branch d _ hp).eqSymm.eqTrans hz.wk) ((positive_branch d _ hp).eqSymm.eqTrans h.wk))
  · have h0 : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    have he := zero_sign_congr_code _ _ (difference_congr (raw_zero_product d z y h0) (raw_zero_product d z x h0))
    exact (zero_branch d _ h0).eqTrans (he.eqTrans
      (QuadraticRationalZeroProjection.less_multiply_positive x y z
        ((zero_branch d _ h0).eqSymm.eqTrans hz.wk) ((zero_branch d _ h0).eqSymm.eqTrans h.wk)))

theorem positive_add (d x y : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (hx : Γ ⊢[PRAAx] positive d x) (hy : Γ ⊢[PRAAx] positive d y) :
    Γ ⊢[PRAAx] positive d (add x y) := by
  refine .orE (radicand_cases d hd) ?_ ?_
  · have hp : (isPositive d :: Γ) ⊢[PRAAx] isPositive d := Prf.hyp0
    exact (positive_branch d _ hp).eqTrans (QuadraticRationalRadicandOrder.positive_add d x y hp
      ((positive_branch d _ hp).eqSymm.eqTrans hx.wk) ((positive_branch d _ hp).eqSymm.eqTrans hy.wk))
  · have hz : (radicandZero d :: Γ) ⊢[PRAAx] radicandZero d := Prf.hyp0
    exact (zero_branch d _ hz).eqTrans (QuadraticRationalZeroProjection.positive_add x y
      ((zero_branch d _ hz).eqSymm.eqTrans hx.wk) ((zero_branch d _ hz).eqSymm.eqTrans hy.wk))

def signF : PR 2 := PTm.toPR (sign (var 0) (var 1))
def run (d x : PTm n) : PTm n := ap2 signF d x

theorem program_at (d x : PTm n) : Γ ⊢[PRAAx] run d x ≐ sign d x := by
  simpa [run,signF,ap2] using toPR_eq (Γ := Γ) (sign (var 0) (var 1) : PTm 2) ![d,x]

theorem actual_nonnegative_radical_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((run (var 0) (var 1) ≐ sign (var 0) (var 1)) ⋏
     ((isPositive (var 0) ⟶ run (var 0) (var 1) ≐ QuadraticRationalRadicand.sign (var 0) (var 1)) ⋏
      (radicandZero (var 0) ⟶ run (var 0) (var 1) ≐ QuadraticRationalZeroProjection.sign (var 1)))) :=
  closeUniv 2 (.andI (program_at _ _) (.andI
    (.impI ((program_at _ _).eqTrans (positive_branch _ _ Prf.hyp0)))
    (.impI ((program_at _ _).eqTrans (zero_branch _ _ Prf.hyp0)))))

theorem actual_nonnegative_radical_trichotomy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (nonnegative (var 0) ⟶ (less (var 0) (var 1) (var 2) ⋎
      (less (var 0) (var 2) (var 1) ⋎ equivalent (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (trichotomy _ _ _ Prf.hyp0))

theorem actual_nonnegative_radical_positive_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (nonnegative (var 0) ⟶ positive (var 0) (var 1) ⟶ positive (var 0) (var 2) ⟶
      positive (var 0) (multiply (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (positive_multiply _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem actual_nonnegative_radical_domain_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (nonnegative (var 0) ⟶ isZero (var 0) (multiply (var 0) (var 1) (var 2)) ⟶
      (isZero (var 0) (var 1) ⋎ isZero (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (zero_product_reflect _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_nonnegative_radical_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (nonnegative (var 0) ⟶ pointNonnegative (var 0) root ⋏ equivalent (var 0) (multiply (var 0) root root) (embed (var 0))) :=
  closeUniv 1 (.impI (root_nonnegative_and_square _ Prf.hyp0))

theorem actual_nonnegative_radical_unique_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (nonnegative (var 0) ⟶ pointNonnegative (var 0) (var 1) ⟶
      equivalent (var 0) (multiply (var 0) (var 1) (var 1)) (embed (var 0)) ⟶ equivalent (var 0) (var 1) root) :=
  closeUniv 2 (.impI (.impI (.impI (unique_actual_root _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem actual_nonnegative_radical_scalar_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (nonnegative (var 0) ⟶
      (Fm.iff (equivalent (var 0) (embed (var 1)) (embed (var 2))) (rationalEq (var 1) (var 2))) ⋏
      Fm.iff (less (var 0) (embed (var 1)) (embed (var 2))) (lt (left (var 1) (var 2)) (left (var 2) (var 1)))) :=
  closeUniv 3 (.impI (.andI (embedding_injective_iff _ _ _ Prf.hyp0) (embedding_order_iff _ _ _ Prf.hyp0)))

theorem actual_nonnegative_radical_multiplication_congruence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (nonnegative (var 0) ⟶ equivalent (var 0) (var 1) (var 2) ⟶ equivalent (var 0) (var 3) (var 4) ⟶
      equivalent (var 0) (multiply (var 0) (var 1) (var 3)) (multiply (var 0) (var 2) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (equivalent_multiply _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem actual_nonnegative_radical_positive_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (nonnegative (var 0) ⟶ positive (var 0) (var 3) ⟶ less (var 0) (var 1) (var 2) ⟶
      less (var 0) (multiply (var 0) (var 3) (var 1)) (multiply (var 0) (var 3) (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (less_multiply_positive _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Algebra.QuadraticRationalNonnegativeRadicand
