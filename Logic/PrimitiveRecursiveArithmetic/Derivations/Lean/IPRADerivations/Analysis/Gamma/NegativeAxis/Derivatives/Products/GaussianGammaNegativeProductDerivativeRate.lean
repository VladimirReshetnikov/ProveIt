import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.Products.GaussianGammaNegativeProductDerivativeCorrection
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.GaussianGammaDigammaTwoShiftFiniteRate

/-!
# Quantitative derivative of the actual negative Gamma shift product

On a negative interval, the positive fractional coordinates share a
denominator and lie in (0,1). A single prefix induction bounds the
original products, their diagonal first coefficients, and the difference
between the actual two-point fold and its diagonal. The cost depends on
the shift length and remains uniform in both fractional coordinates.
-/

set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeProductDerivativeRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaDigammaSeriesTerms (subtract_add_exchange)
open GaussianGammaDigammaTwoShiftFiniteRate (fraction_bound)
open GaussianGammaNegativeCriticalCorrection (bottomDen guard)
open GaussianGammaNegativeProductDerivative (dividedDifference factor_gap firstCoefficient prefixDifference)
open GaussianGammaNegativeProductDerivativeCorrection (negative_factor)
open GaussianGammaPoleFiniteFactors (difference differenceProduct difference_succ)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qadd qmul qzero)
open GaussianRationalMetric (bounded distanceBounded qsub qsub_canonical)
open GaussianRationalPowerDifference (bounded_sum_same distance_refl_zero product_difference)
open GaussianRationalReciprocal (bound_congr bounded_negative bounded_product qone_bounded)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qone)
open GaussianReciprocalHorner (qadd_zero_right)
open GaussianStirlingGammaLogarithm (arg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def productCap (j i : PTm n) : PTm n := pw (succ j) i
def coefficientCap (j i : PTm n) : PTm n := i*productCap j i
def prefixCost (j i : PTm n) : PTm n := i*i*productCap j i
def derivativeCost (j : PTm n) : PTm n := prefixCost j j+coefficientCap j j

@[simp] theorem subst_productCap {m : ℕ} (σ : Fin n → PTm m) (j i : PTm n) :
    Syn.subst σ (productCap j i) = productCap (Syn.subst σ j) (Syn.subst σ i) := by
  simp [productCap]
@[simp] theorem subst_coefficientCap {m : ℕ} (σ : Fin n → PTm m) (j i : PTm n) :
    Syn.subst σ (coefficientCap j i) = coefficientCap (Syn.subst σ j) (Syn.subst σ i) := by
  simp [coefficientCap]
@[simp] theorem subst_prefixCost {m : ℕ} (σ : Fin n → PTm m) (j i : PTm n) :
    Syn.subst σ (prefixCost j i) = prefixCost (Syn.subst σ j) (Syn.subst σ i) := by
  simp [prefixCost]
@[simp] theorem subst_derivativeCost {m : ℕ} (σ : Fin n → PTm m) (j : PTm n) :
    Syn.subst σ (derivativeCost j) = derivativeCost (Syn.subst σ j) := by
  simp [derivativeCost]

private theorem factor_bound (a b j i : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hi : Γ ⊢[PRAAx] le (succ i) j) :
    Γ ⊢[PRAAx] bounded (difference (arg a) b (succ i)) (succ j) one := by
  have hb := le_trans ha.andE₁ (le_of_lt ha.andE₂)
  have bound : Γ ⊢[PRAAx] le (bottomDen a b i) (succ j*b) :=
    le_trans (GaussianRationalMonicReconstruction.monus_le_left _ _)
      (mul_le_mul_right b (le_trans hi (le_succ_self j)))
  exact bound_congr (negative_factor a b i ha).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_negative _ _ _ (le_refl one) (fraction_bound _ _ _ hb bound))

private theorem append_error (x y f g T A B M K D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D)
    (hy : Γ ⊢[PRAAx] bounded y B one) (hf : Γ ⊢[PRAAx] bounded f M one)
    (hxy : Γ ⊢[PRAAx] distanceBounded x y K D) (hfg : Γ ⊢[PRAAx] distanceBounded f g A D) :
    Γ ⊢[PRAAx] distanceBounded (qadd (qmul x f) T) (qadd (qmul y g) T) (K*M+B*A) D := by
  have first := bound_congr (.eqRefl _) (.eqRefl _) ((mul_comm D one).eqTrans (one_mul D))
    (bounded_product (qsub x y) f K D M one hD (le_refl one) hxy hf)
  have second := bound_congr (.eqRefl _) (.eqRefl _) (one_mul D)
    (bounded_product y (qsub f g) B one A D (le_refl one) hD hy hfg)
  have remove : Γ ⊢[PRAAx] qsub (qadd (qmul x f) T) (qadd (qmul y g) T) ≐ qsub (qmul x f) (qmul y g) :=
    (subtract_add_exchange (qmul x f) (qmul y g) T T).eqSymm.eqTrans
      ((qadd_congr (.eqRefl _) (GaussianCoefficientNormOrder.qsub_self T)).eqTrans
        (qadd_zero_right _ (qsub_canonical _ _)))
  exact bound_congr (remove.eqTrans (product_difference x y f g)).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_sum_same _ _ _ _ D hD first second)

def prefixBounds (a c b j A D i : PTm n) : Fm PTm n :=
  bounded (differenceProduct (arg a) b i) (productCap j i) one ⋏
    (bounded (prefixDifference (arg a) (arg a) b i) (coefficientCap j i) one ⋏
      distanceBounded (prefixDifference (arg a) (arg c) b i) (prefixDifference (arg a) (arg a) b i)
        (prefixCost j i*A) D)

@[simp] theorem subst_prefixBounds {m : ℕ} (σ : Fin n → PTm m) (a c b j A D i : PTm n) :
    (prefixBounds a c b j A D i).subst σ =
      prefixBounds (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ j)
        (Syn.subst σ A) (Syn.subst σ D) (Syn.subst σ i) := by
  simp [prefixBounds,one]

private theorem bounds_zero (a c b j A D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] prefixBounds a c b j A D zero := by
  have ez : Γ ⊢[PRAAx] prefixDifference (arg a) (arg a) b zero ≐ qzero :=
    GaussianGammaNegativeProductDerivative.prefix_zero _ _ _
  have ec : Γ ⊢[PRAAx] prefixDifference (arg a) (arg c) b zero ≐ qzero :=
    GaussianGammaNegativeProductDerivative.prefix_zero _ _ _
  have norm : Γ ⊢[PRAAx] bounded (qzero : PTm n) zero one :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ (le_refl one)).iffMp
      (distance_refl_zero _ _ (le_refl one))
  exact .andI
    (bound_congr (GaussianGammaNegativeProductDerivative.difference_product_zero _ _).eqSymm
      (pw_zero _).eqSymm (.eqRefl _) qone_bounded)
    (.andI (bound_congr ez.eqSymm (by unfold coefficientCap; ipra_ring) (.eqRefl _) norm)
      (distance_congr ec.eqSymm ez.eqSymm (by unfold prefixCost; ipra_ring) (.eqRefl _) (distance_refl_zero _ _ hD)))

private theorem bounds_succ (a c b j A D i : PTm n)
    (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b) (hD : Γ ⊢[PRAAx] le one D)
    (hIn : Γ ⊢[PRAAx] distanceBounded (fraction c b) (fraction a b) A D)
    (hi : Γ ⊢[PRAAx] le (succ i) j) (ih : Γ ⊢[PRAAx] prefixBounds a c b j A D i) :
    Γ ⊢[PRAAx] prefixBounds a c b j A D (succ i) := by
  let x := arg a
  let y := arg c
  let H := succ j
  let P := differenceProduct x b i
  let X := prefixDifference x y b i
  let Y := prefixDifference x x b i
  let f := difference y b (succ i)
  let g := difference x b (succ i)
  have hH : Γ ⊢[PRAAx] le one H := zero_lt_succ j
  have hb := le_trans ha.andE₁ (le_of_lt ha.andE₂)
  have hf := factor_bound c b j i hc hi
  have hg := factor_bound a b j i ha hi
  have power : Γ ⊢[PRAAx] productCap j (succ i) ≐ productCap j i*H := pw_succ H i
  have product : Γ ⊢[PRAAx] bounded (differenceProduct x b (succ i)) (productCap j (succ i)) one :=
    bound_congr (difference_succ x b i).eqSymm power.eqSymm (one_mul one)
      (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) ih.andE₁ hg)
  have mainCoeff := bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
    (bounded_product Y g (coefficientCap j i) one H one (le_refl one) (le_refl one) ih.andE₂.andE₁ hg)
  have coeffBound := bounded_sum_same (qmul Y g) P _ _ one (le_refl one) mainCoeff ih.andE₁
  have coeffCmp : Γ ⊢[PRAAx] le ((coefficientCap j i*H+productCap j i)*one) (coefficientCap j (succ i)*one) := by
    have e := natEq power
    unfold coefficientCap
    ipra_le 𝔞 (productCap j i)*sl hH using
      linear_combination (𝔞 i+1)*e
  have coeff := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one) coeffCmp coeffBound
  have e : Γ ⊢[PRAAx] distanceBounded f g A D :=
    bound_congr (factor_gap x y b (succ i) hb).eqSymm (.eqRefl _) (.eqRefl _) hIn
  have raw := append_error X Y f g P A (coefficientCap j i) H (prefixCost j i*A) D
    hD ih.andE₂.andE₁ hf ih.andE₂.andE₂ e
  have errorCmp : Γ ⊢[PRAAx] le (((prefixCost j i*A)*H+coefficientCap j i*A)*D) ((prefixCost j (succ i)*A)*D) := by
    have e := natEq power
    unfold prefixCost coefficientCap
    ipra_le 𝔞 A*𝔞 D*𝔞 (productCap j i)*(2*𝔞 i*sl hH+𝔞 i+𝔞 H) using
      linear_combination (𝔞 i+1)^2*𝔞 A*𝔞 D*e
  exact .andI product (.andI
    (bound_congr (GaussianGammaNegativeProductDerivative.prefix_succ x x b i).eqSymm (.eqRefl _) (.eqRefl _) coeff)
    (distance_congr (GaussianGammaNegativeProductDerivative.prefix_succ x y b i).eqSymm
      (GaussianGammaNegativeProductDerivative.prefix_succ x x b i).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ hD hD errorCmp raw)))

theorem prefix_bounds (a c b j A D i : PTm n)
    (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b) (hD : Γ ⊢[PRAAx] le one D)
    (hIn : Γ ⊢[PRAAx] distanceBounded (fraction c b) (fraction a b) A D) (hi : Γ ⊢[PRAAx] le i j) :
    Γ ⊢[PRAAx] prefixBounds a c b j A D i := by
  let Δ := Γ.map Fm.shift
  let sh (v : PTm n) := Syn.shift v
  have ha' : Δ ⊢[PRAAx] guard (sh a) (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using ha.shift
  have hc' : Δ ⊢[PRAAx] guard (sh c) (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hc.shift
  have hD' : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hD.shift
  have hIn' : Δ ⊢[PRAAx] distanceBounded (fraction (sh c) (sh b)) (fraction (sh a) (sh b)) (sh A) (sh D) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hIn.shift
  have all : Γ ⊢[PRAAx] .all (le (var 0) (sh j) ⟶ prefixBounds (sh a) (sh c) (sh b) (sh j) (sh A) (sh D) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,⟨trivial,⟨trivial,trivial⟩⟩⟩ ?_ ?_
    · simp only [Fm.subst_imp,subst_le,subst_prefixBounds,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh]
      exact .impI (bounds_zero a c b j A D hD.wk)
    · simp only [Fm.subst_imp,subst_le,subst_prefixBounds,Syn.subst_var,Syn.repl_zero,subst_repl_shift,sh]
      refine .impI ?_
      exact bounds_succ (sh a) (sh c) (sh b) (sh j) (sh A) (sh D) (var 0)
        ha'.wk.wk hc'.wk.wk hD'.wk.wk hIn'.wk.wk Prf.hyp0
        (Prf.hyp1.impE (le_trans (le_succ_self _) Prf.hyp0))
  have gate : Γ ⊢[PRAAx] le i j ⟶ prefixBounds a c b j A D i := by
    simpa only [Fm.subst_imp,subst_le,subst_prefixBounds,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using all.allE i
  exact gate.impE hi

theorem derivative_error (a c b j A D : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b) (hD : Γ ⊢[PRAAx] le one D)
    (hIn : Γ ⊢[PRAAx] distanceBounded (fraction c b) (fraction a b) A D) :
    Γ ⊢[PRAAx] distanceBounded (dividedDifference (arg a) (arg c) b j) (firstCoefficient (arg a) b j)
      (derivativeCost j*A) D := by
  have h := prefix_bounds a c b j A D j ha hc hD hIn (le_refl j)
  have hb := le_trans ha.andE₁ (le_of_lt ha.andE₂)
  have endBound : Γ ⊢[PRAAx] bounded (fraction c b) one one :=
    fraction_bound c b one hb (le_congr (.eqRefl _) (one_mul b).eqSymm (le_of_lt hc.andE₂))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold derivativeCost; ipra_ring) (.eqRefl _)
    (append_error _ _ (fraction c b) (fraction a b) _ A (coefficientCap j j) one (prefixCost j j*A) D
      hD h.andE₂.andE₁ endBound h.andE₂.andE₂ hIn)

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeProductDerivativeRate
