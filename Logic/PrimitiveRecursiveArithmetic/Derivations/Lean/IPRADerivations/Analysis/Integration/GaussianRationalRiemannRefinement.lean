import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalBlockSums
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalNaturalScale
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalRoundedPower
import IPRADerivations.Analysis.Names.GaussianNameArithmetic
import IPRADerivations.Core.BlockSum

/-!
# Actual Gaussian left-sum refinement

Source Gamma finite calculus and compact Euler quadrature. All sums are
SAME original GaussianFiniteSum programs, with original sample codes and
independent data. The local cell-distance contract is the numerical input
that an original Lipschitz/evaluation theorem must discharge. No weighted
sum, refinement law or output regularity is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRiemannRefinement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qadd qmul ofGaussian positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRationalFiniteSum (sum sum_zero sum_succ sum_index_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalNaturalScale (natScale naturalPoint)
open ComplexLogarithmRemainder (oneCode scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def termsDistance (f g : PTm 2) (N x y A D : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ distanceBounded (inst2 f (var 0) (Syn.shift x))
    (inst2 g (var 0) (Syn.shift y)) (Syn.shift A) (Syn.shift D))
def sumLaw (f g : PTm 2) (N x y A D k : PTm n) : Fm PTm n := le k N ⟶
  distanceBounded (sum f k x) (sum g k y) (k*A) D
@[simp] theorem subst_termsDistance {l : ℕ} (σ : Fin n → PTm l) (f g : PTm 2) (N x y A D : PTm n) :
    (termsDistance f g N x y A D).subst σ = termsDistance f g (Syn.subst σ N) (Syn.subst σ x)
      (Syn.subst σ y) (Syn.subst σ A) (Syn.subst σ D) := by simp [termsDistance,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_sumLaw {l : ℕ} (σ : Fin n → PTm l) (f g : PTm 2) (N x y A D k : PTm n) :
    (sumLaw f g N x y A D k).subst σ = sumLaw f g (Syn.subst σ N) (Syn.subst σ x)
      (Syn.subst σ y) (Syn.subst σ A) (Syn.subst σ D) (Syn.subst σ k) := by simp [sumLaw]

theorem term_distance_at (f g : PTm 2) (N x y A D i : PTm n)
    (h : Γ ⊢[PRAAx] termsDistance f g N x y A D) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded (inst2 f i x) (inst2 g i y) A D := by
  have old := h.allE i
  simp only [termsDistance,Fm.subst_imp,subst_lt,GaussianRationalMetric.subst_distanceBounded,subst_inst2,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] at old
  exact .impE old hi

theorem sum_distance_step (f g : PTm 2) (N x y A D k : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] termsDistance f g N x y A D) (hk : Γ ⊢[PRAAx] lt k N)
    (ih : Γ ⊢[PRAAx] distanceBounded (sum f k x) (sum g k y) (k*A) D) : Γ ⊢[PRAAx]
    distanceBounded (sum f (succ k) x) (sum g (succ k) y) (succ k*A) D :=
  distance_congr (GaussianRationalFiniteSum.sum_succ f k x).eqSymm (GaussianRationalFiniteSum.sum_succ g k y).eqSymm
    (succ_mul k A).eqSymm (.eqRefl _) (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hD ih (term_distance_at f g N x y A D k h hk))

theorem sum_distance (f g : PTm 2) (N x y A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] termsDistance f g N x y A D) : Γ ⊢[PRAAx]
    distanceBounded (sum f N x) (sum g N y) (N*A) D := by
  have ds : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by simpa [Fm.shift,Syn.shift] using hD.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] termsDistance f g (Syn.shift N) (Syn.shift x) (Syn.shift y) (Syn.shift A) (Syn.shift D) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (sumLaw f g (Syn.shift N) (Syn.shift x) (Syn.shift y) (Syn.shift A) (Syn.shift D) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_sumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (distance_congr (GaussianRationalFiniteSum.sum_zero f x).eqSymm (GaussianRationalFiniteSum.sum_zero g y).eqSymm (zero_mul A).eqSymm (.eqRefl _)
        (GaussianRationalPowerDifference.distance_refl_zero qzero D hD.wk))
    · simp only [subst_sumLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact sum_distance_step f g _ _ _ _ _ _ ds.wk.wk hs.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have done : Γ ⊢[PRAAx] sumLaw f g N x y A D N := by
    simpa only [subst_sumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact .impE done (le_refl _)

def constantBody : PTm 2 := var 1
@[simp] theorem constant_entry (i q : PTm n) : inst2 constantBody i q = q := by simp [constantBody,inst2]
def constantLaw (q K : PTm n) : Fm PTm n := sum constantBody K q ≐ natScale K q
@[simp] theorem subst_constantLaw {l : ℕ} (σ : Fin n → PTm l) (q K : PTm n) :
    (constantLaw q K).subst σ = constantLaw (Syn.subst σ q) (Syn.subst σ K) := by simp [constantLaw]

theorem natural_scale_succ (K q : PTm n) : Γ ⊢[PRAAx] natScale (succ K) q ≐ qadd (natScale K q) q :=
  (GaussianRationalNaturalScale.natScale_congr (succ_eq_add_one K) (.eqRefl q)).eqTrans
    ((GaussianRationalNaturalScale.natScale_add K one q).eqTrans
      ((qadd_congr (.eqRefl _) (GaussianRationalNaturalScale.natScale_one q)).eqTrans
        (GaussianRationalSyntheticCoefficientValues.qadd_recode_right _ _)))

theorem constant_sum (q K : PTm n) : Γ ⊢[PRAAx] constantLaw q K := by
  have all : Γ ⊢[PRAAx] .all (constantLaw (Syn.shift q) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_constantLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (GaussianRationalFiniteSum.sum_zero _ _).eqTrans (GaussianRationalNaturalScale.natScale_zero q).eqSymm
    · simp only [subst_constantLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (GaussianRationalFiniteSum.sum_succ constantBody _ _).eqTrans ((qadd_congr Prf.hyp0 (.eqRefl _)).eqTrans (natural_scale_succ _ _).eqSymm)
  simpa only [subst_constantLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE K

def repeatBody (c : PTm 2) : PTm 2 := inst2 c (quo (var 0) (fstT (var 1))) (sndT (var 1))
@[simp] theorem repeat_entry (c : PTm 2) (i u : PTm n) :
    inst2 (repeatBody c) i u = inst2 c (quo i (fstT u)) (sndT u) := by
  simp only [repeatBody,inst2,Syn.subst_subst]
  congr 1
  funext k
  fin_cases k <;> simp

theorem repeat_body_at (c : PTm 2) (i R y : PTm n) : Γ ⊢[PRAAx]
    inst2 (repeatBody c) i (pairT R y) ≐ inst2 c (quo i R) y := by
  rw [repeat_entry]
  exact congrInst2 c (congrAp2 quoF (.eqRefl _) (fst_pair _ _)) (snd_pair _ _)

theorem repeated_block (c : PTm 2) (R k y : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    sum (offB (repeatBody c)) R (pairT (R*k) (pairT R y)) ≐ qmul (naturalPoint R) (inst2 c k y) := by
  apply Prf.eqTrans (GaussianRationalFiniteSum.sum_congr_bounded _ constantBody R _ (inst2 c k y) (.allI (.impI ?_)))
    ((constant_sum _ _).eqTrans (GaussianRationalNaturalScale.natScale_as_product _ _))
  have rs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hR.shift
  have positive := pos_of_eq_succ ((eq_add_of_le rs.wk).eqTrans (by ipra_ring : lt (var 0) (Syn.shift R)::Γ.map Fm.shift ⊢[PRAAx]
    one+LeanProofs.IPRA.PTm.monus (Syn.shift R) one ≐ succ (LeanProofs.IPRA.PTm.monus (Syn.shift R) one)))
  have div := (BlockSum.qr_block (i := Syn.shift k) positive Prf.hyp0).andE₁
  have off := GaussianRationalFiniteProduct.offset_at (Γ := lt (var 0) (Syn.shift R)::Γ.map Fm.shift) (repeatBody c) (Syn.shift R*Syn.shift k) (var 0) (pairT (Syn.shift R) (Syn.shift y))
  have rd := repeat_body_at (Γ := lt (var 0) (Syn.shift R)::Γ.map Fm.shift) c (Syn.shift R*Syn.shift k+var 0) (Syn.shift R) (Syn.shift y)
  have div' : lt (var 0) (Syn.shift R)::Γ.map Fm.shift ⊢[PRAAx]
      quo (Syn.shift R*Syn.shift k+var 0) (Syn.shift R) ≐ Syn.shift k :=
    (congrAp2 quoF (congrAdd (mul_comm _ _) (.eqRefl _)) (.eqRefl _)).eqTrans div
  simpa only [Syn.shift,subst_pairT,PTm.subst_mul,subst_inst2,constant_entry] using
    off.eqTrans (rd.eqTrans (congrInst2 c div' (.eqRefl _)))

def repeatLaw (c : PTm 2) (R N y : PTm n) : Fm PTm n :=
  sum (repeatBody c) (R*N) (pairT R y) ≐ qmul (naturalPoint R) (sum c N y)
@[simp] theorem subst_repeatLaw {l : ℕ} (σ : Fin n → PTm l) (c : PTm 2) (R N y : PTm n) :
    (repeatLaw c R N y).subst σ = repeatLaw c (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ y) := by simp [repeatLaw]

theorem repeated_step (c : PTm 2) (R N y : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (ih : Γ ⊢[PRAAx] repeatLaw c R N y) : Γ ⊢[PRAAx] repeatLaw c R (succ N) y := by
  have split := (sum_index_congr (repeatBody c) (by ipra_ring : Γ ⊢[PRAAx] R*succ N ≐ R*N+R) (.eqRefl (pairT R y))).eqTrans
    (GaussianRationalMatrixFiniteSums.sum_split (repeatBody c) (R*N) R (pairT R y))
  have parts := qadd_congr ih (repeated_block c R N y hR)
  have merge := (GaussianRationalCoefficientScaling.qmul_add (Γ := Γ) (naturalPoint R) (sum c N y) (inst2 c N y)).eqSymm.eqTrans
    (qmul_congr (.eqRefl _) (GaussianRationalFiniteSum.sum_succ c N y).eqSymm)
  exact split.eqTrans (parts.eqTrans merge)

theorem repeated_sum (c : PTm 2) (R N y : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx] repeatLaw c R N y := by
  have rs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hR.shift
  have all : Γ ⊢[PRAAx] .all (repeatLaw c (Syn.shift R) (var 0) (Syn.shift y)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_repeatLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (sum_index_congr (repeatBody c) (mul_zero R) (.eqRefl (pairT R y))).eqTrans ((GaussianRationalFiniteSum.sum_zero (repeatBody c) (pairT R y)).eqTrans
        ((qmul_congr (.eqRefl _) (GaussianRationalFiniteSum.sum_zero c y)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right (naturalPoint R))).eqSymm)
    · simp only [subst_repeatLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact repeated_step c _ _ _ rs.wk Prf.hyp0
  simpa only [subst_repeatLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

def cellDistances (f c : PTm 2) (N R x y A D : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift R*Syn.shift N) ⟶ distanceBounded (inst2 f (var 0) (Syn.shift x))
    (inst2 c (quo (var 0) (Syn.shift R)) (Syn.shift y)) (Syn.shift A) (Syn.shift D))
@[simp] theorem subst_cellDistances {l : ℕ} (σ : Fin n → PTm l) (f c : PTm 2) (N R x y A D : PTm n) :
    (cellDistances f c N R x y A D).subst σ = cellDistances f c (Syn.subst σ N) (Syn.subst σ R)
      (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ A) (Syn.subst σ D) := by simp [cellDistances,Syn.subst_shift,Syn.shift_subst]

theorem cell_distance_at (f c : PTm 2) (N R x y A D i : PTm n)
    (h : Γ ⊢[PRAAx] cellDistances f c N R x y A D) (hi : Γ ⊢[PRAAx] lt i (R*N)) : Γ ⊢[PRAAx]
    distanceBounded (inst2 f i x) (inst2 c (quo i R) y) A D := by
  have old := h.allE i
  simp only [cellDistances,Fm.subst_imp,subst_lt,GaussianRationalMetric.subst_distanceBounded,subst_inst2,subst_ap2,
    PTm.subst_mul,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] at old
  exact .impE old hi

theorem fine_coarse_sum (f c : PTm 2) (N R x y A D : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] cellDistances f c N R x y A D) : Γ ⊢[PRAAx]
    distanceBounded (sum f (R*N) x) (qmul (naturalPoint R) (sum c N y)) ((R*N)*A) D := by
  have terms : Γ ⊢[PRAAx] termsDistance f (repeatBody c) (R*N) x (pairT R y) A D := by
    refine .allI (.impI ?_)
    have hs : Γ.map Fm.shift ⊢[PRAAx] cellDistances f c (Syn.shift N) (Syn.shift R) (Syn.shift x) (Syn.shift y) (Syn.shift A) (Syn.shift D) := by
      simpa [Fm.shift,Syn.shift] using h.shift
    have old := cell_distance_at f c _ _ _ _ _ _ (var 0) hs.wk Prf.hyp0
    simpa only [Syn.shift,subst_pairT,PTm.subst_mul] using distance_congr (.eqRefl _)
      (repeat_body_at c (var 0) (Syn.shift R) (Syn.shift y)).eqSymm (.eqRefl _) (.eqRefl _) old
  exact distance_congr (.eqRefl _) (repeated_sum c R N y hR) (.eqRefl _) (.eqRefl _)
    (sum_distance f (repeatBody c) (R*N) x (pairT R y) A D hD terms)

def weight (C E N : PTm n) : PTm n := ofGaussian (scale C oneCode) (E*N)
def leftSum (f : PTm 2) (N x C E : PTm n) : PTm n := qmul (weight C E N) (sum f N x)
@[simp] theorem subst_weight {l : ℕ} (σ : Fin n → PTm l) (C E N : PTm n) :
    Syn.subst σ (weight C E N) = weight (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ N) := by simp [weight]
@[simp] theorem subst_leftSum {l : ℕ} (σ : Fin n → PTm l) (f : PTm 2) (N x C E : PTm n) :
    Syn.subst σ (leftSum f N x C E) = leftSum f (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ C) (Syn.subst σ E) := by simp [leftSum]

theorem weight_bound (C E N : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (weight C E N) C (E*N) := by
  have hp := positive_product (Γ := Γ) _ _ hE hN
  have eq : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (scale C oneCode) ≐ C*C :=
    (ComplexLogarithmRemainder.normSq_scale C oneCode).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hp hp (GaussianRationalHorner.ofGaussian_represents _ _ hp)
  exact le_congr (congrMul (.eqRefl _) eq).eqSymm (.eqRefl _) (le_of_eq_add (d := zero) (by ipra_ring))

theorem weight_repetition (C E R N : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hR : Γ ⊢[PRAAx] le one R) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    qmul (weight C E (R*N)) (naturalPoint R) ≐ weight C E N := by
  let T := (E*N)*R
  have en := positive_product (Γ := Γ) _ _ hE hN
  have ern := positive_product (Γ := Γ) _ _ hE (positive_product _ _ hR hN)
  have ht := positive_product (Γ := Γ) _ _ en hR
  have product := GaussianRationalHorner.qmul_represents (weight C E (R*N)) (naturalPoint R)
    (scale C oneCode) (scale R oneCode) (E*(R*N)) one ern (le_refl one)
    (GaussianRationalHorner.ofGaussian_represents _ _ ern) (GaussianRationalNaturalScale.natural_point_represents R)
  have target := GaussianRationalSyntheticDivision.rescale_to (weight C E N) (scale C oneCode) (E*N) R T
    (GaussianRationalHorner.ofGaussian_represents _ _ en) (.eqRefl _)
  apply GaussianRationalHorner.canonical_unique _ _ _ T (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ en) ht (hrv := target)
  apply GaussianRationalHorner.represents_congr (.eqRefl _) ?_ (by unfold T; ipra_ring) product
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ring

/-- Actual weighted Gaussian left sums on an interval of length C/E.
The original per-cell sample distance is the only function-value premise. -/
theorem refinement (f c : PTm 2) (N R x y C E A D : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le one R)
    (hE : Γ ⊢[PRAAx] le one E) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] cellDistances f c N R x y A D) : Γ ⊢[PRAAx]
    distanceBounded (leftSum f (R*N) x C E) (leftSum c N y C E) (C*A) (E*D) := by
  have fine := positive_product (Γ := Γ) _ _ hR hN
  have den := positive_product (Γ := Γ) _ _ hE fine
  have raw := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ den hD
    (weight_bound C E (R*N) hE fine) (fine_coarse_sum f c N R x y A D hR hD h)
  have scaled := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference (weight C E (R*N)) _ _).eqSymm (.eqRefl _) (.eqRefl _) raw
  have coarse := (GaussianReciprocalHorner.qmul_associative (Γ := Γ) (weight C E (R*N)) (naturalPoint R) (sum c N y)).eqSymm.eqTrans
    (qmul_congr (weight_repetition C E R N hE hR hN) (.eqRefl _))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ den hD) (positive_product _ _ hE hD)
    (le_of_eq_add (d := zero) (by ipra_ring))
    (distance_congr (.eqRefl _) coarse (.eqRefl _) (.eqRefl _) scaled)

def input (f c : PTm 2) (N R x y E A D : PTm n) : Fm PTm n :=
  le one N ⋏ (le one R ⋏ (le one E ⋏ (le one D ⋏ cellDistances f c N R x y A D)))
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (f c : PTm 2) (N R x y E A D : PTm n) :
    (input f c N R x y E A D).subst σ = input f c (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ x)
      (Syn.subst σ y) (Syn.subst σ E) (Syn.subst σ A) (Syn.subst σ D) := by simp [input]

/-- Actual fine/coarse left sums and their derived rational distance budget. -/
def output (f c : PTm 2) (N R x y C E A D : PTm n) : PTm n := pairT (leftSum f (R*N) x C E)
  (pairT (leftSum c N y C E) (pairT (C*A) (E*D)))
def outputF (f c : PTm 2) : PR 8 := PTm.toPR (output f c (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (f c : PTm 2) (N R x y C E A D : PTm n) : PTm n := PTm.app (outputF f c) ![N,R,x,y,C,E,A,D]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (f c : PTm 2) (N R x y C E A D : PTm n) :
    Syn.subst σ (output f c N R x y C E A D) = output f c (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ x)
      (Syn.subst σ y) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ A) (Syn.subst σ D) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (f c : PTm 2) (N R x y C E A D : PTm n) :
    Syn.subst σ (run f c N R x y C E A D) = run f c (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ x)
      (Syn.subst σ y) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ A) (Syn.subst σ D) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem program_at (f c : PTm 2) (N R x y C E A D : PTm n) : Γ ⊢[PRAAx]
    run f c N R x y C E A D ≐ output f c N R x y C E A D := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output f c (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![N,R,x,y,C,E,A,D]
theorem returned_fine (f c : PTm 2) (N R x y C E A D : PTm n) : Γ ⊢[PRAAx]
    fstT (run f c N R x y C E A D) ≐ leftSum f (R*N) x C E :=
  (congrFst (program_at f c N R x y C E A D)).eqTrans (fst_pair _ _)
theorem returned_coarse (f c : PTm 2) (N R x y C E A D : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run f c N R x y C E A D)) ≐ leftSum c N y C E :=
  ((congrFst (congrSnd (program_at f c N R x y C E A D))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_numerator (f c : PTm 2) (N R x y C E A D : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run f c N R x y C E A D))) ≐ C*A :=
  (((congrFst (congrSnd (congrSnd (program_at f c N R x y C E A D)))).eqTrans (congrFst (congrSnd (snd_pair _ _)))).eqTrans
    (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_denominator (f c : PTm 2) (N R x y C E A D : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run f c N R x y C E A D))) ≐ E*D :=
  (((congrSnd (congrSnd (congrSnd (program_at f c N R x y C E A D)))).eqTrans (congrSnd (congrSnd (snd_pair _ _)))).eqTrans
    (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_distance (f c : PTm 2) (N R x y C E A D : PTm n)
    (h : Γ ⊢[PRAAx] input f c N R x y E A D) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run f c N R x y C E A D)) (fstT (sndT (run f c N R x y C E A D)))
      (fstT (sndT (sndT (run f c N R x y C E A D)))) (sndT (sndT (sndT (run f c N R x y C E A D)))) :=
  distance_congr (returned_fine f c N R x y C E A D).eqSymm (returned_coarse f c N R x y C E A D).eqSymm
    (returned_numerator f c N R x y C E A D).eqSymm (returned_denominator f c N R x y C E A D).eqSymm
    (refinement f c N R x y C E A D h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂)

theorem actual_Gaussian_finite_sum_distance_closed (f g : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 4) ⋏ termsDistance f g (var 0) (var 1) (var 2) (var 3) (var 4)) ⟶
      distanceBounded (sum f (var 0) (var 1)) (sum g (var 0) (var 2)) (var 0*var 3) (var 4)) :=
  closeUniv 5 (.impI (sum_distance _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_raw_constant_Gaussian_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (sum constantBody (var 1) (var 0) ≐ natScale (var 1) (var 0)) := closeUniv 2 (constant_sum _ _)
theorem actual_quotient_coarse_reader_repetition_closed (c : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ repeatLaw c (var 0) (var 1) (var 2)) := closeUniv 3 (.impI (repeated_sum _ _ _ _ Prf.hyp0))
theorem actual_Gaussian_left_sum_refinement_closed (f c : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input f c (var 0) (var 1) (var 2) (var 3) (var 5) (var 6) (var 7) ⟶
      distanceBounded (leftSum f (var 1*var 0) (var 2) (var 4) (var 5)) (leftSum c (var 0) (var 3) (var 4) (var 5))
        (var 4*var 6) (var 5*var 7)) := closeUniv 8 (.impI (refinement _ _ _ _ _ _ _ _ _ _
          Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))
theorem actual_Gaussian_left_sum_refinement_program_closed (f c : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (run f c (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
      output f c (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) := closeUniv 8 (program_at _ _ _ _ _ _ _ _ _ _)
theorem actual_returned_Gaussian_left_sum_refinement_closed (f c : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input f c (var 0) (var 1) (var 2) (var 3) (var 5) (var 6) (var 7) ⟶
      distanceBounded (fstT (run f c (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
        (fstT (sndT (run f c (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))))
        (fstT (sndT (sndT (run f c (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))))
        (sndT (sndT (sndT (run f c (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))))) :=
  closeUniv 8 (.impI (returned_distance _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalRiemannRefinement
