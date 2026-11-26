import IPRADerivations.Analysis.RationalArithmetic.RationalGaussianRealPart
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalNaturalScale
import IPRADerivations.Analysis.Exponential.Polynomials.GaussianRationalPolynomialExponential

/-!
# Nonnegative real values of the actual Gaussian rational programs

The predicate is quantifier free: the imaginary value is zero and the
decoded real numerator is nonnegative. Closure is proved for the actual
normalized arithmetic, powers and finite sums, with no value or sign law
for a computed output as a premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveRealArithmetic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalSupMetric (numeratorOf denominatorOf)
open RationalGaussianEmbedding (embed axis native)
open GaussianRationalHorner (qzero qadd qmul canonical positive_product)
open GaussianRationalReciprocal (power)
open GaussianRationalNaturalScale (naturalPoint)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def sign (a : PTm n) : Fm PTm n := le (numeratorOf a).neg (numeratorOf a).pos
def positive (q : PTm n) : Fm PTm n := axis q ⋏ sign (fstT q)
def numerator (a : PTm n) : PTm n := monus (numeratorOf a).pos (numeratorOf a).neg

@[simp] theorem subst_sign {m : ℕ} (σ : Fin n → PTm m) (a : PTm n) :
    (sign a).subst σ = sign (Syn.subst σ a) := by simp [sign,numeratorOf,ZT.subst]
@[simp] theorem subst_positive {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    (positive q).subst σ = positive (Syn.subst σ q) := by simp [positive]

theorem sign_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) (ha : Γ ⊢[PRAAx] sign a) :
    Γ ⊢[PRAAx] sign b := by
  simpa using Prf.eqSubst (sign (var 0) : Fm PTm 1) (σ := ![a]) (σ' := ![b])
    (fun i => by fin_cases i; exact h) (by simpa using ha)

theorem positive_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) (hq : Γ ⊢[PRAAx] positive q) :
    Γ ⊢[PRAAx] positive r :=
  .andI (RationalGaussianEmbedding.axis_congr h hq.andE₁) (sign_congr (congrFst h) hq.andE₂)

theorem natural_representation (a : PTm n) (ha : Γ ⊢[PRAAx] sign a) : Γ ⊢[PRAAx]
    RationalArithmetic.represents a (ZT.ofNat (numerator a)) (denominatorOf a) := by
  have e := natEq (eq_add_of_le ha)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ,numerator]
  ipra_simps
  linear_combination -𝔞 (denominatorOf a)*e

theorem sign_add (a b : PTm n) (ha : Γ ⊢[PRAAx] sign a) (hb : Γ ⊢[PRAAx] sign b) :
    Γ ⊢[PRAAx] sign (RationalArithmetic.add a b) := by
  have r := RationalRepresentations.represents_add _ _ _ _ _ _ (natural_representation a ha) (natural_representation b hb)
  apply GaussianRationalL1.nonnegative_of_representation _
    (numerator a*denominatorOf b+numerator b*denominatorOf a) (denominatorOf a*denominatorOf b)
    (RationalArithmetic.product_denominator_positive a b)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) _ (.eqRefl _) r
  apply ZT.derive
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_add,Q.mk_mul,map_add,map_mul]

theorem sign_multiply (a b : PTm n) (ha : Γ ⊢[PRAAx] sign a) (hb : Γ ⊢[PRAAx] sign b) :
    Γ ⊢[PRAAx] sign (RationalArithmetic.multiply a b) := by
  have r := RationalRepresentations.represents_multiply _ _ _ _ _ _ (natural_representation a ha) (natural_representation b hb)
  apply GaussianRationalL1.nonnegative_of_representation _ (numerator a*numerator b) (denominatorOf a*denominatorOf b)
    (RationalArithmetic.product_denominator_positive a b)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) _ (.eqRefl _) r
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]

theorem positive_embed (a : PTm n) (ha : Γ ⊢[PRAAx] sign a) : Γ ⊢[PRAAx] positive (embed a) := by
  refine .andI (RationalGaussianEmbedding.embed_axis a) ?_
  apply sign_congr (fst_pair _ _).eqSymm
  exact GaussianRationalL1.nonnegative_of_representation _ _ _ (RationalArgmin.denominator_positive a)
    (RationalGaussianEmbedding.scalar_recode_represents _ _ _ (natural_representation a ha))

theorem positive_from_representation (q A D : PTm n) (hq : Γ ⊢[PRAAx] canonical q)
    (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] GaussianRationalHorner.represents q (native (ZT.ofNat A)) D) : Γ ⊢[PRAAx] positive q := by
  let r := RationalIntegerNormalization.normalize (ZT.ofNat A) D
  have hr := RationalIntegerNormalization.normalize_preserves_value (Γ := Γ) (ZT.ofNat A) D hD
  have e := GaussianRationalHorner.canonical_unique q (embed r) _ D hq
    (RationalGaussianEmbedding.embed_canonical r) hD h (RationalGaussianEmbedding.embed_from_representation r _ D hr)
  exact positive_congr e.eqSymm (positive_embed r (GaussianRationalL1.nonnegative_of_representation _ _ _ hD hr))

theorem positive_zero : Γ ⊢[PRAAx] positive (qzero : PTm n) := by
  apply positive_from_representation _ zero one GaussianRationalSyntheticDivision.qzero_canonical (le_refl one)
  exact GaussianRationalHorner.zero_represents one

theorem positive_one : Γ ⊢[PRAAx] positive (GaussianRationalSyntheticDivision.qone : PTm n) :=
  positive_from_representation _ one one GaussianRationalSyntheticDivision.qone_canonical (le_refl one)
    (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl one))

theorem positive_natural (R : PTm n) : Γ ⊢[PRAAx] positive (naturalPoint R) := by
  apply positive_from_representation _ R one
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)) (le_refl one)
  apply GaussianRationalHorner.represents_congr (.eqRefl _) _ (.eqRefl _) (GaussianRationalNaturalScale.natural_point_represents R)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,
      native,ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]

theorem positive_add (q r : PTm n) (hq : Γ ⊢[PRAAx] positive q) (hr : Γ ⊢[PRAAx] positive r) :
    Γ ⊢[PRAAx] positive (qadd q r) :=
  positive_congr (RationalGaussianEmbedding.axis_add_representation q r hq.andE₁ hr.andE₁).eqSymm
    (positive_embed _ (sign_add _ _ hq.andE₂ hr.andE₂))

theorem positive_multiply (q r : PTm n) (hq : Γ ⊢[PRAAx] positive q) (hr : Γ ⊢[PRAAx] positive r) :
    Γ ⊢[PRAAx] positive (qmul q r) :=
  positive_congr (RationalGaussianEmbedding.axis_multiply_representation q r hq.andE₁ hr.andE₁).eqSymm
    (positive_embed _ (sign_multiply _ _ hq.andE₂ hr.andE₂))

theorem positive_power (q k : PTm n) (hq : Γ ⊢[PRAAx] positive q) : Γ ⊢[PRAAx] positive (power q k) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] positive (Syn.shift q) := by simpa [Fm.shift,Syn.shift] using hq.shift
  have all : Γ ⊢[PRAAx] .all (positive (power (Syn.shift q) (var 0))) := by
    refine PRA.qfInd _ (by simp [positive,axis,RationalArgmin.rationalEq,sign,Fm.QF,le_QF]) ?_ ?_
    · simp only [subst_positive,GaussianRationalReciprocal.subst_power,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact positive_congr (GaussianRationalReciprocal.power_zero q).eqSymm positive_one
    · simp only [subst_positive,GaussianRationalReciprocal.subst_power,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact positive_congr (GaussianRationalReciprocal.power_succ _ _).eqSymm (positive_multiply _ _ Prf.hyp0 hs.wk)
  simpa only [subst_positive,GaussianRationalReciprocal.subst_power,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

def positiveTerms (t : PTm 2) (T x : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift T) ⟶ positive (inst2 t (var 0) (Syn.shift x)))
@[simp] theorem subst_positiveTerms {m : ℕ} (σ : Fin n → PTm m) (t : PTm 2) (T x : PTm n) :
    (positiveTerms t T x).subst σ = positiveTerms t (Syn.subst σ T) (Syn.subst σ x) := by
  simp [positiveTerms,Syn.subst_shift,Syn.shift_subst]

theorem positive_term (t : PTm 2) (T x i : PTm n) (h : Γ ⊢[PRAAx] positiveTerms t T x)
    (hi : Γ ⊢[PRAAx] lt i T) : Γ ⊢[PRAAx] positive (inst2 t i x) := by
  have e : Γ ⊢[PRAAx] lt i T ⟶ positive (inst2 t i x) := by
    simpa [positiveTerms] using h.allE i
  exact .impE e hi

def sumLaw (t : PTm 2) (T x j : PTm n) : Fm PTm n := le j T ⟶ positive (GaussianRationalFiniteSum.sum t j x)
@[simp] theorem subst_sumLaw {m : ℕ} (σ : Fin n → PTm m) (t : PTm 2) (T x j : PTm n) :
    (sumLaw t T x j).subst σ = sumLaw t (Syn.subst σ T) (Syn.subst σ x) (Syn.subst σ j) := by simp [sumLaw]

theorem positive_sum (t : PTm 2) (T x : PTm n) (h : Γ ⊢[PRAAx] positiveTerms t T x) :
    Γ ⊢[PRAAx] positive (GaussianRationalFiniteSum.sum t T x) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] positiveTerms t (Syn.shift T) (Syn.shift x) := by
    simpa only [Fm.shift,subst_positiveTerms,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (sumLaw t (Syn.shift T) (Syn.shift x) (var 0)) := by
    refine PRA.qfInd _ (by simp [sumLaw,positive,axis,RationalArgmin.rationalEq,sign,Fm.QF,le_QF]) ?_ ?_
    · simp only [subst_sumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (positive_congr (GaussianRationalFiniteSum.sum_zero t x).eqSymm positive_zero)
    · simp only [subst_sumLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI (positive_congr (GaussianRationalFiniteSum.sum_succ _ _ _).eqSymm (positive_add _ _
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)) ?_))
      exact positive_term _ _ _ _ hs.wk.wk Prf.hyp0
  have last : Γ ⊢[PRAAx] sumLaw t T x T := by
    simpa only [subst_sumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE T
  exact .impE last (le_refl _)

theorem positive_inverse_factorial (e : PTm n) : Γ ⊢[PRAAx]
    positive (GaussianRationalPolynomialExponential.inverseFactorial e) :=
  positive_from_representation _ one (Products.fact e)
    (GaussianRationalPolynomialExponential.inverse_factorial_canonical e)
    (GaussianRationalPolynomialExponential.factorial_positive e)
    (GaussianRationalPolynomialExponential.inverse_factorial_represents e)

theorem actual_positive_gaussian_arithmetic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (positive (var 0) ⟶ positive (var 1) ⟶
      positive (qadd (var 0) (var 1)) ⋏ positive (qmul (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (.andI (positive_add _ _ Prf.hyp1 Prf.hyp0) (positive_multiply _ _ Prf.hyp1 Prf.hyp0))))
theorem actual_positive_gaussian_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (positive (var 0) ⟶ positive (power (var 0) (var 1))) :=
  closeUniv 2 (.impI (positive_power _ _ Prf.hyp0))
theorem actual_positive_gaussian_sum_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (positiveTerms t (var 0) (var 1) ⟶ positive (GaussianRationalFiniteSum.sum t (var 0) (var 1))) :=
  closeUniv 2 (.impI (positive_sum t _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPositiveRealArithmetic
