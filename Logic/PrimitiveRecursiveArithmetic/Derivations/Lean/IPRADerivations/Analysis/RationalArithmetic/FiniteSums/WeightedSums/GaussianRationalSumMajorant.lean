import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianPositiveRealArithmetic
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRationalReciprocal
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalIdentities.RationalFiniteSum
import IPRADerivations.Analysis.Polynomials.Coefficients.NamedCoefficients.GaussianCoefficientNameBounds
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerDifference
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.DirectionSelection.GaussianDominantPairAlgebra

/-!
# Nonnegative rational majorants for actual Gaussian finite sums

A scalar majorant can vary from term to term. The actual finite
Gaussian sum is bounded by the actual scalar sum of those budgets.
The induction retains the normalized scalar code and its exact
numerator and denominator at every prefix.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalSumMajorant

open_ipra
open GaussianPositiveRealArithmetic (sign sign_add sign_multiply numerator natural_representation)
open GaussianRationalHorner (qadd qzero qmul positive_product scalar_congr)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bounded_sum bounded_product bound_congr)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalArithmetic (represents)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def majorized (u v : PTm n) : Fm PTm n := sign v ⋏ bounded u (numerator v) (denominatorOf v)

ipra_subst majorized [numerator, numeratorOf]

private theorem natural_numerator_value (r : PTm n) (h : Γ ⊢[PRAAx] sign r) :
    ZT.toZ Γ (numeratorOf r) = 𝔞(numerator r) := by
  have e := natEq (eq_add_of_le h)
  simp only [Q.mk_add,map_add] at e
  simp only [ZT.toZ,numerator]
  linear_combination e

private theorem natural_radius_equation (r A B : PTm n) (h : Γ ⊢[PRAAx] sign r)
    (hr : Γ ⊢[PRAAx] represents r (ZT.ofNat A) B) :
    Γ ⊢[PRAAx] A*denominatorOf r ≐ numerator r*B := by
  have value := ZT.toZ_eq hr
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,natural_numerator_value r h] at value
  apply deriveNat
  simp only [Q.mk_mul,map_mul]
  exact value

theorem from_representation (u r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] sign r)
    (hr : Γ ⊢[PRAAx] represents r (ZT.ofNat A) B) (hu : Γ ⊢[PRAAx] bounded u A B) :
    Γ ⊢[PRAAx] majorized u r :=
  .andI h (bounded_radius_mono _ _ _ _ _ hB (RationalArgmin.denominator_positive r)
    (le_congr (natural_radius_equation r A B h hr).eqSymm (.eqRefl _) (le_refl _)) hu)

/-- A bound by a natural ratio provides the corresponding nonnegative scalar majorant. -/
theorem fraction_majorized (u A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] bounded u A B) : Γ ⊢[PRAAx] majorized u (GaussianEuclideanDistanceName.fraction A B) := by
  have rep := GaussianEuclideanDistanceName.fraction_represents (Γ := Γ) A B hB
  exact from_representation _ _ _ _ hB (GaussianRationalL1.nonnegative_of_representation _ _ _ hB rep) rep h

theorem majorant_bound (u r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] majorized u r) (hr : Γ ⊢[PRAAx] bounded (RationalGaussianEmbedding.embed r) A B) :
    Γ ⊢[PRAAx] bounded u A B := by
  let D := denominatorOf r
  let M := numerator r
  have hD : Γ ⊢[PRAAx] le one D := RationalArgmin.denominator_positive r
  have rep := RationalGaussianEmbedding.embed_from_representation r (ZT.ofNat M) D (natural_representation r h.andE₁)
  have clear := GaussianRationalMetric.bounded_to_cleared _ _ _ _ _ hD hB rep hr
  have hn := GaussianDominantPairAlgebra.radius_numerator_norm (Γ := Γ) M
  have sq : Γ ⊢[PRAAx] le ((M*B)*(M*B)) ((A*D)*(A*D)) :=
    le_congr ((congrMul (.eqRefl _) hn).eqTrans (by ipra_ring)) (by ipra_ring) clear
  exact bounded_radius_mono _ _ _ _ _ hD hB (nat_sqrt_mono sq) h.andE₂

theorem majorized_congr {u v a b : PTm n} (hu : Γ ⊢[PRAAx] u ≐ v) (ha : Γ ⊢[PRAAx] a ≐ b)
    (h : Γ ⊢[PRAAx] majorized u a) : Γ ⊢[PRAAx] majorized v b := by
  simpa using Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (majorized (var 0) (var 1) : Fm PTm 2) ![u,a] ![v,b]
    (fun i => by fin_cases i; exact hu; exact ha) (by simpa using h)

theorem majorized_add (u v a b : PTm n) (ha : Γ ⊢[PRAAx] majorized u a) (hb : Γ ⊢[PRAAx] majorized v b) :
    Γ ⊢[PRAAx] majorized (qadd u v) (RationalArithmetic.add a b) := by
  let A := numerator a
  let B := numerator b
  let D := denominatorOf a
  let E := denominatorOf b
  have hd := RationalArgmin.denominator_positive (Γ := Γ) a
  have he := RationalArgmin.denominator_positive (Γ := Γ) b
  have r := RationalRepresentations.represents_add a b (ZT.ofNat A) (ZT.ofNat B) D E
    (natural_representation a ha.andE₁) (natural_representation b hb.andE₁)
  refine from_representation _ _ (A*E+B*D) (D*E) (positive_product D E hd he) (sign_add a b ha.andE₁ hb.andE₁) ?_
    (bounded_sum u v A D B E hd he ha.andE₂ hb.andE₂)
  refine scalar_congr (.eqRefl _) ?_ (.eqRefl _) r
  apply ZT.derive
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_add,Q.mk_mul,map_add,map_mul]

theorem majorized_multiply (u v a b : PTm n) (ha : Γ ⊢[PRAAx] majorized u a) (hb : Γ ⊢[PRAAx] majorized v b) :
    Γ ⊢[PRAAx] majorized (qmul u v) (RationalArithmetic.multiply a b) := by
  let A := numerator a
  let B := numerator b
  let D := denominatorOf a
  let E := denominatorOf b
  have hd := RationalArgmin.denominator_positive (Γ := Γ) a
  have he := RationalArgmin.denominator_positive (Γ := Γ) b
  have r := RationalRepresentations.represents_multiply a b (ZT.ofNat A) (ZT.ofNat B) D E
    (natural_representation a ha.andE₁) (natural_representation b hb.andE₁)
  refine from_representation _ _ (A*B) (D*E) (positive_product D E hd he) (sign_multiply a b ha.andE₁ hb.andE₁) ?_
    (bounded_product u v A D B E hd he ha.andE₂ hb.andE₂)
  refine scalar_congr (.eqRefl _) ?_ (.eqRefl _) r
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]

def termsMajorized (f g : PTm 2) (N x y : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ majorized (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift y)))
def prefixMajorized (f g : PTm 2) (N x y k : PTm n) : Fm PTm n := le k N ⟶
  majorized (GaussianRationalFiniteSum.sum f k x) (RationalFiniteSum.sum g k y)

ipra_subst termsMajorized [Syn.subst_shift, Syn.shift_subst]
ipra_subst prefixMajorized

private theorem zero_majorized : Γ ⊢[PRAAx]
    majorized (qzero : PTm n) (RationalIntegerNormalization.integerCode (ZT.natLit 0)) := by
  have eq : Γ ⊢[PRAAx] RationalGaussianEmbedding.scalarZero ≐ RationalIntegerNormalization.integerCode (ZT.natLit 0) := by
    apply RationalIntegerNormalization.normalize_integer _ _ _ (le_refl one)
    apply ZT.derive
    rw [ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_ofNat,ZT.toZ_natLit]
    ipra_simps
    norm_num
  apply majorized_congr (.eqRefl _) eq
  have r := RationalGaussianEmbedding.scalar_zero_represents (Γ := Γ) (one : PTm n)
  exact from_representation _ _ zero one (le_refl one)
    (GaussianRationalL1.nonnegative_of_representation _ _ _ (le_refl one) r) r
    ((GaussianReconstructionRoots.distance_zero_iff qzero zero one (le_refl one)).iffMp
      (GaussianRationalPowerDifference.distance_refl_zero qzero one (le_refl one)))

theorem term_majorized_at (f g : PTm 2) (N x y i : PTm n)
    (h : Γ ⊢[PRAAx] termsMajorized f g N x y) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] majorized (inst2 f i x) (inst2 g i y) := by
  have rule : Γ ⊢[PRAAx] lt i N ⟶ majorized (inst2 f i x) (inst2 g i y) := by simpa [termsMajorized] using h.allE i
  exact .impE rule hi

theorem sum_majorized (f g : PTm 2) (N x y : PTm n) (h : Γ ⊢[PRAAx] termsMajorized f g N x y) :
    Γ ⊢[PRAAx] majorized (GaussianRationalFiniteSum.sum f N x) (RationalFiniteSum.sum g N y) := by
  let invariant := majorized (GaussianRationalFiniteSum.sum f (var 0) (Syn.shift x))
    (RationalFiniteSum.sum g (var 0) (Syn.shift y))
  have shifted : Γ.map Fm.shift ⊢[PRAAx] termsMajorized f g (Syn.shift N) (Syn.shift x) (Syn.shift y) := by
    simpa [Fm.shift, Syn.shift] using h.shift
  have hQF : invariant.QF := by simp [invariant, majorized, sign, bounded, RationalArgmin.rationalLE, Fm.QF, le_QF]
  suffices result : Γ ⊢[PRAAx] invariant.subst (Syn.inst N) by simpa [invariant] using result
  refine qfIndUpTo N hQF ?_ ?_
  · simpa [invariant] using majorized_congr (GaussianRationalFiniteSum.sum_zero (Γ := Γ) f x).eqSymm
      (RationalFiniteSum.sum_zero g y).eqSymm zero_majorized
  · simp [invariant]
    refine .impI (majorized_congr (GaussianRationalFiniteSum.sum_succ f _ _).eqSymm
      (RationalFiniteSum.sum_succ g _ _).eqSymm ?_)
    exact majorized_add _ _ _ _ Prf.hyp1 (term_majorized_at f g _ _ _ _ shifted.wk.wk Prf.hyp0)

theorem actual_scalar_majorant_sum_closed (f g : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (termsMajorized f g (var 0) (var 1) (var 2) ⟶
      majorized (GaussianRationalFiniteSum.sum f (var 0) (var 1)) (RationalFiniteSum.sum g (var 0) (var 2))) :=
  closeUniv 3 (.impI (sum_majorized f g _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalSumMajorant
