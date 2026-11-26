import IPRADerivations.Analysis.GaussianBarnesCanonicalPrefactorInverse
import IPRADerivations.Analysis.GaussianBarnesCanonicalHeadCorrectionDerivative
import IPRADerivations.Analysis.GaussianGammaEulerRationalLogOrder
import IPRADerivations.Analysis.GaussianGammaDigammaTwoShiftNamedSize
import IPRADerivations.Analysis.GaussianNamedGammaHalfShift
import IPRADerivations.Analysis.GaussianRationalLinearProduct
import IPRADerivations.Analysis.GaussianRationalRoundedPower

/-!
# Exact linear algebra of the original Barnes prefactor exponent

The two rational entries of the original exponent are its argument and
its square. The executable prefactor exponent is additive and
homogeneous in these entries while retaining both named constants.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorExponentDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalPrefactor
  (linearF quadraticCoefficientF quadraticCoefficientData quadraticF polynomialF negativeHalf correctionF
    quadratic_coefficient_regular)
open GaussianBarnesCanonicalPrefactorInverse (exponentF exponentData)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaDigammaTwoShiftNamedSize (constant_product)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_commutative multiply_associative distributive)
open GaussianNamedGammaHalfShift (add_cross constant_sum)
open GaussianRationalHorner (ofGaussian qadd qmul qmul_canonical ofGaussian_canonical)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalReciprocal (qone)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "Q" => quadraticCoefficientF

def linearOf (a : PTm n) : PTm n := multiplyData C GaussianStirlingConstant.nameF a (GaussianStirlingConstant.nameData zero)
def quadraticOf (b : PTm n) : PTm n := multiplyData C Q b quadraticCoefficientData
def polynomialOf (a b : PTm n) : PTm n := addData a (quadraticOf b)
def correctionOf (a b : PTm n) : PTm n := multiplyData C polynomialF negativeHalf (polynomialOf a b)
def exponentOf (a b : PTm n) : PTm n := addData (linearOf a) (correctionOf a b)

def square (z B : PTm n) : PTm n := qmul (ofGaussian z B) (ofGaussian z B)
def squareStep (z h B : PTm n) : PTm n := qsub (square (add z h) B) (square z B)
def twicePoint (z B : PTm n) : PTm n := qadd (ofGaussian z B) (ofGaussian z B)
def linearSquare (z h B : PTm n) : PTm n := qmul (ofGaussian h B) (twicePoint z B)

def incrementData (z h B : PTm n) : PTm n := exponentOf (ofGaussian h B) (squareStep z h B)
def linearData (z h B : PTm n) : PTm n := exponentOf (ofGaussian h B) (linearSquare z h B)
def derivativeData (z B : PTm n) : PTm n := exponentOf qone (twicePoint z B)

@[simp] theorem subst_exponentOf {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (exponentOf a b) = exponentOf (Syn.subst σ a) (Syn.subst σ b) :=
  by simp [exponentOf,linearOf,correctionOf,polynomialOf,quadraticOf,quadraticCoefficientData,negativeHalf,one,two]
@[simp] theorem subst_square {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (square z B) = square (Syn.subst σ z) (Syn.subst σ B) := by simp [square]
@[simp] theorem subst_squareStep {m : ℕ} (σ : Fin n → PTm m) (z h B : PTm n) :
    Syn.subst σ (squareStep z h B) = squareStep (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) := by simp [squareStep]
@[simp] theorem subst_twicePoint {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (twicePoint z B) = twicePoint (Syn.subst σ z) (Syn.subst σ B) := by simp [twicePoint]
@[simp] theorem subst_linearSquare {m : ℕ} (σ : Fin n → PTm m) (z h B : PTm n) :
    Syn.subst σ (linearSquare z h B) = linearSquare (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) :=
  by simp [linearSquare]
@[simp] theorem subst_incrementData {m : ℕ} (σ : Fin n → PTm m) (z h B : PTm n) :
    Syn.subst σ (incrementData z h B) = incrementData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) :=
  by simp [incrementData]
@[simp] theorem subst_linearData {m : ℕ} (σ : Fin n → PTm m) (z h B : PTm n) :
    Syn.subst σ (linearData z h B) = linearData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) :=
  by simp [linearData]
@[simp] theorem subst_derivativeData {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (derivativeData z B) = derivativeData (Syn.subst σ z) (Syn.subst σ B) :=
  by simp [derivativeData]

private theorem linear_regular (a : PTm n) : Γ ⊢[PRAAx] pointCN linearF (linearOf a) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianStirlingConstant.name_regular zero)
private theorem quadratic_regular (b : PTm n) : Γ ⊢[PRAAx] pointCN quadraticF (quadraticOf b) :=
  multiply_fast _ _ _ _ (constant_regular _) quadratic_coefficient_regular
private theorem polynomial_regular (a b : PTm n) : Γ ⊢[PRAAx] pointCN polynomialF (polynomialOf a b) :=
  add_fast _ _ _ _ (constant_regular _) (quadratic_regular b)
private theorem correction_regular (a b : PTm n) : Γ ⊢[PRAAx] pointCN correctionF (correctionOf a b) :=
  multiply_fast _ _ _ _ (constant_regular _) (polynomial_regular a b)

theorem regular (a b : PTm n) : Γ ⊢[PRAAx] pointCN exponentF (exponentOf a b) :=
  add_fast _ _ _ _ (linear_regular a) (correction_regular a b)

private theorem add_fixed_right (f : PR 2) (x a b u : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (h : Γ ⊢[PRAAx] qadd a b ≐ u) :
    Γ ⊢[PRAAx] crossEquivalent (addF (multiplyF C f) (multiplyF C f)) (multiplyF C f)
      (addData (multiplyData C f a x) (multiplyData C f b x)) (multiplyData C f u x) := by
  let ca := constant_regular (Γ := Γ) a
  let cb := constant_regular (Γ := Γ) b
  let cu := constant_regular (Γ := Γ) u
  let ab := add_fast C C a b ca cb
  let M := multiplyF C f
  let W := multiplyF f C
  have move := add_cross M W M W (multiplyData C f a x) (multiplyData f C x a) (multiplyData C f b x) (multiplyData f C x b)
    (multiply_fast _ _ _ _ ca hf) (multiply_fast _ _ _ _ hf ca) (multiply_fast _ _ _ _ cb hf) (multiply_fast _ _ _ _ hf cb)
    (multiply_commutative C f a x ca hf) (multiply_commutative C f b x cb hf)
  have group := cross_symm _ _ _ _ (distributive f C C x a b hf ca cb)
  have result := multiply_cross f f (addF C C) C x x (addData a b) u hf hf ab cu (cross_refl _ _ hf) (constant_sum a b u h)
  exact cross_trans _ _ _ _ _ _ move (cross_trans _ _ _ _ _ _ group
    (cross_trans _ _ _ _ _ _ result (multiply_commutative f C x u hf cu)))

theorem add_entries (a b c d u v : PTm n) (e : Γ ⊢[PRAAx] qadd a c ≐ u) (f : Γ ⊢[PRAAx] qadd b d ≐ v) :
    Γ ⊢[PRAAx] crossEquivalent (addF exponentF exponentF) exponentF
      (addData (exponentOf a b) (exponentOf c d)) (exponentOf u v) := by
  let s : PTm n := GaussianStirlingConstant.nameData zero
  let q : PTm n := quadraticCoefficientData
  have ha := constant_regular (Γ := Γ) a
  have hc := constant_regular (Γ := Γ) c
  have hu := constant_regular (Γ := Γ) u
  have lin := add_fixed_right GaussianStirlingConstant.nameF s a c u (GaussianStirlingConstant.name_regular _) e
  have quad := add_fixed_right Q q b d v quadratic_coefficient_regular f
  have rearrange := GaussianGammaEulerRationalLogOrder.add_interleave C quadraticF C quadraticF a (quadraticOf b) c (quadraticOf d)
    ha (quadratic_regular b) hc (quadratic_regular d)
  have poly := add_cross (addF C C) C (addF quadraticF quadraticF) quadraticF (addData a c) u
    (addData (quadraticOf b) (quadraticOf d)) (quadraticOf v) (add_fast _ _ _ _ ha hc) hu
    (add_fast _ _ _ _ (quadratic_regular b) (quadratic_regular d)) (quadratic_regular v) (constant_sum a c u e) quad
  have neg := constant_regular (Γ := Γ) (negativeHalf : PTm n)
  have ca := polynomial_regular (Γ := Γ) a b
  have cc := polynomial_regular (Γ := Γ) c d
  have cp := add_fast _ _ _ _ ca cc
  have corr := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (distributive C polynomialF polynomialF negativeHalf
    (polynomialOf a b) (polynomialOf c d) neg ca cc))
    (multiply_cross C C (addF polynomialF polynomialF) polynomialF negativeHalf negativeHalf
      (addData (polynomialOf a b) (polynomialOf c d)) (polynomialOf u v) neg neg cp (polynomial_regular u v) (cross_refl _ _ neg)
      (cross_trans _ _ _ _ _ _ rearrange poly))
  have initial := GaussianGammaEulerRationalLogOrder.add_interleave (Γ := Γ) linearF correctionF linearF correctionF
    (linearOf a) (correctionOf a b) (linearOf c) (correctionOf c d)
    (linear_regular a) (correction_regular a b) (linear_regular c) (correction_regular c d)
  have final := add_cross (addF linearF linearF) linearF (addF correctionF correctionF) correctionF
    (addData (linearOf a) (linearOf c)) (linearOf u) (addData (correctionOf a b) (correctionOf c d)) (correctionOf u v)
    (add_fast _ _ _ _ (linear_regular a) (linear_regular c)) (linear_regular u)
    (add_fast _ _ _ _ (correction_regular a b) (correction_regular c d)) (correction_regular u v) lin corr
  exact cross_trans _ _ _ _ _ _ initial final

theorem increment_add (z h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (addF exponentF exponentF) exponentF
      (addData (exponentData z B) (incrementData z h B)) (exponentData (add z h) B) := by
  let a := ofGaussian z B
  let b := ofGaussian (add z h) B
  let c := ofGaussian h B
  have step := GaussianBarnesCanonicalHeadCorrectionDerivative.point_increment z h B hB
  have first := (qadd_congr (.eqRefl a) step.eqSymm).eqTrans
    (GaussianRationalLinearProduct.add_sub_right a b (ofGaussian_canonical _ _ hB))
  have second := GaussianRationalLinearProduct.add_sub_right (Γ := Γ) (square z B) (square (add z h) B) (qmul_canonical _ _)
  exact add_entries a (square z B) c (squareStep z h B) b (square (add z h) B) first second

private theorem scale_right (f : PR 2) (x s a u : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (h : Γ ⊢[PRAAx] qmul s a ≐ u) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF C (multiplyF C f)) (multiplyF C f)
      (multiplyData C (multiplyF C f) s (multiplyData C f a x)) (multiplyData C f u x) := by
  have hs := constant_regular (Γ := Γ) s
  have ha := constant_regular (Γ := Γ) a
  have hu := constant_regular (Γ := Γ) u
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative C C f s a x hs ha hf))
    (multiply_cross (multiplyF C C) C f f (multiplyData C C s a) u x x (multiply_fast _ _ _ _ hs ha) hu hf hf
      (constant_product s a u h) (cross_refl _ _ hf))

theorem scale_entries (s a b u v : PTm n) (e : Γ ⊢[PRAAx] qmul s a ≐ u) (f : Γ ⊢[PRAAx] qmul s b ≐ v) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF C exponentF) exponentF
      (multiplyData C exponentF s (exponentOf a b)) (exponentOf u v) := by
  let c : PTm n := negativeHalf
  have hs := constant_regular (Γ := Γ) s
  have hc := constant_regular (Γ := Γ) c
  have ha := constant_regular (Γ := Γ) a
  have hu := constant_regular (Γ := Γ) u
  have hq := quadratic_regular (Γ := Γ) b
  have hp := polynomial_regular (Γ := Γ) a b
  have hP := polynomial_regular (Γ := Γ) u v
  have linear := scale_right GaussianStirlingConstant.nameF _ s a u (GaussianStirlingConstant.name_regular zero) e
  have quadratic := scale_right Q _ s b v quadratic_coefficient_regular f
  have poly := cross_trans _ _ _ _ _ _ (distributive C C quadraticF s a (quadraticOf b) hs ha hq)
    (add_cross (multiplyF C C) C (multiplyF C quadraticF) quadraticF (multiplyData C C s a) u
      (multiplyData C quadraticF s (quadraticOf b)) (quadraticOf v)
      (multiply_fast _ _ _ _ hs ha) hu (multiply_fast _ _ _ _ hs hq) (quadratic_regular v) (constant_product s a u e) quadratic)
  have reassociate := cross_symm _ _ _ _ (multiply_associative C C polynomialF s c (polynomialOf a b) hs hc hp)
  have swap := multiply_cross (multiplyF C C) (multiplyF C C) polynomialF polynomialF (multiplyData C C s c)
    (multiplyData C C c s) (polynomialOf a b) (polynomialOf a b) (multiply_fast _ _ _ _ hs hc) (multiply_fast _ _ _ _ hc hs)
    hp hp (multiply_commutative C C s c hs hc) (cross_refl _ _ hp)
  have regroup := multiply_associative C C polynomialF c s (polynomialOf a b) hc hs hp
  have correction := cross_trans _ _ _ _ _ _ reassociate (cross_trans _ _ _ _ _ _ swap
    (cross_trans _ _ _ _ _ _ regroup (multiply_cross C C (multiplyF C polynomialF) polynomialF c c
      (multiplyData C polynomialF s (polynomialOf a b)) (polynomialOf u v) hc hc
      (multiply_fast _ _ _ _ hs hp) hP (cross_refl _ _ hc) poly)))
  have a₀ := linear_regular (Γ := Γ) a
  have c₀ := correction_regular (Γ := Γ) a b
  have split := distributive C linearF correctionF s (linearOf a) (correctionOf a b) hs a₀ c₀
  exact cross_trans _ _ _ _ _ _ split (add_cross (multiplyF C linearF) linearF (multiplyF C correctionF) correctionF
    (multiplyData C linearF s (linearOf a)) (linearOf u) (multiplyData C correctionF s (correctionOf a b)) (correctionOf u v)
    (multiply_fast _ _ _ _ hs a₀) (linear_regular u) (multiply_fast _ _ _ _ hs c₀) (correction_regular u v) linear correction)

theorem linear_factor (z h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF C exponentF) exponentF
      (multiplyData C exponentF (ofGaussian h B) (derivativeData z B)) (linearData z h B) :=
  scale_entries (ofGaussian h B) qone (twicePoint z B) (ofGaussian h B) (linearSquare z h B)
    (GaussianReciprocalHorner.qmul_one_right _ (ofGaussian_canonical _ _ hB)) (.eqRefl _)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorExponentDerivative
