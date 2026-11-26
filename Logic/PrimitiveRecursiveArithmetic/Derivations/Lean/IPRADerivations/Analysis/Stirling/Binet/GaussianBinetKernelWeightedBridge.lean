import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetKernelHalfExponential
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetKernelRationalTimeCleared
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetWeightedExponential
import IPRADerivations.Analysis.Names.GaussianNamedStrictOrderDifference
import IPRADerivations.Analysis.Names.GaussianNamedDifferenceAlgebra

/-!
# The nonsingular weighted Binet kernel at positive time

Multiplying the cleared hyperbolic identity by the actual negative
half-time exponential turns its two sides into expressions involving
the original full-time decay. The resulting scaled difference agrees
with the endpoint expression of the actual weighted exponential
quadrature. Only the explicit positive-time scalar is inverted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelWeightedBridge

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetKernelFrozenHyperbolic (fixedExpF fixedExpData fixed_exp_regular)
open GaussianBinetKernelHalfExponential (half_square half_mixed)
open GaussianBinetKernelImaginaryRatioPrefix (timeSquare)
open GaussianBinetWeightedExponentialAlgebra (integrationScale inverseScale leftCoefficient rightCoefficient)
open GaussianBoundedConstantProductName (constantF constant_at constant_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianEulerDecayQuadraturePrecision (observation_regular)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast addF addData add_fast multiplyModulus)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm)
open GaussianNameRingLaws
  (oneF one_fast one_at zeroF zero_fast zero_at negativeF negativeData add_negative multiply_one add_zero
    equivalent_of_envelope through_identity product_right_error multiply_sample_error)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (positive_product qadd qmul qzero canonical_unique represents_congr)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMetric (qsub qnegative qsub_represents qnegative_represents qsub_canonical qnegative_canonical)
open GaussianRationalSyntheticDivision (qone qadd_congr qsub_congr qmul_congr rescale_to)
open GaussianRootAlgebra (equal_of_values re_neg im_neg re_sub im_sub)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

abbrev dampingF : PR 2 := Diff constantF decayF
def dampingData (A B : PTm n) : PTm n := dd qone (decayData A B)

abbrev nameF : PR 2 := multiplyF dampingF GaussianBinetKernelCofinal.nameF
def data (A B : PTm n) : PTm n := multiplyData dampingF GaussianBinetKernelCofinal.nameF
  (dampingData A B) (GaussianBinetKernelRows.inputData A B)

@[simp] theorem subst_dampingData {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (dampingData A B) = dampingData (Syn.subst σ A) (Syn.subst σ B) := by
  simp [dampingData,decayData,GaussianGammaFiniteApproximantName.exponentialInputData]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (data A B) = data (Syn.subst σ A) (Syn.subst σ B) := by simp [data]

theorem damping_regular (A B : PTm n) : Γ ⊢[PRAAx] pointCN dampingF (dampingData A B) :=
  GaussianNamedDifference.name_regular _ _ _ _ (constant_regular _) (observation_regular A B)

theorem regular (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] pointCN nameF (data A B) :=
  multiply_fast _ _ _ _ (damping_regular A B) (GaussianBinetKernelCofinal.regular A B hB)

-- Keep each regularity proof with the original evaluator and its data.
private structure Named (Γ : List (Fm PTm n)) where
  prog : PR 2
  arg : PTm n
  reg : Γ ⊢[PRAAx] pointCN prog arg

private def cst (a : PTm n) : Named Γ := ⟨constantF, a, constant_regular a⟩
private def namedOne (a : PTm n) : Named Γ := ⟨oneF, a, one_fast a⟩
private def namedZero (a : PTm n) : Named Γ := ⟨zeroF, a, zero_fast a⟩
private def mul (a b : Named Γ) : Named Γ :=
  ⟨multiplyF a.prog b.prog, multiplyData a.prog b.prog a.arg b.arg, multiply_fast _ _ _ _ a.reg b.reg⟩
private def add (a b : Named Γ) : Named Γ :=
  ⟨addF a.prog b.prog, addData a.arg b.arg, add_fast _ _ _ _ a.reg b.reg⟩
private def sub (a b : Named Γ) : Named Γ :=
  ⟨Diff a.prog b.prog, dd a.arg b.arg, GaussianNamedDifference.name_regular _ _ _ _ a.reg b.reg⟩
private def same (a b : Named Γ) : Prop :=
  Γ ⊢[PRAAx] crossEquivalent a.prog b.prog a.arg b.arg

local infixl:70 " *ₙ " => mul
local infixl:65 " +ₙ " => add
local infixl:65 " -ₙ " => sub
local infix:50 " ≈ₙ " => same

private theorem refl (a : Named Γ) : a ≈ₙ a := cross_refl _ _ a.reg
private theorem symm {a b : Named Γ} (h : a ≈ₙ b) : b ≈ₙ a := cross_symm _ _ _ _ h
private theorem trans {a b c : Named Γ} (h : a ≈ₙ b) (h' : b ≈ₙ c) : a ≈ₙ c := cross_trans _ _ _ _ _ _ h h'
local instance : Trans (same (Γ := Γ)) (same (Γ := Γ)) (same (Γ := Γ)) := ⟨trans⟩

private theorem mul_congr {a b c d : Named Γ} (h : a ≈ₙ b) (h' : c ≈ₙ d) : a *ₙ c ≈ₙ b *ₙ d :=
  GaussianGammaAdjacentCutoff.multiply_cross _ _ _ _ _ _ _ _ a.reg b.reg c.reg d.reg h h'
private theorem add_congr {a b c d : Named Γ} (h : a ≈ₙ b) (h' : c ≈ₙ d) : a +ₙ c ≈ₙ b +ₙ d :=
  GaussianNamedGammaHalfShift.add_cross _ _ _ _ _ _ _ _ a.reg b.reg c.reg d.reg h h'
private theorem sub_congr {a b c d : Named Γ} (h : a ≈ₙ b) (h' : c ≈ₙ d) : a -ₙ c ≈ₙ b -ₙ d :=
  GaussianNamedDifferenceQuotientProperness.difference_proper _ _ _ _ _ _ _ _ a.reg b.reg c.reg d.reg h h'
private theorem mul_assoc (a b c : Named Γ) : (a *ₙ b) *ₙ c ≈ₙ a *ₙ (b *ₙ c) :=
  GaussianNameRingLaws.multiply_associative _ _ _ _ _ _ a.reg b.reg c.reg
private theorem mul_comm (a b : Named Γ) : a *ₙ b ≈ₙ b *ₙ a :=
  GaussianNameRingLaws.multiply_commutative _ _ _ _ a.reg b.reg
private theorem add_assoc (a b c : Named Γ) : (a +ₙ b) +ₙ c ≈ₙ a +ₙ (b +ₙ c) :=
  GaussianNameRingLaws.add_associative _ _ _ _ _ _ a.reg b.reg c.reg
private theorem add_comm (a b : Named Γ) : a +ₙ b ≈ₙ b +ₙ a :=
  GaussianNameRingLaws.add_commutative _ _ _ _ a.reg b.reg
private theorem mul_add (a b c : Named Γ) : a *ₙ (b +ₙ c) ≈ₙ (a *ₙ b) +ₙ (a *ₙ c) :=
  GaussianNameRingLaws.distributive _ _ _ _ _ _ a.reg b.reg c.reg
private theorem add_mul (a b c : Named Γ) : (a +ₙ b) *ₙ c ≈ₙ (a *ₙ c) +ₙ (b *ₙ c) :=
  GaussianNameRingLaws.right_distributive _ _ _ _ _ _ a.reg b.reg c.reg
private theorem mul_sub (a b c : Named Γ) : a *ₙ (b -ₙ c) ≈ₙ (a *ₙ b) -ₙ (a *ₙ c) :=
  GaussianNamedDifferenceAlgebra.distribute _ _ _ _ _ _ a.reg b.reg c.reg
private theorem add_sub (a b : Named Γ) : (a +ₙ b) -ₙ b ≈ₙ a :=
  GaussianNamedStrictOrderDifference.sum_sub_right _ _ _ _ a.reg b.reg

private theorem one_as_constant (a : PTm n) : (namedOne a : Named Γ) ≈ₙ cst qone := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (one_fast a) (constant_regular _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,cst,GaussianRationalSyntheticDivision.subst_qone] using
    (one_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift a)).eqTrans (constant_at (var 0) qone).eqSymm

private theorem zero_change (a b : PTm n) : (namedZero a : Named Γ) ≈ₙ namedZero b :=
  GaussianNameConjugation.equal_samples_cross _ _ _ _ (zero_fast a) (zero_fast b)
    (.allI ((zero_at (var 0) (Syn.shift a)).eqTrans (zero_at (var 0) (Syn.shift b)).eqSymm))

private theorem sub_add (a b : Named Γ) : (a -ₙ b) +ₙ b ≈ₙ a := by
  let nb : Named Γ := ⟨negativeF b.prog, negativeData b.arg, GaussianNameRingLaws.negative_fast _ _ b.reg⟩
  change (a +ₙ nb) +ₙ b ≈ₙ a
  have neg : nb +ₙ b ≈ₙ namedZero b.arg :=
    trans (add_comm nb b) (add_negative _ _ b.reg)
  exact trans (add_assoc a nb b) (trans
    (add_congr (refl a) (trans neg (zero_change b.arg a.arg))) (GaussianNameRingLaws.add_zero _ _ a.reg))

private theorem mul_one_const (a : Named Γ) : a *ₙ cst qone ≈ₙ a :=
  trans (mul_congr (refl a) (symm (one_as_constant a.arg))) (multiply_one _ _ a.reg)
private theorem one_const_mul (a : Named Γ) : cst qone *ₙ a ≈ₙ a :=
  trans (mul_comm _ _) (mul_one_const a)
private theorem constant_mul {a b c : PTm n} (h : Γ ⊢[PRAAx] qmul a b ≐ c) : cst (Γ := Γ) a *ₙ cst b ≈ₙ cst c :=
  cross_trans _ _ _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_product_cross a b)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ h)
private theorem constant_add {a b c : PTm n} (h : Γ ⊢[PRAAx] qadd a b ≐ c) : cst (Γ := Γ) a +ₙ cst b ≈ₙ cst c :=
  GaussianNamedGammaHalfShift.constant_sum _ _ _ h

private theorem multiply_exchange (a b c d : Named Γ) : (a *ₙ b) *ₙ (c *ₙ d) ≈ₙ (a *ₙ c) *ₙ (b *ₙ d) := by
  calc
    (a *ₙ b) *ₙ (c *ₙ d) ≈ₙ a *ₙ (b *ₙ (c *ₙ d)) := mul_assoc _ _ _
    _ ≈ₙ a *ₙ ((b *ₙ c) *ₙ d) := mul_congr (refl a) (symm (mul_assoc _ _ _))
    _ ≈ₙ a *ₙ ((c *ₙ b) *ₙ d) := mul_congr (refl a) (mul_congr (mul_comm _ _) (refl d))
    _ ≈ₙ a *ₙ (c *ₙ (b *ₙ d)) := mul_congr (refl a) (mul_assoc _ _ _)
    _ ≈ₙ (a *ₙ c) *ₙ (b *ₙ d) := symm (mul_assoc _ _ _)

private theorem negative_sub_flip (a b : PTm n) : Γ ⊢[PRAAx] qnegative (qsub a b) ≐ qsub b a := by
  let A := rawGaussian a
  let B := rawGaussian b
  let D := rawDen a*rawDen b
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (raw_den_positive a) (raw_den_positive b)
  have ha := rescale_to a A (rawDen a) (rawDen b) D (raw_represents (Γ := Γ) a) (.eqRefl _)
  have hb := rescale_to b B (rawDen b) (rawDen a) D (raw_represents (Γ := Γ) b) (by dsimp only [D]; ipra_ring)
  have hl := qnegative_represents _ _ _ (qsub_represents _ _ _ _ D hd ha hb)
  have hr := qsub_represents _ _ _ _ D hd hb ha
  apply canonical_unique _ _ _ _ (qnegative_canonical _) (qsub_canonical _ _) hd (hrv := hr)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := hl)
  apply equal_of_values <;> simp only [re_neg,im_neg,re_sub,im_sub] <;> ring

private theorem minus_one_swap (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) :
    cst (qnegative qone) *ₙ (⟨f,x,hf⟩ -ₙ ⟨g,y,hg⟩) ≈ₙ (⟨g,y,hg⟩ -ₙ ⟨f,x,hf⟩) := by
  let c : PTm n := qnegative qone
  let L := Diff f g
  let r := dd x y
  let C := multiplyModulus constantF L c r+one+U constantF c*num 6+num 6
  apply equivalent_of_envelope _ _ _ _ C
    (multiply_fast _ _ _ _ (constant_regular c) (GaussianNamedDifference.name_regular _ _ _ _ hf hg))
    (GaussianNamedDifference.name_regular _ _ _ _ hg hf)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let X := Syn.shift x
  let Y := Syn.shift y
  let q : PTm (n+1) := qnegative qone
  let R := dd X Y
  let F := ap2 f p X
  let G := ap2 g p Y
  have fx : Δ ⊢[PRAAx] pointCN f X := by simpa [Δ,X,Fm.shift,Syn.shift] using hf.shift
  have gy : Δ ⊢[PRAAx] pointCN g Y := by simpa [Δ,Y,Fm.shift,Syn.shift] using hg.shift
  have hD := GaussianNamedDifference.name_regular _ _ _ _ fx gy
  have hQ := constant_regular (Γ := Δ) q
  have hU := unit_positive (Γ := Δ) p
  have raw := multiply_sample_error constantF L q R p hQ hD
  have step := product_right_error (ap2 constantF p q) (ap2 L p R) (qsub F G) _ _ _ _ hU
    (GaussianNamedDifference.sample_error f g X Y p fx gy) (sample_bound _ _ p hD) (sample_bound _ _ p hQ)
  have left := distance_triangle_same _ _ _ _ _ _ hU raw step
  have flip : Δ ⊢[PRAAx] qmul (ap2 constantF p q) (qsub F G) ≐ qsub G F := by
    let d := qsub F G
    have unit : Δ ⊢[PRAAx] qmul qone d ≐ d :=
      (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
        (GaussianReciprocalHorner.qmul_one_right _ (qsub_canonical _ _))
    exact (qmul_congr (constant_at p q) (.eqRefl d)).eqTrans
      ((GaussianInverseBinomialRows.negative_product qone d).eqSymm.eqTrans
        ((GaussianInverseBinomialRows.negative_congr unit).eqTrans (negative_sub_flip F G)))
  have finish := through_identity _ _ _ _ _ _ _ hU left (GaussianNamedDifference.sample_error g f Y X p gy fx) flip
  simpa only [same,GaussianValueNormalizerExtensionality.rawDiagonal,c,L,r,C,Δ,p,X,Y,q,R,Syn.shift,
    GaussianNameArithmetic.subst_multiplyData,GaussianNamedDifference.subst_data,
    GaussianNameArithmetic.subst_multiplyModulus,GaussianNameBounds.subst_U,GaussianRationalMetric.subst_qnegative,
    GaussianRationalSyntheticDivision.subst_qone,PTm.subst_add,PTm.subst_mul,PTm.subst_num,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using finish

private theorem double_half (s : Bool) : Γ ⊢[PRAAx]
    qmul (fraction two one) (GaussianPiRationalScale.point s one two) ≐
      (if s then qnegative qone else qone) := by
  let q : PTm n := fraction two one
  have h2 := le_succ_self (Γ := Γ) one
  have pos : Γ ⊢[PRAAx] GaussianPiRationalScale.point false one two ≐ fraction one two :=
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point one two h2).eqSymm
  have e : Γ ⊢[PRAAx] qmul q (GaussianPiRationalScale.point false one two) ≐ qone :=
    (qmul_congr (.eqRefl q) pos).eqTrans (GaussianGammaHalfEulerSquare.inverse_fraction two one h2 (le_refl one))
  cases s
  · exact e
  · exact (qmul_congr (.eqRefl q) (GaussianPiRationalScale.point_negate false one two h2).eqSymm).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
        ((GaussianInverseBinomialRows.negative_product _ _).eqSymm.eqTrans
          (GaussianInverseBinomialRows.negative_congr ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans e))))

private def negExp (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Named Γ :=
  ⟨fixedExpF, fixedExpData true A B, fixed_exp_regular true A B hB⟩
private def posExp (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Named Γ :=
  ⟨fixedExpF, fixedExpData false A B, fixed_exp_regular false A B hB⟩
private def decay (A B : PTm n) : Named Γ := ⟨decayF,decayData A B,observation_regular A B⟩

private theorem half_cosh (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    (cst (fraction two one) *ₙ negExp A B hB) *ₙ
      (cst (GaussianPiRationalScale.point false one two) *ₙ (negExp A B hB +ₙ posExp A B hB))
      ≈ₙ cst qone +ₙ decay A B := by
  let a := negExp A B hB
  let b := posExp A B hB
  let d := decay (Γ := Γ) A B
  let e : PTm n := GaussianPiRationalScale.point false one two
  let c : Named Γ := cst (fraction two one)
  calc
    (c *ₙ a) *ₙ (cst e *ₙ (a +ₙ b)) ≈ₙ (c *ₙ cst e) *ₙ (a *ₙ (a +ₙ b)) := multiply_exchange _ _ _ _
    _ ≈ₙ cst qone *ₙ (a *ₙ (a +ₙ b)) := mul_congr (constant_mul (double_half false)) (refl _)
    _ ≈ₙ a *ₙ (a +ₙ b) := one_const_mul _
    _ ≈ₙ (a *ₙ a) +ₙ (a *ₙ b) := mul_add _ _ _
    _ ≈ₙ d +ₙ cst qone := add_congr (half_square A B hB) (half_mixed A B hB)
    _ ≈ₙ cst qone +ₙ d := add_comm _ _

private theorem half_sinh (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    (cst (fraction two one) *ₙ negExp A B hB) *ₙ
      (cst (GaussianPiRationalScale.point true one two) *ₙ (negExp A B hB -ₙ posExp A B hB))
      ≈ₙ cst qone -ₙ decay A B := by
  let a := negExp A B hB
  let b := posExp A B hB
  let d := decay (Γ := Γ) A B
  let e : PTm n := GaussianPiRationalScale.point true one two
  let c : Named Γ := cst (fraction two one)
  let neg : Named Γ := cst (qnegative qone)
  calc
    (c *ₙ a) *ₙ (cst e *ₙ (a -ₙ b)) ≈ₙ (c *ₙ cst e) *ₙ (a *ₙ (a -ₙ b)) := multiply_exchange _ _ _ _
    _ ≈ₙ neg *ₙ (a *ₙ (a -ₙ b)) := mul_congr (constant_mul (double_half true)) (refl _)
    _ ≈ₙ neg *ₙ ((a *ₙ a) -ₙ (a *ₙ b)) := mul_congr (refl _) (mul_sub _ _ _)
    _ ≈ₙ neg *ₙ (d -ₙ cst qone) := mul_congr (refl _) (sub_congr (half_square A B hB) (half_mixed A B hB))
    _ ≈ₙ cst qone -ₙ d := minus_one_swap _ _ _ _ d.reg (constant_regular _)

private theorem subtract_with_balance (a b x y l : Named Γ) (h : a +ₙ l ≈ₙ b) :
    (a +ₙ x) -ₙ (b -ₙ y) ≈ₙ (x +ₙ y) -ₙ l := by
  let u := (a +ₙ x) -ₙ (b -ₙ y)
  let v := (x +ₙ y) -ₙ l
  let c := b -ₙ y
  have p : (u +ₙ c) +ₙ y ≈ₙ a +ₙ (x +ₙ y) :=
    trans (add_congr (sub_add _ _) (refl _)) (add_assoc _ _ _)
  have q : (v +ₙ c) +ₙ y ≈ₙ a +ₙ (x +ₙ y) := by
    calc
      (v +ₙ c) +ₙ y ≈ₙ v +ₙ (c +ₙ y) := add_assoc _ _ _
      _ ≈ₙ v +ₙ b := add_congr (refl _) (sub_add _ _)
      _ ≈ₙ v +ₙ (a +ₙ l) := add_congr (refl _) (symm h)
      _ ≈ₙ v +ₙ (l +ₙ a) := add_congr (refl _) (add_comm _ _)
      _ ≈ₙ (v +ₙ l) +ₙ a := symm (add_assoc _ _ _)
      _ ≈ₙ (x +ₙ y) +ₙ a := add_congr (sub_add _ _) (refl _)
      _ ≈ₙ a +ₙ (x +ₙ y) := add_comm _ _
  have move := sub_congr (trans p (symm q)) (refl y)
  have cancel := trans (symm (add_sub (u +ₙ c) y)) (trans move (add_sub (v +ₙ c) y))
  exact trans (symm (add_sub u c)) (trans (sub_congr cancel (refl c)) (add_sub v c))

private theorem raw_left_coefficient (A B : PTm n) :
    Γ ⊢[PRAAx] qadd (fraction A one) (leftCoefficient A B) ≐ fraction (two*B) one :=
  GaussianRationalLinearProduct.add_sub_right _ _ (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one))

private theorem raw_right_coefficient (A B : PTm n) : Γ ⊢[PRAAx]
    qadd (fraction A one) (fraction (two*B) one) ≐ rightCoefficient A B := by
  let z := ComplexLogarithmRemainder.scale A ComplexLogarithmRemainder.oneCode
  let w := ComplexLogarithmRemainder.scale (two*B) ComplexLogarithmRemainder.oneCode
  have rep := GaussianRationalHorner.qadd_represents (Γ := Γ) _ _ z w one (le_refl one)
    (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl one)) (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl one))
  apply canonical_unique _ _ _ one (GaussianRationalHorner.qadd_canonical _ _) (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one))
    (le_refl one) (hrv := GaussianRationalHorner.ofGaussian_represents _ _ (le_refl one))
  apply represents_congr (.eqRefl _) _ (.eqRefl _) rep
  apply equal_of_values <;>
    simp only [z,w,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ipra_simps <;> ring

private theorem scale_half_time (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (fraction (two*B) one) (GaussianBinetKernelFrozenHyperbolic.halfTime false A B) ≐ fraction A one := by
  let E := two*B
  have he := positive_product _ _ (le_succ_self (Γ := Γ) one) hB
  have point : Γ ⊢[PRAAx] GaussianBinetKernelFrozenHyperbolic.halfTime false A B ≐ fraction A E :=
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point A E he).eqSymm
  have prod := GaussianEulerDampedTimeRate.fraction_product E one A E (le_refl one) he
  have step : Γ ⊢[PRAAx] fraction (E*A) (one*E) ≐ fraction (E*A) (E*one) :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (by ipra_ring)
  have again := GaussianEulerDecayFactorBounds.fraction_is_radius_point (Γ := Γ) (E*A) (E*one) (positive_product _ _ he (le_refl one))
  exact (qmul_congr (.eqRefl _) point).eqTrans (prod.eqTrans (step.eqTrans
    (again.eqTrans ((GaussianPiRationalScaleRepresentation.point_rescale false A one E (le_refl one) he).eqTrans
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point A one (le_refl one)).eqSymm))))

private theorem scale_time_square (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (fraction (two*B) one) (timeSquare A B) ≐ integrationScale A B := by
  have hb := positive_product _ _ hB hB
  have f := GaussianEulerDampedTimeRate.fraction_product (two*B) one (A*A) (B*B) (le_refl one) hb
  have e : Γ ⊢[PRAAx] fraction ((two*B)*(A*A)) (one*(B*B)) ≐ fraction (B*(two*A*A)) (B*B) :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (by ipra_ring)
  have r := GaussianPiRationalScaleRepresentation.point_rescale false (two*A*A) B B hB hB
  exact f.eqTrans (e.eqTrans ((GaussianEulerDecayFactorBounds.fraction_is_radius_point _ _ hb).eqTrans
    (r.eqTrans (GaussianEulerDecayFactorBounds.fraction_is_radius_point _ _ hB).eqSymm)))

private theorem endpoint_balance (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    cst (fraction (two*B) one) *ₙ
      ((cst (GaussianBinetKernelFrozenHyperbolic.halfTime false A B) *ₙ (cst qone +ₙ decay (Γ := Γ) A B))
       -ₙ (cst qone -ₙ decay A B))
    ≈ₙ (cst (rightCoefficient A B) *ₙ decay A B) -ₙ cst (leftCoefficient A B) := by
  let c : Named Γ := cst (fraction (two*B) one)
  let z := decay (Γ := Γ) A B
  let o : Named Γ := cst qone
  let H : Named Γ := cst (GaussianBinetKernelFrozenHyperbolic.halfTime false A B)
  let a : Named Γ := cst (fraction A one)
  let l : Named Γ := cst (leftCoefficient A B)
  have first : c *ₙ (H *ₙ (o +ₙ z)) ≈ₙ a +ₙ (a *ₙ z) := by
    calc
      c *ₙ (H *ₙ (o +ₙ z)) ≈ₙ (c *ₙ H) *ₙ (o +ₙ z) := symm (mul_assoc _ _ _)
      _ ≈ₙ a *ₙ (o +ₙ z) := mul_congr (constant_mul (scale_half_time A B hB)) (refl _)
      _ ≈ₙ (a *ₙ o) +ₙ (a *ₙ z) := mul_add _ _ _
      _ ≈ₙ a +ₙ (a *ₙ z) := add_congr (mul_one_const _) (refl _)
  have second : c *ₙ (o -ₙ z) ≈ₙ c -ₙ (c *ₙ z) :=
    trans (mul_sub _ _ _) (sub_congr (mul_one_const _) (refl _))
  calc
    c *ₙ ((H *ₙ (o +ₙ z)) -ₙ (o -ₙ z)) ≈ₙ (c *ₙ (H *ₙ (o +ₙ z))) -ₙ (c *ₙ (o -ₙ z)) := mul_sub _ _ _
    _ ≈ₙ (a +ₙ (a *ₙ z)) -ₙ (c -ₙ (c *ₙ z)) := sub_congr first second
    _ ≈ₙ ((a *ₙ z) +ₙ (c *ₙ z)) -ₙ l := subtract_with_balance _ _ _ _ _ (constant_add (raw_left_coefficient A B))
    _ ≈ₙ ((a +ₙ c) *ₙ z) -ₙ l := sub_congr (symm (add_mul _ _ _)) (refl _)
    _ ≈ₙ (cst (rightCoefficient A B) *ₙ z) -ₙ l :=
      sub_congr (mul_congr (constant_add (raw_right_coefficient A B)) (refl _)) (refl _)

theorem positive_time_bridge (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent nameF GaussianBinetWeightedExponential.nameF
      (data A B) (GaussianBinetWeightedExponential.data A B) := by
  let neg := negExp A B hB
  let pos := posExp A B hB
  let c : Named Γ := cst (fraction two one) *ₙ neg
  let s := cst (GaussianPiRationalScale.point true one two) *ₙ (neg -ₙ pos)
  let h := cst (GaussianPiRationalScale.point false one two) *ₙ (neg +ₙ pos)
  let H : Named Γ := cst (GaussianBinetKernelFrozenHyperbolic.halfTime false A B)
  let o : Named Γ := cst qone
  let z := decay (Γ := Γ) A B
  let e := o -ₙ z
  let u : Named Γ := namedOne (GaussianBinetKernelRows.inputData A B)
  let k : Named Γ := ⟨GaussianBinetKernelCofinal.nameF,GaussianBinetKernelRows.inputData A B,
    GaussianBinetKernelCofinal.regular A B hB⟩
  let t : Named Γ := cst (timeSquare A B)
  let w := e *ₙ k
  let v := ((H *ₙ (o +ₙ z)) -ₙ e)
  let b : Named Γ := cst (fraction (two*B) one)
  let m : Named Γ := cst (integrationScale A B)
  let i : Named Γ := cst (inverseScale A B)
  let Q := (cst (rightCoefficient A B) *ₙ z) -ₙ cst (leftCoefficient A B)
  have hNative : (H *ₙ h) ≈ₙ s *ₙ (u +ₙ (t *ₙ k)) :=
    GaussianBinetKernelRationalTimeCleared.cleared_kernel A B hB
  have cleared : H *ₙ (o +ₙ z) ≈ₙ e *ₙ (u +ₙ (t *ₙ k)) := by
    calc
      H *ₙ (o +ₙ z) ≈ₙ H *ₙ (c *ₙ h) := mul_congr (refl _) (symm (half_cosh A B hB))
      _ ≈ₙ (H *ₙ c) *ₙ h := symm (mul_assoc _ _ _)
      _ ≈ₙ (c *ₙ H) *ₙ h := mul_congr (mul_comm _ _) (refl _)
      _ ≈ₙ c *ₙ (H *ₙ h) := mul_assoc _ _ _
      _ ≈ₙ c *ₙ (s *ₙ (u +ₙ (t *ₙ k))) := mul_congr (refl _) hNative
      _ ≈ₙ (c *ₙ s) *ₙ (u +ₙ (t *ₙ k)) := symm (mul_assoc _ _ _)
      _ ≈ₙ e *ₙ (u +ₙ (t *ₙ k)) := mul_congr (half_sinh A B hB) (refl _)
  have norm : v ≈ₙ t *ₙ w := by
    calc
      v ≈ₙ (e *ₙ (u +ₙ (t *ₙ k))) -ₙ e := sub_congr cleared (refl _)
      _ ≈ₙ ((e *ₙ u) +ₙ (e *ₙ (t *ₙ k))) -ₙ e := sub_congr (mul_add _ _ _) (refl _)
      _ ≈ₙ (e +ₙ (e *ₙ (t *ₙ k))) -ₙ e :=
        sub_congr (add_congr (trans (mul_congr (refl _) (one_as_constant _)) (mul_one_const _)) (refl _)) (refl _)
      _ ≈ₙ ((e *ₙ (t *ₙ k)) +ₙ e) -ₙ e := sub_congr (add_comm _ _) (refl _)
      _ ≈ₙ e *ₙ (t *ₙ k) := add_sub _ _
      _ ≈ₙ (e *ₙ t) *ₙ k := symm (mul_assoc _ _ _)
      _ ≈ₙ (t *ₙ e) *ₙ k := mul_congr (mul_comm _ _) (refl _)
      _ ≈ₙ t *ₙ w := mul_assoc _ _ _
  have scaled : m *ₙ w ≈ₙ Q := by
    calc
      m *ₙ w ≈ₙ (b *ₙ t) *ₙ w := mul_congr (symm (constant_mul (scale_time_square A B hB))) (refl _)
      _ ≈ₙ b *ₙ (t *ₙ w) := mul_assoc _ _ _
      _ ≈ₙ b *ₙ v := mul_congr (refl _) (symm norm)
      _ ≈ₙ Q := endpoint_balance A B hB
  have result : w ≈ₙ i *ₙ Q := by
    calc
      w ≈ₙ cst qone *ₙ w := symm (one_const_mul _)
      _ ≈ₙ (i *ₙ m) *ₙ w :=
        mul_congr (symm (constant_mul (GaussianBinetWeightedExponentialAlgebra.inverse_product A B hA hB))) (refl _)
      _ ≈ₙ i *ₙ (m *ₙ w) := mul_assoc _ _ _
      _ ≈ₙ i *ₙ Q := mul_congr (refl _) scaled
  exact cross_trans _ _ _ _ _ _ result (cross_symm _ _ _ _ (GaussianBinetWeightedExponential.equivalent A B (.andI hA hB)))

theorem actual_Binet_weighted_kernel_positive_time_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ le one (var 1) ⟶
      crossEquivalent nameF GaussianBinetWeightedExponential.nameF
        (data (var 0) (var 1)) (GaussianBinetWeightedExponential.data (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (positive_time_bridge _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetKernelWeightedBridge
