import IPRADerivations.Analysis.Trigonometry.Arctangent.DivisionAngles.GaussianArctangentDivisionAngleRoots
import IPRADerivations.Analysis.Trigonometry.Arctangent.Inverse.GaussianArctangentInverseCorrectness
import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.NamedValues.GaussianArctangentNamedCayley
import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.Coordinates.GaussianArctangentCayleyTrig
import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.FiniteTelescopes.GaussianArctangentCayleyExponentialStep
import IPRADerivations.Analysis.Exponential.IntegerPowers.GaussianBoundedIntegerExponentialSample
import IPRADerivations.Analysis.Trigonometry.SineProducts.Roots.GaussianSineSquaredResidual

/-!
# Polynomial residual at the sampled divided-angle Cayley roots

At each precision, the exact rational Cayley sample and its conjugate
are inverse unit points. The original exponential at the scaled angle
identifies the common odd-power limit as a power of minus one. A sine
margin then bounds the actual polynomial residual at the sampled point.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentDivisionAngleResidual

open_ipra
open ComplexLogarithmRemainder (normSq normSq_eval eval_re_code eval_im_code)
open GaussianArctangentCayleyExponentialStep (conjugate_unit_bound)
open GaussianArctangentCayleyStep (conjugateValue)
open GaussianArctangentCayleyTrig (sinePoint sine_readback conjugate_inverse)
open GaussianArctangentCayleyValues (value denominator_positive unit_bound)
open GaussianArctangentDivisionAngles (source modulus odd_source)
open GaussianArctangentExponentialPeriod (minusOne minusOneCode negative_one_square)
open GaussianBoundedIntegerExponentialSample (sampleBudget)
open GaussianBoundedIntegerExponentialStages (expF expData point)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameReciprocal (lower lower_congr)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans diagonal_at cross_to_diagonal)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (canonical ofGaussian_canonical ofGaussian_represents evaluate qmul positive_product)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded)
open GaussianRationalPowerAlgebra (power_product qmul_commutative)
open GaussianRationalPowerDifference (bounded_power_integer)
open GaussianRationalReciprocal (power powerF qone qone_bounded power_canonical bounded_product bound_congr)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianSineSquaredPolynomial (coefficients)
open GaussianSineSquaredResidual (residual_bound_sharp)
open GaussianSineSquaredTrace (sineValue fromSine)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inverseF : PR 2 := GaussianArctangentNamedInverse.nameF GaussianArctangentDivisionAngles.nameF
def inverseData (k J z : PTm n) : PTm n :=
  GaussianArctangentNamedInverse.data (GaussianArctangentDivisionAngles.data k (modulus J) z)
def mesh (p k J z : PTm n) : PTm n :=
  GaussianArctangentNamedExtension.denominator inverseF (GaussianArctangentNamedCayley.queryPrecision p) (inverseData k J z)
def index (p k J z : PTm n) : PTm n :=
  GaussianArctangentNamedExtension.numerator inverseF (GaussianArctangentNamedCayley.queryPrecision p) (inverseData k J z)
def positiveSample (p k J z : PTm n) : PTm n := value (mesh p k J z) (index p k J z)
def negativeSample (p k J z : PTm n) : PTm n := conjugateValue (mesh p k J z) (index p k J z)
def sineSample (p k J z : PTm n) : PTm n := sinePoint (mesh p k J z) (index p k J z)
def rootSample (p k J z : PTm n) : PTm n := fromSine (sineSample p k J z)
def positiveBudget (J : PTm n) : PTm n := two+sampleBudget (modulus J) (modulus J) two one (num 5)

ipra_subst inverseData

ipra_subst mesh

ipra_subst index

ipra_subst sineSample

ipra_subst rootSample [fromSine]

theorem mesh_positive (p k J z : PTm n) : Γ ⊢[PRAAx] le one (mesh p k J z) :=
  GaussianArctangentNamedExtension.denominator_positive _ _ _

theorem index_le_mesh (p k J z : PTm n) : Γ ⊢[PRAAx] le (index p k J z) (mesh p k J z) :=
  GaussianArctangentNamedExtension.numerator_le _ _ _

theorem sample_inverse (p k J z : PTm n) :
    Γ ⊢[PRAAx] qmul (positiveSample p k J z) (negativeSample p k J z) ≐ qone :=
  (qmul_commutative _ _).eqTrans (conjugate_inverse _ _ (mesh_positive p k J z))

theorem sine_at_sample (p k J z : PTm n) :
    Γ ⊢[PRAAx] sineValue (positiveSample p k J z) (negativeSample p k J z) ≐ sineSample p k J z :=
  sine_readback _ _ (mesh_positive p k J z)

private theorem negative_one_bound : Γ ⊢[PRAAx] bounded (minusOne : PTm n) one one := by
  have e : Γ ⊢[PRAAx] normSq (minusOneCode : PTm n) ≐ one := by
    apply deriveNat
    rw [normSq_eval]
    simp only [minusOneCode,eval_re_code,eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat]
    ipra_simps
    ring
  exact bounded_of_cleared _ _ _ _ _ (le_refl one) (le_refl one) (ofGaussian_represents _ _ (le_refl one))
    (le_congr (e.eqSymm.eqTrans (by ipra_ring)) (by ipra_ring) (le_refl one))

private theorem unit_power (a e : PTm n) (h : Γ ⊢[PRAAx] bounded a one one) :
    Γ ⊢[PRAAx] bounded (power a e) one one :=
  bound_congr (.eqRefl _) (GaussianPolynomialPerturbation.one_power e) (.eqRefl _)
    (bounded_power_integer a one e h)

private theorem powered_inverses (a b e : PTm n) (h : Γ ⊢[PRAAx] qmul a b ≐ qone) :
    Γ ⊢[PRAAx] qmul (power a e) (power b e) ≐ qone :=
  (power_product a b e).eqSymm.eqTrans
    ((congrAp2 powerF (.eqRefl e) h).eqTrans (GaussianRationalRoundedPower.qone_power e))

private theorem sample_baseline (p k J z : PTm n) (h : Γ ⊢[PRAAx] source k (modulus J)) :
    Γ ⊢[PRAAx] distanceBounded (point GaussianArctangentDivisionAngles.nameF p (modulus J) one two
      (GaussianArctangentDivisionAngles.data k (modulus J) z)) (positiveSample p k J z) (num 5) (unit p) := by
  let f := GaussianArctangentDivisionAngles.nameF
  let m := modulus J
  let x := GaussianArctangentDivisionAngles.data k m z
  let F := GaussianArctangentInverseCorrectness.roundTripF f
  let y := inverseData k J z
  have hf := GaussianArctangentDivisionAngles.exponential_input k m z h
  have hRound := GaussianArctangentInverseCorrectness.imaginary_right_inverse f x z
    (GaussianArctangentDivisionAngles.interval_input k m z h)
    (GaussianArctangentDivisionAngles.imaginary_samples k m z h.andE₁)
  have hToRound := GaussianExponentialRadiusIndependence.independent_radii_proper f F two two x y hf
    (GaussianArctangentNamedCayley.exp_input inverseF y
      (GaussianArctangentNamedInverse.name_regular f x z (GaussianArctangentDivisionAngles.interval_input k m z h)))
    (cross_symm _ _ _ _ hRound)
  have both := cross_trans _ _ _ _ _ _ (GaussianBoundedIntegerExponentialSample.one_cross f m two x hf h.andE₁) hToRound
  have near := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ both)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) near (GaussianArctangentNamedCayley.raw_distance inverseF p y))

theorem positive_power_bound (p k J z : PTm n) (hk : Γ ⊢[PRAAx] le k J) :
    Γ ⊢[PRAAx] distanceBounded (power (positiveSample p k J z) (modulus J)) (power minusOne k)
      (positiveBudget J) (unit p) := by
  let f := GaussianArctangentDivisionAngles.nameF
  let m := modulus J
  let x := GaussianArctangentDivisionAngles.data k m z
  let a := positiveSample p k J z
  have hs := odd_source k J hk
  have hf := GaussianArctangentDivisionAngles.exponential_input k m z hs
  have compare := GaussianBoundedIntegerExponentialSample.prefix_error f p m m two x a one (num 5)
    hf (unit_bound _ _ (mesh_positive p k J z)) (sample_baseline p k J z hs) (le_refl _)
  have final := GaussianArctangentDivisionAngleRoots.multiple_exponential k m z hs
  have close := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ final)
  have close' := distance_congr (.eqRefl _) (constant_at p (power minusOne k)) (.eqRefl _) (.eqRefl _) close
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold positiveBudget; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p)
      (distance_symmetric _ _ _ _ (unit_positive p) compare) close')

private theorem reverse_power_bound (a b c H K : PTm n)
    (hk : Γ ⊢[PRAAx] le one K) (hb : Γ ⊢[PRAAx] bounded b one one)
    (hc : Γ ⊢[PRAAx] bounded c one one) (cb : Γ ⊢[PRAAx] canonical b) (cc : Γ ⊢[PRAAx] canonical c)
    (hab : Γ ⊢[PRAAx] qmul a b ≐ qone) (hcc : Γ ⊢[PRAAx] qmul c c ≐ qone)
    (h : Γ ⊢[PRAAx] distanceBounded a c H K) :
    Γ ⊢[PRAAx] distanceBounded c b H K := by
  let t := qmul c b
  have ht : Γ ⊢[PRAAx] bounded t one one :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _) hc hb)
  have left : Γ ⊢[PRAAx] qmul t a ≐ c :=
    (qmul_associative c b a).eqTrans
      ((qmul_congr (.eqRefl _) ((qmul_commutative _ _).eqTrans hab)).eqTrans (qmul_one_right _ cc))
  have right : Γ ⊢[PRAAx] qmul t c ≐ b :=
    (qmul_commutative t c).eqTrans ((qmul_associative c c b).eqSymm.eqTrans
      ((qmul_congr hcc (.eqRefl _)).eqTrans ((qmul_commutative _ _).eqTrans (qmul_one_right _ cb))))
  exact distance_congr left right (.eqRefl _) (.eqRefl _)
    (GaussianRationalRoundedPower.multiply_distance_bound t a c H K hk ht h)

theorem power_pair_bound (p k J z : PTm n) (hk : Γ ⊢[PRAAx] le k J) :
    Γ ⊢[PRAAx] distanceBounded (power (positiveSample p k J z) (modulus J))
      (power (negativeSample p k J z) (modulus J)) (two*positiveBudget J) (unit p) := by
  let a := positiveSample p k J z
  let b := negativeSample p k J z
  let m := modulus J
  let c := power minusOne k
  have near := positive_power_bound p k J z hk
  have hb := unit_power (Γ := Γ) b m (conjugate_unit_bound _ _ (mesh_positive p k J z))
  have hc := unit_power minusOne k (negative_one_bound (Γ := Γ))
  have back := reverse_power_bound (power a m) (power b m) c _ _ (unit_positive p) hb hc
    (power_canonical _ _) (power_canonical _ _) (powered_inverses a b m (sample_inverse p k J z))
    (powered_inverses minusOne minusOne k negative_one_square) near
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) near back)

theorem sampled_root_residual (p k J z D : PTm n) (hk : Γ ⊢[PRAAx] le k J)
    (hD : Γ ⊢[PRAAx] le one D) (hs : Γ ⊢[PRAAx] lower (sineSample p k J z) D) :
    Γ ⊢[PRAAx] bounded (evaluate (coefficients J) (rootSample p k J z)) (D*(two*positiveBudget J)) (two*unit p) := by
  have posDen := denominator_positive (Γ := Γ) (mesh p k J z) (index p k J z) (mesh_positive p k J z)
  have same := sine_at_sample (Γ := Γ) p k J z
  have hs' := lower_congr same.eqSymm (.eqRefl _) hs
  have eroot : Γ ⊢[PRAAx] fromSine (sineValue (positiveSample p k J z) (negativeSample p k J z)) ≐ rootSample p k J z :=
    qmul_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl _) (qmul_congr same same))
  exact bound_congr (GaussianRationalMonicReduction.evaluate_congr (.eqRefl _) eroot) (.eqRefl _) (.eqRefl _)
    (residual_bound_sharp _ _ J _ _ D (ofGaussian_canonical _ _ posDen) (ofGaussian_canonical _ _ posDen)
      (sample_inverse p k J z) (unit_positive p) hD hs' (power_pair_bound p k J z hk))

theorem actual_divided_angle_sample_residual_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le (var 1) (var 2) ⋏ le one (var 4)) ⟶ lower (sineSample (var 0) (var 1) (var 2) (var 3)) (var 4) ⟶
      bounded (evaluate (coefficients (var 2)) (rootSample (var 0) (var 1) (var 2) (var 3)))
        (var 4*(two*positiveBudget (var 2))) (two*unit (var 0))) :=
  closeUniv 5 (.impI (.impI (sampled_root_residual _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentDivisionAngleResidual
