import IPRADerivations.Analysis.Polynomials.Products.Powers.GaussianRationalPolynomialPowers
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerNonzero
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerAlgebra
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums
import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalScalarPowerGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Representation.RationalPolynomialGaussianEmbedding
import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianNormFiberDivisibility

/-!
# The collapse polynomial of the original rational section equation

For the source line equation P(x)+a*y=0 and curve y^r=f(x), construct
the stored polynomial H=(-P)^r-a^r*f in the exact Gaussian-rational
extension of the original rational coefficient codes. When r*s<m
and a is nonzero, the actual leading coefficient of H is the nonzero
coefficient -a^r*f_m. The curve and line equations imply H(x)=0 by
finite coefficient and evaluation identities.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalSectionCollapse

open_ipra
open RationalGaussianEmbedding (embed scalarZero embed_canonical embed_equal rational_equal_of_embed negative_congr)
open RationalPolynomialGaussianEmbedding (coefficients coefficients_length coefficient_lookup)
open GaussianRationalHorner (canonical evaluate qadd qmul qzero)
open GaussianRationalMetric (qnegative qsub qnegative_canonical)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr qzero_add qmul_zero_right)
open GaussianRationalMatrixFiniteSums (minusOne negative_as_minusOne)
open GaussianRationalCoefficientScaling (scaled scaled_length scaled_lookup evaluation_linearity)
open GaussianRationalPolynomialBuffers (leftPad pad_length pad_leading pad_evaluation added added_length added_lookup added_evaluation)
open GaussianRationalMonicReduction (evaluate_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def negativePolynomial (C : PTm n) : PTm n := scaled C minusOne

def firstSummand (P s r m : PTm n) : PTm n :=
  leftPad (GaussianRationalPolynomialPowers.power (negativePolynomial (coefficients P (succ s))) s r)
    (monus m (r*s))

def factor (a r : PTm n) : PTm n := GaussianRationalReciprocal.power (embed a) r

def secondSummand (f a r m : PTm n) : PTm n :=
  negativePolynomial (scaled (coefficients f (succ m)) (factor a r))

def polynomial (P f a s r m : PTm n) : PTm n :=
  added (firstSummand P s r m) (secondSummand f a r m) (succ m)

def nonzero (x : PTm n) : Fm PTm n := neg (RationalArgmin.rationalEq x scalarZero)

def line (P a x y : PTm n) : Fm PTm n :=
  RationalArgmin.rationalEq
    (RationalArithmetic.add (RationalPolynomialGaussianEmbedding.evaluate P x) (RationalArithmetic.multiply a y))
    scalarZero

def curve (f r x y : PTm n) : Fm PTm n :=
  RationalArgmin.rationalEq (RationalScalarPowerGaussianEmbedding.power y r)
    (RationalPolynomialGaussianEmbedding.evaluate f x)

ipra_subst negativePolynomial
ipra_subst firstSummand
ipra_subst factor
ipra_subst secondSummand
ipra_subst polynomial
ipra_subst nonzero
ipra_subst line
ipra_subst curve

theorem negative_evaluation (C z : PTm n) : Γ ⊢[PRAAx]
    evaluate (negativePolynomial C) z ≐ qnegative (evaluate C z) :=
  (evaluation_linearity _ _ _).eqTrans (negative_as_minusOne _).eqSymm

theorem first_length (P s r m : PTm n) (h : Γ ⊢[PRAAx] le (r*s) m) :
    Γ ⊢[PRAAx] length (firstSummand P s r m) ≐ succ m := by
  have hLength := GaussianRationalPolynomialPowers.power_length (Γ := Γ) (negativePolynomial (coefficients P (succ s))) s r
  refine (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) hLength).eqTrans ?_)
  exact (add_succ _ _).eqTrans (congrSucc ((add_comm _ _).eqTrans (eq_add_of_le h).eqSymm))

theorem second_length (f a r m : PTm n) : Γ ⊢[PRAAx] length (secondSummand f a r m) ≐ succ m :=
  (scaled_length _ _).eqTrans ((scaled_length _ _).eqTrans (coefficients_length _ _))

theorem polynomial_length (P f a s r m : PTm n) : Γ ⊢[PRAAx] length (polynomial P f a s r m) ≐ succ m :=
  added_length _ _ _

theorem first_leading_zero (P s r m : PTm n) (h : Γ ⊢[PRAAx] lt (r*s) m) :
    Γ ⊢[PRAAx] entry (firstSummand P s r m) zero ≐ qzero := by
  apply pad_leading
  have split : Γ ⊢[PRAAx] m ≐ r*s+succ (monus m (succ (r*s))) :=
    (eq_add_of_le h).eqTrans (by ipra_ring)
  have gap := (congrMonus split (.eqRefl (r*s))).eqTrans (add_monus' (succ (monus m (succ (r*s)))) (r*s))
  exact le_congr (.eqRefl _) gap.eqSymm (zero_lt_succ _)

private theorem evaluate_input (C d x : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ d) : Γ ⊢[PRAAx]
    evaluate (coefficients C (succ d)) (embed x) ≐ embed (RationalPolynomialGaussianEmbedding.evaluate C x) :=
  (evaluate_congr ((RationalPolynomialGaussianEmbedding.coefficients_at C (succ d)).eqSymm.eqTrans
    ((congrAp2 RationalPolynomialGaussianEmbedding.coefficientsF (.eqRefl _) hC.eqSymm).eqTrans
      (RationalPolynomialGaussianEmbedding.coefficients_at C (length C)))) (.eqRefl _)).eqTrans
    (RationalPolynomialGaussianEmbedding.evaluation_conjugacy C x).eqSymm

private theorem scalar_power_congr {x y : PTm n} (r : PTm n) (h : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] GaussianRationalReciprocal.power x r ≐ GaussianRationalReciprocal.power y r := by
  ipra_congr (GaussianRationalReciprocal.power (var 0) (var 1) : PTm 2) with [h, .eqRefl r]

theorem first_evaluation (P s r m x : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ s) : Γ ⊢[PRAAx]
    evaluate (firstSummand P s r m) (embed x) ≐
      GaussianRationalReciprocal.power (qnegative (embed (RationalPolynomialGaussianEmbedding.evaluate P x))) r := by
  have hLen : Γ ⊢[PRAAx] length (negativePolynomial (coefficients P (succ s))) ≐ succ s :=
    (scaled_length _ _).eqTrans (coefficients_length _ _)
  exact (pad_evaluation _ _ _).eqTrans
    ((GaussianRationalPolynomialPowers.power_evaluation _ _ _ _ hLen).eqTrans
      (scalar_power_congr r ((negative_evaluation _ _).eqTrans
        (RationalGaussianEmbedding.negative_congr (evaluate_input P s x hP)))))

theorem second_evaluation (f a r m x : PTm n) (hf : Γ ⊢[PRAAx] length f ≐ succ m) : Γ ⊢[PRAAx]
    evaluate (secondSummand f a r m) (embed x) ≐
      qnegative (qmul (factor a r) (embed (RationalPolynomialGaussianEmbedding.evaluate f x))) :=
  (negative_evaluation _ _).eqTrans (RationalGaussianEmbedding.negative_congr
    ((evaluation_linearity _ _ _).eqTrans (qmul_congr (.eqRefl _) (evaluate_input f m x hf))))

theorem polynomial_evaluation (P f a s r m x : PTm n) (hm : Γ ⊢[PRAAx] le (r*s) m)
    (hP : Γ ⊢[PRAAx] length P ≐ succ s) (hf : Γ ⊢[PRAAx] length f ≐ succ m) : Γ ⊢[PRAAx]
    evaluate (polynomial P f a s r m) (embed x) ≐
      qsub (GaussianRationalReciprocal.power (qnegative (embed (RationalPolynomialGaussianEmbedding.evaluate P x))) r)
        (qmul (factor a r) (embed (RationalPolynomialGaussianEmbedding.evaluate f x))) :=
  (added_evaluation _ _ _ _ (first_length _ _ _ _ hm) (second_length _ _ _ _)).eqTrans
    (qadd_congr (first_evaluation _ _ _ _ _ hP) (second_evaluation _ _ _ _ _ hf))

theorem second_leading_coefficient (f a r m : PTm n) : Γ ⊢[PRAAx]
    entry (secondSummand f a r m) zero ≐ qnegative (qmul (factor a r) (embed (entry f zero))) := by
  have hz : Γ ⊢[PRAAx] lt zero (succ m) := zero_lt_succ m
  exact (scaled_lookup _ _ _ (lt_congr (.eqRefl _) ((scaled_length _ _).eqTrans (coefficients_length _ _)).eqSymm hz)).eqTrans
    ((negative_as_minusOne _).eqSymm.eqTrans (negative_congr
      ((scaled_lookup _ _ _ (lt_congr (.eqRefl _) (coefficients_length _ _).eqSymm hz)).eqTrans
        (qmul_congr (.eqRefl _) (coefficient_lookup _ _ _ hz)))))

theorem leading_coefficient (P f a s r m : PTm n) (hm : Γ ⊢[PRAAx] lt (r*s) m) : Γ ⊢[PRAAx]
    entry (polynomial P f a s r m) zero ≐ qnegative (qmul (factor a r) (embed (entry f zero))) :=
  (added_lookup _ _ _ _ (zero_lt_succ m)).eqTrans
    ((qadd_congr (first_leading_zero P s r m hm) (second_leading_coefficient f a r m)).eqTrans
      (qzero_add _ (qnegative_canonical _)))

theorem embed_nonzero (a : PTm n) (ha : Γ ⊢[PRAAx] nonzero a) : Γ ⊢[PRAAx] neg (embed a ≐ qzero) :=
  .impI (.impE ha.wk ((RationalGaussianEmbedding.zero_iff a).wk.iffMp Prf.hyp0))

theorem negative_nonzero (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) (hz : Γ ⊢[PRAAx] neg (q ≐ qzero)) :
    Γ ⊢[PRAAx] neg (qnegative q ≐ qzero) := by
  have hzero : Γ ⊢[PRAAx] qnegative (qzero : PTm n) ≐ qzero :=
    (negative_as_minusOne _).eqTrans (qmul_zero_right _)
  exact .impI (.impE hz.wk ((GaussianDeterminantSignTransport.negative_involution q hq).wk.eqSymm.eqTrans
    ((negative_congr Prf.hyp0).eqTrans hzero.wk)))

theorem nonzero_leading_coefficient (P f a s r m : PTm n) (hm : Γ ⊢[PRAAx] lt (r*s) m)
    (ha : Γ ⊢[PRAAx] nonzero a) (hf : Γ ⊢[PRAAx] nonzero (entry f zero)) :
    Γ ⊢[PRAAx] GaussianRationalFiniteRoots.nonzeroHead (polynomial P f a s r m) := by
  have hFactor := GaussianRationalPowerNonzero.power_nonzero (embed a) r (embed_canonical _) (embed_nonzero a ha)
  have mulNonzero := GaussianRationalPolynomialProductDegree.multiply_nonzero (factor a r) (embed (entry f zero))
    (GaussianRationalReciprocal.power_canonical _ _) (embed_canonical _) hFactor (embed_nonzero _ hf)
  have ne := negative_nonzero _ (GaussianRationalHorner.qmul_canonical _ _) mulNonzero
  have head := (GaussianTranslatedNonconstant.recode_congr (leading_coefficient P f a s r m hm)).eqTrans
    (GaussianTranslatedNonconstant.recode_eq _ (qnegative_canonical _))
  exact .impI (.impE ne.wk (head.wk.eqSymm.eqTrans Prf.hyp0))

theorem exact_degree (P f a s r m : PTm n) (hm : Γ ⊢[PRAAx] lt (r*s) m)
    (ha : Γ ⊢[PRAAx] nonzero a) (hf : Γ ⊢[PRAAx] nonzero (entry f zero)) :
    Γ ⊢[PRAAx] GaussianRationalPolynomialDegree.degree (polynomial P f a s r m) m ≐ m := by
  let C := polynomial P f a s r m
  have hz : Γ ⊢[PRAAx] GaussianTranslatedNonconstant.zeroPrefix C zero := by
    refine .allI (.impI ?_)
    simp only [Syn.shift,ConciseIPRA.PTm.subst_zero]
    exact le_lt_absurd _ (zero_le _) Prf.hyp0
  have first := GaussianRationalPolynomialProductDegree.first_exact C m zero (zero_le _) hz
    (nonzero_leading_coefficient P f a s r m hm ha hf)
  exact (congrMonus (.eqRefl _) first).eqTrans (monus_zero _)

theorem line_value (P a x y : PTm n) (h : Γ ⊢[PRAAx] line P a x y) : Γ ⊢[PRAAx]
    qnegative (embed (RationalPolynomialGaussianEmbedding.evaluate P x)) ≐ qmul (embed a) (embed y) := by
  let p := RationalPolynomialGaussianEmbedding.evaluate P x
  let w := qmul (embed a) (embed y)
  have sum : Γ ⊢[PRAAx] qadd (embed p) w ≐ qzero :=
    ((RationalGaussianEmbedding.embed_add p (RationalArithmetic.multiply a y)).eqTrans
      (qadd_congr (.eqRefl _) (RationalGaussianEmbedding.embed_multiply a y))).eqSymm.eqTrans
      ((embed_equal _ _ h).eqTrans RationalGaussianEmbedding.embed_zero)
  exact (qzero_add (qnegative (embed p)) (qnegative_canonical _)).eqSymm.eqTrans
    ((qsub_congr sum.eqSymm (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qadd_sub_cancel (embed p) w (GaussianRationalHorner.qmul_canonical _ _)))

theorem curve_value (f r x y : PTm n) (h : Γ ⊢[PRAAx] curve f r x y) :
    Γ ⊢[PRAAx] GaussianRationalReciprocal.power (embed y) r ≐ embed (RationalPolynomialGaussianEmbedding.evaluate f x) :=
  (RationalScalarPowerGaussianEmbedding.power_embedding y r).eqSymm.eqTrans (embed_equal _ _ h)

theorem polynomial_root (P f a s r m x y : PTm n) (hm : Γ ⊢[PRAAx] le (r*s) m)
    (hP : Γ ⊢[PRAAx] length P ≐ succ s) (hf : Γ ⊢[PRAAx] length f ≐ succ m)
    (hl : Γ ⊢[PRAAx] line P a x y) (hc : Γ ⊢[PRAAx] curve f r x y) :
    Γ ⊢[PRAAx] evaluate (polynomial P f a s r m) (embed x) ≐ qzero := by
  have same := (scalar_power_congr r (line_value P a x y hl)).eqTrans
    ((GaussianRationalPowerAlgebra.power_product (embed a) (embed y) r).eqTrans
      (qmul_congr (.eqRefl (factor a r)) (curve_value f r x y hc)))
  exact (polynomial_evaluation P f a s r m x hm hP hf).eqTrans
    ((qsub_congr same (.eqRefl _)).eqTrans (GaussianCoefficientNormOrder.qsub_self _))

theorem ordinate_unique (P a x y u v : PTm n) (ha : Γ ⊢[PRAAx] nonzero a)
    (hy : Γ ⊢[PRAAx] line P a x y) (hv : Γ ⊢[PRAAx] line P a u v)
    (hx : Γ ⊢[PRAAx] RationalArgmin.rationalEq x u) : Γ ⊢[PRAAx] RationalArgmin.rationalEq y v := by
  have values := (RationalPolynomialGaussianEmbedding.evaluation_conjugacy P x).eqTrans
    ((evaluate_congr (.eqRefl _) (embed_equal _ _ hx)).eqTrans
      (RationalPolynomialGaussianEmbedding.evaluation_conjugacy P u).eqSymm)
  have multiplied := (line_value P a x y hy).eqSymm.eqTrans
    ((negative_congr values).eqTrans (line_value P a u v hv))
  have inverse := GaussianRationalReciprocal.reciprocal_identity (embed a)
    (GaussianRationalFiniteRoots.norm_positive_of_nonzero _ (embed_canonical _) (embed_nonzero a ha))
  apply rational_equal_of_embed
  exact (GaussianNormFiberDivisibility.multiply_inverse_cancel _ _ _ inverse (embed_canonical y)).eqSymm.eqTrans
    ((qmul_congr (.eqRefl _) multiplied).eqTrans
      (GaussianNormFiberDivisibility.multiply_inverse_cancel _ _ _ inverse (embed_canonical v)))

def polynomialF : PR 6 := PTm.toPR (polynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (P f a s r m : PTm n) : PTm n := app polynomialF ![P,f,a,s,r,m]
ipra_subst run

theorem program_at (P f a s r m : PTm n) : Γ ⊢[PRAAx] run P f a s r m ≐ polynomial P f a s r m := by
  simpa [run,polynomialF] using toPR_eq (Γ := Γ)
    (polynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![P,f,a,s,r,m]

theorem returned_root (P f a s r m x y : PTm n) (hm : Γ ⊢[PRAAx] le (r*s) m)
    (hP : Γ ⊢[PRAAx] length P ≐ succ s) (hf : Γ ⊢[PRAAx] length f ≐ succ m)
    (hl : Γ ⊢[PRAAx] line P a x y) (hc : Γ ⊢[PRAAx] curve f r x y) : Γ ⊢[PRAAx]
    evaluate (run P f a s r m) (embed x) ≐ qzero :=
  (evaluate_congr (program_at _ _ _ _ _ _) (.eqRefl _)).eqTrans (polynomial_root _ _ _ _ _ _ _ _ hm hP hf hl hc)

theorem actual_section_collapse_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ polynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)

theorem actual_section_collapse_leading_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 4*var 3) (var 5) ⟶ entry (polynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) zero ≐
      qnegative (qmul (factor (var 2) (var 4)) (embed (entry (var 1) zero)))) :=
  closeUniv 6 (.impI (leading_coefficient _ _ _ _ _ _ Prf.hyp0))

theorem actual_section_collapse_exact_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 4*var 3) (var 5) ⟶ nonzero (var 2) ⟶ nonzero (entry (var 1) zero) ⟶
      GaussianRationalPolynomialDegree.degree (polynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 5) ≐ var 5) :=
  closeUniv 6 (.impI (.impI (.impI (exact_degree _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem actual_section_collapse_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le (var 4*var 3) (var 5) ⟶ length (var 0) ≐ succ (var 3) ⟶ length (var 1) ≐ succ (var 5) ⟶
      line (var 0) (var 2) (var 6) (var 7) ⟶ curve (var 1) (var 4) (var 6) (var 7) ⟶
      evaluate (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (embed (var 6)) ≐ qzero) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI (returned_root _ _ _ _ _ _ _ _
    (.hyp (by simp)) (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0))))))

theorem actual_section_ordinate_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (nonzero (var 1) ⟶ line (var 0) (var 1) (var 2) (var 3) ⟶ line (var 0) (var 1) (var 4) (var 5) ⟶
      RationalArgmin.rationalEq (var 2) (var 4) ⟶ RationalArgmin.rationalEq (var 3) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (ordinate_unique _ _ _ _ _ _
    (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.RationalSectionCollapse
