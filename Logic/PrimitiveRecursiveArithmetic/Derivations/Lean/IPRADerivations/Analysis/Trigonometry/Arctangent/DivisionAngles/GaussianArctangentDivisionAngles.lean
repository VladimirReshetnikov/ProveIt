import IPRADerivations.Analysis.Trigonometry.Arctangent.Inverse.GaussianArctangentInverseForward
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentOriginalExponential
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianBoundedConstantProductName
import IPRADerivations.Analysis.Names.ImaginaryParts.GaussianImaginaryNameConjugation

/-!
# The original names for the divided angles i·kπ/m

These names multiply the actual quarter turn by the fixed rational
coefficient 2k/m. Their independent-precision order against zero and
the quarter turn follows from the exact nonnegative quadrature
numerator and the numerical bound 2k ≤ m.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianArctangentDivisionAngles

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode zeroCode normSq normSq_eval eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianArctangentExponentialPrefix (prefixValue total at_pi_observation)
open GaussianArctangentNamedChord (imaginary_coordinate_radius)
open GaussianArctangentQuarterExponential (quarterF quarter_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaHalfPiName (meshAt clearing)
open GaussianImaginaryNameConjugation (imaginarySamples)
open GaussianNameEquivalence (point_at)
open GaussianNameRingLaws (zeroF zero_at)
open GaussianRationalHorner (ofGaussian positive_product ofGaussian_represents qmul_represents qmul_canonical
  canonical canonical_congr represents represents_congr scalar_congr qzero zero_represents)
open GaussianRationalMetric (bounded bounded_of_cleared comparison_of_cleared)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRootAlgebra (equal equal_of_values re_scale im_scale re_one im_one re_mul im_mul)
open RationalGaussianEmbedding (scalarZero scalar_zero_represents)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper upper_order_left upper_mono upper_of_radius upper_of_order)
open Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (k m : PTm n) : Fm PTm n := le one m ⋏ le (two*k) m
def modulus (J : PTm n) : PTm n := succ (two*J)
def coefficient (k m : PTm n) : PTm n := ofGaussian (scale (two*k) oneCode) m
def nameF : PR 2 := GaussianBoundedConstantProductName.nameF quarterF
def data (k m z : PTm n) : PTm n := GaussianBoundedConstantProductName.data one (coefficient k m) z
def clock (p : PTm n) : PTm n := GaussianBoundedConstantProductName.clock p one
def quarterNumerator (p : PTm n) : PTm n := two*total (meshAt p) (meshAt p) (clearing p)
def quarterDenominator (p : PTm n) : PTm n := fact (clearing p)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (k d : PTm n) :
    (source k d).subst σ = source (Syn.subst σ k) (Syn.subst σ d) := by simp [source]
@[simp] theorem subst_modulus {m : ℕ} (σ : Fin n → PTm m) (J : PTm n) :
    Syn.subst σ (modulus J) = modulus (Syn.subst σ J) := by simp [modulus]
@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (k d : PTm n) :
    Syn.subst σ (coefficient k d) = coefficient (Syn.subst σ k) (Syn.subst σ d) := by simp [coefficient]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (k d z : PTm n) :
    Syn.subst σ (data k d z) = data (Syn.subst σ k) (Syn.subst σ d) (Syn.subst σ z) := by simp [data]

theorem odd_reserve (k J : PTm n) (hk : Γ ⊢[PRAAx] le k J) :
    Γ ⊢[PRAAx] le (succ (two*k)) (modulus J) :=
  by
    have h := le_mul_mono (le_refl two) hk
    unfold modulus
    ipra_le sl h

theorem odd_source (k J : PTm n) (hk : Γ ⊢[PRAAx] le k J) :
    Γ ⊢[PRAAx] source k (modulus J) :=
  .andI (zero_lt_succ _) (le_trans (le_succ_self _) (odd_reserve k J hk))

theorem coefficient_bound (k m : PTm n) (h : Γ ⊢[PRAAx] source k m) :
    Γ ⊢[PRAAx] bounded (coefficient k m) one one := by
  let A := two*k
  have hn : Γ ⊢[PRAAx] normSq (scale A oneCode) ≐ A*A := by
    apply deriveNat
    rw [normSq_eval]
    simp only [re_scale, im_scale, re_one, im_one]
    ipra_simps
    ring
  apply bounded_of_cleared _ _ m one one h.andE₁ (le_refl _) (ofGaussian_represents _ _ h.andE₁)
  exact le_congr (hn.eqSymm.eqTrans (by ipra_ring)) (by ipra_ring) (le_mul_mono h.andE₂ h.andE₂)

theorem sample_at (k m z p : PTm n) :
    Γ ⊢[PRAAx] ap2 nameF p (data k m z) ≐ GaussianRationalHorner.qmul (coefficient k m) (ap2 quarterF (clock p) z) :=
  GaussianBoundedConstantProductName.sample_at quarterF p one (coefficient k m) z

theorem name_regular (k m z : PTm n) (h : Γ ⊢[PRAAx] source k m) :
    Γ ⊢[PRAAx] pointCN nameF (data k m z) :=
  GaussianBoundedConstantProductName.name_regular quarterF one (coefficient k m) z
    (.andI (quarter_regular z) (coefficient_bound k m h))

theorem quarter_represents (p z : PTm n) :
    Γ ⊢[PRAAx] represents (ap2 quarterF p z) (scale (quarterNumerator p) imaginaryCode) (quarterDenominator p) :=
  represents_congr ((at_pi_observation p z).eqTrans (GaussianArctangentQuarterExponential.sample_at p z).eqSymm)
    (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
    (ofGaussian_represents _ _ (GaussianRationalPolynomialExponential.factorial_positive _))

theorem sample_represents (k m z p : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] represents (ap2 nameF p (data k m z))
      (scale (two*k*quarterNumerator (clock p)) imaginaryCode) (m*quarterDenominator (clock p)) := by
  let a := scale (two*k) oneCode
  let b := scale (quarterNumerator (clock p)) imaginaryCode
  let D := quarterDenominator (clock p)
  have hD := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) (clearing (clock p))
  have prod := qmul_represents (coefficient k m) (ap2 quarterF (clock p) z) a b m D hm hD
    (ofGaussian_represents _ _ hm) (quarter_represents (clock p) z)
  have e : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.mul a b) (scale (two*k*quarterNumerator (clock p)) imaginaryCode) := by
    dsimp only [a,b]
    apply equal_of_values <;>
      simp only [re_mul, im_mul, re_scale, im_scale, re_one, im_one, imaginaryCode, eval_re_code, eval_im_code, ZT.toZ_ofNat] <;>
      ipra_simps <;> ring
  exact represents_congr (sample_at k m z p).eqSymm e (.eqRefl _) prod

private theorem prefix_ordinate {q U D : PTm n} (h : Γ ⊢[PRAAx] represents q (scale U imaginaryCode) D) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (sndT q) (ZT.ofNat U) D := by
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) h.andE₂
  apply ZT.derive
  simp only [im_scale, imaginaryCode, eval_im_code, ZT.toZ_ofNat]
  ipra_simps
  ring

theorem sample_axis_at (k m z p : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] fstT (ap2 nameF p (data k m z)) ≐ scalarZero := by
  have hF := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) (clearing (clock p))
  have hD := positive_product _ _ hm hF
  have hc := canonical_congr (sample_at (Γ := Γ) k m z p) (qmul_canonical _ _)
  have r := sample_represents k m z p hm
  have nativeZero : Γ ⊢[PRAAx]
      ZT.eq (ComplexLogarithmRemainder.re (scale (two*k*quarterNumerator (clock p)) imaginaryCode)) (ZT.ofNat zero) := by
    apply ZT.derive
    simp [re_scale,imaginaryCode,eval_re_code,ZT.toZ_ofNat,Q.mk_zero,map_zero]
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ one hc.andE₂.andE₁
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (scalar_congr (.eqRefl _) nativeZero (.eqRefl _) r.andE₁) (scalar_zero_represents one) hD (le_refl one)
  apply ZT.derive
  simp [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_zero,map_zero]

theorem imaginary_samples (k m z : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] imaginarySamples nameF (data k m z) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift] using hm.shift
  simpa only [imaginarySamples, Syn.shift, subst_data] using
    sample_axis_at (Syn.shift k) (Syn.shift m) (Syn.shift z) (var 0) hs

theorem exponential_input (k m z : PTm n) (h : Γ ⊢[PRAAx] source k m) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input nameF two (data k m z) := by
  refine .andI (name_regular k m z h) (.allI ?_)
  let a := Syn.shift k
  let d := Syn.shift m
  let x := Syn.shift z
  let p : PTm (n+1) := var 0
  have s : Γ.map Fm.shift ⊢[PRAAx] source a d := by simpa [Fm.shift,Syn.shift,a,d] using h.shift
  have b := GaussianRadiusExponentialName.bounded_samples_at (Γ := Γ.map Fm.shift) quarterF two x (clock p)
    (GaussianArctangentQuarterExponential.quarter_input x
      (GaussianArctangentQuarterExponential.original_bounded_arguments x)).andE₂
  have bp := bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _) (coefficient_bound a d s) b
  simpa only [GaussianRadiusExponentialName.boundedSamples, Syn.shift, subst_data, two, one,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,a,d,x,p] using
    bound_congr (sample_at a d x p).eqSymm (one_mul two) (one_mul one) bp

private theorem lower_at (k m z p q : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] upper (sndT (ap2 zeroF p z)) (sndT (ap2 nameF q (data k m z)))
      (unit p+unit q) (unit p*unit q) := by
  have hd := positive_product _ _ hm (GaussianRationalPolynomialExponential.factorial_positive (clearing (clock q)))
  have hz : Γ ⊢[PRAAx] RationalArithmetic.represents (sndT qzero) (ZT.ofNat zero) one := by
    apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) (zero_represents one).andE₂
    apply ZT.derive
    simp [zeroCode,eval_im_code,ZT.toZ_ofNat]
  have ord := comparison_of_cleared _ _ _ _ _ _ (le_refl _) hd hz (prefix_ordinate (sample_represents k m z q hm))
    (le_congr (mul_zero _).eqSymm (.eqRefl _) (zero_le _))
  exact upper_of_order _ _ _ _ (rationalLE_congr (congrSnd (zero_at p z)).eqSymm (.eqRefl _) ord)

private theorem upper_at (k m z p q : PTm n) (h : Γ ⊢[PRAAx] source k m) :
    Γ ⊢[PRAAx] upper (sndT (ap2 nameF p (data k m z))) (sndT (ap2 quarterF q z))
      (unit p+unit q) (unit p*unit q) := by
  let V := unit (clock p)
  let P := unit p
  let Q := unit q
  let K := quarterNumerator (clock p)
  let D := quarterDenominator (clock p)
  have hD := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) (clearing (clock p))
  have hprod := positive_product _ _ h.andE₁ hD
  have cle : Γ ⊢[PRAAx] le (D*(two*k*K)) (K*(m*D)) :=
    le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono h.andE₂ (le_refl (D*K)))
  have ord := comparison_of_cleared _ _ _ _ _ _ hprod hD
    (prefix_ordinate (sample_represents k m z p h.andE₁))
    (prefix_ordinate (quarter_represents (clock p) z)) cle
  have hvq := positive_product (Γ := Γ) _ _ (unit_positive (clock p)) (unit_positive q)
  have d := imaginary_coordinate_radius _ _ _ _ hvq (point_at quarterF z (clock p) q (quarter_regular z))
  have hP : Γ ⊢[PRAAx] le P V := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  exact upper_mono _ _ (V+Q) (V*Q) (P+Q) (P*Q) hvq
    (upper_order_left _ _ _ _ _ ord (upper_of_radius _ _ _ _ d))
    (by ipra_le 𝔞 Q*𝔞 Q*sl hP)

theorem interval_input (k m z : PTm n) (h : Γ ⊢[PRAAx] source k m) :
    Γ ⊢[PRAAx] GaussianArctangentInverseForward.input nameF (data k m z) z := by
  let a := Syn.shift (Syn.shift k)
  let d := Syn.shift (Syn.shift m)
  let x := Syn.shift (Syn.shift z)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source a d := by
    simpa [Fm.shift,Syn.shift,a,d] using h.shift.shift
  refine .andI (name_regular k m z h) (.andI (.allI (.allI ?_)) (.allI (.allI ?_)))
  · simpa only [GaussianArctangentInverseForward.imaginaryOrder,GaussianArctangentInverseSampler.ordinate,
      Syn.shift,subst_data,a,d,x] using lower_at a d x (var 1) (var 0) hs.andE₁
  · simpa only [GaussianArctangentInverseForward.imaginaryOrder,GaussianArctangentInverseSampler.ordinate,
      Syn.shift,subst_data,a,d,x] using upper_at a d x (var 1) (var 0) hs

theorem actual_odd_division_angles_in_interval_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 0) (var 1) ⟶
      (le (succ (two*var 0)) (modulus (var 1)) ⋏
        (GaussianArctangentInverseForward.input nameF (data (var 0) (modulus (var 1)) (var 2)) (var 2) ⋏
          (GaussianRadiusExponentialName.input nameF two (data (var 0) (modulus (var 1)) (var 2)) ⋏
            imaginarySamples nameF (data (var 0) (modulus (var 1)) (var 2)))))) :=
  closeUniv 3 (.impI (.andI (odd_reserve _ _ Prf.hyp0)
    (.andI (interval_input _ _ _ (odd_source _ _ Prf.hyp0))
      (.andI (exponential_input _ _ _ (odd_source _ _ Prf.hyp0))
        (imaginary_samples _ _ _ (odd_source _ _ Prf.hyp0).andE₁)))))

end LeanProofs.IPRA.Analysis.GaussianArctangentDivisionAngles
