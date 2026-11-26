import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelRows
import IPRADerivations.Analysis.Trigonometry.GaussianSineProductImaginaryScaling

/-!
# Exact original Binet row at a matched rational π sample

At the rational time (2π_p A/B), multiplying the original (j)-th
kernel row by (4π_p^2 A/B) gives the original logarithmic derivative row
of the imaginary sine product. Both occurrences of (π_p) use the
same original sampler observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelImaginaryRatioRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (scale oneCode eval_re_code eval_im_code)
open GaussianBinetKernelPi (sample sample_fraction sample_margins)
open GaussianBinetKernelRows (nativeNum nativeDen weight value_fraction value rowF rowData)
open GaussianCompactRiemannName (fraction_congr)
open GaussianEulerDampedTimeRate (fraction_product)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul ofGaussian_represents ofGaussian_canonical positive_product
  canonical_unique represents_congr)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRootAlgebra (equal equal_of_values re_scale im_scale re_one im_one)
open GaussianSineProductImaginaryLogDerivative (logarithmRow rationalReal realNumerator squareDenominator)
open GaussianStirlingConstant (piNumerator piDenominator)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def timeNumerator (p A : PTm n) : PTm n := two*piNumerator p*A
def timeDenominator (p B : PTm n) : PTm n := piDenominator p*B
def multiplierNumerator (p A : PTm n) : PTm n := num 4*(piNumerator p*piNumerator p)*A
def multiplierDenominator (p B : PTm n) : PTm n := (piDenominator p*piDenominator p)*B
def multiplier (p A B : PTm n) : PTm n := fraction (multiplierNumerator p A) (multiplierDenominator p B)

theorem time_denominator_positive (p B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (timeDenominator p B) :=
  positive_product _ _ (GaussianBinetKernelPi.denominator_positive p) hB

theorem time_value (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (sample p) (fraction (two*A) B) ≐ fraction (timeNumerator p A) (timeDenominator p B) := by
  have hπ := GaussianBinetKernelPi.denominator_positive (Γ := Γ) p
  exact (qmul_congr (sample_fraction p) (.eqRefl _)).eqTrans
    ((fraction_product (piNumerator p) (piDenominator p) (two*A) B hπ hB).eqTrans
      (fraction_congr _ _ _ _ (by dsimp only [timeNumerator]; ipra_ring) (.eqRefl _)))

theorem multiplier_value (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (qmul (sample p) (sample p)) (fraction (num 4*A) B) ≐ multiplier p A B := by
  let u := piNumerator p
  let v := piDenominator p
  have hπ := GaussianBinetKernelPi.denominator_positive (Γ := Γ) p
  have e := sample_fraction (Γ := Γ) p
  have square := (qmul_congr e e).eqTrans (fraction_product u v u v hπ hπ)
  exact (qmul_congr square (.eqRefl _)).eqTrans
    ((fraction_product (u*u) (v*v) (num 4*A) B (positive_product _ _ hπ hπ) hB).eqTrans
      (fraction_congr _ _ _ _ (by dsimp only [u,multiplierNumerator]; ipra_ring) (.eqRefl _)))

private theorem same_fraction_code (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] fraction A B ≐ rationalReal A B := by
  have e : Γ ⊢[PRAAx] equal (scale A oneCode) (realNumerator A) := by
    apply equal_of_values <;> simp [realNumerator,re_scale,im_scale,re_one,im_one,
      eval_re_code,eval_im_code,ZT.toZ_ofNat]
  exact canonical_unique _ _ _ B (ofGaussian_canonical _ _ hB) (ofGaussian_canonical _ _ hB) hB
    (represents_congr (.eqRefl _) e (.eqRefl _) (ofGaussian_represents _ _ hB)) (ofGaussian_represents _ _ hB)

theorem matched_row (p i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (multiplier p A B) (value p (succ i) (timeNumerator p A) (timeDenominator p B)) ≐ logarithmRow i A B := by
  let u := piNumerator p
  let v := piDenominator p
  let a := timeNumerator p A
  let b := timeDenominator p B
  let P := multiplierNumerator p A
  let D := multiplierDenominator p B
  let L := nativeNum a b (succ i) u v
  let S := squareDenominator i B+A*A
  let M := num 4*((u*u)*(v*v))
  let K := M*D
  have h₄ : Γ ⊢[PRAAx] le one (num 4) := by ipra_le 3
  have hj : Γ ⊢[PRAAx] le one (succ i) := zero_lt_succ _
  have hv : Γ ⊢[PRAAx] le one v := GaussianBinetKernelPi.denominator_positive p
  have hu : Γ ⊢[PRAAx] le one u := le_trans (positive_product _ _ (le_succ_self one) hv)
    (sample_margins (Γ := Γ) p).andE₁
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ hv hv) hB
  have hb : Γ ⊢[PRAAx] le one b := time_denominator_positive p B hB
  have hBj := positive_product _ _ hB hj
  have hS : Γ ⊢[PRAAx] le one S := le_trans (positive_product _ _ hBj hBj) (le_add_right _ _)
  have hM : Γ ⊢[PRAAx] le one M :=
    positive_product _ _ h₄ (positive_product _ _ (positive_product _ _ hu hu) (positive_product _ _ hv hv))
  have hK : Γ ⊢[PRAAx] le one K := positive_product _ _ hM hD
  have e : Γ ⊢[PRAAx] M*S ≐ L := by
    dsimp only [M,S,L,a,b,u,v,timeNumerator,timeDenominator,nativeNum,weight,squareDenominator]
    ipra_ring
  have hL : Γ ⊢[PRAAx] le one L := le_congr (.eqRefl _) e (positive_product _ _ hM hS)
  have row := value_fraction p (succ i) a b hb hj
  have prod := fraction_product P D (two*nativeDen b v) L hD hL
  have numerator : Γ ⊢[PRAAx] P*(two*nativeDen b v) ≐ K*(two*A*B) := by
    dsimp only [P,K,M,D,b,u,v,multiplierNumerator,multiplierDenominator,timeDenominator,nativeDen]
    ipra_ring
  have denominator : Γ ⊢[PRAAx] D*L ≐ K*S :=
    (congrMul (.eqRefl D) e.eqSymm).eqTrans (by dsimp only [K]; ipra_ring)
  exact (qmul_congr (.eqRefl _) row).eqTrans (prod.eqTrans
    ((fraction_congr _ _ _ _ numerator denominator).eqTrans
      ((same_fraction_code _ _ (positive_product _ _ hK hS)).eqTrans
        (GaussianSineProductImaginaryScaling.rational_real_rescale (two*A*B) S K hS hK))))

theorem matched_original_row (p i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (multiplier p A B)
      (ap2 rowF p (rowData i (timeNumerator p A) (timeDenominator p B))) ≐ logarithmRow i A B :=
  (qmul_congr (.eqRefl _) (GaussianBinetKernelRows.row_sample p i _ _)).eqTrans (matched_row p i A B hB)

def ratioNumerator (p A : PTm n) : PTm n := A*piDenominator p
def ratioDenominator (p B : PTm n) : PTm n := two*B*piNumerator p
def ratioRadius (A : PTm n) : PTm n := A+one

@[simp] theorem subst_ratioNumerator {m : ℕ} (σ : Fin n → PTm m) (p A : PTm n) :
    Syn.subst σ (ratioNumerator p A) = ratioNumerator (Syn.subst σ p) (Syn.subst σ A) := by
  simp [ratioNumerator,piDenominator,GaussianGammaHalfPiName.clearing,GaussianGammaHalfPiName.meshAt,
    GaussianGammaHalfPiName.meshIndex,GaussianGammaHalfPiName.orderAt,GaussianGammaHalfPiName.orderIndex,
    Products.fact,two,one]
@[simp] theorem subst_ratioDenominator {m : ℕ} (σ : Fin n → PTm m) (p B : PTm n) :
    Syn.subst σ (ratioDenominator p B) = ratioDenominator (Syn.subst σ p) (Syn.subst σ B) := by
  simp [ratioDenominator,piNumerator,BaselQuadrature.Q,GaussianGammaHalfPiName.clearing,
    GaussianGammaHalfPiName.meshAt,GaussianGammaHalfPiName.meshIndex,GaussianGammaHalfPiName.orderAt,
    GaussianGammaHalfPiName.orderIndex,two,one]

theorem ratio_source (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    le one (ratioRadius A) ⋏ (le one (ratioDenominator p B) ⋏
      le (ratioNumerator p A+one) (ratioRadius A*ratioDenominator p B)) := by
  let u := piNumerator p
  let v := piDenominator p
  have hv : Γ ⊢[PRAAx] le one v := GaussianBinetKernelPi.denominator_positive p
  have m : Γ ⊢[PRAAx] le (two*v) u := (sample_margins (Γ := Γ) p).andE₁
  have h : Γ ⊢[PRAAx] le v (ratioDenominator p B) := by
    dsimp only [ratioDenominator]
    ipra_le 2*𝔞 B*sl m+4*𝔞 v*sl hB+3*𝔞 v
  have hA : Γ ⊢[PRAAx] le (ratioNumerator p A+one) (ratioRadius A*v) := by
    dsimp only [ratioNumerator,ratioRadius]
    ipra_le sl hv
  exact .andI (le_add_left _ _) (.andI (le_trans hv h) (le_trans hA (le_mul_mono (le_refl _) h)))

private theorem fraction_rescale (a B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] fraction (k*a) (k*B) ≐ fraction a B :=
  (same_fraction_code _ _ (positive_product _ _ hk hB)).eqTrans
    ((GaussianSineProductImaginaryScaling.rational_real_rescale a B k hB hk).eqTrans (same_fraction_code _ _ hB).eqSymm)

/-- With the frozen ratio (r=(A/B)/(2π_p)), the extra factor
(r) removes even the rational π observation from the multiplier:
(r S_{j}(r)=(A/B)^2 K_{j,p}(A/B)). -/
theorem rational_time_row (p i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (fraction (A*A) (B*B)) (ap2 rowF p (rowData i A B)) ≐
      qmul (rationalReal (ratioNumerator p A) (ratioDenominator p B))
        (logarithmRow i (ratioNumerator p A) (ratioDenominator p B)) := by
  let u := piNumerator p
  let v := piDenominator p
  let a := ratioNumerator p A
  let b := ratioDenominator p B
  let j := succ i
  let S := squareDenominator i b+a*a
  let L := nativeNum A B j u v
  let J := two*(A*A)*(v*v)
  have hb : Γ ⊢[PRAAx] le one b := (ratio_source p A B hB).andE₂.andE₁
  have hB₂ := positive_product _ _ hB hB
  have hj : Γ ⊢[PRAAx] le one j := zero_lt_succ i
  have hbj := positive_product _ _ hb hj
  have hS : Γ ⊢[PRAAx] le one S := le_trans (positive_product _ _ hbj hbj) (le_add_right _ _)
  have eq : Γ ⊢[PRAAx] S ≐ L := by
    dsimp only [S,L,a,b,u,v,j,squareDenominator,nativeNum,weight,ratioNumerator,ratioDenominator]
    ipra_ring
  have hL : Γ ⊢[PRAAx] le one L := le_congr (.eqRefl _) eq hS
  have left := (qmul_congr (.eqRefl (fraction (A*A) (B*B)))
    ((GaussianBinetKernelRows.row_sample p i A B).eqTrans (value_fraction p j A B hB hj))).eqTrans
      (fraction_product (A*A) (B*B) (two*nativeDen B v) L hB₂ hL)
  have left' := (fraction_congr ((A*A)*(two*nativeDen B v)) ((B*B)*J) (B*B*L) ((B*B)*L)
    (by dsimp only [nativeDen,J]; ipra_ring) (.eqRefl _)).eqTrans (fraction_rescale J L (B*B) hL hB₂)
  have right := (qmul_congr (same_fraction_code a b hb).eqSymm (same_fraction_code (two*a*b) S hS).eqSymm).eqTrans
    (fraction_product a b (two*a*b) S hb hS)
  have right' := (fraction_congr (a*(two*a*b)) (b*J) (b*S) (b*L)
    (by dsimp only [J,a,ratioNumerator]; ipra_ring) (congrMul (.eqRefl _) eq)).eqTrans (fraction_rescale J L b hL hb)
  exact (left.eqTrans left').eqTrans (right.eqTrans right').eqSymm

theorem actual_matched_pi_Binet_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ qmul (multiplier (var 0) (var 2) (var 3))
      (ap2 rowF (var 0) (rowData (var 1) (timeNumerator (var 0) (var 2)) (timeDenominator (var 0) (var 3)))) ≐
        logarithmRow (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (matched_original_row _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetKernelImaginaryRatioRows
