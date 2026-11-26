import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentDivisionAngles
import IPRADerivations.Analysis.Trigonometry.GaussianNamedSincQuadraticBounds
import IPRADerivations.Analysis.Trigonometry.GaussianSineProductT4Budget

/-!
# Actual scaled arguments for the sine product

The name of `πz/(Bm)` is obtained from the original quarter-turn
name by the fixed Gaussian coefficient `−2iz/(Bm)`. Its observations
have the rational radius `4R/m` whenever the encoded input `z/B`
has radius `R`. The same program gives the real argument `kπ/m`
when the Gaussian numerator encodes the natural number `k`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductScaledArguments

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale mul normSq normSq_neg normSq_eval normSq_scale normSq_mul oneCode
  eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianArctangentQuarterExponential (quarterF quarter_regular)
open GaussianArctangentDivisionAngles (quarterNumerator quarterDenominator quarter_represents)
open GaussianArctangentExponentialPrefix (prefix_bound original_mesh_source at_pi_observation)
open GaussianGammaHalfPiName (meshAt clearing)
open GaussianBoundedConstantProductName (clock)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product represents represents_congr)
open GaussianRationalMetric (bounded bounded_iff)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianNamedSincQuadraticBounds (observationBound)
open GaussianRadiusExponentialName (input)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRootAlgebra (re_mul im_mul re_neg im_neg re_scale im_scale equal_of_values)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def coefficient (z B m : PTm n) : PTm n :=
  ofGaussian (scale two (mul (ComplexLogarithmRemainder.neg imaginaryCode) z)) (B*m)

def nameF : PR 2 := GaussianBoundedConstantProductName.nameF quarterF
def data (z R B m x : PTm n) : PTm n := GaussianBoundedConstantProductName.data (two*R) (coefficient z B m) x

@[simp] theorem subst_coefficient {l : ℕ} (σ : Fin n → PTm l) (z B m : PTm n) :
    Syn.subst σ (coefficient z B m) = coefficient (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ m) := by
  simp [coefficient,imaginaryCode]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (z R B m x : PTm n) :
    Syn.subst σ (data z R B m x) =
      data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ x) := by
  simp [data]

theorem sample_at (z R B m x p : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B m x) ≐ GaussianRationalHorner.qmul (coefficient z B m) (ap2 quarterF (clock p (two*R)) x) :=
  GaussianBoundedConstantProductName.sample_at quarterF p (two*R) (coefficient z B m) x

theorem sample_represents (z R B m x p : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] represents (ap2 nameF p (data z R B m x))
      (scale (two*quarterNumerator (clock p (two*R))) z) ((B*m)*quarterDenominator (clock p (two*R))) := by
  let a := scale two (mul (ComplexLogarithmRemainder.neg imaginaryCode) z)
  let P := quarterNumerator (clock p (two*R))
  let b := scale P imaginaryCode
  let D := quarterDenominator (clock p (two*R))
  have hD : Γ ⊢[PRAAx] le one D := GaussianRationalPolynomialExponential.factorial_positive _
  have hBm := positive_product B m hB hm
  have raw := GaussianRationalHorner.qmul_represents (coefficient z B m) (ap2 quarterF (clock p (two*R)) x)
    a b (B*m) D hBm hD (ofGaussian_represents _ _ hBm) (quarter_represents _ x)
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (mul a b) (scale (two*P) z) := by
    dsimp only [a,b]
    apply equal_of_values <;>
      simp only [re_mul,im_mul,re_neg,im_neg,re_scale,im_scale,imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_ofNat] <;>
      ipra_simps <;> ring
  exact represents_congr (sample_at z R B m x p).eqSymm e (.eqRefl _) raw

theorem coefficient_bound (z R B m : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (coefficient z B m) (two*R) m := by
  let a := scale two (mul (ComplexLogarithmRemainder.neg imaginaryCode) z)
  have hI : Γ ⊢[PRAAx] normSq (imaginaryCode : PTm n) ≐ one := by
    apply deriveNat
    rw [normSq_eval]
    simp only [imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  have norm : Γ ⊢[PRAAx] normSq a ≐ (two*two)*normSq z :=
    (normSq_scale two _).eqTrans (congrMul (.eqRefl _)
      ((normSq_mul _ z).eqTrans ((congrMul ((normSq_neg _).eqTrans hI) (.eqRefl _)).eqTrans (one_mul _))))
  have hBm := positive_product B m hB hm
  have scaled := le_mul_mono (le_refl ((two*m)*(two*m))) hz
  apply (bounded_iff _ a (B*m) (two*R) m hBm hm (ofGaussian_represents _ _ hBm)).iffMpr
  exact le_congr (by
    have eq := natEq norm
    apply deriveNat
    ipra_simps
    rw [eq]
    ring) (by ipra_ring) scaled

theorem name_regular (z R B m x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx] pointCN nameF (data z R B m x) := by
  have coarse := bounded_radius_mono _ _ _ (two*R) one hm (le_refl one)
    (le_mul_mono (le_refl (two*R)) hm) (coefficient_bound z R B m hB hm hz)
  exact GaussianBoundedConstantProductName.name_regular quarterF (two*R) (coefficient z B m) x
    (.andI (quarter_regular x) coarse)

theorem quarter_bound (p x : PTm n) : Γ ⊢[PRAAx] bounded (ap2 quarterF p x) two one := by
  let M := meshAt p
  let L := clearing p
  have e := (at_pi_observation (Γ := Γ) p x).eqTrans (GaussianArctangentQuarterExponential.sample_at p x).eqSymm
  exact bound_congr e (.eqRefl _) (.eqRefl _) (prefix_bound M M L (original_mesh_source p) (le_refl M))

theorem observation_bound_at (z R B m x p : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data z R B m x)) (num 4*R) m :=
  bound_congr (sample_at z R B m x p).eqSymm (by ipra_ring) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ hm (le_refl one)
      (coefficient_bound z R B m hB hm hz) (quarter_bound (clock p (two*R)) x))

theorem observation_bound (z R B m x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] observationBound nameF (data z R B m x) (num 4*R) m := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  have hB' : Δ ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift,Δ,one] using hB.shift
  have hm' : Δ ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift,Δ,one] using hm.shift
  have hz' : Δ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (Syn.shift z) (Syn.shift R*Syn.shift B) := by
    simpa [Fm.shift,Syn.shift,Δ] using hz.shift
  simpa only [observationBound,Syn.shift,subst_data,PTm.subst_mul,PTm.subst_num,Δ] using
    observation_bound_at (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift m) (Syn.shift x) (var 0) hB' hm' hz'

theorem unit_disk_input (z R B m x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) (hR : Γ ⊢[PRAAx] le (num 4*R) m) :
    Γ ⊢[PRAAx] input nameF one (data z R B m x) := by
  refine .andI (name_regular z R B m x hB hm hz) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let z' := Syn.shift z
  let R' := Syn.shift R
  let B' := Syn.shift B
  let m' := Syn.shift m
  let x' := Syn.shift x
  have hB' : Δ ⊢[PRAAx] le one B' := by simpa [Fm.shift,Syn.shift,Δ,B',one] using hB.shift
  have hm' : Δ ⊢[PRAAx] le one m' := by simpa [Fm.shift,Syn.shift,Δ,m',one] using hm.shift
  have hz' : Δ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z' (R'*B') := by
    simpa [Fm.shift,Syn.shift,Δ,z',R',B'] using hz.shift
  have hR' : Δ ⊢[PRAAx] le (num 4*R') m' := by simpa [Fm.shift,Syn.shift,Δ,R',m'] using hR.shift
  have b := observation_bound_at z' R' B' m' x' (var 0) hB' hm' hz'
  have res := bounded_radius_mono _ _ _ one one hm' (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) hR') b
  simpa [GaussianRadiusExponentialName.boundedSamples,Syn.shift,Δ,z',R',B',m',x',one] using res

theorem natural_code_bound (k : PTm n) : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (scale k oneCode) (k*one) :=
  le_congr ((normSq_scale k oneCode).eqTrans
      (congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one)).eqSymm (by ipra_ring) (le_refl (k*k*one))

theorem t4_argument_input (z R B K x : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    (input nameF one (data z R B (GaussianSineProductT4Budget.multiple R K) x)) ⋏
      observationBound nameF (data z R B (GaussianSineProductT4Budget.multiple R K) x)
        (num 4*R) (GaussianSineProductT4Budget.multiple R K) :=
  .andI (unit_disk_input _ _ _ _ _ hB (GaussianSineProductT4Budget.multiple_positive R K) hz
    (GaussianSineProductT4Budget.argument_disk R K hR hK))
    (observation_bound _ _ _ _ _ hB (GaussianSineProductT4Budget.multiple_positive R K) hz)

theorem t4_root_input (k R K x : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) (hk : Γ ⊢[PRAAx] le k K) : Γ ⊢[PRAAx]
    (input nameF one (data (scale k oneCode) k one (GaussianSineProductT4Budget.multiple R K) x)) ⋏
      observationBound nameF (data (scale k oneCode) k one (GaussianSineProductT4Budget.multiple R K) x)
        (num 4*k) (GaussianSineProductT4Budget.multiple R K) :=
  .andI (unit_disk_input _ _ _ _ _ (le_refl one) (GaussianSineProductT4Budget.multiple_positive R K)
    (natural_code_bound k) (GaussianSineProductT4Budget.root_disk R K k hR hK hk))
    (observation_bound _ _ _ _ _ (le_refl one) (GaussianSineProductT4Budget.multiple_positive R K) (natural_code_bound k))

theorem actual_scaled_pi_argument_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 2) ⋏ le one (var 1)) ⟶ ComplexLogarithmRemainder.bounded (var 4) (var 3*var 2) ⟶
      observationBound nameF (data (var 4) (var 3) (var 2) (var 1) (var 0)) (num 4*var 3) (var 1)) :=
  closeUniv 5 (.impI (.impI (observation_bound _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSineProductScaledArguments
