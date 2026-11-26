import IPRADerivations.Analysis.Names.Apartness.GaussianNamedPositiveReciprocal
import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGamma

/-!
# Named rescaled half-plane input for Euler power damping

Multiplying the original encoded z/B by the actual positive reciprocal
sampler gives a regular name for z/r. The original lower margin 1/A
and the upper bound T for r give the explicit margin 1/(T*A).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingParameter

open_ipra
open GaussianNamedPositiveReciprocal (swapped_domain)
open GaussianNamedRightHalfPlane (marginPoint certificate)
open GaussianNamedPositiveLogarithm (numerator denominator)
open GaussianRationalMetric (bounded)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at)
open ComplexLogarithmRemainder (re oneCode)
open RationalValueBounds (upper upper_of_order upper_congr upper_mono)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev nameF (f : PR 2) : PR 2 :=
  GaussianBoundedConstantProductName.nameF (GaussianNamedPositiveReciprocal.nameF f)
def data (z R B x E : PTm n) : PTm n :=
  GaussianBoundedConstantProductName.data R (ofGaussian z B) (GaussianNamedPositiveReciprocal.data x E)

def source (f : PR 2) (z R B A x E T : PTm n) : Fm PTm n :=
  GaussianEulerIntegralGammaIdentification.source z R B A ⋏
    (le one T ⋏ GaussianNamedPositiveLogarithm.source f x E T)

ipra_subst data

theorem regular (f : PR 2) (z R B A x E T : PTm n) (hs : Γ ⊢[PRAAx] source f z R B A x E T) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data z R B x E) := by
  have orig := hs.andE₁.andE₁.andE₂.andE₁
  have coeff : Γ ⊢[PRAAx] bounded (ofGaussian z B) R one :=
    GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ orig.andE₁ (le_refl one)
      (ofGaussian_represents z B orig.andE₁) (le_congr (by ipra_ring) (by ipra_ring) orig.andE₂)
  exact GaussianBoundedConstantProductName.name_regular _ _ _ _
    (.andI (GaussianNamedPositiveReciprocal.name_regular f x E T hs.andE₂.andE₂) coeff)

private theorem native_margin (z A B : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.realLower z A B) :
    Γ ⊢[PRAAx] upper (fstT (marginPoint A)) (fstT (ofGaussian z B)) zero one := by
  have margin : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (marginPoint A)) (ZT.ofNat one) A :=
    GaussianRationalHorner.scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp only [GaussianRootAlgebra.re_one,ZT.toZ_ofNat]
      ipra_simps
      ring) (.eqRefl _) (ofGaussian_represents oneCode A hA).andE₁
  have order := PolynomialBisection.zle_congr
    (by simp only [ZT.toZ_mul,ZT.toZ_ofNat]; ipra_simps; ring :
      ZT.toZ Γ (ZT.ofNat B) = ZT.toZ Γ (ZT.ofNat one*ZT.ofNat B))
    (by simp only [ZT.toZ_mul,ZT.toZ_ofNat]; ring :
      ZT.toZ Γ (ZT.ofNat A*re z) = ZT.toZ Γ (re z*ZT.ofNat A)) h
  exact upper_of_order _ _ zero one (RationalArithmetic.order_of_representations _ _ _ _ _ _
    margin (ofGaussian_represents z B hB).andE₁ hA hB order)

theorem sample_margin (f : PR 2) (p z R B A x E T : PTm n)
    (hs : Γ ⊢[PRAAx] source f z R B A x E T) : Γ ⊢[PRAAx]
    upper (fstT (marginPoint (T*A))) (fstT (ap2 (nameF f) p (data z R B x E))) zero one := by
  let g := GaussianNamedPositiveReciprocal.nameF f
  let r := GaussianBoundedConstantProductName.clock p R
  let s := GaussianNamedPositiveReciprocal.clock r E
  let a := denominator f s x
  let b := numerator f s x
  have positive := swapped_domain f r x E T hs.andE₂.andE₂
  have hB := hs.andE₁.andE₁.andE₂.andE₁.andE₁
  have input : Γ ⊢[PRAAx] GaussianEulerPowerScalingParameter.source z R B A b a E T :=
    .andI hs.andE₁ (.andI positive.andE₁.andE₂ (.andI positive.andE₁.andE₁
      (.andI hs.andE₂.andE₂.andE₂.andE₁ (.andI hs.andE₂.andE₁
        (.andI positive.andE₂.andE₂ positive.andE₂.andE₁)))))
  have encoded := GaussianEulerPowerScalingParameter.original_rescaled_source z R B A b a E T input
  have value := (GaussianBoundedConstantProductName.sample_at g p R (ofGaussian z B)
      (GaussianNamedPositiveReciprocal.data x E)).eqTrans
    ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
      (GaussianNamedPositiveReciprocal.name_at f r x E)).eqTrans
      (GaussianEulerPowerScalingParameter.original_rescaled_value z B b a hB positive.andE₁.andE₂))
  exact upper_congr (.eqRefl _) (congrFst value).eqSymm (.eqRefl _) (.eqRefl _)
    (native_margin _ _ _ encoded.andE₁.andE₁ encoded.andE₁.andE₂.andE₁.andE₁ encoded.andE₁.andE₂.andE₂)

theorem named_half_plane (f : PR 2) (z R B A x E T : PTm n)
    (hs : Γ ⊢[PRAAx] source f z R B A x E T) : Γ ⊢[PRAAx]
    GaussianNamedRightHalfPlane.source (nameF f) (data z R B x E) (T*A) := by
  have margin := positive_product T A hs.andE₂.andE₁ hs.andE₁.andE₁.andE₁
  refine .andI (regular f z R B A x E T hs) (.andI margin (.allI (.allI ?_)))
  let sh (x : PTm n) := Syn.shift (Syn.shift x)
  have shifted : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh z) (sh R) (sh B) (sh A) (sh x) (sh E) (sh T) := by
    simpa [source,Fm.shift,Syn.shift,one,sh] using hs.shift.shift
  let y := data (sh z) (sh R) (sh B) (sh x) (sh E)
  let m := marginPoint (sh T*sh A)
  have orig := sample_margin f (var 0) (sh z) (sh R) (sh B) (sh A) (sh x) (sh E) (sh T) shifted
  have later := upper_mono _ _ zero one (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))
    (le_refl one) orig (le_congr (zero_mul _).eqSymm (.eqRefl _) (zero_le _))
  have moved := upper_congr (congrFst (constant_at (var 1) m)).eqSymm
    (.eqRefl (fstT (ap2 (nameF f) (var 0) y))) (.eqRefl _) (.eqRefl _) later
  simpa only [certificate,GaussianNamedPositiveExponentialOrder.realOrder,Syn.shift,subst_data,
    GaussianNamedRightHalfPlane.subst_marginPoint,LeanProofs.IPRA.PTm.subst_mul,sh,y,m] using moved

theorem actual_named_power_damping_rescaled_half_plane_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      GaussianNamedRightHalfPlane.source (nameF f) (data (var 0) (var 1) (var 2) (var 4) (var 5)) (var 6*var 3)) :=
  closeUniv 7 (.impI (named_half_plane f _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingParameter
