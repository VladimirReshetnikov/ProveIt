import IPRADerivations.Analysis.Optimization.Convexity.Moduli.RationalConvexEndpointBudget

/-!
# The computed local modulus on actual rational samples

The sample precision is `e+T` for a desired additional error `2^(-e)`
and the actual cleared displacement `T`. Both secants at that precision,
with their finite tolerance, give the original dyadic conclusion with
that additional error. Endpoint bounds are computed from precision zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalConvexFiniteModulus

open_ipra
open RationalCubeMidpoint (fraction fraction_represents)
open RationalSupMetric (denominatorOf)
open RationalArgmin (rationalLE denominator_positive)
open RationalArithmetic (represents add)
open GaussianRationalSyntheticBounds (natCode natCode_represents)
open GaussianRationalHorner (scalar_congr scalar_rescale)
open RationalConvexSecants (bound nonnegative scale affine naturalNumerator rescaled_representation
  multiply_natural_representation add_natural_representation affine_representation compare_same_to_natural compare_same_from_natural)
open RationalConvexSecantWeights (margin margin_positive modulus dyadic_secant displacement leftPoint rightPoint
  leftWidth rightWidth leftRemainder rightRemainder)
open RationalConvexEndpointBudget (sample M localModulus actual_two_endpoint_sample_bounds)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def eps (p : PTm n) : PTm n := fraction one (pw two p)
def endpoint (m p : PTm n) : PTm n := add (natCode m) (eps p)
def precision (T e : PTm n) : PTm n := e+T
def allowance (k e : PTm n) : PTm n := add (eps k) (eps e)

theorem power_positive (p : PTm n) : Γ ⊢[PRAAx] le one (pw two p) :=
  GaussianPolynomialPerturbation.power_positive two p (le_succ_self one)

theorem eps_nonnegative (p : PTm n) : Γ ⊢[PRAAx] nonnegative (eps p) := by
  apply GaussianRationalMetric.comparison_of_cleared _ _ zero one one (pw two p)
    (le_refl _) (power_positive p) (natCode_represents zero) (fraction_represents _ _ (power_positive p))
  exact le_congr (mul_zero _).eqSymm (one_mul _).eqSymm (zero_le _)

theorem endpoint_nonnegative (m p : PTm n) : Γ ⊢[PRAAx] nonnegative (endpoint m p) := by
  have h := GaussianRationalSyntheticBounds.add_monotone (Γ := Γ) (natCode zero) (natCode m) (natCode zero) (eps p)
    (GaussianRationalSyntheticBounds.natCode_order zero m (zero_le _)) (eps_nonnegative p)
  exact RationalArgmin.rationalLE_congr ((GaussianRationalSyntheticBounds.natCode_add zero zero).eqTrans
    (GaussianRationalSyntheticBounds.natCode_congr (add_zero zero))) (.eqRefl _) h

theorem rescale_natural (q a t D J : PTm n) (hq : Γ ⊢[PRAAx] represents q (ZT.ofNat a) D)
    (hJ : Γ ⊢[PRAAx] D*t ≐ J) : Γ ⊢[PRAAx] represents q (ZT.ofNat (a*t)) J := by
  refine scalar_congr (.eqRefl _) ?_ hJ (scalar_rescale q (ZT.ofNat a) D t hq)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]

theorem eps_representation (p t J : PTm n) (hJ : Γ ⊢[PRAAx] pw two p*t ≐ J) :
    Γ ⊢[PRAAx] represents (eps p) (ZT.ofNat t) J := by
  refine scalar_congr (.eqRefl _) ?_ (.eqRefl J)
    (rescale_natural (eps p) one t (pw two p) J (fraction_represents one _ (power_positive p)) hJ)
  apply ZT.derive
  simp only [ZT.toZ_ofNat]
  exact natEq (one_mul t)

theorem integer_representation (m J : PTm n) : Γ ⊢[PRAAx] represents (natCode m) (ZT.ofNat (m*J)) J :=
  rescale_natural (natCode m) m J one J (natCode_represents m) (one_mul J)

theorem remove_sample_weights (δ T U V M J K E R : PTm n) (hδ : Γ ⊢[PRAAx] le one δ)
    (hgeom : Γ ⊢[PRAAx] le (M*T*J) (δ*K)) (herror : Γ ⊢[PRAAx] le (succ T*R) E)
    (h : Γ ⊢[PRAAx] le (δ*V) (δ*U+T*(M*J+R)+δ*R)) : Γ ⊢[PRAAx] le V (U+(K+E)) := by
  have hT : Γ ⊢[PRAAx] le ((T+δ)*R) (δ*E) := by
    ipra_le 𝔟 δ*sl herror + 𝔟 T*𝔟 R*sl hδ
  have hs : Γ ⊢[PRAAx] le (δ*V) (δ*(U+(K+E))) := by ipra_le sl h + sl hgeom + sl hT
  exact RationalValueBounds.positive_cancel hδ hs

theorem rational_sample_clock (D P m k T e U V : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hP : Γ ⊢[PRAAx] le one P)
    (ht : Γ ⊢[PRAAx] le (T*pw two (modulus D P m k)) (two*D))
    (hU : Γ ⊢[PRAAx] nonnegative U) (hV : Γ ⊢[PRAAx] nonnegative V)
    (hv : Γ ⊢[PRAAx] bound (margin D P) T U V (endpoint m (precision T e)) (eps (precision T e))) :
    Γ ⊢[PRAAx] rationalLE V (add U (allowance k e)) := by
  let p := precision T e
  let a := denominatorOf U
  let b := denominatorOf V
  let C := a*b
  let K := pw two k
  let E := pw two e
  let R := pw two p
  let J := C*K*E*R
  let jK := C*E*R
  let jE := C*K*R
  let jR := C*K*E
  let δ := margin D P
  have prod {A B : PTm n} := @RationalAlgebra.positive_product n Γ A B
  have hJ : Γ ⊢[PRAAx] le one J := prod
    (prod (prod (prod (denominator_positive U) (denominator_positive V)) (power_positive k)) (power_positive e))
    (power_positive p)
  have ru := rescaled_representation U (b*K*E*R) J hU (by dsimp [J,C,a,b,K,E,R]; ipra_ring)
  have rv := rescaled_representation V (a*K*E*R) J hV (by dsimp [J,C,a,b,K,E,R]; ipra_ring)
  have rk := eps_representation (Γ := Γ) k jK J (by dsimp [jK,J,K,E,R]; ipra_ring)
  have re := eps_representation (Γ := Γ) e jE J (by dsimp [jE,J,K,E,R]; ipra_ring)
  have rr := eps_representation (Γ := Γ) p jR J (by dsimp [jR,J,K,E,R]; ipra_ring)
  have rm := add_natural_representation (natCode m) (eps p) _ _ J hJ (integer_representation m J) rr
  have h₁ := compare_same_to_natural _ _ _ _ J hJ (multiply_natural_representation δ V _ J rv)
    (affine_representation δ T δ U (endpoint m p) (eps p) _ _ _ J hJ ru rm rr) hv
  have hg : Γ ⊢[PRAAx] le (m*T*J) (δ*jK) :=
    le_congr (by dsimp [J,jK,K,E,R]; ipra_ring) (.eqRefl _)
      (mul_le_mul_right jK (dyadic_secant D P m k T hD hP ht))
  have ep : Γ ⊢[PRAAx] R ≐ E*pw two T := pw_add two e T
  have he : Γ ⊢[PRAAx] le (succ T*jR) jE := by
    have base := mul_le_mul_right (C*K*E) (Foundations.DyadicGain.amplitude_reserve (Γ := Γ) T)
    exact le_congr (.eqRefl _) ((show Γ ⊢[PRAAx] pw two T*(C*K*E) ≐ C*K*(E*pw two T) by ipra_ring).eqTrans
      (congrMul (.eqRefl (C*K)) ep.eqSymm)) base
  have hn := remove_sample_weights δ T _ _ m J jK jE jR (margin_positive D P hD hP) hg he h₁
  exact compare_same_from_natural _ _ _ _ J hJ rv
    (add_natural_representation U (allowance k e) _ _ J hJ ru
      (add_natural_representation (eps k) (eps e) _ _ J hJ rk re)) hn

def samplePrecision (X Y e : PTm n) : PTm n := precision (displacement X Y) e
def atLeft (A : PR 3) (D P X Y e x : PTm n) : PTm n :=
  sample A (leftPoint D P) (samplePrecision X Y e) x
def atRight (A : PR 3) (D Q X Y e x : PTm n) : PTm n :=
  sample A (rightPoint D Q) (samplePrecision X Y e) x
def atInterior (A : PR 3) (D Z X Y e x : PTm n) : PTm n :=
  sample A (fraction Z D) (samplePrecision X Y e) x

def endpointRegular (A : PR 3) (q p x : PTm n) : Fm PTm n :=
  RationalValueBounds.upper (sample A q p x) (sample A q zero x) (pw two p+one) (pw two p)

def finiteInput (A : PR 3) (D P Q X Y e x : PTm n) : Fm PTm n :=
  let a := atLeft A D P X Y e x
  let b := atRight A D Q X Y e x
  let u := atInterior A D X X Y e x
  let v := atInterior A D Y X Y e x
  let p := samplePrecision X Y e
  let T := displacement X Y
  (le one D ⋏ (le one P ⋏ (le P X ⋏ (le X Y ⋏ le Y Q)))) ⋏
    ((nonnegative a ⋏ (nonnegative u ⋏ (nonnegative v ⋏ nonnegative b))) ⋏
      ((endpointRegular A (leftPoint D P) p x ⋏ endpointRegular A (rightPoint D Q) p x) ⋏
        (RationalConvexSecants.within (leftWidth P Y) T (leftRemainder P X) v u a (eps p) ⋏
          RationalConvexSecants.within (rightWidth D Q X) T (rightRemainder D Q Y) u v b (eps p))))

def withinModulus (A : PR 3) (D P Q X Y k x : PTm n) : Fm PTm n :=
  le (displacement X Y*pw two (localModulus A D P Q k x)) (two*D)

def sampleConclusion (A : PR 3) (D X Y k e x : PTm n) : Fm PTm n :=
  let u := atInterior A D X X Y e x
  let v := atInterior A D Y X Y e x
  rationalLE u (add v (allowance k e)) ⋏ rationalLE v (add u (allowance k e))

theorem actual_local_sample_bound (A : PR 3) (D P Q X Y k e x : PTm n)
    (h : Γ ⊢[PRAAx] finiteInput A D P Q X Y e x) (ht : Γ ⊢[PRAAx] withinModulus A D P Q X Y k x) :
    Γ ⊢[PRAAx] sampleConclusion A D X Y k e x := by
  let p := samplePrecision X Y e
  let T := displacement X Y
  let a := atLeft A D P X Y e x
  let b := atRight A D Q X Y e x
  let u := atInterior A D X X Y e x
  let v := atInterior A D Y X Y e x
  let m := M A D P Q x
  have geom : Γ ⊢[PRAAx] le one D ⋏ (le one P ⋏ (le P X ⋏ (le X Y ⋏ le Y Q))) := h.andE₁
  have hn : Γ ⊢[PRAAx] nonnegative a ⋏ (nonnegative u ⋏ (nonnegative v ⋏ nonnegative b)) := h.andE₂.andE₁
  have reg := h.andE₂.andE₂.andE₁
  have secants := h.andE₂.andE₂.andE₂
  have hb := actual_two_endpoint_sample_bounds A D P Q p x reg.andE₁ reg.andE₂
  have full : Γ ⊢[PRAAx] RationalConvexSecants.nonnegativeSamples a u v b (endpoint m p) (eps p) :=
    .andI hn.andE₁ (.andI hn.andE₂.andE₁ (.andI hn.andE₂.andE₂.andE₁ (.andI hn.andE₂.andE₂.andE₂
      (.andI (endpoint_nonnegative m p) (eps_nonnegative p)))))
  have slopes := RationalConvexSecants.rational_two_endpoints D P Q X Y a u v b (endpoint m p) (eps p)
    geom.andE₂.andE₂.andE₁ geom.andE₂.andE₂.andE₂.andE₁ geom.andE₂.andE₂.andE₂.andE₂
    full hb.andE₁ hb.andE₂ secants.andE₁ secants.andE₂
  exact .andI
    (rational_sample_clock D P m k T e v u geom.andE₁ geom.andE₂.andE₁ ht hn.andE₂.andE₂.andE₁ hn.andE₂.andE₁ slopes.andE₁)
    (rational_sample_clock D P m k T e u v geom.andE₁ geom.andE₂.andE₁ ht hn.andE₂.andE₁ hn.andE₂.andE₂.andE₁ slopes.andE₂)

theorem actual_convex_local_sample_modulus_closed (A : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (finiteInput A (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 7) ⟶
      withinModulus A (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7) ⟶
      sampleConclusion A (var 0) (var 3) (var 4) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (.impI (.impI (actual_local_sample_bound A _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalConvexFiniteModulus
