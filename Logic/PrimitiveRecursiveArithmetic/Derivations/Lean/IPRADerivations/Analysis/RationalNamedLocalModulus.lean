import IPRADerivations.Analysis.RationalNestedConvexDistance
import IPRADerivations.Analysis.RationalIntervalPowerComparison

/-!
# The named local modulus from the two actual power comparisons

The two multiplicative hypotheses are comparisons of the cofinal
midpoints of the actual power and product intervals. Reflecting them
at one computed precision gives the exact two secants. The original
modulus then bounds both cross-endpoint differences of the named values
with no residual finite-sampling error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalNamedLocalModulus

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (succ zero)
open RationalConvexSecantWeights (leftPoint rightPoint leftRemainder rightRemainder displacement)
open RationalConvexFiniteModulus (samplePrecision withinModulus)
open RationalNestedIntervals (centerF read)
open RationalNestedConvexModulus (pointInputs geometry afterWitnesses witnessIndex witnessExponent witnessFloor
  endpointSecants interior)
open RationalNestedConvexDistance (comparisonPrecision precise_named_comparison errorCapacity)
open RationalIntervalPowerComparison (centerOrder multiplicative_of_center_order positive_witness_refine)
open RationalValueBounds (upper)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def powerComparisons (L U : PR 3) (D P Q X Y o x : PTm n) : Fm PTm n :=
  centerOrder L U (interior D Y) (leftPoint D P) (interior D X)
    (leftRemainder P X) (displacement X Y) o x ⋏
  centerOrder L U (interior D X) (rightPoint D Q) (interior D Y)
    (rightRemainder D Q Y) (displacement X Y) o x

def crossBounds (L U : PR 3) (D X Y k i j x : PTm n) : Fm PTm n :=
  upper (read L (interior D X) i x) (read U (interior D Y) j x) one (pw two k) ⋏
  upper (read L (interior D Y) j x) (read U (interior D X) i x) one (pw two k)

def barycentric (w a b X Y Z : PTm n) : Fm PTm n :=
  RationalConvexSecants.scale w Z ≐ RationalMultiplicativeConvexity.weighted a b X Y

theorem barycentric_of_natural (w a b X Y Z A B C D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D)
    (hx : Γ ⊢[PRAAx] RationalArithmetic.represents X (ZT.ofNat A) D)
    (hy : Γ ⊢[PRAAx] RationalArithmetic.represents Y (ZT.ofNat B) D)
    (hz : Γ ⊢[PRAAx] RationalArithmetic.represents Z (ZT.ofNat C) D)
    (h : Γ ⊢[PRAAx] w*C ≐ a*A+b*B) : Γ ⊢[PRAAx] barycentric w a b X Y Z := by
  open RationalConvexSecants in
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _) (RationalArithmetic.add_guard _ _)
    (multiply_natural_representation w Z C D hz)
    (add_natural_representation _ _ _ _ D hD (multiply_natural_representation a X A D hx)
      (multiply_natural_representation b Y B D hy)) hD hD
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  rw [natEq h]

theorem original_barycenters (D P Q X Y : PTm n) (h : Γ ⊢[PRAAx] geometry D P Q X Y) :
    Γ ⊢[PRAAx] barycentric (RationalConvexSecantWeights.leftWidth P Y) (leftRemainder P X) (displacement X Y)
      (interior D Y) (leftPoint D P) (interior D X) ⋏
      barycentric (RationalConvexSecantWeights.rightWidth D Q X) (rightRemainder D Q Y) (displacement X Y)
        (interior D X) (rightPoint D Q) (interior D Y) := by
  let E := two*D
  have e : Γ ⊢[PRAAx] le one E := RationalAlgebra.positive_product (le_succ_self one) h.andE₁
  have rep (n : PTm _) : Γ ⊢[PRAAx] RationalArithmetic.represents (interior D n) (ZT.ofNat (two*n)) E :=
    GaussianRationalHorner.scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp only [ZT.toZ_mul,ZT.toZ_ofNat,LeanProofs.IPRA.Q.mk_mul,map_mul]
      ring) (mul_comm D two)
      (GaussianRationalHorner.scalar_rescale _ _ _ two (RationalCubeMidpoint.fraction_represents n D h.andE₁))
  exact .andI (barycentric_of_natural _ _ _ _ _ _ _ _ _ E e (rep Y) (RationalCubeMidpoint.fraction_represents P E e)
    (rep X) (RationalConvexSecantWeights.left_barycenter P X Y h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁))
    (barycentric_of_natural _ _ _ _ _ _ _ _ _ D h.andE₁
      (RationalCubeMidpoint.fraction_represents X D h.andE₁)
      (RationalCubeMidpoint.fraction_represents (Q+D) D h.andE₁)
      (RationalCubeMidpoint.fraction_represents Y D h.andE₁)
      (RationalConvexSecantWeights.right_barycenter D Q X Y h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂))

theorem offset_below_precision (L U : PR 3) (W : PR 2) (D P Q X Y k i j o x : PTm n) :
    Γ ⊢[PRAAx] le o (samplePrecision X Y (comparisonPrecision L U W D P Q X Y k i j o x)) := by
  let A := errorCapacity (read L (interior D X) i x) (read U (interior D Y) j x) k
  let B := errorCapacity (read L (interior D Y) j x) (read U (interior D X) i x) k
  let T := displacement X Y
  let F := witnessFloor W D P Q X Y x
  change Γ ⊢[PRAAx] le o (F+o+i+j+A+B+T)
  ipra_le 𝔟 F+𝔟 i+𝔟 j+𝔟 A+𝔟 B+𝔟 T

theorem actual_endpoint_secants (L U : PR 3) (W : PR 2) (D P Q X Y o p x : PTm n)
    (hpts : Γ ⊢[PRAAx] pointInputs L U W D P Q X Y x)
    (ho : Γ ⊢[PRAAx] afterWitnesses W D P Q X Y o x) (hp : Γ ⊢[PRAAx] le o p)
    (hc : Γ ⊢[PRAAx] powerComparisons L U D P Q X Y o x) :
    Γ ⊢[PRAAx] endpointSecants L U D P Q X Y p x := by
  let A := leftPoint D P
  let B := rightPoint D Q
  let F := interior D X
  let G := interior D Y
  let sa := witnessExponent W A x
  let sb := witnessExponent W B x
  let sf := witnessExponent W F x
  let sg := witnessExponent W G x
  have a := hpts.andE₁
  have b := hpts.andE₂.andE₁
  have f := hpts.andE₂.andE₂.andE₁
  have g := hpts.andE₂.andE₂.andE₂
  have pa := positive_witness_refine L U A (witnessIndex W A x) o sa x a.andE₁ a.andE₂ ho.andE₁
  have pb := positive_witness_refine L U B (witnessIndex W B x) o sb x b.andE₁ b.andE₂ ho.andE₂.andE₁
  have pf := positive_witness_refine L U F (witnessIndex W F x) o sf x f.andE₁ f.andE₂ ho.andE₂.andE₂.andE₁
  have pg := positive_witness_refine L U G (witnessIndex W G x) o sg x g.andE₁ g.andE₂ ho.andE₂.andE₂.andE₂
  exact .andI (multiplicative_of_center_order L U G A F (leftRemainder P X) (displacement X Y) o p sg sa sf x
    g.andE₁ a.andE₁ f.andE₁ pg pa pf hp hc.andE₁)
    (multiplicative_of_center_order L U F B G (rightRemainder D Q Y) (displacement X Y) o p sf sb sg x
      f.andE₁ b.andE₁ g.andE₁ pf pb pg hp hc.andE₂)

theorem exact_named_local_modulus (L U : PR 3) (W : PR 2) (D P Q X Y k i j o x : PTm n)
    (h : Γ ⊢[PRAAx] geometry D P Q X Y) (hpts : Γ ⊢[PRAAx] pointInputs L U W D P Q X Y x)
    (ho : Γ ⊢[PRAAx] afterWitnesses W D P Q X Y o x) (hc : Γ ⊢[PRAAx] powerComparisons L U D P Q X Y o x)
    (ht : Γ ⊢[PRAAx] withinModulus (centerF L U) D P Q X Y k x) : Γ ⊢[PRAAx] crossBounds L U D X Y k i j x :=
  precise_named_comparison L U W D P Q X Y k i j o x h hpts ht
    (actual_endpoint_secants L U W D P Q X Y o _ x hpts ho
      (offset_below_precision L U W D P Q X Y k i j o x) hc)

/-- A cross-endpoint comparison and the two original widths yield the midpoint comparison. -/
theorem centers_of_cross (L U : PR 3) (q z p k x : PTm n)
    (hr : Γ ⊢[PRAAx] RationalNestedIntervals.regular L U q x)
    (hs : Γ ⊢[PRAAx] RationalNestedIntervals.regular L U z x)
    (h : Γ ⊢[PRAAx] upper (read L q p x) (read U z p x) one (pw two k)) :
    Γ ⊢[PRAAx] upper (RationalNestedIntervals.center L U q p x) (RationalNestedIntervals.center L U z p x)
      (pw two k+pw two p) (pw two k*pw two p) := by
  let K := pw two k
  let S := pw two p
  let A := RationalNestedIntervals.center L U q p x
  let B := RationalNestedIntervals.center L U z p x
  have qW := (RationalNestedIntervals.step_at L U q p x hr).andE₂.andE₂.andE₂
  have zW := (RationalNestedIntervals.step_at L U z p x hs).andE₂.andE₂.andE₂
  have ha : Γ ⊢[PRAAx] upper A (read L q p x) one (two*S) :=
    RationalCubeInfimumName.midpoint_half_left _ _ _ _ qW
  have hb : Γ ⊢[PRAAx] upper (read U z p x) B one (two*S) :=
    RationalCubeInfimumName.midpoint_half_right _ _ _ _ zW
  have hsk := RationalConvexIntervalBounds.half_width_positive (Γ := Γ) p
  have Dpos := RationalAlgebra.positive_product (RationalAlgebra.positive_product hsk
    (RationalConvexFiniteModulus.power_positive (Γ := Γ) k)) hsk
  have first := RationalValueBounds.upper_triangle A (read L q p x) (read U z p x) one (two*S) one K ha h
  have next := RationalValueBounds.upper_triangle A (read U z p x) B (one*K+one*(two*S)) ((two*S)*K)
    one (two*S) first hb
  exact RationalValueBounds.upper_mono _ _ _ _ _ _ Dpos next (le_of_eq_add (d := zero) (by ipra_ring))

theorem named_center_modulus (L U : PR 3) (W : PR 2) (D P Q X Y k t o x : PTm n)
    (h : Γ ⊢[PRAAx] geometry D P Q X Y) (hpts : Γ ⊢[PRAAx] pointInputs L U W D P Q X Y x)
    (ho : Γ ⊢[PRAAx] afterWitnesses W D P Q X Y o x) (hc : Γ ⊢[PRAAx] powerComparisons L U D P Q X Y o x)
    (ht : Γ ⊢[PRAAx] withinModulus (centerF L U) D P Q X Y k x) :
    Γ ⊢[PRAAx] RationalValueBounds.radius
      (RationalNestedIntervals.center L U (interior D X) (succ (succ t)) x)
      (RationalNestedIntervals.center L U (interior D Y) (succ (succ t)) x)
      (pw two k+pw two t) (pw two k*pw two t) := by
  let p := succ (succ t)
  let F := interior D X
  let G := interior D Y
  let K := pw two k
  let S := pw two p
  let T := pw two t
  have hh := exact_named_local_modulus L U W D P Q X Y k p p o x h hpts ho hc ht
  have hx := hpts.andE₂.andE₂.andE₁.andE₁
  have hy := hpts.andE₂.andE₂.andE₂.andE₁
  have hf := centers_of_cross L U F G p k x hx hy hh.andE₁
  have hg := centers_of_cross L U G F p k x hy hx hh.andE₂
  have hs : Γ ⊢[PRAAx] le T S := by
    have e₁ := natEq (pw_succ (Γ := Γ) two t)
    have e₂ := natEq (pw_succ (Γ := Γ) two (succ t))
    change Γ ⊢[PRAAx] le (pw two t) (pw two (succ (succ t)))
    ipra_le 3*𝔟 (pw two t) using linear_combination 2*e₁+e₂
  have Bpos := RationalAlgebra.positive_product (RationalConvexFiniteModulus.power_positive (Γ := Γ) k)
    (RationalConvexFiniteModulus.power_positive p)
  have budget : Γ ⊢[PRAAx] le ((K+S)*(K*T)) ((K+T)*(K*S)) := by ipra_le 𝔟 K*𝔟 K*sl hs
  exact RationalValueBounds.radius_of_upper _ _ _ _
    (RationalValueBounds.upper_mono _ _ _ _ _ _ Bpos hf budget)
    (RationalValueBounds.upper_mono _ _ _ _ _ _ Bpos hg budget)

theorem actual_named_convex_local_modulus_closed (L U : PR 3) (W : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((geometry (var 0) (var 1) (var 2) (var 3) (var 4) ⋏ pointInputs L U W (var 0) (var 1) (var 2) (var 3) (var 4) (var 9)) ⟶
      (afterWitnesses W (var 0) (var 1) (var 2) (var 3) (var 4) (var 8) (var 9) ⋏
        powerComparisons L U (var 0) (var 1) (var 2) (var 3) (var 4) (var 8) (var 9)) ⟶
      withinModulus (centerF L U) (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 9) ⟶
      crossBounds L U (var 0) (var 3) (var 4) (var 5) (var 6) (var 7) (var 9)) :=
  closeUniv 10 (.impI (.impI (.impI (exact_named_local_modulus L U W _ _ _ _ _ _ _ _ _ _
    hyp2.andE₁ hyp2.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))))

theorem actual_named_center_modulus_closed (L U : PR 3) (W : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((geometry (var 0) (var 1) (var 2) (var 3) (var 4) ⋏ pointInputs L U W (var 0) (var 1) (var 2) (var 3) (var 4) (var 8)) ⟶
      (afterWitnesses W (var 0) (var 1) (var 2) (var 3) (var 4) (var 7) (var 8) ⋏
        powerComparisons L U (var 0) (var 1) (var 2) (var 3) (var 4) (var 7) (var 8)) ⟶
      withinModulus (centerF L U) (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 8) ⟶
      RationalValueBounds.radius
        (RationalNestedIntervals.center L U (interior (var 0) (var 3)) (succ (succ (var 6))) (var 8))
        (RationalNestedIntervals.center L U (interior (var 0) (var 4)) (succ (succ (var 6))) (var 8))
        (pw two (var 5)+pw two (var 6)) (pw two (var 5)*pw two (var 6))) :=
  closeUniv 9 (.impI (.impI (.impI (named_center_modulus L U W _ _ _ _ _ _ _ _ _
    hyp2.andE₁ hyp2.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalNamedLocalModulus
