import IPRADerivations.Analysis.Optimization.Convexity.RationalNestedConvexModulus

/-!
# Exact named distance from the original convex sampling bound

The comparison is between any lower endpoint of one original name and
any upper endpoint of the other. A computed common sample precision
dominates the two endpoint indices and all four positivity witnesses.
At that precision the auxiliary dyadic sampling error is smaller than
the least possible strict gap in the requested exact comparison.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalNestedConvexDistance

open_ipra
open RationalArgmin (rationalLE rationalLE_congr denominator_positive)
open RationalSupMetric (denominatorOf numeratorOf)
open RationalArithmetic (add represents)
open RationalValueBounds (upper crossLeft upper_order_left upper_order_right)
open RationalConvexFiniteModulus (eps power_positive allowance samplePrecision withinModulus)
open RationalNestedIntervals (read center center_at centerF center_in_interval)
open RationalNestedConvexModulus (pointInputs geometry afterWitnesses endpointSecants actual_named_samples
  witnessIndex witnessFloor witness_floor_bound interior)
open RationalConvexSecantWeights (displacement)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem allowance_representation (k e : PTm n) : Γ ⊢[PRAAx]
    represents (allowance k e) (ZT.ofNat (pw two k+pw two e)) (pw two k*pw two e) := by
  have h := RationalRepresentations.represents_add (Γ := Γ) (eps k) (eps e) _ _ _ _
    (RationalCubeMidpoint.fraction_represents one _ (power_positive k))
    (RationalCubeMidpoint.fraction_represents one _ (power_positive e))
  refine GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _) h
  ipra_lc

theorem upper_of_sample_allowance (a b k e : PTm n)
    (h : Γ ⊢[PRAAx] rationalLE a (add b (allowance k e))) :
    Γ ⊢[PRAAx] upper a b (pw two k+pw two e) (pw two k*pw two e) := by
  let K := pw two k
  let E := pw two e
  have hP := RationalAlgebra.positive_product (power_positive (Γ := Γ) k) (power_positive e)
  have r := RationalRepresentations.represents_add (Γ := Γ) b (allowance k e) _ _ _ _
    (RationalRepresentations.represents_self b) (allowance_representation k e)
  apply upper_order_left _ _ _ _ _ h
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ _ _ (K+E) (K*E)
    (RationalAlgebra.positive_product (denominator_positive b) hP) (denominator_positive b)
    r (RationalRepresentations.represents_self b)
  apply zle_of_toZ zero
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_ofNat]
  ipra_simps
  ring

def errorCapacity (a b k : PTm n) : PTm n := pw two k*denominatorOf a*denominatorOf b

theorem remove_extra_allowance (a b k e : PTm n)
    (he : Γ ⊢[PRAAx] le (errorCapacity a b k) e)
    (h : Γ ⊢[PRAAx] upper a b (pw two k+pw two e) (pw two k*pw two e)) :
    Γ ⊢[PRAAx] upper a b one (pw two k) := by
  let K := pw two k
  let E := pw two e
  let A := denominatorOf a
  let B := denominatorOf b
  have less : Γ ⊢[PRAAx] lt (K*A*B) E :=
    lt_of_le_of_lt he (LeanProofs.IPRA.AnalyticNumberTheory.Valuation.lt_pw (le_refl two) e)
  have raw : Γ ⊢[PRAAx] le ((K*crossLeft a b)*E)
      ((K*crossLeft b a+one*A*B)*E+K*A*B) :=
    le_congr (by dsimp only [K,E]; ipra_ring) (by dsimp only [K,E,A,B]; ipra_ring) h
  exact GapRemoval.gap_of less raw

def comparisonPrecision (L U : PR 3) (W : PR 2) (D P Q X Y k i j offset x : PTm n) : PTm n :=
  witnessFloor W D P Q X Y x+offset+i+j+
    errorCapacity (read L (interior D X) i x) (read U (interior D Y) j x) k+
    errorCapacity (read L (interior D Y) j x) (read U (interior D X) i x) k

theorem precise_named_comparison (L U : PR 3) (W : PR 2) (D P Q X Y k i j offset x : PTm n)
    (h : Γ ⊢[PRAAx] geometry D P Q X Y) (hpts : Γ ⊢[PRAAx] pointInputs L U W D P Q X Y x)
    (ht : Γ ⊢[PRAAx] withinModulus (centerF L U) D P Q X Y k x)
    (hs : Γ ⊢[PRAAx] endpointSecants L U D P Q X Y
      (samplePrecision X Y (comparisonPrecision L U W D P Q X Y k i j offset x)) x) :
    Γ ⊢[PRAAx] upper (read L (interior D X) i x) (read U (interior D Y) j x) one (pw two k) ⋏
      upper (read L (interior D Y) j x) (read U (interior D X) i x) one (pw two k) := by
  let X' := interior D X
  let Y' := interior D Y
  let a := read L X' i x
  let b := read U Y' j x
  let c := read L Y' j x
  let d := read U X' i x
  let W0 := witnessFloor W D P Q X Y x
  let ca := errorCapacity a b k
  let cb := errorCapacity c d k
  let e := comparisonPrecision L U W D P Q X Y k i j offset x
  let p := samplePrecision X Y e
  let t := displacement X Y
  have ead : Γ ⊢[PRAAx] e ≐ W0+offset+i+j+ca+cb := .eqRefl _
  have ei : Γ ⊢[PRAAx] le i p := by
    have ep := natEq (congrAdd ead (.eqRefl t))
    change Γ ⊢[PRAAx] le i (e+t)
    ipra_le 𝔟 W0+𝔟 offset+𝔟 j+𝔟 ca+𝔟 cb+𝔟 t using linear_combination ep
  have ej : Γ ⊢[PRAAx] le j p := by
    have ep := natEq (congrAdd ead (.eqRefl t))
    change Γ ⊢[PRAAx] le j (e+t)
    ipra_le 𝔟 W0+𝔟 offset+𝔟 i+𝔟 ca+𝔟 cb+𝔟 t using linear_combination ep
  have ea : Γ ⊢[PRAAx] le ca e := by
    have ee := natEq ead
    ipra_le 𝔟 W0+𝔟 offset+𝔟 i+𝔟 j+𝔟 cb using linear_combination ee
  have eb : Γ ⊢[PRAAx] le cb e := by
    have ee := natEq ead
    ipra_le 𝔟 W0+𝔟 offset+𝔟 i+𝔟 j+𝔟 ca using linear_combination ee
  have eq : Γ ⊢[PRAAx] W0+(offset+i+j+ca+cb+t) ≐ p :=
    (by ipra_ring : Γ ⊢[PRAAx] W0+(offset+i+j+ca+cb+t) ≐ (W0+offset+i+j+ca+cb)+t).eqTrans
      (congrAdd ead.eqSymm (.eqRefl t))
  have hp0 := witness_floor_bound (Γ := Γ) W D P Q X Y (offset+i+j+ca+cb+t) x
  have hp : Γ ⊢[PRAAx] afterWitnesses W D P Q X Y p x :=
    .andI (le_congr (.eqRefl _) eq hp0.andE₁)
      (.andI (le_congr (.eqRefl _) eq hp0.andE₂.andE₁)
        (.andI (le_congr (.eqRefl _) eq hp0.andE₂.andE₂.andE₁)
          (le_congr (.eqRefl _) eq hp0.andE₂.andE₂.andE₂)))
  have samples := actual_named_samples L U W D P Q X Y k e x h hpts hp hs ht
  have hx := center_in_interval L U X' i p x hpts.andE₂.andE₂.andE₁.andE₁ ei
  have hy := center_in_interval L U Y' j p x hpts.andE₂.andE₂.andE₂.andE₁ ej
  have ex := center_at (Γ := Γ) L U X' p x
  have ey := center_at (Γ := Γ) L U Y' p x
  have hab := upper_of_sample_allowance _ _ k e
    (rationalLE_congr ex (RationalAlgebra.add_congr ey (.eqRefl _)) samples.andE₁)
  have hcd := upper_of_sample_allowance _ _ k e
    (rationalLE_congr ey (RationalAlgebra.add_congr ex (.eqRefl _)) samples.andE₂)
  exact .andI (remove_extra_allowance a b k e ea
    (upper_order_left _ _ _ _ _ hx.andE₁ (upper_order_right _ _ _ _ _ hab hy.andE₂)))
    (remove_extra_allowance c d k e eb
      (upper_order_left _ _ _ _ _ hy.andE₁ (upper_order_right _ _ _ _ _ hcd hx.andE₂)))

theorem actual_excess_name_error_removal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (errorCapacity (var 0) (var 1) (var 2)) (var 3) ⟶
      upper (var 0) (var 1) (pw two (var 2)+pw two (var 3)) (pw two (var 2)*pw two (var 3)) ⟶
      upper (var 0) (var 1) one (pw two (var 2))) :=
  closeUniv 4 (.impI (.impI (remove_extra_allowance _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalNestedConvexDistance
