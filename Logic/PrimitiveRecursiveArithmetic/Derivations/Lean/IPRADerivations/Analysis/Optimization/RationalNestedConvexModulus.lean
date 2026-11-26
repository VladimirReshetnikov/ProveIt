import IPRADerivations.Analysis.Optimization.RationalConvexIntervalBounds

/-!
# The two-endpoint modulus for the actual midpoint sampler

The strong-positivity data are read from the original primitive-recursive
witness function. A common precision above all four witnesses permits
the use of the actual multiplicative endpoint comparisons. Those
comparisons supply the two finite secants and their sample tolerance;
no separate centered-sampler convexity or continuity law is required.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalNestedConvexModulus

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)
open RationalArgmin (rationalLE transitive rationalLE_congr)
open RationalConvexSecants (nonnegative within scale affine)
open RationalConvexSecantWeights (leftPoint rightPoint displacement leftWidth rightWidth leftRemainder rightRemainder
  left_width right_width)
open RationalNestedIntervals (read center centerF center_at regular positiveWitness nesting ordered step_at center_of_positive endpoint_regular)
open RationalConvexIntervalBounds (centered_secant)
open RationalMultiplicativeConvexity (multiplicative multiplicative_to_ordinary)
open RationalCubeMidpoint (fraction)
open RationalConvexFiniteModulus (eps finiteInput samplePrecision withinModulus sampleConclusion actual_local_sample_bound)
open RationalAlgebra (multiply_congr add_congr)
open GaussianRationalSyntheticBounds (natCode_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def witnessIndex (W : PR 2) (q x : PTm n) : PTm n := fstT (ap2 W q x)
def witnessExponent (W : PR 2) (q x : PTm n) : PTm n := sndT (ap2 W q x)
def presented (L U : PR 3) (W : PR 2) (q x : PTm n) : Fm PTm n :=
  regular L U q x ⋏ positiveWitness L q (witnessIndex W q x) (witnessExponent W q x) x

def interior (D X : PTm n) : PTm n := fraction X D

def witnessFloor (W : PR 2) (D P Q X Y x : PTm n) : PTm n :=
  witnessIndex W (leftPoint D P) x + witnessIndex W (rightPoint D Q) x +
    witnessIndex W (interior D X) x + witnessIndex W (interior D Y) x

def geometry (D P Q X Y : PTm n) : Fm PTm n :=
  le one D ⋏ (le one P ⋏ (le P X ⋏ (le X Y ⋏ le Y Q)))

def pointInputs (L U : PR 3) (W : PR 2) (D P Q X Y x : PTm n) : Fm PTm n :=
  presented L U W (leftPoint D P) x ⋏ (presented L U W (rightPoint D Q) x ⋏
    (presented L U W (interior D X) x ⋏ presented L U W (interior D Y) x))

def endpointSecants (L U : PR 3) (D P Q X Y p x : PTm n) : Fm PTm n :=
  multiplicative (leftRemainder P X) (displacement X Y)
    (read U (interior D Y) p x) (read U (leftPoint D P) p x) (read L (interior D X) p x) ⋏
  multiplicative (rightRemainder D Q Y) (displacement X Y)
    (read U (interior D X) p x) (read U (rightPoint D Q) p x) (read L (interior D Y) p x)

def afterWitnesses (W : PR 2) (D P Q X Y p x : PTm n) : Fm PTm n :=
  le (witnessIndex W (leftPoint D P) x) p ⋏
    (le (witnessIndex W (rightPoint D Q) x) p ⋏
      (le (witnessIndex W (interior D X) x) p ⋏ le (witnessIndex W (interior D Y) x) p))

theorem witness_floor_bound (W : PR 2) (D P Q X Y r x : PTm n) :
    Γ ⊢[PRAAx] afterWitnesses W D P Q X Y (witnessFloor W D P Q X Y x+r) x := by
  let A := witnessIndex W (leftPoint D P) x
  let B := witnessIndex W (rightPoint D Q) x
  let C := witnessIndex W (interior D X) x
  let E := witnessIndex W (interior D Y) x
  let K := witnessFloor W D P Q X Y x+r
  have ha : Γ ⊢[PRAAx] le A K := le_of_eq_add (d := B+C+E+r) (by dsimp only [K,witnessFloor]; ipra_ring)
  have hb : Γ ⊢[PRAAx] le B K := le_of_eq_add (d := A+C+E+r) (by dsimp only [K,witnessFloor]; ipra_ring)
  have hc : Γ ⊢[PRAAx] le C K := le_of_eq_add (d := A+B+E+r) (by dsimp only [K,witnessFloor]; ipra_ring)
  have he : Γ ⊢[PRAAx] le E K := le_of_eq_add (d := A+B+C+r) (by dsimp only [K,witnessFloor]; ipra_ring)
  exact .andI ha (.andI hb (.andI hc he))

theorem lower_nonnegative (L U : PR 3) (W : PR 2) (q p x : PTm n) (h : Γ ⊢[PRAAx] presented L U W q x)
    (hp : Γ ⊢[PRAAx] le (witnessIndex W q x) p) : Γ ⊢[PRAAx] nonnegative (read L q p x) :=
  transitive (RationalConvexFiniteModulus.eps_nonnegative _) (transitive h.andE₂
    (nesting L U q (witnessIndex W q x) p x h.andE₁ hp).andE₁)

theorem upper_nonnegative (L U : PR 3) (W : PR 2) (q p x : PTm n) (h : Γ ⊢[PRAAx] presented L U W q x)
    (hp : Γ ⊢[PRAAx] le (witnessIndex W q x) p) : Γ ⊢[PRAAx] nonnegative (read U q p x) :=
  transitive (lower_nonnegative L U W q p x h hp) (ordered L U q p x h.andE₁)

theorem actual_center_nonnegative (L U : PR 3) (W : PR 2) (q p x : PTm n)
    (h : Γ ⊢[PRAAx] presented L U W q x) (hp : Γ ⊢[PRAAx] le (witnessIndex W q x) p) :
    Γ ⊢[PRAAx] nonnegative (RationalConvexEndpointBudget.sample (centerF L U) q p x) :=
  rationalLE_congr (.eqRefl _) (center_at L U q p x).eqSymm
    (center_of_positive L U q (witnessIndex W q x) p (witnessExponent W q x) x h.andE₁ h.andE₂ hp)

theorem left_weight_positive (P X : PTm n) (hP : Γ ⊢[PRAAx] le one P)
    (hPX : Γ ⊢[PRAAx] le P X) : Γ ⊢[PRAAx] le one (leftRemainder P X) := by
  have less : Γ ⊢[PRAAx] le P (two*X) := by ipra_le sl hPX + 𝔟 X
  have eq := natEq (eq_add_of_le less)
  unfold leftRemainder
  ipra_le sl hP + 2*sl hPX using linear_combination -eq

theorem right_weight_positive (D Q Y : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hYQ : Γ ⊢[PRAAx] le Y Q) : Γ ⊢[PRAAx] le one (rightRemainder D Q Y) := by
  have less : Γ ⊢[PRAAx] le Y (Q+D) := by ipra_le sl hYQ + 𝔟 D
  have eq := natEq (eq_add_of_le less)
  unfold rightRemainder
  ipra_le 2*sl hD + 2*sl hYQ + 1 using linear_combination -2*eq

private theorem scale_congr {a b x y : PTm n} (ha : Γ ⊢[PRAAx] a ≐ b) (hx : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] scale a x ≐ scale b y := multiply_congr (natCode_congr ha) hx

private theorem within_congr {w v t u X Y B E X' Y' B' : PTm n}
    (hw : Γ ⊢[PRAAx] w ≐ v) (hx : Γ ⊢[PRAAx] X ≐ X') (hy : Γ ⊢[PRAAx] Y ≐ Y') (hb : Γ ⊢[PRAAx] B ≐ B')
    (h : Γ ⊢[PRAAx] within w t u X Y B E) : Γ ⊢[PRAAx] within v t u X' Y' B' E :=
  rationalLE_congr (scale_congr hw hy)
    (add_congr (add_congr (scale_congr (.eqRefl _) hx) (scale_congr (.eqRefl _) hb))
      (scale_congr hw (.eqRefl _))) h

theorem one_actual_secant (L U : PR 3) (W : PR 2) (X Y Z a b w p x : PTm n)
    (hw : Γ ⊢[PRAAx] a+b ≐ w) (ha : Γ ⊢[PRAAx] le one a)
    (hx : Γ ⊢[PRAAx] presented L U W X x) (hy : Γ ⊢[PRAAx] presented L U W Y x)
    (hz : Γ ⊢[PRAAx] presented L U W Z x) (hpx : Γ ⊢[PRAAx] le (witnessIndex W X x) p)
    (hpy : Γ ⊢[PRAAx] le (witnessIndex W Y x) p) (hpz : Γ ⊢[PRAAx] le (witnessIndex W Z x) p)
    (hc : Γ ⊢[PRAAx] multiplicative a b (read U X p x) (read U Y p x) (read L Z p x)) :
    Γ ⊢[PRAAx] within w b a (RationalConvexEndpointBudget.sample (centerF L U) X p x)
      (RationalConvexEndpointBudget.sample (centerF L U) Z p x)
      (RationalConvexEndpointBudget.sample (centerF L U) Y p x) (eps p) := by
  have cx := upper_nonnegative L U W X p x hx hpx
  have cy := upper_nonnegative L U W Y p x hy hpy
  have cz := lower_nonnegative L U W Z p x hz hpz
  have ordinary := multiplicative_to_ordinary a b _ _ _ ha cx cy cz hc
  have hx' := (step_at L U X p x hx.andE₁).andE₂.andE₂.andE₂
  have hy' := (step_at L U Y p x hy.andE₁).andE₂.andE₂.andE₂
  have hz' := (step_at L U Z p x hz.andE₁).andE₂.andE₂.andE₂
  have centered := centered_secant a b _ _ _ _ _ _ p hx' hy' hz' ordinary
  exact within_congr hw (center_at L U X p x).eqSymm (center_at L U Z p x).eqSymm (center_at L U Y p x).eqSymm centered

theorem derive_finite_input (L U : PR 3) (W : PR 2) (D P Q X Y e x : PTm n)
    (h : Γ ⊢[PRAAx] geometry D P Q X Y) (hpts : Γ ⊢[PRAAx] pointInputs L U W D P Q X Y x)
    (hp : Γ ⊢[PRAAx] afterWitnesses W D P Q X Y (samplePrecision X Y e) x)
    (hc : Γ ⊢[PRAAx] endpointSecants L U D P Q X Y (samplePrecision X Y e) x) :
    Γ ⊢[PRAAx] finiteInput (centerF L U) D P Q X Y e x := by
  let p := samplePrecision X Y e
  let a := leftPoint D P
  let b := rightPoint D Q
  let u := interior D X
  let v := interior D Y
  have hPX := h.andE₂.andE₂.andE₁
  have hXY := h.andE₂.andE₂.andE₂.andE₁
  have hYQ := h.andE₂.andE₂.andE₂.andE₂
  have l := one_actual_secant L U W v a u (leftRemainder P X) (displacement X Y) (leftWidth P Y) p x
    ((add_comm _ _).eqTrans (left_width P X Y hPX hXY).eqSymm) (left_weight_positive P X h.andE₂.andE₁ hPX)
    hpts.andE₂.andE₂.andE₂ hpts.andE₁ hpts.andE₂.andE₂.andE₁ hp.andE₂.andE₂.andE₂ hp.andE₁ hp.andE₂.andE₂.andE₁ hc.andE₁
  have r := one_actual_secant L U W u b v (rightRemainder D Q Y) (displacement X Y) (rightWidth D Q X) p x
    ((add_comm _ _).eqTrans (right_width D Q X Y hXY hYQ).eqSymm) (right_weight_positive D Q Y h.andE₁ hYQ)
    hpts.andE₂.andE₂.andE₁ hpts.andE₂.andE₁ hpts.andE₂.andE₂.andE₂
    hp.andE₂.andE₂.andE₁ hp.andE₂.andE₁ hp.andE₂.andE₂.andE₂ hc.andE₂
  exact .andI h (.andI (.andI (actual_center_nonnegative L U W a p x hpts.andE₁ hp.andE₁)
    (.andI (actual_center_nonnegative L U W u p x hpts.andE₂.andE₂.andE₁ hp.andE₂.andE₂.andE₁)
      (.andI (actual_center_nonnegative L U W v p x hpts.andE₂.andE₂.andE₂ hp.andE₂.andE₂.andE₂)
        (actual_center_nonnegative L U W b p x hpts.andE₂.andE₁ hp.andE₂.andE₁))))
    (.andI (.andI (endpoint_regular L U a p x hpts.andE₁.andE₁)
      (endpoint_regular L U b p x hpts.andE₂.andE₁.andE₁)) (.andI l r)))

theorem actual_named_samples (L U : PR 3) (W : PR 2) (D P Q X Y k e x : PTm n)
    (h : Γ ⊢[PRAAx] geometry D P Q X Y) (hpts : Γ ⊢[PRAAx] pointInputs L U W D P Q X Y x)
    (hp : Γ ⊢[PRAAx] afterWitnesses W D P Q X Y (samplePrecision X Y e) x)
    (hc : Γ ⊢[PRAAx] endpointSecants L U D P Q X Y (samplePrecision X Y e) x)
    (ht : Γ ⊢[PRAAx] withinModulus (centerF L U) D P Q X Y k x) :
    Γ ⊢[PRAAx] sampleConclusion (centerF L U) D X Y k e x :=
  actual_local_sample_bound _ _ _ _ _ _ _ _ _ (derive_finite_input L U W D P Q X Y e x h hpts hp hc) ht

theorem actual_nested_finite_secants_closed (L U : PR 3) (W : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((geometry (var 0) (var 1) (var 2) (var 3) (var 4) ⋏ pointInputs L U W (var 0) (var 1) (var 2) (var 3) (var 4) (var 6)) ⟶
      (afterWitnesses W (var 0) (var 1) (var 2) (var 3) (var 4) (samplePrecision (var 3) (var 4) (var 5)) (var 6) ⋏
        endpointSecants L U (var 0) (var 1) (var 2) (var 3) (var 4) (samplePrecision (var 3) (var 4) (var 5)) (var 6)) ⟶
      finiteInput (centerF L U) (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (.impI (derive_finite_input L U W _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂
    Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.RationalNestedConvexModulus
