import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GlobalComparison.GaussianGammaMinimumGlobalComparison
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.RationalUpperAddition

/-!
# Transfer a fixed positive margin in a frozen rational Gamma comparison

Adding the same rational margin to the two left observations preserves
their freeze error. At a clock that pays for all the errors, one observed
margin rules out the reverse exact order of the original log names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumGlobalStrictComparison

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianExponentialReference (unit_monotone)
open GaussianGammaDigammaDyadicLocation (locationF)
open GaussianGammaDigammaLocationInput (named_real_source)
open GaussianGammaMinimumFreeze (nameF data)
open GaussianGammaMinimumGlobalComparison (lateClock late_clock_bounds rootObservation comparisonObservation frozen_radii)
open GaussianNamedGammaPositiveLower (source)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianRationalHorner (positive_product)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)
open RationalArithmetic (add)
open RationalRepresentedUpper (left right to_signed)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (upper upper_of_order upper_of_radius radius_symmetric upper_triangle upper_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "G" => GaussianNamedGamma.nameF
local notation "gd" => GaussianNamedGamma.data
local notation "namedRoot(" p "," x ")" => fstT (ap2 (nameF locationF) p (data x one))
local notation "namedPoint(" f "," p "," y "," A ")" => fstT (ap2 (nameF f) p (data y A))

def nativeMarginAt (f : PR 2) (p x y A C E : PTm n) : Fm PTm n :=
  let k := lateClock f p x y A
  upper (add (fraction one E) (rootObservation p k)) (comparisonObservation f p k y)
    (C*unit p+two*unit k) (unit k*unit p)

theorem margin_observation (f : PR 2) (p x y A C E : PTm n)
    (hs : Γ ⊢[PRAAx] source f y A) (hn : Γ ⊢[PRAAx] nativeMarginAt f p x y A C E) :
    Γ ⊢[PRAAx] upper (add (fraction one E) (namedRoot(p,x))) (namedPoint(f,p,y,A)) (C+num 78) (unit p) := by
  let k := lateClock f p x y A
  let U := unit p
  let K := unit k
  let r := rootObservation p k
  let s := comparisonObservation f p k y
  let z := fraction one E
  let a := namedRoot(p,x)
  let b := namedPoint(f,p,y,A)
  have hk := late_clock_bounds (Γ := Γ) f p x y A
  have hu := unit_positive (Γ := Γ) p
  have hku := positive_product _ _ (unit_positive k) hu
  have grow : Γ ⊢[PRAAx] le U K := unit_monotone hk.andE₁
  have radii := frozen_radii f p x y A hs
  have first : Γ ⊢[PRAAx] upper (add z a) (add z r) (num 38) U := by
    have h := RationalUpperAddition.add_upper z z a r zero one (num 38) U
      (upper_of_order z z zero one (RationalArgmin.reflexive z)) (upper_of_radius _ _ _ _ radii.andE₁)
    apply upper_mono _ _ _ _ _ _ (positive_product _ _ (le_refl one) hu) h
    exact le_of_eq_add (d := zero) (by ipra_ring)
  have last : Γ ⊢[PRAAx] upper s b (num 38) U := upper_of_radius _ _ _ _ (radius_symmetric _ _ _ _ radii.andE₂)
  have middle : Γ ⊢[PRAAx] upper (add z r) s (C+two) U := by
    apply upper_mono _ _ _ _ _ _ hku hn
    change Γ ⊢[PRAAx] le ((C*U+two*K)*U) ((C+two)*(K*U))
    ipra_le 𝔞 C*𝔞 U*sl grow
  have all := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ first middle) last
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hu hu) hu) all
  exact le_of_eq_add (d := zero) (by ipra_ring)

private theorem constant_margin_paid (x E C U : PTm n) (he : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] upper (add (fraction one E) x) x C U) :
    Γ ⊢[PRAAx] le U (E*C) := by
  let d := denominatorOf x
  let v := numeratorOf x
  let w := ZT.ofNat one*ZT.ofNat d+v*ZT.ofNat E
  let a := left w d U
  let b := right v (E*d) d C U
  have q := RationalRepresentations.represents_self (Γ := Γ) x
  have rep := RationalRepresentations.represents_add (fraction one E) x (ZT.ofNat one) v E d
    (fraction_represents one E he) q
  have e := zle_toZ (to_signed (add (fraction one E) x) x w v (E*d) d C U rep q h)
  have hd := RationalArgmin.denominator_positive (Γ := Γ) x
  apply RationalValueBounds.positive_cancel (c := d*d) (positive_product _ _ hd hd)
  apply le_of_eq_add (d := PolynomialBisection.slack a b)
  apply deriveNat
  dsimp only [a,b,w] at e ⊢
  simp only [left,right,PolynomialBisection.slack,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at e ⊢
  ipra_simps
  linear_combination -e

theorem strict_log_order_at (f : PR 2) (p x y A C E : PTm n) (hs : Γ ⊢[PRAAx] source f y A)
    (hw : Γ ⊢[PRAAx] realOrder (nameF locationF) (nameF f) (data x one) (data y A))
    (he : Γ ⊢[PRAAx] le one E) (hp : Γ ⊢[PRAAx] lt (E*(C+num 80)) (unit p))
    (hn : Γ ⊢[PRAAx] nativeMarginAt f p x y A C E) :
    Γ ⊢[PRAAx] strictOrder (nameF locationF) (nameF f) (data x one) (data y A) := by
  refine .andI hw (.impI ?_)
  let Δ := realOrder (nameF f) (nameF locationF) (data y A) (data x one) :: Γ
  let U := unit p
  let a := namedRoot(p,x)
  let b := namedPoint(f,p,y,A)
  have hU := unit_positive (Γ := Δ) p
  have reverse := real_order_at (nameF f) (nameF locationF) (data y A) (data x one) p p (Prf.hyp0 (Γ := Γ))
  have h : Δ ⊢[PRAAx] upper b a two U :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ hU hU) reverse
      (le_of_eq_add (d := zero) (by dsimp only [U]; ipra_ring))
  have forward := margin_observation (Γ := Δ) f p x y A C E hs.wk hn.wk
  have joined : Δ ⊢[PRAAx] upper (add (fraction one E) a) a (C+num 80) U :=
    RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (RationalValueBounds.upper_triangle_same hU forward h)
  exact lt_irrefl _ _ (lt_of_lt_of_le hp.wk (constant_margin_paid a E (C+num 80) U he.wk joined))

theorem strict_minimum_at (f : PR 2) (p x y A C E : PTm n) (hs : Γ ⊢[PRAAx] source f y A)
    (hw : Γ ⊢[PRAAx] realOrder (nameF locationF) (nameF f) (data x one) (data y A))
    (he : Γ ⊢[PRAAx] le one E) (hp : Γ ⊢[PRAAx] lt (E*(C+num 80)) (unit p))
    (hn : Γ ⊢[PRAAx] nativeMarginAt f p x y A C E) :
    Γ ⊢[PRAAx] strictOrder (G locationF) (G f) (gd x one) (gd y A) :=
  GaussianGammaMinimumFreezeOrder.strict_order_from_log locationF f x y one A (named_real_source x) hs
    (strict_log_order_at f p x y A C E hs hw he hp hn)

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumGlobalStrictComparison
