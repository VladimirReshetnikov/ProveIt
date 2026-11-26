import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerPositivePowerChart
import IPRADerivations.Analysis.Exponential.GaussianRealExponentialPositiveIncrement
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUpperPowerOrder
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerPositiveTimePowerProduct
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerPowerInputProperness
import IPRADerivations.Analysis.RationalArithmetic.RationalUpperRepresentation
import IPRADerivations.Analysis.Optimization.RationalCubeInfimumIntervals

/-!
# Genuine monotonicity of the actual positive rational power chart

A nonnegative ordered harmonic-log increment at the exact ratio of the
two positive rational times gives exponential order. The actual logarithm
product and original exponent properness identify the upper endpoint;
rounded logarithm observations are never assumed exactly monotone.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChart (argument parameters coefficient_exact)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianEulerIntegrandName (powerF powerData powerExponentF powerExponentData powerRadius coefficient)
open GaussianRationalHorner (positive_product)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_refl cross_to_diagonal)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianNamedPositiveExponentialOrder (positiveSamples realOrder real_order_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactLogarithmBounds (domain)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

abbrev logarithmF : PR 2 := GaussianHarmonicLogarithmName.nameF
abbrev inputF : PR 2 := GaussianBoundedConstantProductName.nameF logarithmF
def inputData (e f Q a b : PTm n) : PTm n :=
  GaussianBoundedConstantProductName.data Q (fraction e f) (GaussianHarmonicLogarithmName.data a b)
def source (e f d h Q S E T a b c v : PTm n) : Fm PTm n :=
  GaussianEulerPositivePowerChart.source e f d h Q S E T a b ⋏
    (domain c v E T ⋏ le (a*v) (b*c))
@[simp] theorem subst_inputData {m : ℕ} (σ : Fin n → PTm m) (e f Q a b : PTm n) :
    Syn.subst σ (inputData e f Q a b) = inputData (Syn.subst σ e) (Syn.subst σ f)
      (Syn.subst σ Q) (Syn.subst σ a) (Syn.subst σ b) := by simp [inputData]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (e f d h Q S E T a b c v : PTm n) :
    (source e f d h Q S E T a b c v).subst σ = source (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ d)
      (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ v) := by simp [source]

theorem fraction_positive (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    GaussianPositiveRealArithmetic.positive (fraction a b) :=
  GaussianPositiveRealArithmetic.positive_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hb).eqSymm
    (GaussianPositiveExponentialTermBound.actual_positive_fraction a b hb)

theorem coefficient_bound (e f Q : PTm n) (hf : Γ ⊢[PRAAx] le one f) (hQ : Γ ⊢[PRAAx] le e (Q*f)) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (fraction e f) Q one := GaussianEulerExponentCompactBounds.fraction_bound e f Q hf hQ

theorem input_regular (e f Q a b : PTm n) (hf : Γ ⊢[PRAAx] le one f) (hQ : Γ ⊢[PRAAx] le e (Q*f))
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx] pointCN inputF (inputData e f Q a b) :=
  GaussianBoundedConstantProductName.name_regular logarithmF Q (fraction e f) _
    (.andI (GaussianHarmonicLogarithmName.name_regular a b ht) (coefficient_bound e f Q hf hQ))

theorem input_real_samples (e f Q a b : PTm n) (hf : Γ ⊢[PRAAx] le one f) : Γ ⊢[PRAAx]
    realSamples inputF (inputData e f Q a b) :=
  GaussianEulerUpperPowerOrder.product_real_samples Q (fraction e f) a b
    (fraction_positive e f hf).andE₁

theorem input_positive_samples (e f Q a b : PTm n) (hf : Γ ⊢[PRAAx] le one f) (ht : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    positiveSamples inputF (inputData e f Q a b) := by
  refine .allI ?_
  have fs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift f) := by simpa [Fm.shift,Syn.shift,one] using hf.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift b) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using ht.shift
  let p : PTm (n+1) := var 0
  let t := GaussianBoundedConstantProductName.clock p (Syn.shift Q)
  have pos := GaussianPositiveRealArithmetic.positive_multiply (fraction (Syn.shift e) (Syn.shift f))
    (GaussianHarmonicLogarithmName.sample t (Syn.shift a) (Syn.shift b))
    (fraction_positive _ _ fs)
    (GaussianEulerUpperPowerCoefficients.harmonic_sample_nonnegative t _ _ ts)
  simpa only [positiveSamples,Syn.shift,subst_inputData,inputData,GaussianBoundedConstantProductName.sample,
    GaussianBoundedConstantProductName.subst_data,GaussianPositiveRationalLogarithm.subst_fraction,GaussianHarmonicLogarithmName.subst_data,p] using
    GaussianPositiveRealArithmetic.positive_congr
      (GaussianBoundedConstantProductName.sample_at logarithmF p (Syn.shift Q) (fraction (Syn.shift e) (Syn.shift f))
        (GaussianHarmonicLogarithmName.data (Syn.shift a) (Syn.shift b))).eqSymm pos

/-- The ordered input is identified with the ORIGINAL exponent program,
not just with an unspecified exponential having the desired value. -/
theorem input_cross (e f Q a b : PTm n) (hf : Γ ⊢[PRAAx] le one f) (hQ : Γ ⊢[PRAAx] le e (Q*f))
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    crossEquivalent inputF powerExponentF (inputData e f Q a b) (powerExponentData (argument e f) f a b) := by
  let H := logarithmF
  let L := GaussianPositiveRationalLogarithm.logF
  let k := fraction e f
  let c := coefficient (argument e f) f
  let X := GaussianHarmonicLogarithmName.data a b
  let Y := GaussianPositiveRationalLogarithm.data a b
  have first := GaussianBoundedConstantProductName.ordinary_product_identity H Q k X
    (.andI (GaussianHarmonicLogarithmName.name_regular a b ht) (coefficient_bound e f Q hf hQ))
  have second := GaussianGammaAdjacentCutoff.multiply_cross GaussianGammaCanonicalExponent.constantF GaussianGammaCanonicalExponent.constantF H L
    k c X Y (GaussianGammaCanonicalExponent.constant_regular k) (GaussianGammaCanonicalExponent.constant_regular c)
    (GaussianHarmonicLogarithmName.name_regular a b ht) (GaussianPositiveRationalLogarithm.name_regular a b ht)
    (GaussianSignedNameExponentialOrder.constant_equal_cross k c (coefficient_exact e f hf).eqSymm)
    (cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original a b ht))
  exact cross_trans _ _ _ _ _ _ first second

/-- Exact rational time order gives a nonnegative ratio increment, while
all original left/right exponential clocks remain unchanged. -/
theorem original_power_order (e f Q a b c v : PTm n) (hf : Γ ⊢[PRAAx] le one f)
    (hQ : Γ ⊢[PRAAx] le e (Q*f)) (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b)
    (hu : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source c v) (ho : Γ ⊢[PRAAx] le (a*v) (b*c)) : Γ ⊢[PRAAx]
    realOrder powerF powerF (powerData (argument e f) f a b) (powerData (argument e f) f c v) := by
  let r := b*c
  let s := a*v
  let X := inputData e f Q a b
  let Y := inputData e f Q r s
  let Z := addData X Y
  let H := addF inputF inputF
  let Rx := GaussianNameBounds.U inputF X
  let Rz := GaussianNameBounds.U H Z
  have ratio : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source r s :=
    .andI (positive_product b c ht.andE₂ hu.andE₁) (positive_product a v ht.andE₁ hu.andE₂)
  have hx := input_regular e f Q a b hf hQ ht
  have hy := input_regular e f Q r s hf hQ ratio
  have hz := GaussianNameArithmetic.add_fast inputF inputF X Y hx hy
  have ix := GaussianGammaFiniteApproximantName.exponential_input inputF X hx
  have iz := GaussianGammaFiniteApproximantName.exponential_input H Z hz
  have order := GaussianRealExponentialPositiveIncrement.exponential_order inputF inputF Rx Rz X Y ix hy iz
    (input_real_samples e f Q a b hf) (input_real_samples e f Q r s hf) (input_positive_samples e f Q r s hf ho)
  have leftInner := input_cross e f Q a b hf hQ ht
  have ratioInner := input_cross e f Q r s hf hQ ratio
  have sumInner := GaussianNameArithmetic.add_equivalent inputF powerExponentF inputF powerExponentF X (powerExponentData (argument e f) f a b)
    Y (powerExponentData (argument e f) f r s) hx (GaussianEulerIntegrandName.power_exponent_regular _ _ _ _ (.andI hf ht))
    hy (GaussianEulerIntegrandName.power_exponent_regular _ _ _ _ (.andI hf ratio))
    (cross_to_diagonal _ _ _ _ leftInner) (cross_to_diagonal _ _ _ _ ratioInner)
  have productInner := GaussianEulerPositiveTimePowerProduct.power_exponent_product (argument e f) f a b r s (.andI hf (.andI ht ratio))
  have prodTime := GaussianHarmonicLogarithmProduct.product_source a b r s (.andI ht ratio)
  have properInner := GaussianEulerPowerInputProperness.exponent_proper (argument e f) f (a*r) (b*s) c v prodTime hu (by dsimp only [r,s]; ipra_ring)
  have rightInner := cross_trans _ _ _ _ _ _ sumInner (cross_trans _ _ _ _ _ _ productInner properInner)
  have left := GaussianExponentialRadiusIndependence.independent_radii_proper inputF powerExponentF Rx (powerRadius (argument e f) f a b)
    X (powerExponentData (argument e f) f a b) ix (GaussianEulerIntegrandName.power_input _ _ _ _ (.andI hf ht)) leftInner
  have right := GaussianExponentialRadiusIndependence.independent_radii_proper H powerExponentF Rz (powerRadius (argument e f) f c v)
    Z (powerExponentData (argument e f) f c v) iz (GaussianEulerIntegrandName.power_input _ _ _ _ (.andI hf hu)) rightInner
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ left) right order

/-- Exact positive rational scaling of a one-sided real observation error.
All four input scalar codes may be raw and use unrelated denominators. -/
theorem scale_upper (d h x y A B : PTm n) (hh : Γ ⊢[PRAAx] le one h)
    (ho : Γ ⊢[PRAAx] RationalValueBounds.upper (fstT x) (fstT y) A B) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (GaussianRationalHorner.qmul (fraction d h) x))
      (fstT (GaussianRationalHorner.qmul (fraction d h) y)) (d*A) (h*B) := by
  let u := RationalSupMetric.numeratorOf (fstT x)
  let v := RationalSupMetric.numeratorOf (fstT y)
  let P := RationalSupMetric.denominatorOf (fstT x)
  let Qr := RationalSupMetric.denominatorOf (fstT y)
  have cr : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (fraction d h)) (ZT.ofNat d) h :=
    GaussianRationalHorner.scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_ofNat]
      ring) (.eqRefl _) (GaussianRationalHorner.ofGaussian_represents _ _ hh).andE₁
  have xr := RationalRepresentations.represents_self (Γ := Γ) (fstT x)
  have yr := RationalRepresentations.represents_self (Γ := Γ) (fstT y)
  have clear := RationalUpperRepresentation.upper_from_representations (fstT x) (fstT y) P Qr A B u v xr yr ho
  have cx := RationalRepresentations.represents_multiply _ _ _ _ _ _ cr xr
  have cy := RationalRepresentations.represents_multiply _ _ _ _ _ _ cr yr
  have hc := (fraction_positive d h hh).andE₁
  have realX : Γ ⊢[PRAAx] fstT (GaussianRationalHorner.qmul (fraction d h) x) ≐
      RationalArithmetic.multiply (fstT (fraction d h)) (fstT x) :=
    (congrFst (GaussianRationalPowerAlgebra.qmul_commutative _ _)).eqTrans
      ((GaussianPositiveExponentialProduct.real_product x (fraction d h) hc).eqTrans (RationalAlgebra.multiply_commutative _ _))
  have realY : Γ ⊢[PRAAx] fstT (GaussianRationalHorner.qmul (fraction d h) y) ≐
      RationalArithmetic.multiply (fstT (fraction d h)) (fstT y) :=
    (congrFst (GaussianRationalPowerAlgebra.qmul_commutative _ _)).eqTrans
      ((GaussianPositiveExponentialProduct.real_product y (fraction d h) hc).eqTrans (RationalAlgebra.multiply_commutative _ _))
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ (ZT.ofNat d*u) (ZT.ofNat d*v) (h*P) (h*Qr) (d*A) (h*B)
    (positive_product _ _ hh (RationalArgmin.denominator_positive _))
    (positive_product _ _ hh (RationalArgmin.denominator_positive _))
    (GaussianRationalHorner.scalar_congr realX.eqSymm (ZT.derive rfl) (.eqRefl _) cx)
    (GaussianRationalHorner.scalar_congr realY.eqSymm (ZT.derive rfl) (.eqRefl _) cy)
  have bound := zle_toZ clear
  apply zle_of_toZ (d*h*h*PTm.monus
    ((ZT.ofNat (B*P)*v+ZT.ofNat (A*P*Qr)).pos+(ZT.ofNat (B*Qr)*u).neg)
    ((ZT.ofNat (B*Qr)*u).pos+(ZT.ofNat (B*P)*v+ZT.ofNat (A*P*Qr)).neg))
  simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_add,ZT.toZ_ofNat] at bound ⊢
  ipra_simps
  linear_combination 𝔞 d*𝔞 h*𝔞 h*bound

/-- The actual original charts are monotone at independent requested
observations, retaining only their own two dyadic allowances. -/
theorem original_observations (p q e f d h Q S E T a b c v : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b c v) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (ap2 GaussianEulerPositivePowerChart.nameF p (GaussianEulerPositivePowerChart.data e f d h S a b)))
      (fstT (ap2 GaussianEulerPositivePowerChart.nameF q (GaussianEulerPositivePowerChart.data e f d h S c v)))
      (unit p+unit q) (unit p*unit q) := by
  let u := GaussianEulerPositivePowerChart.clock p S
  let w := GaussianEulerPositivePowerChart.clock q S
  let P := unit p
  let Qr := unit q
  let U := unit u
  let V := unit w
  have hf := hs.andE₁.andE₁.andE₁.andE₂
  have hh := hs.andE₁.andE₁.andE₂.andE₁.andE₂
  have exponent := hs.andE₁.andE₁.andE₂.andE₂.andE₂.andE₁
  have scale := hs.andE₁.andE₁.andE₂.andE₂.andE₂.andE₂
  have old := real_order_at _ _ _ _ u w
    (original_power_order e f Q a b c v hf exponent hs.andE₁.andE₂.andE₂.andE₁ hs.andE₂.andE₁.andE₁ hs.andE₂.andE₂)
  have scaled := scale_upper d h (ap2 powerF u (powerData (argument e f) f a b))
    (ap2 powerF w (powerData (argument e f) f c v)) (U+V) (U*V) hh old
  have bP : Γ ⊢[PRAAx] le (S*P) U := GaussianFastValueCut.query_budget S p
  have bQ : Γ ⊢[PRAAx] le (S*Qr) V := GaussianFastValueCut.query_budget S q
  have coarsened := RationalValueBounds.upper_mono _ _ _ _ (P+Qr) (P*Qr)
    (positive_product _ _ hh (positive_product _ _ (unit_positive u) (unit_positive w))) scaled (by
      ipra_le (𝔞 h*𝔞 V*𝔞 Qr)*sl bP+(𝔞 h*𝔞 U*𝔞 P)*sl bQ+(𝔞 P*𝔞 Qr*(𝔞 U+𝔞 V))*sl scale)
  exact RationalValueBounds.upper_congr
    (congrFst (GaussianEulerPositivePowerChart.sample_at p e f d h S a b)).eqSymm
    (congrFst (GaussianEulerPositivePowerChart.sample_at q e f d h S c v)).eqSymm (.eqRefl _) (.eqRefl _) coarsened

theorem actual_original_positive_power_chart_monotone_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) ⟶
      RationalValueBounds.upper
        (fstT (ap2 GaussianEulerPositivePowerChart.nameF (var 0)
          (GaussianEulerPositivePowerChart.data (var 2) (var 3) (var 4) (var 5) (var 7) (var 10) (var 11))))
        (fstT (ap2 GaussianEulerPositivePowerChart.nameF (var 1)
          (GaussianEulerPositivePowerChart.data (var 2) (var 3) (var 4) (var 5) (var 7) (var 12) (var 13))))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 14 (.impI (original_observations _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartOrder
