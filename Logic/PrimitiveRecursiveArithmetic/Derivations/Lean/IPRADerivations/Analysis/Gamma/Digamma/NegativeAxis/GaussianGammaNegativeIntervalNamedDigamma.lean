import IPRADerivations.Analysis.Gamma.Digamma.NegativeAxis.GaussianGammaNegativeIntervalNamedDigammaRationalRate
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.Named.GaussianNamedEulerUnitTime

/-!
# Shifted negative digamma at a regular real offset

Each returned observation evaluates the real reference for the original
shifted digamma at a decoded rational observation of the input. The
input clock pays for the uniform rational Lipschitz bound. The frozen
comparison retains the unchanged original shifted digamma at an
arbitrary rational observation of the input.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDigamma

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaNegativeCriticalLocationResidual (realF realData real_samples original_cross)
open GaussianGammaNegativeCriticalSlope (coefficient)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianUnitIntervalInputDecoding (numerator denominator fraction_recode)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "NF" => GaussianGammaNegativeCriticalEndpoints.nameF
local notation "nd" => GaussianGammaNegativeCriticalEndpoints.nameData

abbrev source (f : PR 2) (x E : PTm n) : Fm PTm n := GaussianNamedEulerUnitTime.source f x E
def clock (p E N : PTm n) : PTm n := exponent (coefficient N E) (succ p)
def frozenData (f : PR 2) (k x N : PTm n) : PTm n :=
  nd (numerator (ap2 f k x)) (denominator (ap2 f k x)) N
def frozenRealData (f : PR 2) (k x N : PTm n) : PTm n :=
  realData (numerator (ap2 f k x)) (denominator (ap2 f k x)) N
def observation (f : PR 2) (p x E N : PTm n) : PTm n :=
  ap2 realF (succ p) (frozenRealData f (clock p E N) x N)
def data (x E N : PTm n) : PTm n := pairT x (pairT E N)
def nameF (f : PR 2) : PR 2 := PTm.toPR
  (observation f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)

ipra_subst clock
ipra_subst frozenData
ipra_subst frozenRealData
ipra_subst observation
ipra_subst data

theorem sample_at (f : PR 2) (p x E N : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF f) p (data x E N) ≐ observation f p x E N := by
  simpa [nameF, data, pairVector, pairVectorField] using
    (toPR_pairVector_eq (Γ := Γ) (k := 2) (observation f (var 0) (var 1) (var 2) (var 3)) p ![x, E, N])

private theorem rational_inputs (f g : PR 2) (r s x y E X D : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] distanceBounded (ap2 f r x) (ap2 g s y) X D) :
    Γ ⊢[PRAAx] GaussianGammaNegativeIntervalNamedDigammaRationalRate.input
      (numerator (ap2 f r x)) (denominator (ap2 f r x))
      (numerator (ap2 g s y)) (denominator (ap2 g s y)) E X D :=
  .andI (GaussianNamedEulerUnitTime.encoded_source f r x E hf)
    (.andI (GaussianNamedEulerUnitTime.encoded_source g s y E hg) (.andI hD
      (distance_congr (fraction_recode _ E (GaussianNamedEulerUnitTime.source_at f r x E hf)).eqSymm
        (fraction_recode _ E (GaussianNamedEulerUnitTime.source_at g s y E hg)).eqSymm (.eqRefl _) (.eqRefl _)
        (GaussianFastValueCut.recode_distance_bound _ _ _ _ hD h))))

private theorem twice_unit (p : PTm n) : Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p :=
  (pw_succ two p).eqTrans (mul_comm _ _)

theorem clock_budget (p E N : PTm n) : Γ ⊢[PRAAx] le (two*coefficient N E*unit p) (unit (clock p E N)) :=
  le_congr ((congrMul (.eqRefl _) (twice_unit p)).eqTrans (by ipra_ring)) (.eqRefl _)
    (query_budget (coefficient N E) (succ p))

private theorem variation_at (f g : PR 2) (p q x y E N A D : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded (ap2 f (clock p E N) x) (ap2 g (clock q E N) y)
      (rateNumerator A D (clock p E N) (clock q E N)) (rateDenominator D (clock p E N) (clock q E N))) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x E N)) (ap2 (nameF g) q (data y E N))
      (rateNumerator (coefficient N E*A) D p q) (rateDenominator D p q) := by
  let r := clock p E N
  let s := clock q E N
  let C := coefficient N E
  let X := rateNumerator A D r s
  let Y := rateDenominator D r s
  have hY := denominator_positive D r s hD
  have inputs := rational_inputs f g r s x y E X Y hf hg hY h
  have inputRate := GaussianGammaNegativeIntervalNamedDigammaRationalRate.real_rate _ _ _ _ N E X Y inputs
  have raw := rate_at realF realF (frozenRealData f r x N) (frozenRealData g s y N) (C*X) Y (succ p) (succ q) inputRate
  have up := twice_unit (Γ := Γ) p
  have uq := twice_unit (Γ := Γ) q
  have eN : Γ ⊢[PRAAx] rateNumerator (C*X) Y (succ p) (succ q) ≐
      (C*X)*(two*unit p)*(two*unit q)+Y*(two*unit p+two*unit q) :=
    congrAdd (congrMul (congrMul (.eqRefl _) up) uq) (congrMul (.eqRefl _) (congrAdd up uq))
  have eD : Γ ⊢[PRAAx] rateDenominator Y (succ p) (succ q) ≐ Y*(two*unit p)*(two*unit q) :=
    congrMul (congrMul (.eqRefl _) up) uq
  apply distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hY (positive_product _ _ RationalAlgebra.two_positive (unit_positive p)))
      (positive_product _ _ RationalAlgebra.two_positive (unit_positive q))) (denominator_positive D p q hD) ?_
    (distance_congr (sample_at f p x E N).eqSymm (sample_at g q y E N).eqSymm eN eD raw)
  dsimp only [X,Y,rateNumerator,rateDenominator]
  ipra_le (2*(𝔞 D)^2*𝔞(unit p)*𝔞(unit q)*𝔞(unit s)*𝔞(unit q))*sl (clock_budget p E N)+
    (2*(𝔞 D)^2*𝔞(unit p)*𝔞(unit q)*𝔞(unit r)*𝔞(unit p))*sl (clock_budget q E N)

theorem original_observations (f g : PR 2) (p q x y E N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x E N)) (ap2 (nameF g) q (data y E N))
      (unit p+unit q) (unit p*unit q) := by
  let r := clock p E N
  let s := clock q E N
  have h := cross_at f g x y r s he
  have near := variation_at f g p q x y E N zero one hf hg (le_refl one)
    (distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring)
      (by unfold rateDenominator; ipra_ring) h)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring)
    (by unfold rateDenominator; ipra_ring) near

theorem proper (f g : PR 2) (x y E N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E) (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x E N) (data y E N) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have fs : Δ ⊢[PRAAx] source f (sh x) (sh E) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hf.shift.shift
  have gs : Δ ⊢[PRAAx] source g (sh y) (sh E) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hg.shift.shift
  have es : Δ ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) := by simpa [Δ,Fm.shift,Syn.shift,sh] using he.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,subst_data,Syn.shift,sh] using
    original_observations f g (var 1) (var 0) (sh x) (sh y) (sh E) (sh N) fs gs es

theorem name_regular (f : PR 2) (x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x E N) :=
  proper f f x x E N h h (cross_refl _ _ h.andE₁)

theorem independent_rate (f g : PR 2) (x y E N A D : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] independentRate f g x y A D) :
    Γ ⊢[PRAAx] independentRate (nameF f) (nameF g) (data x E N) (data y E N) (coefficient N E*A) D := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have fs : Δ ⊢[PRAAx] source f (sh x) (sh E) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hf.shift.shift
  have gs : Δ ⊢[PRAAx] source g (sh y) (sh E) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hg.shift.shift
  have ds : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using hD.shift.shift
  have hs : Δ ⊢[PRAAx] independentRate f g (sh x) (sh y) (sh A) (sh D) := by simpa [Δ,Fm.shift,Syn.shift,sh] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,subst_data,GaussianGammaNegativeCriticalSlope.subst_coefficient,PTm.subst_mul,Syn.shift,sh] using
    variation_at f g (var 1) (var 0) (sh x) (sh y) (sh E) (sh N) (sh A) (sh D) fs gs ds
      (rate_at f g _ _ _ _ (clock (var 1) (sh E) (sh N)) (clock (var 0) (sh E) (sh N)) hs)

private theorem frozen_observations (f : PR 2) (p q k x E N : PTm n) (hf : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x E N)) (ap2 realF q (frozenRealData f k x N))
      (rateNumerator (coefficient N E) (unit k) p q) (rateDenominator (unit k) p q) := by
  let r := clock p E N
  let C := coefficient N E
  let A := unit r+unit k
  let D := unit r*unit k
  have hk := unit_positive (Γ := Γ) k
  have hD := positive_product _ _ (unit_positive r) hk
  have input := rational_inputs f f r k x x E A D hf hf hD (cross_at f f x x r k (cross_refl _ _ hf.andE₁))
  have h := GaussianGammaNegativeIntervalNamedDigammaRationalRate.real_rate _ _ _ _ N E A D input
  have raw := rate_at realF realF (frozenRealData f r x N) (frozenRealData f k x N) (C*A) D (succ p) q h
  have up := twice_unit (Γ := Γ) p
  have eN : Γ ⊢[PRAAx] rateNumerator (C*A) D (succ p) q ≐
      (C*A)*(two*unit p)*unit q+D*(two*unit p+unit q) :=
    congrAdd (congrMul (congrMul (.eqRefl _) up) (.eqRefl _)) (congrMul (.eqRefl _) (congrAdd up (.eqRefl _)))
  have eD : Γ ⊢[PRAAx] rateDenominator D (succ p) q ≐ D*(two*unit p)*unit q :=
    congrMul (congrMul (.eqRefl _) up) (.eqRefl _)
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hD (positive_product _ _ RationalAlgebra.two_positive (unit_positive p))) (unit_positive q))
    (denominator_positive _ p q hk) (by
      dsimp only [A,D,rateNumerator,rateDenominator]
      ipra_le (𝔞(unit k)^2*𝔞(unit p)*𝔞(unit q)^2)*sl (clock_budget p E N))
    (distance_congr (sample_at f p x E N).eqSymm (.eqRefl _) eN eD raw)

private theorem frozen_real_rate (f : PR 2) (k x E N : PTm n) (hf : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] independentRate (nameF f) realF (data x E N) (frozenRealData f k x N) (coefficient N E) (unit k) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh x) (sh E) :=
    by simpa [Fm.shift,Syn.shift,sh] using hf.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,subst_data,subst_frozenRealData,GaussianGammaNegativeCriticalSlope.subst_coefficient,
    GaussianCoefficientNameBounds.subst_unit,Syn.shift,sh] using
    frozen_observations f (var 1) (var 0) (sh k) (sh x) (sh E) (sh N) hs

theorem original_frozen_rate (f : PR 2) (k x E N : PTm n) (hf : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] independentRate (nameF f) NF (data x E N) (frozenData f k x N) (coefficient N E) (unit k) :=
  GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ (unit_positive k)
    (frozen_real_rate f k x E N hf) (cross_refl _ _ (name_regular f x E N hf))
    (original_cross _ _ N (GaussianNamedEulerUnitTime.encoded_source f k x E hf).andE₁)

theorem original_real_samples (f : PR 2) (x E N : PTm n) (hf : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] realSamples (nameF f) (data x E N) := by
  let sh (t : PTm n) := Syn.shift t
  let p : PTm (n+1) := var 0
  let r := clock p (sh E) (sh N)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (sh x) (sh E) := by simpa [Fm.shift,Syn.shift,sh] using hf.shift
  have sample := real_sample_at realF (frozenRealData f r (sh x) (sh N)) (succ p)
    (real_samples _ _ _ (GaussianNamedEulerUnitTime.encoded_source f r (sh x) (sh E) hs).andE₁)
  have eq := sample_at (Γ := Γ.map Fm.shift) f p (sh x) (sh E) (sh N)
  refine .allI ?_
  simpa only [realSamples,subst_data,sh,Syn.shift,p] using
    Prf.andI (GaussianRationalHorner.canonical_congr eq sample.andE₁)
      (RationalGaussianEmbedding.axis_congr eq.eqSymm sample.andE₂)

theorem actual_original_negative_interval_named_digamma_frozen_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source f (var 1) (var 2) ⟶ independentRate (nameF f) NF (data (var 1) (var 2) (var 3))
        (frozenData f (var 0) (var 1) (var 3)) (coefficient (var 3) (var 2)) (unit (var 0))) :=
  closeUniv 4 (.impI (original_frozen_rate f _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDigamma
