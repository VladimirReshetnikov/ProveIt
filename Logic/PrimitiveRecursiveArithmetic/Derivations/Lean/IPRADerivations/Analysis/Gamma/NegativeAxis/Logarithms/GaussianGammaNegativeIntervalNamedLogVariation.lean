import IPRADerivations.Analysis.Gamma.NegativeAxis.Logarithms.GaussianGammaNegativeIntervalNamedLogTerminal
import IPRADerivations.Analysis.Gamma.NegativeAxis.Logarithms.GaussianGammaNegativeIntervalLogAbsoluteRetiming
import IPRADerivations.Analysis.Gamma.NegativeAxis.Logarithms.GaussianGammaNegativeIntervalLogAbsoluteProperness
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.Products.GaussianGammaNegativeProductDerivativeInverseRate
import IPRADerivations.Analysis.Logarithm.PositiveAxis.NamedValues.GaussianNamedPositiveLogarithmRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedAddRate
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.Bounds.GaussianEulerUnitCompactTimeBounds

/-!
# A uniform modulus for the original negative log-Gamma

The terminal Gamma varies in a fixed disk. On a window separated
from both poles by 1/E, the original inverse shift multipliers
have norm at most E² and an explicit finite Lipschitz bound. The
uniform signed Gamma floor pays for the logarithm transfer.
-/

set_option autoImplicit false
set_option maxHeartbeats 1900000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedLogVariation

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalGammaSign (signedF signedData)
open GaussianGammaNegativeIntervalInverseBound (literal_inverse bound_from_margin)
open GaussianGammaNegativeIntervalInverseRecurrence (inverse liftedF liftedData original_inverse_product)
open GaussianGammaNegativeIntervalLogAbsolute (nameF nameData)
open GaussianGammaNegativeIntervalLogAbsoluteRetiming (inputF inputData input_cross log_cross positive_source)
open GaussianGammaNegativeIntervalNamedLogTerminal (terminalModulus modulus_later terminal_rate)
open GaussianGammaNegativeIntervalProductSign (signUnit)
open GaussianGammaNegativeIntervalUniformBounds (positive_bound)
open GaussianGammaNegativeProductDerivativeInverseRate (inverseGapCost original_inverse_gap_bound)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameEquivalence (crossEquivalent cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound leadingNumerator leadingDenominator)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerAlgebra (unit_bounded unit_power norm_one)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qone)
open GaussianStirlingGammaLogarithm (gammaData gamma_regular)
open GaussianStirlingRationalTelescopers (fraction_same)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "G" => gammaF
local notation "gd" => GaussianGammaNegativeIntervalNative.data
local notation "L" => nameF
local notation "R" => GaussianNamedPositiveLogarithm.nameF inputF
local notation "rd" => GaussianGammaNegativeIntervalLogAbsoluteRetiming.nameData

abbrev window (a b E : PTm n) : Fm PTm n := GaussianEulerUnitCompactTimeBounds.source a b E
def inverseCost (E N : PTm n) : PTm n := inverseGapCost (succ N) (E*E)
def gammaCost (E N : PTm n) : PTm n := GaussianGammaDigammaLocationProduct.gammaCap*inverseCost E N+E*E
def logCost (E N : PTm n) : PTm n := GaussianGammaNegativeIntervalLogAbsoluteRetiming.margin N*gammaCost E N
def time (s E N : PTm n) : PTm n := GaussianFastValueCut.exponent (logCost E N) s
def modulus (s E N : PTm n) : PTm n := terminalModulus (time s E N)

ipra_subst modulus [time, logCost, gammaCost, inverseCost, GaussianGammaDigammaLocationProduct.gammaCap, one, two]

private theorem inverse_bound (a b E N : PTm n) (h : Γ ⊢[PRAAx] window a b E) :
    Γ ⊢[PRAAx] bounded (inverse a b N) (E*E) one :=
  bound_from_margin a b N (E*E) h.andE₁
    (le_congr (.eqRefl _) (by ipra_ring)
      (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono h.andE₂.andE₂.andE₁
        (GaussianEulerUnitCompactTimeBounds.gap_margin a b E h)))

private theorem constant_samples (x H : PTm n) (h : Γ ⊢[PRAAx] bounded x H one) :
    Γ ⊢[PRAAx] sampleBound C x H := by
  let Δ := Γ.map Fm.shift
  let X := Syn.shift x
  let K := Syn.shift H
  have hs : Δ ⊢[PRAAx] bounded X K one := by simpa [Δ,X,K,Fm.shift,Syn.shift,one] using h.shift
  refine .allI ?_
  simpa only [sampleBound,Syn.shift,Δ,X,K] using
    bound_congr (constant_at (var 0) X).eqSymm (.eqRefl _) (.eqRefl _) hs

private theorem terminal_samples (a b : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] sampleBound G (gammaData (b+a) b) GaussianGammaDigammaLocationProduct.gammaCap := by
  let Δ := Γ.map Fm.shift
  let A := Syn.shift a
  let B := Syn.shift b
  have hs : Δ ⊢[PRAAx] guard A B := by simpa [Δ,A,B,Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa [sampleBound,Δ,A,B,Syn.shift,GaussianGammaDigammaLocationProduct.gammaCap,one] using
    positive_bound A B (var 0) hs

private theorem inverse_rate (s a c b E N : PTm n) (ha : Γ ⊢[PRAAx] window a b E)
    (hc : Γ ⊢[PRAAx] window c b E)
    (hIn : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c b) one (unit s)) :
    Γ ⊢[PRAAx] independentRate C C (inverse a b N) (inverse c b N) (inverseCost E N) (unit s) := by
  have hu := unit_positive (Γ := Γ) s
  have gap := original_inverse_gap_bound c a b N (inverse a b N) (inverse c b N) (E*E) one (unit s)
    hc.andE₁ ha.andE₁ (qmul_canonical _ _) (qmul_canonical _ _)
    (literal_inverse a b N ha.andE₁) (literal_inverse c b N hc.andE₁)
    (inverse_bound a b E N ha) (inverse_bound c b E N hc) hu hIn
  exact GaussianNamedAddRate.constant_rate _ _ _ _ hu
    (distance_congr (.eqRefl _) (.eqRefl _) (by unfold inverseCost; ipra_ring) (.eqRefl _) gap)

private theorem original_gamma_rate (s a c b E N : PTm n)
    (ha : Γ ⊢[PRAAx] window a b E) (hc : Γ ⊢[PRAAx] window c b E)
    (hIn : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c b) one (unit (terminalModulus s))) :
    Γ ⊢[PRAAx] independentRate G G (gd a b N) (gd c b N) (gammaCost E N) (unit s) := by
  let U := unit s
  let M : PTm n := GaussianGammaDigammaLocationProduct.gammaCap
  let V := inverseCost E N
  let x := gammaData (b+a) b
  let y := gammaData (b+c) b
  let u := inverse a b N
  let v := inverse c b N
  have hu := unit_positive (Γ := Γ) s
  have small : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c b) one U :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive (terminalModulus s)) hu
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm
      (GaussianExponentialReference.unit_monotone (modulus_later s))) hIn
  have rate := GaussianNamedMultiplyRate.independent_rate C G C G u x v y V U one U M (E*E)
    hu hu (constant_regular _) (gamma_regular _ _ (GaussianGammaNegativeCriticalEndpoints.shifted_source _ _ ha.andE₁))
    (constant_regular _) (gamma_regular _ _ (GaussianGammaNegativeCriticalEndpoints.shifted_source _ _ hc.andE₁))
    (terminal_samples a b ha.andE₁) (constant_samples v (E*E) (inverse_bound c b E N hc))
    (inverse_rate s a c b E N ha hc small) (terminal_rate s a b c b ha.andE₁ hc.andE₁ hIn)
  have flat := GaussianNamedRateRadius.weaken liftedF liftedF (liftedData a b N) (liftedData c b N)
    (leadingNumerator V U one U M (E*E)) (leadingDenominator U U) (gammaCost E N) U
    (positive_product _ _ hu hu) hu (le_of_eq_add (d := zero)
      (by unfold leadingNumerator leadingDenominator gammaCost; dsimp only [M,V]; ipra_ring)) rate
  exact GaussianNamedRateTransport.transport liftedF liftedF G G _ _ _ _ _ _ hu flat
    (original_inverse_product a b N ha.andE₁) (original_inverse_product c b N hc.andE₁)

private theorem sign_samples (N : PTm n) : Γ ⊢[PRAAx] sampleBound C (signUnit (succ N)) one :=
  constant_samples (signUnit (succ N)) one
    (unit_bounded _ (unit_power _ _ ((GaussianRationalRelativeTwoTerm.norm_negative qone).eqTrans norm_one)))

private theorem signed_rate (s a c b E N : PTm n)
    (ha : Γ ⊢[PRAAx] window a b E) (hc : Γ ⊢[PRAAx] window c b E)
    (hIn : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c b) one (unit (terminalModulus s))) :
    Γ ⊢[PRAAx] independentRate signedF signedF (signedData a b N) (signedData c b N) (gammaCost E N) (unit s) := by
  let x := gd a b N
  let y := gd c b N
  let S := signUnit (succ N)
  let A := gammaCost E N
  let U := unit s
  have hs := constant_regular (Γ := Γ) S
  have hx := GaussianGammaNegativeIntervalNative.negative_regular a b N ha.andE₁
  have hy := GaussianGammaNegativeIntervalNative.negative_regular c b N hc.andE₁
  have hu := unit_positive (Γ := Γ) s
  have rate := GaussianNamedMultiplyRate.independent_rate C G C G S x S y zero one A U
    (GaussianNameBounds.U G x) one (le_refl one) hu hs hx hs hy
    (GaussianNameBounds.all_samples_bounded G x hx) (sign_samples N)
    (GaussianNamedAddRate.self_rate C S hs) (original_gamma_rate s a c b E N ha hc hIn)
  exact GaussianNamedDifferenceRate.rate_parameters_congr signedF signedF _ _ _ _ _ _
    (by unfold leadingNumerator; ipra_ring) (by unfold leadingDenominator; ipra_ring) rate

private theorem common_denominator_rate (s a c b E N : PTm n)
    (ha : Γ ⊢[PRAAx] window a b E) (hc : Γ ⊢[PRAAx] window c b E)
    (hIn : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c b) one (unit (modulus s E N))) :
    Γ ⊢[PRAAx] independentRate L L (nameData a b N) (nameData c b N) one (unit s) := by
  let t := time s E N
  let U := unit t
  let A := gammaCost E N
  let M := GaussianGammaNegativeIntervalLogAbsoluteRetiming.margin N
  have hu := unit_positive (Γ := Γ) t
  have native := signed_rate t a c b E N ha hc hIn
  have moved := GaussianNamedRateTransport.transport signedF signedF inputF inputF _ _ _ _ A U hu native
    (cross_symm _ _ _ _ (input_cross a b N ha.andE₁)) (cross_symm _ _ _ _ (input_cross c b N hc.andE₁))
  have log := GaussianNamedPositiveLogarithmRate.log_rate inputF inputF (inputData a b N) (inputData c b N) M _ _ A U
    (positive_source a b N ha.andE₁) (positive_source c b N hc.andE₁) hu moved
  have fast := GaussianNamedRateRadius.weaken R R (rd a b N) (rd c b N) (M*A) U one (unit s)
    hu (unit_positive s) (le_congr (.eqRefl _) (one_mul U).eqSymm (GaussianFastValueCut.query_budget (logCost E N) s)) log
  exact GaussianNamedRateTransport.transport R R L L _ _ _ _ one (unit s) (unit_positive s) fast
    (log_cross a b N ha.andE₁) (log_cross c b N hc.andE₁)

private theorem rescaled_window (a b E T : PTm n)
    (h : Γ ⊢[PRAAx] window a b E) (hT : Γ ⊢[PRAAx] le one T) :
    Γ ⊢[PRAAx] window (T*a) (T*b) E := by
  refine .andI (GaussianGammaNegativeIntervalRescale.guard_rescale a b T h.andE₁ hT)
    (.andI h.andE₂.andE₁ (.andI ?_ ?_))
  · exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right T h.andE₂.andE₂.andE₁)
  · exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right T h.andE₂.andE₂.andE₂)

private theorem window_congr {a b b' E : PTm n} (e : Γ ⊢[PRAAx] b ≐ b')
    (h : Γ ⊢[PRAAx] window a b E) : Γ ⊢[PRAAx] window a b' E := by
  simpa only [GaussianEulerUnitCompactTimeBounds.subst_source,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqSubst (window (var 0) (var 1) (var 2) : Fm PTm 3) ![a,b,E] ![a,b',E]
      (fun k => by fin_cases k; exact .eqRefl a; exact e; exact .eqRefl E) (by simpa using h)

private theorem log_data_congr {a b b' N : PTm n} (e : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] nameData a b N ≐ nameData a b' N := by
  simpa only [GaussianGammaNegativeIntervalLogAbsolute.subst_nameData,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (nameData (var 0) (var 1) (var 2) : PTm 3) (σ := ![a,b,N]) (σ' := ![a,b',N])
      (fun k => by fin_cases k; exact .eqRefl a; exact e; exact .eqRefl N)

theorem rational_rate (s a b c d E N : PTm n)
    (ha : Γ ⊢[PRAAx] window a b E) (hc : Γ ⊢[PRAAx] window c d E)
    (hIn : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) one (unit (modulus s E N))) :
    Γ ⊢[PRAAx] independentRate L L (nameData a b N) (nameData c d N) one (unit s) := by
  let B := d*b
  let A := d*a
  let C' := b*c
  have hb := le_trans ha.andE₁.andE₁ (le_of_lt ha.andE₁.andE₂)
  have hd := le_trans hc.andE₁.andE₁ (le_of_lt hc.andE₁.andE₂)
  have hB : Γ ⊢[PRAAx] le one B := positive_product _ _ hd hb
  have ha' : Γ ⊢[PRAAx] window A B E := rescaled_window a b E d ha hd
  have hc' : Γ ⊢[PRAAx] window C' B E :=
    window_congr (a := C') (E := E) (mul_comm b d) (rescaled_window c d E b hc hb)
  have input : Γ ⊢[PRAAx] distanceBounded (fraction A B) (fraction C' B) one (unit (modulus s E N)) :=
    distance_congr (fraction_same A B a b hB hb (by dsimp only [A,B]; ipra_ring)).eqSymm
      (fraction_same C' B c d hB hd (by dsimp only [C',B]; ipra_ring)).eqSymm (.eqRefl _) (.eqRefl _) hIn
  have left := GaussianGammaNegativeIntervalLogAbsoluteProperness.log_absolute_rescale a b d N ha.andE₁ hd
  have right := GaussianGammaCompactCutoffAlignment.cross_data_congr L L (nameData C' (b*d) N) (nameData C' B N)
    (nameData c d N) (nameData c d N) (log_data_congr (a := C') (N := N) (mul_comm b d)) (.eqRefl _)
    (GaussianGammaNegativeIntervalLogAbsoluteProperness.log_absolute_rescale c d b N hc.andE₁ hb)
  exact GaussianNamedRateTransport.transport L L L L _ _ _ _ one (unit s) (unit_positive s)
    (common_denominator_rate s A C' B E N ha' hc' input)
    (cross_symm _ _ _ _ left) (cross_symm _ _ _ _ right)

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedLogVariation
