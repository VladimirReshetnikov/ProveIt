import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Named.GaussianGammaDigammaTwoShiftNamedFreeze
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.GaussianGammaDigammaTwoShiftBinding
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedAddRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedUniformRateClosure
import IPRADerivations.Analysis.Stirling.GaussianStirlingNames

/-!
# Original normalized Gamma ratio on regular positive real names

The name uses the original real log-Gamma programs at the two endpoints
and the original logarithm of the base. Its normalized quotient log
has a uniform independent rate to the checked rational quotient log
at the common late chart.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedBinding

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaTwoShiftNamedFreeze (source baseLogF baseLogData baseNumerator leftNumerator rightNumerator
  chartDenominator clock freeze_operands baseLog_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRightHalfPlane (threshold)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianSignedNameExponentialOrder (realSamples own_sample_rate)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData gammaLogMargin log_gamma_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "GF" => GaussianGammaMinimumFreeze.nameF
local notation "GD" => GaussianGammaMinimumFreeze.data
local notation "Diff" => GaussianNamedDifference.nameF
local notation "DD" => GaussianNamedDifference.data
local notation "RF" => GaussianGammaDigammaTwoShiftBinding.quotientLogF
local notation "RD" => GaussianGammaDigammaTwoShiftBinding.quotientLogData
local notation "U" => GaussianNameBounds.U

def powerLogF (f g h : PR 2) : PR 2 := multiplyF (Diff g h) (baseLogF f)
def powerLogData (f g h : PR 2) (x y z M : PTm n) : PTm n :=
  multiplyData (Diff g h) (baseLogF f) (DD y z) (baseLogData x M)

def denominatorLogF (f g h : PR 2) : PR 2 := addF (GF h) (powerLogF f g h)
def denominatorLogData (f g h : PR 2) (x y z M : PTm n) : PTm n := addData (GD z M) (powerLogData f g h x y z M)

def quotientLogF (f g h : PR 2) : PR 2 := Diff (GF g) (denominatorLogF f g h)
def quotientLogData (f g h : PR 2) (x y z M : PTm n) : PTm n :=
  DD (GD y M) (denominatorLogData f g h x y z M)

def quotientF (f g h : PR 2) : PR 2 := GaussianRadiusExponentialName.nameF (quotientLogF f g h)
def quotientData (f g h : PR 2) (x y z M : PTm n) : PTm n :=
  GaussianGammaFiniteApproximantName.exponentialInputData (quotientLogF f g h) (quotientLogData f g h x y z M)

def powerBudget (f g h : PR 2) (x y z M : PTm n) : PTm n :=
  GaussianNamedUniformRateClosure.productBudget two (two*M) (U (baseLogF f) (baseLogData x M)) (U (Diff g h) (DD y z))

def budget (f g h : PR 2) (x y z M : PTm n) : PTm n := gammaLogMargin+(gammaLogMargin+powerBudget f g h x y z M)

ipra_subst quotientLogData [denominatorLogData, powerLogData]

ipra_subst quotientData [GaussianGammaFiniteApproximantName.exponentialInputData]

ipra_subst budget [powerBudget, GaussianNamedUniformRateClosure.productBudget, GaussianStirlingGammaLogarithm.gammaLogMargin, one, two]

theorem quotient_log_regular (f g h : PR 2) (x y z M : PTm n) (hs : Γ ⊢[PRAAx] source f g h x y z M) :
    Γ ⊢[PRAAx] pointCN (quotientLogF f g h) (quotientLogData f g h x y z M) :=
  GaussianNamedDifference.name_regular _ _ _ _ (GaussianGammaMinimumFreeze.name_regular g y M hs.andE₂.andE₁)
    (add_fast _ _ _ _ (GaussianGammaMinimumFreeze.name_regular h z M hs.andE₂.andE₂)
      (multiply_fast _ _ _ _
        (GaussianNamedDifference.name_regular _ _ _ _ hs.andE₂.andE₁.andE₁.andE₁ hs.andE₂.andE₂.andE₁.andE₁)
        (baseLog_regular f x M hs.andE₁)))

theorem quotient_regular (f g h : PR 2) (x y z M : PTm n) (hs : Γ ⊢[PRAAx] source f g h x y z M) :
    Γ ⊢[PRAAx] pointCN (quotientF f g h) (quotientData f g h x y z M) :=
  GaussianStirlingLogDuplication.exponential_regular _ _ (quotient_log_regular f g h x y z M hs)

private theorem difference_real (f g : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] realSamples f x)
    (hg : Γ ⊢[PRAAx] realSamples g y) :
    Γ ⊢[PRAAx] realSamples (Diff f g) (DD x y) :=
  GaussianStirlingNames.add_real _ _ _ _ hf (GaussianNamedDampingPowerRealSamples.negative_real _ _ hg)

theorem quotient_log_real (f g h : PR 2) (x y z M : PTm n) (hs : Γ ⊢[PRAAx] source f g h x y z M) :
    Γ ⊢[PRAAx] realSamples (quotientLogF f g h) (quotientLogData f g h x y z M) :=
  difference_real _ _ _ _
    (GaussianStirlingNames.positive_log_real _ _ _)
    (GaussianStirlingNames.add_real _ _ _ _
      (GaussianStirlingNames.positive_log_real _ _ _)
      (GaussianStirlingNames.multiply_real _ _ _ _
        (difference_real _ _ _ _ hs.andE₂.andE₁.andE₂ hs.andE₂.andE₂.andE₂)
        (GaussianStirlingNames.positive_log_real _ _ _)))

private theorem difference_rate (F G H K : PR 2) (x y u v A B D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (hh : Γ ⊢[PRAAx] pointCN H u) (hk : Γ ⊢[PRAAx] pointCN K v)
    (hA : Γ ⊢[PRAAx] independentRate F H x u A D) (hB : Γ ⊢[PRAAx] independentRate G K y v B D) :
    Γ ⊢[PRAAx] independentRate (Diff F G) (Diff H K) (DD x y) (DD u v) (A+B) D := by
  have raw := GaussianNamedDifferenceRate.original_rate F G H K x y u v A D B D
    (.andI (.andI hD hD) (.andI (.andI hf hg) (.andI (.andI hh hk) (.andI hA hB))))
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hD hD) hD
    (le_of_eq_add (d := zero) (by simp only [GaussianNamedDifferenceRate.leadingNumerator]; ipra_ring)) raw

private theorem addition_rate (F G H K : PR 2) (x y u v A B D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D)
    (hA : Γ ⊢[PRAAx] independentRate F H x u A D) (hB : Γ ⊢[PRAAx] independentRate G K y v B D) :
    Γ ⊢[PRAAx] independentRate (addF F G) (addF H K) (addData x y) (addData u v) (A+B) D := by
  have raw := GaussianNamedAddRate.independent_rate F G H K x y u v A D B D hD hD hA hB
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hD hD) hD
    (le_of_eq_add (d := zero) (by simp only [GaussianNamedRateComposition.leadingNumerator]; ipra_ring)) raw

private theorem constant_difference (a b : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (Diff constantF constantF) constantF (DD a b) (qsub a b) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 6)
    (GaussianNamedDifference.name_regular _ _ _ _ (constant_regular _) (constant_regular _)) (constant_regular _)
  refine .allI ?_
  have raw := GaussianNamedDifference.sample_error (Γ := Γ.map Fm.shift) constantF constantF
    (Syn.shift a) (Syn.shift b) (var 0) (constant_regular _) (constant_regular _)
  have actual := distance_congr (.eqRefl _)
    ((qsub_congr (constant_at _ _) (constant_at _ _)).eqTrans (constant_at (var 0) (qsub (Syn.shift a) (Syn.shift b))).eqSymm)
    (.eqRefl _) (.eqRefl _) raw
  simpa only [GaussianNamedDifference.subst_data,GaussianRationalMetric.subst_qsub,PTm.subst_num,Syn.shift] using actual

private theorem sampled_rate (f : PR 2) (x s k q : PTm n) (h : Γ ⊢[PRAAx] pointCN f x)
    (hsk : Γ ⊢[PRAAx] le s k) (hq : Γ ⊢[PRAAx] ap2 f k x ≐ q) :
    Γ ⊢[PRAAx] independentRate f constantF x q one (unit s) := by
  have grow := GaussianExponentialReference.unit_monotone hsk
  have raw : Γ ⊢[PRAAx] independentRate f constantF x (ap2 f k x) one (unit s) :=
    GaussianNamedRateRadius.weaken f constantF x (ap2 f k x) one (unit k) one (unit s)
      (unit_positive k) (unit_positive s) (by ipra_le sl grow) (own_sample_rate f x k h)
  exact GaussianNamedRateTransport.transport f constantF f constantF x (ap2 f k x) x q one (unit s)
    (unit_positive s) raw (cross_refl f x h)
    (GaussianSignedNameExponentialOrder.constant_equal_cross q (ap2 f k x) hq.eqSymm)

private theorem coefficient_rate (g h : PR 2) (y z s k b c d : PTm n)
    (hy : Γ ⊢[PRAAx] pointCN g y) (hz : Γ ⊢[PRAAx] pointCN h z)
    (hk : Γ ⊢[PRAAx] le s k)
    (hc : Γ ⊢[PRAAx] ap2 g k y ≐ fraction c b) (hd : Γ ⊢[PRAAx] ap2 h k z ≐ fraction d b) :
    Γ ⊢[PRAAx] independentRate (Diff g h) constantF (DD y z) (GaussianGammaDigammaTwoShiftBinding.coefficient b c d) two (unit s) := by
  have hD := unit_positive (Γ := Γ) s
  have raw := difference_rate g h constantF constantF y z (fraction c b) (fraction d b) one one (unit s)
    hD hy hz (constant_regular _) (constant_regular _) (sampled_rate g y s k _ hy hk hc) (sampled_rate h z s k _ hz hk hd)
  let a := fraction c b
  let e := fraction d b
  let u := qsub a e
  have hLeft := GaussianNamedDifference.name_regular g h y z hy hz
  have hRight := constant_difference (Γ := Γ) a e
  exact GaussianNamedRateTransport.transport (Diff g h) (Diff constantF constantF) (Diff g h) constantF
    (DD y z) (DD a e) (DD y z) u two (unit s) hD
    (GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ (one+one) (unit s) two (unit s)
      (by ipra_ring) (.eqRefl _) raw)
    (cross_refl (Diff g h) (DD y z) hLeft)
    (cross_symm (Diff constantF constantF) constantF (DD a e) u hRight)

def frozenRate (f g h : PR 2) (s x y z M : PTm n) : Fm PTm n :=
  let k := clock g h s y z M
  let a := baseNumerator f g h k x y z
  let b := chartDenominator f g h k x y z
  let c := leftNumerator f g h k x y z
  let d := rightNumerator f g h k x y z
  independentRate (quotientLogF f g h) RF (quotientLogData f g h x y z M) (RD a b c d)
    (budget f g h x y z M) (unit s)

theorem frozen_log_rate (f g h : PR 2) (s x y z M : PTm n) (hs : Γ ⊢[PRAAx] source f g h x y z M) :
    Γ ⊢[PRAAx] frozenRate f g h s x y z M := by
  let k := clock g h s y z M
  let a := baseNumerator f g h k x y z
  let b := chartDenominator f g h k x y z
  let c := leftNumerator f g h k x y z
  let d := rightNumerator f g h k x y z
  let L := GaussianHarmonicLogarithmName.nameF
  let l := GaussianHarmonicLogarithmName.data a b
  let C := GaussianGammaDigammaTwoShiftBinding.coefficient b c d
  let P := GaussianGammaDigammaTwoShiftBinding.powerLogF
  let u := GaussianGammaDigammaTwoShiftBinding.powerLogData a b c d
  have hD := unit_positive (Γ := Γ) s
  have hk : Γ ⊢[PRAAx] le (threshold M) k := le_add_left _ _
  have hsk : Γ ⊢[PRAAx] le s k := le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have chart := GaussianGammaDigammaTwoShiftNamedFreeze.charts f g h k x y z M hs hk
  have val := GaussianGammaDigammaTwoShiftNamedFreeze.values f g h k x y z M hs hk
  have hy := hs.andE₂.andE₁.andE₁.andE₁
  have hz := hs.andE₂.andE₂.andE₁.andE₁
  have coeff := coefficient_rate g h y z s k b c d hy hz hsk val.andE₂.andE₁ val.andE₂.andE₂
  have regs := freeze_operands f g h s x y z M hs
  have left := baseLog_regular f x M hs.andE₁
  have coefReg := GaussianNamedDifference.name_regular _ _ _ _ hy hz
  have right := GaussianHarmonicLogarithmName.name_regular a b chart.andE₁
  have product : Γ ⊢[PRAAx] independentRate (powerLogF f g h) P (powerLogData f g h x y z M) u
      (powerBudget f g h x y z M) (unit s) :=
    GaussianNamedUniformRateClosure.same_denominator_product (Diff g h) (baseLogF f) constantF L
      (DD y z) (baseLogData x M) C l two (two*M) (unit s) _ _ hD coefReg left (constant_regular C) right
      (GaussianNameBounds.all_samples_bounded _ _ left) (GaussianNameBounds.all_samples_bounded _ _ coefReg) coeff regs.andE₁
  have denom := addition_rate (GF h) (powerLogF f g h) logGammaF P (GD z M) (powerLogData f g h x y z M)
    (logGammaData d b) u gammaLogMargin (powerBudget f g h x y z M) (unit s) hD regs.andE₂.andE₂ product
  have regY := GaussianGammaMinimumFreeze.name_regular g y M hs.andE₂.andE₁
  have regZ := GaussianGammaMinimumFreeze.name_regular h z M hs.andE₂.andE₂
  have regDenom : Γ ⊢[PRAAx] pointCN (denominatorLogF f g h) (denominatorLogData f g h x y z M) :=
    add_fast _ _ _ _ regZ (multiply_fast _ _ _ _ coefReg left)
  exact difference_rate (GF g) (denominatorLogF f g h) logGammaF GaussianGammaDigammaTwoShiftBinding.denominatorLogF
    (GD y M) (denominatorLogData f g h x y z M) (logGammaData c b) (GaussianGammaDigammaTwoShiftBinding.denominatorLogData a b c d)
    gammaLogMargin (gammaLogMargin+powerBudget f g h x y z M) (unit s) hD regY regDenom
    (log_gamma_regular c b chart.andE₂.andE₁)
    (GaussianGammaDigammaTwoShiftBinding.denominator_log_regular a b c d chart.andE₁ chart.andE₂.andE₂)
    regs.andE₂.andE₁ denom

theorem actual_named_two_shift_quotient_log_frozen_closed (f g h : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f g h (var 1) (var 2) (var 3) (var 4) ⟶ frozenRate f g h (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (frozen_log_rate f g h _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedBinding
