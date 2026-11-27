import IPRADerivations.Analysis.Stirling.Bounds.Logarithmic.GaussianStirlingGlobalBoundsShiftAlgebra
import IPRADerivations.Analysis.Stirling.Robbins.GaussianStirlingRobbins
import IPRADerivations.Analysis.Stirling.Bounds.Logarithmic.GaussianStirlingGlobalBoundsRemainder
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedInverseRate

/-!
# Transport of the logarithmic gamma squeeze to the original Stirling limit

A positive fractional part and its reference integer use the same
cofinal clock. The original Stirling increment differs from the
logarithmic gamma increment error by the bounded elementary correction.
The final rate is uniform over all positive rational shifts.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingGlobalBoundsTranslatedRate

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (cross_diagonal_at)
open GaussianNameRingLaws (add_sample_error)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded qsub qsub_canonical)
open GaussianRationalReciprocal (bound_congr)
open GaussianStirlingGlobalBounds (translatedRate translatedPoint limitRemainderF limitRemainderData firstOrderBounds)
open GaussianStirlingGlobalBoundsShiftArguments
  (shiftedNumerator fractionNumerator integerAnchor deltaF deltaData slopeF slopeData delta_regular slope_regular
    fractional_guard anchor_later anchor_pred_later argument_readback shifted_positive)
open GaussianStirlingGlobalBoundsShiftCorrection (correctionF correctionData correction_regular uniform_sample_bound)
open GaussianStirlingGlobalBoundsShiftAlgebra
  (differenceF differenceData slopeResidualF slopeResidualData slope_residual_regular splitF splitData exact_split)
open GaussianStirlingNames (source nameData name_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "A" => GaussianStirlingNames.nameF
local notation "I" => GaussianStirlingIntegerLimit.nameF
local notation "C" => GaussianStirlingConstant.nameF

/-- The logarithmic gamma squeeze with its canonical named arguments. -/
def incrementRate (i r b : PTm n) : Fm PTm n :=
  independentRate deltaF slopeF (deltaData i r b) (slopeData i r b) one (pred i)

ipra_subst incrementRate

theorem shift_bound (i r b p : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hb : Γ ⊢[PRAAx] le one b)
    (hr : Γ ⊢[PRAAx] le r b) (hp : Γ ⊢[PRAAx] le (unit p) (pred i))
    (hc : Γ ⊢[PRAAx] incrementRate i r b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 A p (nameData (shiftedNumerator i r b) b)) (ap2 A p (nameData i one))
      (num 28) (unit p) := by
  let U := unit p
  let N := pred i
  let d := ap2 deltaF p (deltaData i r b)
  let s := ap2 slopeF p (slopeData i r b)
  let z := slopeResidualData i r b
  let w := correctionData i r b
  let S := ap2 slopeResidualF p z
  let T := ap2 correctionF p w
  let x := nameData (shiftedNumerator i r b) b
  let y := nameData i one
  let M := ap2 A p x
  let K := ap2 A p y
  have hu := unit_positive (Γ := Γ) p
  have hN := le_trans hu hp
  have e := natEq (pos_of_one_le hi)
  have hpred : Γ ⊢[PRAAx] le N i := by
    dsimp [N]
    ipra_le 1 using linear_combination e
  have hI : Γ ⊢[PRAAx] le U i := le_trans hp hpred
  have gamma := diagonal_rate deltaF slopeF (deltaData i r b) (slopeData i r b) one N p hN hc
  have smallGamma : Γ ⊢[PRAAx] distanceBounded d s (num 3) U :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hN hu) hu (by ipra_le 𝔞 U*sl hp) gamma
  have toZero : Γ ⊢[PRAAx] distanceBounded (qsub d s) qzero (num 3) U :=
    bound_congr (GaussianRationalReconstruction.qsub_zero_right (qsub d s) (qsub_canonical _ _)).eqSymm
      (.eqRefl _) (.eqRefl _) smallGamma
  have sr := GaussianNamedDifference.sample_error deltaF slopeF (deltaData i r b) (slopeData i r b) p
    (delta_regular i r b hi hb) (slope_regular i r b hi)
  have Ssmall : Γ ⊢[PRAAx] distanceBounded S qzero (num 9) U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hu sr toZero)
  have Tsmall : Γ ⊢[PRAAx] distanceBounded T qzero (num 8) U :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hi hu) hu (by ipra_le 5*𝔞 U*sl hI)
      (uniform_sample_bound i r b p hi hb hr)
  have sum := GaussianNameArithmetic.sum_distance S qzero T qzero (num 9) (num 8) U hu Ssmall Tsmall
  have addition := add_sample_error slopeResidualF correctionF z w p
    (slope_residual_regular i r b hi hb) (correction_regular i r b hi hb)
  have splitSmall : Γ ⊢[PRAAx] distanceBounded (ap2 splitF p (splitData i r b)) qzero (num 20) U :=
    distance_congr (.eqRefl _) GaussianRationalMonicReconstruction.zero_add_zero
      (by dsimp [GaussianNameRingLaws.three]; ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hu addition sum)
  have split := cross_diagonal_at p (exact_split i r b hi hb)
  have obs := GaussianNamedDifference.sample_error A A x y p
    (name_regular _ _ (.andI (shifted_positive _ _ _ hi hb) hb)) (name_regular _ _ (.andI hi (le_refl one)))
  have mid := distance_triangle_same _ _ _ _ _ _ hu split splitSmall
  have raw : Γ ⊢[PRAAx] distanceBounded (qsub M K) qzero (num 28) U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hu (distance_symmetric _ _ _ _ hu obs) mid)
  exact bound_congr (GaussianRationalReconstruction.qsub_zero_right (qsub M K) (qsub_canonical _ _))
    (.eqRefl _) (.eqRefl _) raw

theorem anchor_readback (a b p : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] ap2 A p (nameData (shiftedNumerator (integerAnchor a b p) (fractionNumerator a b) b) b)
      ≐ translatedPoint a b p := by
  apply congrAp2 A (.eqRefl _)
  have h := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (nameData (var 0) (var 1) : PTm 2)
    (σ := ![shiftedNumerator (integerAnchor a b p) (fractionNumerator a b) b, b])
    (σ' := ![GaussianStirlingTelescope.shifted a b (GaussianStirlingGlobalBounds.steps p), b])
    (fun i => by fin_cases i; exact argument_readback a b p hs; exact .eqRefl _)
  simpa using h

theorem translated_at (a b x p : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hIncrement : Γ ⊢[PRAAx] incrementRate (integerAnchor a b p) (fractionNumerator a b) b) :
    Γ ⊢[PRAAx] distanceBounded (translatedPoint a b p) (ap2 I p x) (num 30) (unit p) := by
  let i := integerAnchor a b p
  let r := fractionNumerator a b
  let U := unit p
  have hx := anchor_later (Γ := Γ) a b p
  have hn : Γ ⊢[PRAAx] le one i := le_trans (zero_lt_succ _) hx
  have hPred := le_trans (GaussianStirlingIntegerLimit.index_dominates_unit (Γ := Γ) p) (anchor_pred_later a b p)
  have hR := (fractional_guard a b hs.andE₂).andE₂
  have first := shift_bound i r b p hn hs.andE₂ hR hPred hIncrement
  have near := distance_congr (anchor_readback a b p hs) (.eqRefl _) (.eqRefl _) (.eqRefl _) first
  have later : Γ ⊢[PRAAx] le (GaussianStirlingIntegerLimit.index p) i := le_trans (le_succ_self _) hx
  have d := GaussianStirlingIntegerLimit.later_integer_distance p p i later
    GaussianStirlingOriginalIntegerLimit.integer_tail_contract
  have hu := unit_positive (Γ := Γ) p
  have den := positive_product _ _ hu hu
  have raw := distance_congr (GaussianStirlingIntegerLimit.name_at p x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) d
  have close : Γ ⊢[PRAAx] distanceBounded (ap2 A p (nameData i one)) (ap2 I p x) two U :=
    distance_radius_mono _ _ _ _ _ _ den hu (le_of_eq_add (d := zero) (by ipra_ring))
      (distance_symmetric _ _ _ _ den raw)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu near close)

theorem translated_rate (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (provider : ∀ {l : ℕ} {Δ : List (Fm PTm l)} (i r b : PTm l), (Δ ⊢[PRAAx] le two i) →
      (Δ ⊢[PRAAx] le one b) → (Δ ⊢[PRAAx] le one r) → (Δ ⊢[PRAAx] le r b) →
      (Δ ⊢[PRAAx] incrementRate i r b)) :
    Γ ⊢[PRAAx] translatedRate a b x (num 30) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let t : PTm (n+1) := var 0
  let a' := Syn.shift a
  let b' := Syn.shift b
  let x' := Syn.shift x
  let i := integerAnchor a' b' t
  let r := fractionNumerator a' b'
  have h : Δ ⊢[PRAAx] source a' b' := by simpa [Δ,a',b',Fm.shift,Syn.shift] using hs.shift
  have pk := GaussianStirlingIntegerLimit.index_positive (Γ := Δ) t
  have twoSteps : Δ ⊢[PRAAx] le two (GaussianStirlingGlobalBounds.steps t) := by
    dsimp [GaussianStirlingGlobalBounds.steps]
    ipra_le sl pk
  have hi : Δ ⊢[PRAAx] le two i := le_trans twoSteps (anchor_later _ _ _)
  have hr := fractional_guard a' b' h.andE₂
  have ht := provider i r b' hi h.andE₂ hr.andE₁ hr.andE₂
  simpa [translatedRate,Syn.shift,Δ,t,a',b',x'] using translated_at a' b' x' t h ht

theorem first_order_from_increment (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (provider : ∀ {l : ℕ} {Δ : List (Fm PTm l)} (i r b : PTm l), (Δ ⊢[PRAAx] le two i) →
      (Δ ⊢[PRAAx] le one b) → (Δ ⊢[PRAAx] le one r) → (Δ ⊢[PRAAx] le r b) →
      (Δ ⊢[PRAAx] incrementRate i r b)) :
    Γ ⊢[PRAAx] firstOrderBounds GaussianStirlingGlobalBounds.remainderF a b (GaussianStirlingGlobalBounds.remainderData a b x) :=
  GaussianStirlingGlobalBounds.first_order_bounds a b x (num 30) hs (translated_rate a b x hs provider)
    (GaussianStirlingConstantIdentification.identification x x)

theorem rational_robbins_from_increment (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a)
    (provider : ∀ {l : ℕ} {Δ : List (Fm PTm l)} (i r b : PTm l), (Δ ⊢[PRAAx] le two i) →
      (Δ ⊢[PRAAx] le one b) → (Δ ⊢[PRAAx] le one r) → (Δ ⊢[PRAAx] le r b) →
      (Δ ⊢[PRAAx] incrementRate i r b)) :
    Γ ⊢[PRAAx] GaussianStirlingRobbins.bounds GaussianStirlingGlobalBounds.remainderF a b
      (GaussianStirlingGlobalBounds.remainderData a b x) :=
  GaussianStirlingRobbins.rational_bounds_from_rate a b x (num 30) hs hba (translated_rate a b x hs provider)

theorem positive_series_remainder (N a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (provider : ∀ {l : ℕ} {Δ : List (Fm PTm l)} (i r b : PTm l), (Δ ⊢[PRAAx] le two i) →
      (Δ ⊢[PRAAx] le one b) → (Δ ⊢[PRAAx] le one r) → (Δ ⊢[PRAAx] le r b) →
      (Δ ⊢[PRAAx] incrementRate i r b)) :
    Γ ⊢[PRAAx] GaussianNameEquivalence.crossEquivalent GaussianStirlingGlobalBoundsRemainder.sumF
      GaussianStirlingGlobalBounds.remainderF (GaussianStirlingGlobalBoundsRemainder.sumData N a b x)
      (GaussianStirlingGlobalBounds.remainderData a b x) ⋏
      (GaussianNamedPositiveExponentialOrder.realOrder GaussianGammaCanonicalExponent.constantF
        GaussianStirlingGlobalBounds.remainderF qzero
        (GaussianStirlingGlobalBounds.remainderData (GaussianStirlingTelescope.shifted a b N) b x) ⋏
        GaussianNamedPositiveExponentialOrder.realOrder GaussianStirlingGlobalBounds.remainderF
          GaussianGammaCanonicalExponent.constantF
          (GaussianStirlingGlobalBounds.remainderData (GaussianStirlingTelescope.shifted a b N) b x)
          (GaussianStirlingRationalTelescopers.upperValue (GaussianStirlingTelescope.shifted a b N) b)) :=
  GaussianStirlingGlobalBoundsRemainder.positive_series_remainder_from_rate N a b x (num 30) hs
    (translated_rate _ _ _ (GaussianStirlingTelescope.shifted_source a b N hs) provider)

end LeanProofs.IPRA.Analysis.GaussianStirlingGlobalBoundsTranslatedRate
