import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerNamed
import IPRADerivations.Analysis.Gamma.Names.Derivatives.GaussianNamedLogGammaTaylorFrozen

/-!
# Quadratic Taylor estimate for named log-Gamma

Late original rational observations provide a single signed chart for
the log-Gamma increment and displacement-times-digamma. Their exact
quadratic estimate transfers to arbitrary regular names in the open
right half-plane.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianNamedLogGammaTaylorEstimate

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianLogGammaEulerCommonDenominator
  (admissionBudget commonImag commonReal common_size common_sources continuityRadius continuity_radius_from_distance
    displacement sizeBound)
open GaussianLogGammaEulerNamed (original_chart rationalMap)
open GaussianLogGammaEulerTaylorRows (coefficient)
open GaussianNameArithmetic (multiply_equivalent)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_to_diagonal)
open GaussianNamedInverseRate (independentRate rate_at rateDenominator rateNumerator)
open GaussianNamedLogGammaTaylorFrozen (cost frozenF frozenData regular)
open GaussianNamedRightHalfPlaneLift (clock late_certificate source)
open GaussianNamedRightHalfPlaneSigned (certificate denominator imagNumerator realNumerator sign)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalValueEquality (commonDen common_den_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "logF" => GaussianLogGammaEulerNamed.nameF
local notation "logData" => GaussianLogGammaEulerNamed.data
local notation "cofinalF" => GaussianLogGammaEulerCofinal.nameF
local notation "cofinalData" => GaussianLogGammaEulerCofinal.canonicalData
local notation "digammaMap" => GaussianLogGammaEulerNamedDigamma.rationalMap
local notation "diffF" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data
local notation "productF" => GaussianNamedLogGammaTaylorFrozen.nameF
local notation "productData" => GaussianNamedLogGammaTaylorFrozen.data

def incrementF (f g : PR 2) : PR 2 := diffF (logF g) (logF f)

def incrementData (x y M R : PTm n) : PTm n := diffData (logData y M R) (logData x M R)

def quadraticBudget (P K : PTm n) : PTm n := num 16*(P*P)*(K*K+two)

private theorem small_from_distance (H P K C d D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hStep : Γ ⊢[PRAAx] le (H*D) (two*P*d))
    (hClose : Γ ⊢[PRAAx] le (admissionBudget P K C) D) : Γ ⊢[PRAAx]
    GaussianRightHalfPlaneLogarithmIncrementMargin.smallStep H K C d := by
  apply RationalValueBounds.positive_cancel (c := D) hD
  unfold admissionBudget at hClose
  ipra_le 128*(𝔞(C)+1)*𝔞(K)^2*sl hStep+𝔞(d)*sl hClose

private theorem rational_quadratic_rate (q r R S K P Qd : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K)
    (hK : Γ ⊢[PRAAx] le one K) (hQ : Γ ⊢[PRAAx] le one Qd)
    (hd : Γ ⊢[PRAAx] distanceBounded r q P Qd)
    (hClose : Γ ⊢[PRAAx] le (admissionBudget P K (sizeBound R S)) Qd) :
    Γ ⊢[PRAAx] independentRate (diffF cofinalF cofinalF) frozenF
      (diffData (GaussianLogGammaEulerNamed.pointData r) (GaussianLogGammaEulerNamed.pointData q)) (frozenData q r)
      (quadraticBudget P K) (Qd*Qd) := by
  let d := commonDen q r
  let H := continuityRadius (displacement q r)
  let C := sizeBound R S
  let A := commonReal q r
  let B := commonImag q r
  let a := commonReal r q
  let b := commonImag r q
  have hD := common_den_positive (Γ := Γ) q r
  have sources := common_sources q r R S K hq hr
  have step := continuity_radius_from_distance q r R S K P Qd hq hr hQ hd
  have src : Γ ⊢[PRAAx] GaussianLogGammaEulerTaylorUniform.source A B (sign q) a b (sign r) d H K C :=
    .andI sources.andE₁.andE₁ (.andI sources.andE₂.andE₁.andE₁
      (.andI step.andE₁ (.andI hK (.andI sources.andE₂.andE₂.andE₁ (.andI sources.andE₂.andE₂.andE₂
        (.andI (common_size q r R S K hq hr) (small_from_distance H P K C d Qd hQ step.andE₂ hClose)))))))
  have native := GaussianLogGammaEulerTaylorUniform.independent_rate A B (sign q) a b (sign r) d H K C src
  have hSq : Γ ⊢[PRAAx] le (coefficient H K*(Qd*Qd)) (quadraticBudget P K*(d*d)) := by
    have mul := mul_le_mul_right (num 4*(K*K+two)) (le_mul_mono step.andE₂ step.andE₂)
    exact le_congr (by unfold coefficient H; ipra_ring) (by unfold quadraticBudget d; ipra_ring) mul
  have coarse := GaussianNamedRateRadius.weaken _ _ _ _ (coefficient H K) (d*d) (quadraticBudget P K) (Qd*Qd)
    (positive_product _ _ hD hD) (positive_product _ _ hQ hQ) hSq native
  have chart := original_chart q r R S K hq hr
  have regular_q := GaussianLogGammaEulerCofinal.canonical_regular A B d (sign q) src.andE₁
  have regular_r := GaussianLogGammaEulerCofinal.canonical_regular a b d (sign r) src.andE₂.andE₁
  have regular_original_q := GaussianLogGammaEulerCofinal.canonical_regular
    (realNumerator q) (imagNumerator q) (denominator q) (sign q) hq.andE₁.andE₁
  have regular_original_r := GaussianLogGammaEulerCofinal.canonical_regular
    (realNumerator r) (imagNumerator r) (denominator r) (sign r) hr.andE₁.andE₁
  have left := GaussianNamedDifferenceQuotientProperness.difference_proper cofinalF cofinalF cofinalF cofinalF
    _ _ _ _ regular_original_r regular_r regular_original_q regular_q
    (cross_symm _ _ _ _ chart.andE₂) (cross_symm _ _ _ _ chart.andE₁)
  have eqSlope := GaussianLogGammaEulerDigammaFractionsCofinal.cofinal_equivalent A B d (sign q) src.andE₁
  have slope := GaussianLogGammaEulerReciprocalSlopeCofinal.canonical_regular A B d (sign q) src.andE₁
  have series := GaussianLogGammaEulerDigammaFractionsCofinal.regular A B d (sign q) src.andE₁
  have right := multiply_equivalent constantF constantF _ _ _ _ _ _
    (constant_regular (GaussianNamedLogGammaTaylorFrozen.step q r)) (constant_regular _) series slope
    (cross_to_diagonal _ _ _ _ (cross_refl _ _ (constant_regular _)))
    (cross_to_diagonal _ _ _ _ (cross_symm _ _ _ _ eqSlope))
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ (quadraticBudget P K) (Qd*Qd)
    (positive_product _ _ hQ hQ) coarse left right

private theorem log_frozen (f : PR 2) (x M R s k : PTm n)
    (h : Γ ⊢[PRAAx] source f x M R) (hk : Γ ⊢[PRAAx] le (clock rationalMap s M R) k) :
    Γ ⊢[PRAAx] independentRate (logF f) cofinalF (logData x M R)
      (GaussianLogGammaEulerNamed.pointData (ap2 f k x)) one (unit s) := by
  let q := ap2 f k x
  let z := GaussianLogGammaEulerNamed.pointData q
  let w := GaussianNamedRightHalfPlaneLift.frozenData rationalMap f k x
  have raw := GaussianNamedRightHalfPlaneLift.frozen_rate rationalMap f s k x M R h hk
  have hc := late_certificate f x k M R h (le_trans (GaussianNamedRightHalfPlaneLift.clock_margin rationalMap s M R) hk)
  have hz : Γ ⊢[PRAAx] pointCN cofinalF z := GaussianLogGammaEulerCofinal.canonical_regular _ _ _ _ hc.andE₁.andE₁
  have eq : Γ ⊢[PRAAx] z ≐ w := (GaussianLogGammaEulerNamed.rational_data_at q).eqSymm
  exact GaussianNamedRateTransport.transport (logF f) cofinalF (logF f) cofinalF
    (logData x M R) w (logData x M R) z one (unit s) (unit_positive s) raw
    (cross_refl _ _ (GaussianLogGammaEulerNamed.name_regular f x M R h))
    (cross_data_congr cofinalF cofinalF z z z w (.eqRefl _) eq (cross_refl _ _ hz))

private theorem increment_frozen (f g : PR 2) (x y M R s k : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hg : Γ ⊢[PRAAx] source g y M R)
    (hk : Γ ⊢[PRAAx] le (clock rationalMap s M R) k) :
    Γ ⊢[PRAAx] independentRate (incrementF f g) (diffF cofinalF cofinalF) (incrementData x y M R)
      (diffData (GaussianLogGammaEulerNamed.pointData (ap2 g k y)) (GaussianLogGammaEulerNamed.pointData (ap2 f k x)))
      two (unit s) := by
  let D := unit s
  have hD := unit_positive (Γ := Γ) s
  have hk0 := le_trans (GaussianNamedRightHalfPlaneLift.clock_margin (Γ := Γ) rationalMap s M R) hk
  have hq := late_certificate f x k M R hf hk0
  have hr := late_certificate g y k M R hg hk0
  let q := ap2 f k x
  let r := ap2 g k y
  have rg := GaussianLogGammaEulerCofinal.canonical_regular
    (realNumerator r) (imagNumerator r) (denominator r) (sign r) hr.andE₁.andE₁
  have rf := GaussianLogGammaEulerCofinal.canonical_regular
    (realNumerator q) (imagNumerator q) (denominator q) (sign q) hq.andE₁.andE₁
  have raw := GaussianNamedDifferenceRate.original_rate (logF g) (logF f) cofinalF cofinalF
    (logData y M R) (logData x M R) _ _ one D one D
    (.andI (.andI hD hD) (.andI (.andI (GaussianLogGammaEulerNamed.name_regular g y M R hg)
      (GaussianLogGammaEulerNamed.name_regular f x M R hf)) (.andI (.andI rg rf)
        (.andI (log_frozen g y M R s k hg hk) (log_frozen f x M R s k hf hk)))))
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ two D (positive_product _ _ hD hD) hD
    (le_of_eq_add (d := zero) (by
      dsimp only [D, GaussianNamedDifferenceRate.leadingNumerator, GaussianNamedDifferenceRate.leadingDenominator]
      ipra_ring)) raw

def freezeCost (f : PR 2) (x M R : PTm n) : PTm n := two+cost f x M R

theorem selected_sample_rate (f g : PR 2) (x y M R s k P Qd : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hg : Γ ⊢[PRAAx] source g y M R)
    (hs : Γ ⊢[PRAAx] le s k)
    (hl : Γ ⊢[PRAAx] le (clock rationalMap s M R) k)
    (hp : Γ ⊢[PRAAx] le (clock digammaMap s M R) k)
    (hQ : Γ ⊢[PRAAx] le one Qd)
    (hd : Γ ⊢[PRAAx] distanceBounded (ap2 g k y) (ap2 f k x) P Qd)
    (hClose : Γ ⊢[PRAAx] le (admissionBudget P (two*M) (sizeBound R R)) Qd) :
    Γ ⊢[PRAAx] independentRate (incrementF f g) (productF f g) (incrementData x y M R) (productData f g x y M R)
      (quadraticBudget P (two*M)*unit s+freezeCost f x M R*(Qd*Qd)) ((Qd*Qd)*unit s) := by
  let q := ap2 f k x
  let r := ap2 g k y
  let K := two*M
  let V := Qd*Qd
  let D := unit s
  let E := quadraticBudget P K
  let C := cost f x M R
  have hD := unit_positive (Γ := Γ) s
  have hV := positive_product _ _ hQ hQ
  have hK : Γ ⊢[PRAAx] le one K := positive_product _ _ (zero_lt_succ _) hf.andE₁.andE₂.andE₁
  have hk := le_trans (GaussianNamedRightHalfPlaneLift.clock_margin (Γ := Γ) rationalMap s M R) hl
  have hq := late_certificate f x k M R hf hk
  have hr := late_certificate g y k M R hg hk
  have left := increment_frozen f g x y M R s k hf hg hl
  have middle := rational_quadratic_rate q r R R K P Qd hq hr hK hQ hd hClose
  have right := GaussianNamedRateComposition.symmetric _ _ _ _ C D hD
    (GaussianNamedLogGammaTaylorFrozen.frozen_rate f g x y M R s k hf hg hs hp)
  have both := GaussianNamedRateComposition.compose _ _ _ _ _ _ two D E V hD hV left middle
  have joined := GaussianNamedRateComposition.compose _ _ _ _ _ _ _ _ C D (positive_product _ _ hD hV) hD both right
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hD hV) hD)
    (positive_product _ _ hV hD) (le_of_eq_add (d := zero) (by
      dsimp only [freezeCost, C, D, E, V, GaussianNamedRateComposition.leadingNumerator,
        GaussianNamedRateComposition.leadingDenominator]
      ipra_ring)) joined

def admission (P K C : PTm n) : PTm n := two*admissionBudget P K C

def slackCost (f : PR 2) (x M R P : PTm n) : PTm n :=
  freezeCost f x M R+num 64*((two*M)*(two*M)+two)*(P+one)

private def selectedClock (s M R : PTm n) : PTm n :=
  ((clock rationalMap s M R+clock digammaMap s M R)+s)+
    exponent (num 4*admissionBudget one (two*M) (sizeBound R R)) zero

private theorem sample_admission (P K C Qd V : PTm n)
    (ha : Γ ⊢[PRAAx] le (admission P K C) Qd)
    (hV : Γ ⊢[PRAAx] le (num 4*admissionBudget one K C) V) : Γ ⊢[PRAAx]
    le (admissionBudget (P*V+two*Qd) K C) (Qd*V) := by
  apply RationalValueBounds.positive_cancel (c := two) (zero_lt_succ _)
  unfold admission admissionBudget at ha
  unfold admissionBudget at hV ⊢
  ipra_le 𝔞(V)*sl ha+𝔞(Qd)*sl hV

private theorem enlarged_budget (f : PR 2) (x M R P Qd U V : PTm n)
    (hQV : Γ ⊢[PRAAx] le U (Qd*V)) (hVV : Γ ⊢[PRAAx] le U (V*V)) : Γ ⊢[PRAAx]
    le ((quadraticBudget (P*V+two*Qd) (two*M)*U+freezeCost f x M R*((Qd*V)*(Qd*V)))*((Qd*Qd)*U))
      ((quadraticBudget P (two*M)*U+slackCost f x M R P*(Qd*Qd))*(((Qd*V)*(Qd*V))*U)) := by
  unfold quadraticBudget slackCost
  ipra_le 64*((2*𝔞(M))^2+2)*𝔞(Qd)^2*𝔞(U)*
    (𝔞(P)*𝔞(Qd)*𝔞(V)*sl hQV+𝔞(Qd)^2*sl hVV)

private theorem dyadic_rate (f g : PR 2) (x y M R P Qd s : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hg : Γ ⊢[PRAAx] source g y M R)
    (hQ : Γ ⊢[PRAAx] le one Qd)
    (ha : Γ ⊢[PRAAx] le (admission P (two*M) (sizeBound R R)) Qd)
    (hn : Γ ⊢[PRAAx] independentRate g f y x P Qd) : Γ ⊢[PRAAx]
    independentRate (incrementF f g) (productF f g) (incrementData x y M R) (productData f g x y M R)
      (quadraticBudget P (two*M)*unit s+slackCost f x M R P*(Qd*Qd)) ((Qd*Qd)*unit s) := by
  let k := selectedClock s M R
  let K := two*M
  let C := sizeBound R R
  let X := num 4*admissionBudget one K C
  let U := unit s
  let V := unit k
  let D := Qd*V
  have hU := unit_positive (Γ := Γ) s
  have hV := unit_positive (Γ := Γ) k
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hQ hV
  have hl : Γ ⊢[PRAAx] le (clock rationalMap s M R) k := by
    unfold k selectedClock
    exact le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have hp : Γ ⊢[PRAAx] le (clock digammaMap s M R) k := by
    unfold k selectedClock
    exact le_trans (le_add_left _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have hs : Γ ⊢[PRAAx] le s k := by
    unfold k selectedClock
    exact le_trans (le_add_left _ _) (le_add_right _ _)
  have hb : Γ ⊢[PRAAx] le (exponent X zero) k := le_add_left _ _
  have oneAtZero : Γ ⊢[PRAAx] unit zero ≐ one := pw_zero two
  have cap : Γ ⊢[PRAAx] le X V := le_trans
    (le_congr ((congrMul (.eqRefl X) oneAtZero).eqTrans (by ipra_ring)) (.eqRefl _)
      (query_budget X zero)) (unit_monotone hb)
  have near : Γ ⊢[PRAAx] distanceBounded (ap2 g k y) (ap2 f k x) (P*V+two*Qd) D :=
    GaussianNamedInverseRate.diagonal_rate g f y x P Qd k hQ hn
  have ht := selected_sample_rate f g x y M R s k (P*V+two*Qd) D
    hf hg hs hl hp hD near (sample_admission P K C Qd V ha cap)
  have hUV : Γ ⊢[PRAAx] le U V := unit_monotone hs
  have hQV : Γ ⊢[PRAAx] le U (Qd*V) :=
    le_trans hUV (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right V hQ))
  have hVV : Γ ⊢[PRAAx] le U (V*V) :=
    le_trans hUV (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right V hV))
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hD hD) hU)
    (positive_product _ _ (positive_product _ _ hQ hQ) hU)
    (enlarged_budget f x M R P Qd U V hQV hVV) ht

theorem observations (f g : PR 2) (x y M R P Qd p q : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hg : Γ ⊢[PRAAx] source g y M R)
    (hQ : Γ ⊢[PRAAx] le one Qd)
    (ha : Γ ⊢[PRAAx] le (admission P (two*M) (sizeBound R R)) Qd)
    (hn : Γ ⊢[PRAAx] independentRate g f y x P Qd) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (incrementF f g) p (incrementData x y M R))
      (ap2 (productF f g) q (productData f g x y M R))
      (rateNumerator (quadraticBudget P (two*M)) (Qd*Qd) p q) (rateDenominator (Qd*Qd) p q) := by
  let V := Qd*Qd
  let E := quadraticBudget P (two*M)
  let C := slackCost f x M R P
  let A := rateNumerator E V p q
  let B := rateDenominator V p q
  let d := qsub (ap2 (incrementF f g) p (incrementData x y M R)) (ap2 (productF f g) q (productData f g x y M R))
  let s := GaussianRationalSlackRemoval.precision d A B C
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ hQ hQ
  have hB : Γ ⊢[PRAAx] le one B := GaussianNamedInverseRate.denominator_positive V p q hV
  have raw := rate_at (incrementF f g) (productF f g) (incrementData x y M R) (productData f g x y M R)
    (E*unit s+C*V) (V*unit s) p q (dyadic_rate f g x y M R P Qd s hf hg hQ ha hn)
  exact GaussianRationalSlackRemoval.slack_removal_at d A B C hB
    (GaussianRationalReciprocal.bound_congr (.eqRefl _) (by
      change Γ ⊢[PRAAx] rateNumerator (E*unit s+C*V) (V*unit s) p q ≐ A*unit s+C*B
      dsimp only [A, B, rateNumerator, rateDenominator]
      ipra_ring) (by
        change Γ ⊢[PRAAx] rateDenominator (V*unit s) p q ≐ B*unit s
        dsimp only [B, rateDenominator]
        ipra_ring) raw)

def input (f g : PR 2) (x y M R P Qd : PTm n) : Fm PTm n :=
  source f x M R ⋏ (source g y M R ⋏ (le one Qd ⋏
    (le (admission P (two*M) (sizeBound R R)) Qd ⋏ independentRate g f y x P Qd)))

ipra_subst input [admission, admissionBudget]

theorem independent_rate (f g : PR 2) (x y M R P Qd : PTm n)
    (h : Γ ⊢[PRAAx] input f g x y M R P Qd) : Γ ⊢[PRAAx]
    independentRate (incrementF f g) (productF f g) (incrementData x y M R) (productData f g x y M R)
      (quadraticBudget P (two*M)) (Qd*Qd) := by
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hs : Δ ⊢[PRAAx] input f g (sh x) (sh y) (sh M) (sh R) (sh P) (sh Qd) := by
    simpa only [Δ, sh, Fm.shift, subst_input, Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa [independentRate, incrementData, GaussianNamedLogGammaTaylorFrozen.data, quadraticBudget, sh, Syn.shift,
    Δ, two, GaussianLogGammaEulerNamed.data, GaussianLogGammaEulerNamedDigamma.data] using
    observations f g (sh x) (sh y) (sh M) (sh R) (sh P) (sh Qd) (var 1) (var 0)
      hs.andE₁ hs.andE₂.andE₁ hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₂

theorem actual_named_log_Gamma_quadratic_Taylor_rate_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let x := var 0
       let y := var 1
       let M := var 2
       let R := var 3
       let P := var 4
       let Qd := var 5
       input f g x y M R P Qd ⟶
       independentRate (incrementF f g) (productF f g) (incrementData x y M R) (productData f g x y M R)
         (quadraticBudget P (two*M)) (Qd*Qd)) :=
  closeUniv 6 (.impI (independent_rate f g _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedLogGammaTaylorEstimate
