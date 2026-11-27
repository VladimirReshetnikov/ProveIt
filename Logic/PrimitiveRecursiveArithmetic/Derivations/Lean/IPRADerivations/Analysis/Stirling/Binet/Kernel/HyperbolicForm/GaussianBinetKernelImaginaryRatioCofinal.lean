import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelCofinal
import IPRADerivations.Analysis.Stirling.Binet.Kernel.HyperbolicForm.GaussianBinetKernelImaginaryRatioPrefix
import IPRADerivations.Analysis.Trigonometry.Hyperbolic.Derivatives.GaussianSineProductImaginaryCothExpansion
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedAddRate

/-!
# Cofinal rate for the kernel at a frozen imaginary ratio

The scaled fixed rational-time Binet name is compared to the scaled
cofinal logarithmic derivative at a sampled rational ratio. The same
finite row precision is used to freeze π, so the prefix comparison is
exact. Only the cofinal Binet tail and ordinary name-clock errors remain.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelImaginaryRatioCofinal

open_ipra
open GaussianBinetKernelImaginaryRatioRows (ratioNumerator ratioDenominator ratioRadius ratio_source)
open GaussianBinetKernelImaginaryRatioPrefix (rawPrefix ratio timeSquare rational_time_prefix)
open GaussianBinetKernelRows (inputData rowF rowBody)
open GaussianBinetKernelTail (finiteF finiteData)
open GaussianBoundedConstantProductName (constantF constant_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm point_at)
open GaussianNameRingLaws (oneF one_fast)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Kernel" => GaussianBinetKernelCofinal.nameF
local notation "Rows" => GaussianSineProductImaginaryLogDerivativeTail.nameF
local notation "rowData" => GaussianSineProductImaginaryLogDerivativeTail.data
local notation "Cut" => GaussianBoundedConstantProductName.nameF
local notation "cutData" => GaussianBoundedConstantProductName.data
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def referenceLength (p A : PTm n) : PTm n := GaussianSineProductImaginaryLogDerivativeTail.cutoff (ratioRadius A) p
def referenceClock (p A : PTm n) : PTm n := GaussianFastValueCut.exponent (referenceLength p A) (succ p)
def frozenNumerator (p A : PTm n) : PTm n := ratioNumerator (referenceClock p A) A
def frozenDenominator (p A B : PTm n) : PTm n := ratioDenominator (referenceClock p A) B
def frozenData (p A B : PTm n) : PTm n := rowData (frozenNumerator p A) (frozenDenominator p A B) (ratioRadius A)
def timeSquareF : PR 2 := multiplyF constantF Kernel
def timeSquareData (A B : PTm n) : PTm n := multiplyData constantF Kernel (timeSquare A B) (inputData A B)
def fixedFactorF : PR 2 := addF oneF timeSquareF
def fixedFactorData (A B : PTm n) : PTm n := addData (inputData A B) (timeSquareData A B)
def budget (A : PTm n) : PTm n := (two*(A*A)+two*(A*A)+two*ratioRadius A)+two

ipra_subst referenceClock [referenceLength, ratioRadius, GaussianSineProductImaginaryLogDerivativeTail.cutoff, two, one]

theorem frozen_source (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    le one (ratioRadius A) ⋏ (le one (frozenDenominator p A B) ⋏
      le (frozenNumerator p A+one) (ratioRadius A*frozenDenominator p A B)) :=
  ratio_source (referenceClock p A) A B hB

theorem time_square_bound (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (timeSquare A B) (A*A) one := by
  have hb := positive_product _ _ hB hB
  exact GaussianEulerExponentCompactBounds.fraction_bound _ _ _ hb
    (le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (A*A) hb))

private theorem frozen_bound (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (ratio (referenceClock p A) A B) (ratioRadius A) one := by
  have h := frozen_source p A B hB
  exact GaussianSineProductImaginaryLogDerivativeTail.rational_real_bound _ _ _ _ h.andE₂.andE₁ (le_refl one)
    (le_congr (one_mul _).eqSymm (.eqRefl _) (le_trans (le_add_right _ _) h.andE₂.andE₂))

private theorem fixed_mul_distance (c a b C X D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hc : Γ ⊢[PRAAx] bounded c C one)
    (h : Γ ⊢[PRAAx] distanceBounded a b X D) :
    Γ ⊢[PRAAx] distanceBounded (qmul c a) (qmul c b) (C*X) D :=
  GaussianRationalRoundedPower.distance_mul_left_one hD hc h

private theorem to_twice_at (a b p q : PTm n) (hpq : Γ ⊢[PRAAx] le p q)
    (h : Γ ⊢[PRAAx] distanceBounded a b (unit p+unit q) (unit p*unit q)) :
    Γ ⊢[PRAAx] distanceBounded a b two (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have hm : Γ ⊢[PRAAx] le (unit p) (unit q) := GaussianBalancedRadiusArithmetic.unit_monotone p q hpq
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp (unit_positive q)) hp ?_ h
  ipra_le (𝔞 (unit p))*sl hm

theorem raw_product_bound (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    distanceBounded (qmul (timeSquare A B) (ap2 Kernel p (inputData A B)))
      (qmul (ratio (referenceClock p A) A B) (ap2 Rows p (frozenData p A B))) ((A*A)*two) (unit p) := by
  let N := referenceLength p A
  let k := referenceClock p A
  let R := ratioRadius A
  let a := frozenNumerator p A
  let b := frozenDenominator p A B
  let r := ratio k A B
  let t := timeSquare A B
  have hR : Γ ⊢[PRAAx] le one R := le_add_left _ _
  have hN : Γ ⊢[PRAAx] le (GaussianBinetKernelCofinal.cutoff p) N := by
    dsimp only [GaussianBinetKernelCofinal.cutoff,N,referenceLength,GaussianSineProductImaginaryLogDerivativeTail.cutoff]
    ipra_le 2*𝔞 (unit p)*sl hR+𝔞 (unit p)+1
  have late := GaussianBinetKernelCofinal.late_observations p (succ p) N A B hN hB
  have raw := fixed_mul_distance t _ _ (A*A) two (unit p) (unit_positive p) (time_square_bound A B hB)
    (to_twice_at _ _ p (succ p) (le_succ_self p) late)
  have finiteAt : Γ ⊢[PRAAx] ap2 finiteF (succ p) (finiteData N A B) ≐ rawPrefix k N A B :=
    GaussianNamedFiniteSumFamily.sample_at rowF rowBody (succ p) N (inputData A B)
  have rowAt : Γ ⊢[PRAAx] ap2 Rows p (frozenData p A B) ≐ GaussianSineProductImaginaryLogDerivative.logarithmSum a b N :=
    GaussianSineProductImaginaryLogDerivativeTail.sample_at a b R p
  have e := (qmul_congr (.eqRefl t) finiteAt).eqTrans
    ((rational_time_prefix k N A B hB).eqTrans (qmul_congr (.eqRefl r) rowAt.eqSymm))
  exact distance_congr (.eqRefl _) e (.eqRefl _) (.eqRefl _) raw

private theorem product_readback (F : PR 2) (C c x p : PTm n) (h : Γ ⊢[PRAAx] pointCN F x)
    (hc : Γ ⊢[PRAAx] bounded c C one) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (Cut F) p (cutData C c x)) (qmul c (ap2 F p x)) (C*two) (unit p) := by
  let q := GaussianBoundedConstantProductName.clock p C
  have hq : Γ ⊢[PRAAx] le p q := le_add_right _ _
  have close := point_at F x p q h
  have d := distance_symmetric _ _ _ _ (unit_positive p) (to_twice_at _ _ p q hq close)
  exact distance_congr (GaussianBoundedConstantProductName.sample_at F p C c x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (fixed_mul_distance c _ _ C two (unit p) (unit_positive p) hc d)

private theorem anchored_at (F G : PR 2) (x y p C s t : PTm n) (hF : Γ ⊢[PRAAx] pointCN F x)
    (hG : Γ ⊢[PRAAx] pointCN G y) (h : Γ ⊢[PRAAx] distanceBounded (ap2 F p x) (ap2 G p y) C (unit p)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 F s x) (ap2 G t y) (rateNumerator (C+two) (unit p) s t) (rateDenominator (unit p) s t) := by
  let P := unit p
  let S := unit s
  let T := unit t
  let D := P*S*T
  have hp := unit_positive (Γ := Γ) p
  have hs := unit_positive (Γ := Γ) s
  have ht := unit_positive (Γ := Γ) t
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ hp hs) ht
  have l := distance_radius_mono _ _ _ _ ((S+P)*T) D (positive_product _ _ hs hp) hd
    (le_of_eq_add (d := zero) (by dsimp only [D,S,P,T]; ipra_ring)) (point_at F x s p hF)
  have mid := distance_radius_mono _ _ _ _ (C*S*T) D hp hd
    (le_of_eq_add (d := zero) (by dsimp only [D,S,P,T]; ipra_ring)) h
  have r := distance_radius_mono _ _ _ _ ((P+T)*S) D (positive_product _ _ hp ht) hd
    (le_of_eq_add (d := zero) (by dsimp only [D,S,P,T]; ipra_ring)) (point_at G y p t hG)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [rateNumerator,D,S,P,T]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd l (distance_triangle_same _ _ _ _ _ _ hd mid r))

theorem anchored_rate (F G : PR 2) (x y p C : PTm n) (hF : Γ ⊢[PRAAx] pointCN F x)
    (hG : Γ ⊢[PRAAx] pointCN G y) (h : Γ ⊢[PRAAx] distanceBounded (ap2 F p x) (ap2 G p y) C (unit p)) :
    Γ ⊢[PRAAx] independentRate F G x y (C+two) (unit p) := by
  let sh (a : PTm n) := Syn.shift (Syn.shift a)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have fs : Δ ⊢[PRAAx] pointCN F (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hF.shift.shift
  have gs : Δ ⊢[PRAAx] pointCN G (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hG.shift.shift
  have ds : Δ ⊢[PRAAx] distanceBounded (ap2 F (sh p) (sh x)) (ap2 G (sh p) (sh y)) (sh C) (unit (sh p)) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,Δ,sh,Syn.shift,GaussianCoefficientNameBounds.subst_unit,PTm.subst_add,two,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    anchored_at F G (sh x) (sh y) (sh p) (sh C) (var 1) (var 0) fs gs ds

theorem weighted_rows_rate (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    independentRate timeSquareF GaussianSineProductImaginaryCothExpansion.weightedRowsF (timeSquareData A B)
      (GaussianSineProductImaginaryCothExpansion.weightedRowsData (frozenNumerator p A) (frozenDenominator p A B) (ratioRadius A))
      (budget A) (unit p) := by
  let R := ratioRadius A
  let a := frozenNumerator p A
  let b := frozenDenominator p A B
  let k := referenceClock p A
  let x := inputData A B
  let y := frozenData p A B
  let t := timeSquare A B
  let r := ratio k A B
  have src := frozen_source p A B hB
  have hf := GaussianBinetKernelCofinal.regular A B hB
  have hg := GaussianSineProductImaginaryLogDerivativeTail.regular a b R src.andE₂.andE₁ (le_trans (le_add_right _ _) src.andE₂.andE₂)
  have bt := time_square_bound A B hB
  have br := frozen_bound p A B hB
  have hu := unit_positive (Γ := Γ) p
  have left := product_readback Kernel (A*A) t x p hf bt
  have right := product_readback Rows R r y p hg br
  have close := distance_triangle_same _ _ _ _ _ _ hu left (distance_triangle_same _ _ _ _ _ _ hu
    (raw_product_bound p A B hB) (distance_symmetric _ _ _ _ hu right))
  have close' := distance_congr (.eqRefl _) (.eqRefl _)
    (show Γ ⊢[PRAAx] (A*A)*two+((A*A)*two+R*two) ≐ two*(A*A)+two*(A*A)+two*R by ipra_ring)
    (.eqRefl _) close
  have cw := GaussianBoundedConstantProductName.ordinary_product_identity Kernel (A*A) t x (.andI hf bt)
  have cr := GaussianBoundedConstantProductName.ordinary_product_identity Rows R r y (.andI hg br)
  have h := anchored_rate (Cut Kernel) (Cut Rows) _ _ p _ (GaussianBoundedConstantProductName.name_regular _ _ _ _ (.andI hf bt))
    (GaussianBoundedConstantProductName.name_regular _ _ _ _ (.andI hg br)) close'
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ (budget A) (unit p) hu h
    (cross_symm _ _ _ _ cw) (cross_symm _ _ _ _ cr)

theorem factor_rate (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    independentRate fixedFactorF GaussianSineProductImaginaryCothExpansion.factorF (fixedFactorData A B)
      (GaussianSineProductImaginaryCothExpansion.factorData (frozenNumerator p A) (frozenDenominator p A B) (ratioRadius A))
      (budget A) (unit p) := by
  let x := inputData A B
  let y := GaussianSineProductImaginaryCofinalDerivative.sineData (frozenNumerator p A) (frozenDenominator p A B) (ratioRadius A)
  have unitRate := GaussianNamedRateTransport.transport (Γ := Γ) oneF oneF oneF oneF x x x y zero one (le_refl one)
    (GaussianNamedDifferenceRate.self_rate oneF x (one_fast x)) (cross_refl _ _ (one_fast x))
    (GaussianNamedExponentialDifferenceIdentity.ones_equivalent y x)
  have h := GaussianNamedAddRate.independent_rate oneF timeSquareF oneF GaussianSineProductImaginaryCothExpansion.weightedRowsF
    x (timeSquareData A B) y _ zero one (budget A) (unit p) (le_refl one) (unit_positive p) unitRate (weighted_rows_rate p A B hB)
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by dsimp only [GaussianNamedRateComposition.leadingNumerator]; ipra_ring)
    (by dsimp only [GaussianNamedRateComposition.leadingDenominator]; ipra_ring) h

end LeanProofs.IPRA.Analysis.GaussianBinetKernelImaginaryRatioCofinal
