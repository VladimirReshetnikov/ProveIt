import IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupBracketEnclosure
import IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupBracketWidth
import IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupPositivePresentation

/-!
# Uniqueness by the literal dyadic Bohr–Mollerup brackets

Both presentations use the same exact paper cutoff n=1+B^2*2^(p+2).
Their difference is bounded above by the actual named width U_n-L_n.
The dyadic bound yields equality of the original positive-rational
logarithm presentations by finite rational slack removal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupLiteralUniqueness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBohrMollerupBlockChord (source)
open GaussianBohrMollerupBracketEndpoints (bracketF lowerData upperData widthF widthData endpoint_regular)
open GaussianBohrMollerupBracketEnclosure (enclosure)
open GaussianBohrMollerupBracketWidth (cutoff cutoff_positive width_at_cutoff)
open GaussianBohrMollerupPeriod (differenceF differenceData difference_regular)
open GaussianBohrMollerupPresentation (Presentation argument laws native observe_value)
open GaussianBohrMollerupPositivePresentation (logarithmPresentation logarithm_argument logarithm_program)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData log_gamma_regular gammaData)
open GaussianNameRingLaws (negativeF negativeData zeroF zero_fast zero_at)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open RationalValueBounds (upper upper_congr upper_of_radius upper_triangle upper_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem difference_upper (P Q : Presentation) (a b B j : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hq : Γ ⊢[PRAAx] laws Q) (hs : Γ ⊢[PRAAx] source a b B)
    (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] realOrder (differenceF P Q) widthF (differenceData P Q a b) (widthData a b B j) := by
  let x := argument P a b
  let y := argument Q a b
  let l := lowerData a b j
  let u := upperData a b B j
  have left := (enclosure P a b B j hp hs hj).andE₂
  have right := (enclosure Q a b B j hq hs hj).andE₁
  have hl := endpoint_regular a b j j hs.andE₁ hj
  have hy := (observe_value Q a b hq.andE₂.andE₁ hs.andE₁).andE₁
  have reverse := GaussianNamedRealOrderLinear.negative_order bracketF Q.nameF l y hl hy right
  exact GaussianGammaEulerRationalLogOrder.add_order P.nameF bracketF (negativeF Q.nameF) (negativeF bracketF)
    x u (negativeData y) (negativeData l) left reverse

theorem difference_at_cutoff (P Q : Presentation) (a b B p : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hq : Γ ⊢[PRAAx] laws Q) (hs : Γ ⊢[PRAAx] source a b B) :
    Γ ⊢[PRAAx] realOrder (differenceF P Q) constantF (differenceData P Q a b) (fraction one (unit (p+two))) :=
  GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _
    (difference_upper P Q a b B (cutoff B p) hp hq hs (cutoff_positive B p hs.andE₂.andE₁))
    (width_at_cutoff a b B _ p hs (le_refl _))

private theorem fraction_distance (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded (fraction one D) qzero one D := by
  let x := fraction one D
  have hx := GaussianRationalHorner.ofGaussian_canonical (Γ := Γ)
    (ComplexLogarithmRemainder.scale one ComplexLogarithmRemainder.oneCode) D hD
  have normal := GaussianEulerDecayFactorBounds.fraction_is_radius_point one D hD
  exact bound_congr (GaussianRationalReconstruction.qsub_zero_right x hx).eqSymm (.eqRefl _) (.eqRefl _)
    (bound_congr normal.eqSymm (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded one D hD))

theorem same_precision_comparison (P Q : Presentation) (a b B p y : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hq : Γ ⊢[PRAAx] laws Q) (hs : Γ ⊢[PRAAx] source a b B) :
    Γ ⊢[PRAAx] upper (fstT (ap2 (differenceF P Q) p (differenceData P Q a b))) (fstT (ap2 zeroF p y)) (num 3) (unit p) := by
  let D := unit (p+two)
  let U := unit p
  let k := fraction one D
  have hD := unit_positive (Γ := Γ) (p+two)
  have hU := unit_positive (Γ := Γ) p
  have order := GaussianNamedNaturalScaleOrder.common_upper (differenceF P Q) constantF _ k p
    (difference_at_cutoff P Q a b B p hp hq hs)
  have grow : Γ ⊢[PRAAx] le U D := GaussianExponentialReference.unit_monotone (le_add_right p two)
  have near : Γ ⊢[PRAAx] distanceBounded k qzero one U :=
    distance_radius_mono _ _ one D one U hD hU (le_congr (one_mul U).eqSymm (one_mul D).eqSymm grow)
      (fraction_distance D hD)
  have tail := upper_congr (congrFst (constant_at p k)).eqSymm (congrFst (zero_at p y)).eqSymm (.eqRefl _) (.eqRefl _)
    (upper_of_radius _ _ _ _ (scalar_coordinate_distance k qzero one U hU near))
  have joined := upper_triangle _ _ _ _ _ _ _ order tail
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ hU hU) joined (le_of_eq_add (d := zero) (by
    change Γ ⊢[PRAAx] num 3*(U*U) ≐ (two*U+one*U)*U+zero
    ipra_ring))

theorem order (P Q : Presentation) (a b B : PTm n) (hp : Γ ⊢[PRAAx] laws P)
    (hq : Γ ⊢[PRAAx] laws Q) (hs : Γ ⊢[PRAAx] source a b B) :
    Γ ⊢[PRAAx] realOrder P.nameF Q.nameF (argument P a b) (argument Q a b) := by
  let y := argument Q a b
  let F := differenceF P Q
  let x := differenceData P Q a b
  have rx := difference_regular P Q a b hp.andE₂.andE₁ hq.andE₂.andE₁ hs.andE₁
  have small : Γ ⊢[PRAAx] realOrder F zeroF x y := by
    apply order_from_envelope _ _ _ _ (num 3) rx (zero_fast y)
    refine .allI ?_
    let sh (v : PTm n) := Syn.shift v
    let Δ := Γ.map Fm.shift
    have vp : Δ ⊢[PRAAx] laws P := by simpa [Δ,Fm.shift] using hp.shift
    have vq : Δ ⊢[PRAAx] laws Q := by simpa [Δ,Fm.shift] using hq.shift
    have ss : Δ ⊢[PRAAx] source (sh a) (sh b) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift
    simpa only [envelope,F,x,Δ,Syn.shift,sh,GaussianBohrMollerupPeriod.subst_differenceData,PTm.subst_num] using
      same_precision_comparison P Q (sh a) (sh b) (sh B) (var 0) (sh y) vp vq ss
  exact GaussianBohrMollerupZeroAlgebra.order_of_difference_nonpositive _ _ _ _
    (observe_value P a b hp.andE₂.andE₁ hs.andE₁).andE₁
    (observe_value Q a b hq.andE₂.andE₁ hs.andE₁).andE₁ small

theorem uniqueness (P Q : Presentation) (a b B : PTm n) (hp : Γ ⊢[PRAAx] laws P)
    (hq : Γ ⊢[PRAAx] laws Q) (hs : Γ ⊢[PRAAx] source a b B) :
    Γ ⊢[PRAAx] crossEquivalent P.nameF Q.nameF (argument P a b) (argument Q a b) :=
  GaussianStirlingMultiplicativeBoundsStrictOrder.real_antisymmetry _ _ _ _
    (observe_value P a b hp.andE₂.andE₁ hs.andE₁).andE₂
    (observe_value Q a b hq.andE₂.andE₁ hs.andE₁).andE₂
    (order P Q a b B hp hq hs) (order Q P a b B hq hp hs)

theorem actual_literal_Bohr_Mollerup_uniqueness_closed (P Q : Presentation) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (laws P ⟶ laws Q ⟶ source (var 0) (var 1) (var 2) ⟶
        crossEquivalent P.nameF Q.nameF (argument P (var 0) (var 1)) (argument Q (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (.impI (uniqueness P Q _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem positive_gamma_uniqueness (f : PR 2) (x e : PTm 2) (a b B T : PTm n)
    (hl : Γ ⊢[PRAAx] laws (logarithmPresentation f x e)) (hs : Γ ⊢[PRAAx] source a b B)
    (hp : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f (inst2 x a b) (inst2 e a b) T) :
    Γ ⊢[PRAAx] crossEquivalent f gammaF (inst2 x a b) (gammaData a b) := by
  let d := inst2 x a b
  let m := inst2 e a b
  let F := GaussianNamedPositiveLogarithm.nameF f
  let X := GaussianNamedPositiveLogarithm.data d m
  let Y := logGammaData a b
  let R := GaussianCompactLogarithmBounds.radius m T
  let S := GaussianNameBounds.U logGammaF Y
  have proved := uniqueness (logarithmPresentation f x e) native a b B hl
    GaussianBohrMollerupNativeNormalization.native_laws hs
  have names : Γ ⊢[PRAAx] crossEquivalent F logGammaF X Y := by
    simpa only [logarithm_argument,logarithm_program,GaussianBohrMollerupPresentation.native_program,
      GaussianBohrMollerupPresentation.native_argument,F,X,Y,d,m] using proved
  have hX := GaussianNamedPositiveLogarithm.exponential_input f d m T hp
  have hY := GaussianGammaFiniteApproximantName.exponential_input logGammaF Y (log_gamma_regular a b hs.andE₁)
  have exp := GaussianExponentialRadiusIndependence.independent_radii_proper F logGammaF R S X Y hX hY names
  have left := GaussianNamedPositiveLogarithmExponential.original_recovery f d m T hp
  have right := GaussianStirlingLogDuplication.exponential_gamma a b hs.andE₁
  exact cross_trans f (GaussianRadiusExponentialName.nameF F) gammaF d (GaussianRadiusExponentialName.data R X) (gammaData a b)
    (cross_symm _ _ _ _ left) (cross_trans _ _ _ _ _ _ exp right)

theorem actual_literal_Bohr_Mollerup_positive_gamma_uniqueness_closed (f : PR 2) (x e : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (laws (logarithmPresentation f x e) ⟶ source (var 0) (var 1) (var 2) ⟶
        GaussianNamedPositiveLogarithm.source f (inst2 x (var 0) (var 1)) (inst2 e (var 0) (var 1)) (var 3) ⟶
        crossEquivalent f gammaF (inst2 x (var 0) (var 1)) (gammaData (var 0) (var 1))) :=
  closeUniv 4 (.impI (.impI (.impI (positive_gamma_uniqueness f x e _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupLiteralUniqueness
