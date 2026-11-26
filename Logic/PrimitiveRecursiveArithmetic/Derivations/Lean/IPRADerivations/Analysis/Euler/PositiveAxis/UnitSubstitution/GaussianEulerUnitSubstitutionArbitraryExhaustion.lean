import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionProjectedGap
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelObservedTail

/-!
# Arbitrary rational endpoint exhaustion of the ordinary Gamma integral

For the requested tail accuracy s, the denominator of the fixed inner
reference panel gives a positive rational endpoint tolerance. Any proper
panel meeting that tolerance lies between the reference and a computed
later ordinary panel. Both actual complex omitted strips are controlled
by the real companion gap. A single explicitly computed finite query
removes the auxiliary dyadic error, leaving the two requested observation
errors and the prescribed tail tolerance.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionArbitraryExhaustion

open_ipra
open GaussianEulerUnitSubstitutionArbitraryPanels (exhaustionSource boundarySource innerIndex innerDen surrounding_sources)
open GaussianEulerUnitSubstitutionOrdinaryImproper (source)
open GaussianEulerUnitSubstitutionOrdinaryContainment (containmentIndex containment_index_later)
open GaussianEulerUnitSubstitutionCofinalPanelRate (panelData panel_source)
open GaussianEulerUnitSubstitutionProjectedGap (gapNumerator gapDenominator original_projected_gap late_cofinal_observations)
open GaussianEulerUnitSubstitutionCompactName (stage_budget)
open GaussianEulerUnitKernelCompactName (nameF data name_regular)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem inner_accuracy (s : PTm n) : Γ ⊢[PRAAx] le (two*unit s) (unit (innerIndex s)) :=
  le_trans (le_of_eq_add (d := num 4*unit s) (by ipra_ring)) (stage_budget s)

private theorem observation_slack (p q s u z R B A a C E G : PTm n)
    (h : Γ ⊢[PRAAx] exhaustionSource s z R B A a C E G) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack
      (qsub (ap2 nameF p (data z R B a C E G)) (ap2 gammaF q (gammaData z R B A)))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) (num 28) u := by
  let V := unit s
  let U := unit u
  let P := unit p
  let Q := unit q
  let I := unit (innerIndex s)
  let D := V*P*Q*U
  let x := data z R B a C E G
  let y := panelData (containmentIndex u E) z R B A
  let g := gammaData z R B A
  let Iu := I*U
  have hV := unit_positive (Γ := Γ) s
  have hU := unit_positive (Γ := Γ) u
  have hP := unit_positive (Γ := Γ) p
  have hQ := unit_positive (Γ := Γ) q
  have hI := unit_positive (Γ := Γ) (innerIndex s)
  have hIu : Γ ⊢[PRAAx] le one Iu := positive_product _ _ hI hU
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ (positive_product _ _ hV hP) hQ) hU
  have original := GaussianNameEquivalence.point_at nameF x p u (name_regular z R B a C E G h.andE₂.andE₁)
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p x) (ap2 nameF u x) ((U+P)*(V*Q)) D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hP hU) hD
      (le_of_eq_add (d := zero) (by dsimp only [D,P,U]; ipra_ring)) original
  have gap := original_projected_gap s u z R B A a C E G h
  have tail : Γ ⊢[PRAAx] distanceBounded (ap2 nameF u y) (ap2 nameF u x)
      ((two*U+num 12*I)*U+num 12*Iu) (Iu*U) :=
    GaussianEulerUnitKernelObservedTail.original_tail_bound u z R B _ _ _ _ a C E G _ _
      (surrounding_sources s u z R B A a C E G h).andE₂ hIu gap
  have ht := positive_product (Γ := Γ) _ _ hIu hU
  have grow : Γ ⊢[PRAAx] le (two*V) I := inner_accuracy s
  have second : Γ ⊢[PRAAx] distanceBounded (ap2 nameF u x) (ap2 nameF u y) (P*Q*U+num 24*V*P*Q) D :=
    distance_radius_mono _ _ _ _ _ _ ht hD
      (by dsimp only [Iu,D]; ipra_le 𝔞 P*𝔞 Q*(𝔞 U)^3*sl grow)
      (distance_symmetric _ _ _ _ ht tail)
  have later := late_cofinal_observations u q u (containmentIndex u E) z R B A h.andE₁ (containment_index_later u E)
  have third : Γ ⊢[PRAAx] distanceBounded (ap2 nameF u y) (ap2 gammaF q g) ((num 3*Q+U)*(V*P)) D :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hU) hD
      (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; dsimp only [D,U,Q]; ipra_ring)) later
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold rateNumerator rateDenominator; dsimp only [V,P,Q,U,unit]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD (distance_triangle_same _ _ _ _ _ _ hD first second) third)

theorem original_observations (p q s z R B A a C E G : PTm n)
    (h : Γ ⊢[PRAAx] exhaustionSource s z R B A a C E G) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B a C E G)) (ap2 gammaF q (gammaData z R B A))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  let x := qsub (ap2 nameF p (data z R B a C E G)) (ap2 gammaF q (gammaData z R B A))
  let numerator := rateNumerator one (unit s) p q
  let denominator := rateDenominator (unit s) p q
  have hd : Γ ⊢[PRAAx] le one denominator := denominator_positive _ _ _ (unit_positive s)
  exact GaussianRationalSlackRemoval.slack_removal_at x numerator denominator (num 28) hd
    (observation_slack p q s (GaussianRationalSlackRemoval.precision x numerator denominator (num 28)) z R B A a C E G h)

theorem endpoint_tolerance_positive (s z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] le one (innerDen s A R) :=
  (panel_source (innerIndex s) z R B A h).andE₂.andE₁

/-- The denominator of a proper rational panel certifies its compact
margin automatically. No separate compact certificate is needed. -/
theorem original_proper_observations (p q s z R B A a C E : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hp : Γ ⊢[PRAAx] boundarySource s A R a C E) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B a C E E)) (ap2 gammaF q (gammaData z R B A))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) :=
  original_observations p q s z R B A a C E E
    (.andI h (.andI (GaussianEulerUnitKernelNativePanel.source_at_denominator z R B a C E
      h.andE₁.andE₂.andE₁ hp.andE₁) hp))

theorem actual_original_Gamma_arbitrary_rational_exhaustion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (exhaustionSource (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      distanceBounded
        (ap2 nameF (var 0) (data (var 3) (var 4) (var 5) (var 7) (var 8) (var 9) (var 10)))
        (ap2 gammaF (var 1) (gammaData (var 3) (var 4) (var 5) (var 6)))
        (rateNumerator one (unit (var 2)) (var 0) (var 1)) (rateDenominator (unit (var 2)) (var 0) (var 1))) :=
  closeUniv 11 (.impI (original_observations _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_Gamma_every_proper_rational_exhaustion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((source (var 3) (var 4) (var 5) (var 6) ⋏ boundarySource (var 2) (var 6) (var 4) (var 7) (var 8) (var 9)) ⟶
      distanceBounded
        (ap2 nameF (var 0) (data (var 3) (var 4) (var 5) (var 7) (var 8) (var 9) (var 9)))
        (ap2 gammaF (var 1) (gammaData (var 3) (var 4) (var 5) (var 6)))
        (rateNumerator one (unit (var 2)) (var 0) (var 1)) (rateDenominator (unit (var 2)) (var 0) (var 1))) :=
  closeUniv 10 (.impI (original_proper_observations _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionArbitraryExhaustion
