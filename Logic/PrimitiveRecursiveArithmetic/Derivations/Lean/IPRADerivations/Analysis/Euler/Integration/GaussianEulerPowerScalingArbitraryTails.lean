import IPRADerivations.Analysis.Euler.Integration.GaussianEulerPowerScalingTailGeometry
import IPRADerivations.Analysis.Integration.GaussianCompactTailFromComparison
import IPRADerivations.Analysis.Integration.GaussianCompactIntervalRescaling
import IPRADerivations.Analysis.Integration.GaussianCompactMeshIndependence
import IPRADerivations.Analysis.Integration.GaussianCompactZeroWidth

/-!
# Arbitrary physical tails of the rational power-damped Euler integral

An upper tail is the difference of two panels with a common starting
point below the lower cutoff. A lower tail is the difference of two
panels with a common endpoint above the upper cutoff. Both enclosing
observations compare to the same Gamma formula. Compact additivity and
invariance under rational re-encoding return bounds at the actual input
panel and its original observation clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingArbitraryTails

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPowerScalingGridSchedule (source)
open GaussianEulerPowerChartUniformSchedule (panelStage)
open GaussianEulerPowerChartCofinalSchedule (cutoffSize)
open GaussianEulerPowerChartCofinalEndpoints (lowerDenominator upperNumerator)
open GaussianEulerPowerScalingTailGeometry (upperPrefix lowerSuffix physical_cutoffs_positive upper_geometry lower_geometry)
open GaussianEulerCompactExhaustionScaled (cutoff)
open GaussianEulerPowerScalingImproper (formulaF formulaData)
open GaussianEulerPowerScalingArbitraryObservation (compact_source original_enclosing_observations)
open GaussianEulerPowerScalingCompactRate (lipschitz)
open GaussianEulerPowerScalingCompactName (evaluatorF fixedData)
open GaussianCompactTailFromComparison (observation prefix_bound suffix_bound)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "compactF" => GaussianEulerPowerScalingCompactName.nameF
local notation "compactData" => GaussianEulerPowerScalingCompactName.data
local notation "compactInput" => GaussianCompactRiemannName.input
local notation "compactEncoding" => GaussianCompactRiemannName.data

def above (j R A L Q U E a : PTm n) : Fm PTm n :=
  le (E*upperNumerator U (cutoffSize j (Q*A) (L*R)) L) a
def below (j R A L Q S E a W : PTm n) : Fm PTm n :=
  le ((a+W)*lowerDenominator S (cutoffSize j (Q*A) (L*R)) L) E

private theorem panel_input (z R B A e f d h L Q S E T a W : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S E T a W) : Γ ⊢[PRAAx]
    compactInput evaluatorF a W E (lipschitz R Q S E T) T (fixedData z B e f d h S) :=
  GaussianEulerPowerScalingCompactName.compact_input z R B e f d h Q S a W E T
    (compact_source z R B A e f d h L Q S E T a W hs)

private theorem add_input (F : PR 3) (a C W E J T x : PTm n)
    (hc : Γ ⊢[PRAAx] le one C) (hw : Γ ⊢[PRAAx] le one W)
    (h : Γ ⊢[PRAAx] compactInput F a (C+W) E J T x) : Γ ⊢[PRAAx]
    GaussianCompactNamedAdditivity.input F a C W E J T x :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ (.andI hc (.andI hw h.andE₂.andE₂)))

private theorem same_clock (s p a b : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded a b (rateNumerator one (unit s) p p) (rateDenominator (unit s) p p)) :
    Γ ⊢[PRAAx] distanceBounded a b (unit p+two*unit s) (unit s*unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ (unit_positive s) hp
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hd hp) hd
    (le_of_eq_add (d := zero) (by simp only [rateNumerator]; ipra_ring)) h

private theorem transfer_bound (F : PR 3) (p s x y : PTm n)
    (hc : Γ ⊢[PRAAx] crossEquivalent (GaussianCompactRiemannName.nameF F) (GaussianCompactRiemannName.nameF F) x y)
    (hy : Γ ⊢[PRAAx] bounded (ap2 (GaussianCompactRiemannName.nameF F) p y)
      (two*unit p+num 9*unit s) (unit s*unit p)) : Γ ⊢[PRAAx]
    bounded (ap2 (GaussianCompactRiemannName.nameF F) p x)
      (two*unit p+num 11*unit s) (unit s*unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ (unit_positive s) hp
  have near := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := zero) (by ipra_ring)) (cross_at _ _ _ _ p p hc)
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hp hd near hy
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hp hd) hd
    (le_of_eq_add (d := zero) (by ipra_ring)) raw

private theorem compact_start_congr (F : PR 3) (a b W E J T x : PTm n) (e : Γ ⊢[PRAAx] a ≐ b)
    (h : Γ ⊢[PRAAx] compactInput F a W E J T x) : Γ ⊢[PRAAx] compactInput F b W E J T x := by
  let sh (u : PTm n) := Syn.shift u
  let body := compactInput F (var 0) (sh W) (sh E) (sh J) (sh T) (sh x)
  have hi : Γ ⊢[PRAAx] body.subst (Syn.inst a) := by
    simpa only [body,GaussianCompactRiemannName.subst_input,sh,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h
  simpa only [body,GaussianCompactRiemannName.subst_input,sh,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqSubst1 body e hi

private theorem rescaled_cross (F : PR 3) (D a b W E J T K U x : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (he : Γ ⊢[PRAAx] D*a ≐ b)
    (h : Γ ⊢[PRAAx] compactInput F a W E J T x) (hnew : Γ ⊢[PRAAx] compactInput F b (D*W) (D*E) K U x) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianCompactRiemannName.nameF F) (GaussianCompactRiemannName.nameF F)
      (compactEncoding a W E J T x) (compactEncoding b (D*W) (D*E) K U x) := by
  have scaled := GaussianCompactIntervalRescaling.scaled_input F D a W E J T x (.andI hD h)
  have relation := GaussianCompactIntervalRescaling.name_rescaling F D a W E J T x (.andI hD h)
  have reencode : Γ ⊢[PRAAx] compactEncoding (D*a) (D*W) (D*E) J T x ≐ compactEncoding b (D*W) (D*E) J T x :=
    congrPairT he (.eqRefl _)
  have first := GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ (.eqRefl _) reencode relation
  have second := GaussianCompactMeshIndependence.name_independence F b (D*W) (D*E) J T K U x
    (.andI (compact_start_congr F (D*a) b (D*W) (D*E) J T x he scaled) hnew)
  exact cross_trans _ _ _ _ _ _ first second

private theorem width_zero_bound (F : PR 3) (p s a W E J T x : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hz : Γ ⊢[PRAAx] W ≐ zero) : Γ ⊢[PRAAx]
    bounded (observation F p a W E J T x) (two*unit p+num 11*unit s) (unit s*unit p) := by
  have changeWidth : Γ ⊢[PRAAx] compactEncoding a W E J T x ≐ compactEncoding a zero E J T x :=
    congrPairT (.eqRefl _) (congrPairT hz (.eqRefl _))
  have eq := (congrAp2 (GaussianCompactRiemannName.nameF F) (.eqRefl p) changeWidth).eqTrans
    (GaussianCompactZeroWidth.observation_zero F p a E J T x hE)
  exact bound_congr eq.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerNamedUpperTail.zero_bound _ _ (positive_product _ _ (unit_positive s) (unit_positive p)))

theorem original_upper_tail_bound (s j p z R B A e f d h L Q S U E T a W : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S E T a W)
    (hU : Γ ⊢[PRAAx] le one U) (hu : Γ ⊢[PRAAx] le h (d*U))
    (hj : Γ ⊢[PRAAx] le (cutoff (panelStage s L+two) z R B A e f d h L Q) j)
    (htail : Γ ⊢[PRAAx] above j R A L Q U E a) : Γ ⊢[PRAAx]
    bounded (ap2 compactF p (compactData z R B e f d h Q S a W E T))
      (two*unit p+num 11*unit s) (unit s*unit p) := by
  let Epos := hs.andE₂.andE₂.andE₁
  refine .orE (zero_or_succ W) ?_ ?_
  · exact width_zero_bound evaluatorF p s a W E _ T _ Epos.wk Prf.hyp0
  · let V := cutoffSize j (Q*A) (L*R)
    let D := lowerDenominator S V L
    let β := upperNumerator U V L
    let C := upperPrefix a D
    let J := lipschitz R Q S E T
    let K := lipschitz R Q S (D*E) T
    let x := fixedData z B e f d h S
    let v := ap2 formulaF p (formulaData z R B A e f d h L Q)
    let Δ := (W ≐ succ (pred W)) :: Γ
    have orig : Δ ⊢[PRAAx] source z R B A e f d h L Q S E T a W := hs.wk
    have ed := orig.andE₂.andE₂.andE₁
    have wb : Δ ⊢[PRAAx] le one W := le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ (pred W))
    have pos := physical_cutoffs_positive j (Q*A) (L*R) L S U orig.andE₁.andE₂.andE₂.andE₂.andE₁
      orig.andE₂.andE₁.andE₂.andE₂.andE₁.andE₂ hU.wk
    have hD : Δ ⊢[PRAAx] le one D := le_trans (le_succ_self one) pos.andE₁
    have g := upper_geometry a W E T D β orig.andE₂.andE₂.andE₂.andE₁ ed pos.andE₁ htail.wk orig.andE₂.andE₂.andE₂.andE₂
    have ee := positive_product D E hD ed
    have whole : Δ ⊢[PRAAx] source z R B A e f d h L Q S (D*E) T one (C+D*W) :=
      .andI orig.andE₁ (.andI orig.andE₂.andE₁ (.andI ee (.andI (le_refl one) g.andE₂.andE₂.andE₂.andE₂)))
    have widen : Δ ⊢[PRAAx] le (one+C) (one+(C+D*W)) :=
      add_le_add₂ (le_refl one) (le_add_right C (D*W))
    have initial : Δ ⊢[PRAAx] source z R B A e f d h L Q S (D*E) T one C :=
      .andI orig.andE₁ (.andI orig.andE₂.andE₁ (.andI ee (.andI (le_refl one)
        (le_trans widen g.andE₂.andE₂.andE₂.andE₂))))
    have left : Δ ⊢[PRAAx] le (one*D) (D*E) := le_congr (one_mul D).eqSymm (.eqRefl _) g.andE₂.andE₂.andE₁
    have right := g.andE₂.andE₂.andE₂.andE₁
    have wholeRight : Δ ⊢[PRAAx] le ((D*E)*β) (one+(C+D*W)) :=
      le_trans right widen
    have rawFull := original_enclosing_observations s j p p z R B A e f d h L Q S U (D*E) T one (C+D*W)
      whole hU.wk hu.wk hj.wk left wholeRight
    have rawInitial := original_enclosing_observations s j p p z R B A e f d h L Q S U (D*E) T one C
      initial hU.wk hu.wk hj.wk left right
    have added := add_input evaluatorF one C (D*W) (D*E) K T x g.andE₁ (positive_product _ _ hD wb)
      (panel_input z R B A e f d h L Q S (D*E) T one (C+D*W) whole)
    have tail := suffix_bound evaluatorF p s one C (D*W) (D*E) K T x v added
      (same_clock s p _ _ rawFull) (same_clock s p _ _ rawInitial)
    have relation := rescaled_cross evaluatorF D a (one+C) W E J T K T x hD g.andE₂.andE₁.eqSymm
      (panel_input z R B A e f d h L Q S E T a W orig)
      (GaussianCompactNamedAdditivity.right_input evaluatorF one C (D*W) (D*E) K T x added)
    exact transfer_bound evaluatorF p s _ _ relation tail

theorem original_lower_tail_bound (s j p z R B A e f d h L Q S U E T a W : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S E T a W)
    (hU : Γ ⊢[PRAAx] le one U) (hu : Γ ⊢[PRAAx] le h (d*U))
    (hj : Γ ⊢[PRAAx] le (cutoff (panelStage s L+two) z R B A e f d h L Q) j)
    (htail : Γ ⊢[PRAAx] below j R A L Q S E a W) : Γ ⊢[PRAAx]
    bounded (ap2 compactF p (compactData z R B e f d h Q S a W E T))
      (two*unit p+num 11*unit s) (unit s*unit p) := by
  let Epos := hs.andE₂.andE₂.andE₁
  refine .orE (zero_or_succ W) ?_ ?_
  · exact width_zero_bound evaluatorF p s a W E _ T _ Epos.wk Prf.hyp0
  · let V := cutoffSize j (Q*A) (L*R)
    let D := lowerDenominator S V L
    let β := upperNumerator U V L
    let C := lowerSuffix a W E β
    let T' := T+β
    let J := lipschitz R Q S E T
    let K := lipschitz R Q S E T'
    let x := fixedData z B e f d h S
    let v := ap2 formulaF p (formulaData z R B A e f d h L Q)
    let Δ := (W ≐ succ (pred W)) :: Γ
    have orig : Δ ⊢[PRAAx] source z R B A e f d h L Q S E T a W := hs.wk
    have ed := orig.andE₂.andE₂.andE₁
    have ha := orig.andE₂.andE₂.andE₂.andE₁
    have wb : Δ ⊢[PRAAx] le one W := le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ (pred W))
    have pos := physical_cutoffs_positive j (Q*A) (L*R) L S U orig.andE₁.andE₂.andE₂.andE₂.andE₁
      orig.andE₂.andE₁.andE₂.andE₂.andE₁.andE₂ hU.wk
    have g := lower_geometry a W E T D β ed (le_trans (le_succ_self one) pos.andE₁) pos.andE₂ htail.wk
    have end' : Δ ⊢[PRAAx] le ((a+W)+C) (T'*E) := le_congr (by ipra_ring) (.eqRefl _) g.andE₂.andE₂.andE₂
    have whole : Δ ⊢[PRAAx] source z R B A e f d h L Q S E T' a (W+C) :=
      .andI orig.andE₁ (.andI orig.andE₂.andE₁ (.andI ed (.andI ha g.andE₂.andE₂.andE₂)))
    have rest : Δ ⊢[PRAAx] source z R B A e f d h L Q S E T' (a+W) C :=
      .andI orig.andE₁ (.andI orig.andE₂.andE₁ (.andI ed (.andI (le_trans ha (le_add_right a W)) end')))
    have right : Δ ⊢[PRAAx] le (E*β) ((a+W)+C) := le_congr (.eqRefl _) g.andE₂.andE₁.eqSymm (le_refl _)
    have wholeRight : Δ ⊢[PRAAx] le (E*β) (a+(W+C)) := le_congr (.eqRefl _) (by ipra_ring) right
    have rawFull := original_enclosing_observations s j p p z R B A e f d h L Q S U E T' a (W+C)
      whole hU.wk hu.wk hj.wk g.andE₂.andE₂.andE₁ wholeRight
    have rawRest := original_enclosing_observations s j p p z R B A e f d h L Q S U E T' (a+W) C
      rest hU.wk hu.wk hj.wk htail.wk right
    have added := add_input evaluatorF a W C E K T' x wb g.andE₁ (panel_input z R B A e f d h L Q S E T' a (W+C) whole)
    have tail := prefix_bound evaluatorF p s a W C E K T' x v added (same_clock s p _ _ rawFull) (same_clock s p _ _ rawRest)
    have relation := GaussianCompactMeshIndependence.name_independence evaluatorF a W E J T K T' x
      (.andI (panel_input z R B A e f d h L Q S E T a W orig)
        (GaussianCompactNamedAdditivity.left_input evaluatorF a W C E K T' x added))
    exact transfer_bound evaluatorF p s _ _ relation tail

theorem actual_rational_power_damped_arbitrary_physical_tails_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 19
      ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13)
          (var 15) (var 16) (var 17) (var 18) ⋏
        ((le one (var 14) ⋏ le (var 10) (var 9*var 14)) ⋏
          le (cutoff (panelStage (var 0) (var 11)+two) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
            (var 9) (var 10) (var 11) (var 12)) (var 1))) ⟶
        ((above (var 1) (var 4) (var 6) (var 11) (var 12) (var 14) (var 15) (var 17) ⟶
          bounded (ap2 compactF (var 2) (compactData (var 3) (var 4) (var 5) (var 7) (var 8) (var 9) (var 10)
            (var 12) (var 13) (var 17) (var 18) (var 15) (var 16)))
            (two*unit (var 2)+num 11*unit (var 0)) (unit (var 0)*unit (var 2))) ⋏
         (below (var 1) (var 4) (var 6) (var 11) (var 12) (var 13) (var 15) (var 17) (var 18) ⟶
          bounded (ap2 compactF (var 2) (compactData (var 3) (var 4) (var 5) (var 7) (var 8) (var 9) (var 10)
            (var 12) (var 13) (var 17) (var 18) (var 15) (var 16)))
            (two*unit (var 2)+num 11*unit (var 0)) (unit (var 0)*unit (var 2))))) :=
  closeUniv 19 (.impI (.andI
    (.impI (original_upper_tail_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1.andE₁
      Prf.hyp1.andE₂.andE₁.andE₁ Prf.hyp1.andE₂.andE₁.andE₂ Prf.hyp1.andE₂.andE₂ Prf.hyp0))
    (.impI (original_lower_tail_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1.andE₁
      Prf.hyp1.andE₂.andE₁.andE₁ Prf.hyp1.andE₂.andE₁.andE₂ Prf.hyp1.andE₂.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingArbitraryTails
